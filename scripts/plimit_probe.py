# Session 74 (notes/erdos-470.md): a decider for the sub-tree below a prefix n when the next prime p is LIMIT-DEFICIENT
# (sigma(n) p <= 2 n (p-1), so n p^f is deficient for EVERY f and Lean's fLoop never stops). Python only; it measures
# whether a staircase design closes real sub-trees, and how much work it needs. Decides nothing about #470 (no owf).
#
# Target (same as Lean's subOK, stars r^h with h >= 2 excluded): for all primes p < q < r, none dividing n, all f, e >= 1,
# N = n p^f q^e r is not weird. Tools (all exact integer tests; m always coprime to the new prime):
#   * abundant with interval: IntervalGap chain n -> p^f -> q^e (-> r) with stepOK at every prime (c, g kept), then
#     c <= N and N + c <= sum D(N)  ==> N pseudoperfect, and so are all its multiples (covers every larger r too).
#     Monotone in each exponent (excess A(f+1) = p A(f) + sigma(m) >= A(f)), so an up-set in (f, e).
#   * limit bound: sigma(m) p <= 2 m (p-1) ==> m p^f is not abundant for any f (a whole row / column strip).
#   * deficient exact point with free last prime r: lastOK (all r at once), as in Lean's leafOK.
# Per pair (p, q):
#   pair limit L2 = sigma(n)/n * p/(p-1) * q/(q-1).
#   L2 <= 2: r is bounded (L2 (r+1)/r <= 2 beyond R*); every (p, q, r) is a 2-D staircase with no free prime.
#   L2 >  2: 2-D staircase on (f, e) with a free last prime r: corner points are abOK or lastOK; row / column strips
#            (one exponent fixed, the other free and limit-deficient) bound r and become 1-D loops.
# Staircase on (f, e) (both >= 1): e_inf = first row whose limit (in f) is > 2, f_inf = first such column;
#   rows e < e_inf and columns f < f_inf are strips; f_row = first f with abOK on row e_inf, e_col = first e with abOK on
#   column f_inf; the box [f_inf, f_row) x [e_inf, e_col) is checked point by point; the rest is abundant by monotonicity.
# Env: FASTSTRIP=1 swapped loops in strips with free r; BOUNDED=1 pairs with L2 < 2 by one staircase for all r (session 75); QTRACE=1 one line per q; CAP max exponent.
# Usage: python3 -I scripts/plimit_probe.py --plan 'p^e*p^e*p^e' LIMB p [p ...]      (c, g from plan4, as subok_cost_probe)
#        python3 -I scripts/plimit_probe.py N S c g p [p ...]
#        p = 0 (with --plan): every prime p above the prefix up to the three-prime tail.
import os, sys, time
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import subok_cost_probe as SP

CAP = int(os.environ.get('CAP', '400'))       # max exponent tried in any 1-D loop (fail beyond: incomplete, not unsound)
W = dict(pts=0, lastq=0, strips=0, triples=0, pairs=0, rsteps=0, win=0)

def sig_pp(p, e): return (p ** (e + 1) - 1) // (p - 1)
def isprime(x): return x > 2 and x % 2 == 1 and all(x % d for d in range(3, int(x ** 0.5) + 1, 2))
def step(N, S, c, g, q): return SP.stepOK(N, S, c, g, q)

class Ctx:
    def __init__(s, n, S, c, g): s.n, s.S, s.c, s.g = n, S, c, g

def chain(C, parts):
    """IntervalGap chain n -> parts (list of (prime, exp)); returns (N, sum D(N), ok)."""
    N, S, ok = C.n, C.S, True
    for q, e in parts:
        if not step(N, S, C.c, C.g, q): ok = False
        S = (S + N) * sig_pp(q, e) - N * q ** e; N *= q ** e
    return N, S, ok

def point(C, parts, free_r):
    """One exact point. free_r: the last prime r is still free (lastOK if deficient)."""
    W['pts'] += 1
    N, S, ok = chain(C, parts)
    if ok and C.c <= N and N + C.c <= S: return True               # pseudoperfect with interval (multiples too)
    if S <= N:                                                     # deficient (or perfect: S = N impossible for odd > 1? keep exact)
        if not free_r: return True                                 # not abundant, nothing above it
        if S == N: return False
        v, k = SP.lastOK(N, S, C.c, C.g, (N + S) // (N - S) + 1); W['lastq'] += k
        return v and ok
    return False                                                   # abundant without an interval certificate

def row_limit_def(C, fixed, p):
    """sigma(m) p <= 2 m (p-1) for m = n * fixed: m p^f not abundant for every f."""
    N, S, _ = chain(C, fixed)
    return (S + N) * p <= 2 * N * (p - 1)

def line(C, fixed, p, free_r, order):
    """1-D loop over the exponent of p with the rest fixed: all f >= 1 fine?"""
    if not free_r and row_limit_def(C, fixed, p): return True
    for f in range(1, CAP):
        parts = order(fixed, (p, f))
        N, S, ok = chain(C, parts)
        if ok and C.c <= N and N + C.c <= S: return True          # abOK here, so for every larger f
        if not point(C, parts, free_r): return False
    return False

def strip(C, fixed, p, q_or_r_lo, free_r, order):
    """Strip: `fixed` exponents, p free and limit-deficient on it. If free_r, r is bounded by the limit and every r below
    the bound is a 1-D loop; above it nothing is abundant."""
    W['strips'] += 1
    N, S, _ = chain(C, fixed)
    if not free_r: return line(C, fixed, p, False, order)
    if os.environ.get('FASTSTRIP') == '1': return strip_fast(C, fixed, p, q_or_r_lo, order)
    # m p^f r: ratio < sigma(m)/m * p/(p-1) * (r+1)/r <= 2 once r >= R
    A, B = (S + N) * p, 2 * N * (p - 1)                           # A/B < 1 (limit-deficient strip)
    if A > B: return None                                          # not a strip
    if A == B: return False
    R = A // (B - A) + 1                                           # A (R+1) <= B R
    r = q_or_r_lo
    while r < R:
        W['rsteps'] += 1
        if isprime(r) and C.n % r:
            if not line(C, fixed + [(r, 1)], p, False, order): return False
        r += 2
    return True

def strip_fast(C, fixed, p, r_lo, order):
    """FASTSTRIP=1: the same strip with the loops swapped. For each f (M = m p^f deficient, sigma = S + M, D = 2M - sigma):
    M r is abundant iff r D < sigma, and certified (abOK of M r) iff stepOK(M, S, c, g, r), c <= M r and r D <= sigma - c.
    Both are r-intervals (closed form in Lean: pseudoperfect_mul_prime_of_range), and certification is monotone in f, so stop
    at the first f where every prime r in [r_lo, R) is certified; r >= R is never abundant (limit bound)."""
    N0, S0, _ = chain(C, fixed)
    A, B = (S0 + N0) * p, 2 * N0 * (p - 1)
    if A >= B: return False
    R = A // (B - A) + 1
    def bad(r): return isprime(r) and C.n % r                      # a prime r that would need its own certificate
    def any_bad(lo, hi):                                           # some bad odd r in [lo, hi]? (only small windows scanned)
        lo += (lo % 2 == 0)
        return any(bad(r) for r in range(lo, hi + 1, 2))
    lo = r_lo
    top = R - 1                                                    # every r in [lo, top] must end up certified
    while top >= lo and not bad(top): top -= 1                     # largest bad r below R (a few steps)
    if top < lo: return True
    for f in range(1, CAP):
        W['pts'] += 1
        M, S, ok = chain(C, order(fixed, (p, f)))
        sg = S + M; D = 2 * M - sg
        if D <= 0 or not ok: return False
        ab_hi = (sg - 1) // D                                      # r <= ab_hi: M r abundant
        cert_hi = min((sg - C.c) // D, (S + 1 - 2 * C.c) // C.g)   # r <= cert_hi: excess >= c and q g + 2c <= S + 1
        cert_lo = max(-(-(M + 2 * C.c - 1) // S) - 1, -(-C.c // M))  # (r + 1) S + 1 >= M + 2c and c <= M r
        if any_bad(lo, min(cert_lo - 1, ab_hi, top)): return False # abundant below the certified range
        w_lo, w_hi = max(lo, cert_hi + 1), min(ab_hi, top)
        if w_hi - w_lo > 10 ** 6: return False                     # window too large to scan (not expected)
        W['win'] += max(0, (w_hi - w_lo) // 2 + 1)
        if any_bad(w_lo, w_hi): return False                       # abundant but not certified
        if cert_hi >= top: return True                             # every bad r < R certified from this f on
    return False

SIEVE = bytearray()
def bad_sieve(C, X):
    """bytearray s with s[r] = 1 iff r < X is an odd prime not dividing n (cached; grows on demand)."""
    global SIEVE
    if len(SIEVE) < X:
        X = max(X, 2 * len(SIEVE))
        s = bytearray([1]) * X; s[0:2] = b'\x00\x00'
        for i in range(2, int(X ** 0.5) + 1):
            if s[i]: s[i * i::i] = bytearray(len(range(i * i, X, i)))
        s[2] = 0
        for i in range(3, min(X, 10 ** 6), 2):
            if s[i] and C.n % i == 0: s[i] = 0
        SIEVE = s
    return SIEVE

def stair_bounded(C, p, q, R):
    """BOUNDED=1: pair (p, q) with pair limit L2 < 2, so only primes r in (q, R) matter, all at once. Staircase on (f, e)
    over M = n p^f q^e (always deficient here); per point, M r is abundant iff r <= ab_hi = (sigma-1)//D, certified (IntervalGap
    chain n -> p^f -> q^e -> r) iff r in [cert_lo, cert_hi]; a 'bad' prime (odd prime, r not dividing n) that is abundant but
    not certified is a failure (returned). Row e (q^e fixed, p free) only needs r < R_e (its limit bound), column f likewise;
    a point where every relevant bad r is certified ends its row/column (certification is monotone in each exponent).
    Returns (ok, info)."""
    s = bad_sieve(C, R + 1)
    lo0 = s.find(1, q + 2, R)
    if lo0 < 0: return True, 'no r'
    def top_below(X):                                              # largest bad prime in [q+2, min(X, R)) or -1
        return s.rfind(1, q + 2, min(X, R))
    def rbound(fixed, x):                                          # relevant r for the line where x is free: r < bound
        N, S, _ = chain(C, fixed)
        A, B = (S + N) * x, 2 * N * (x - 1)
        if A >= B: return R
        return min(R, -(-A // (B - A)))
    def check(f, e, top):
        """Point (f, e), relevant bad r in [q+2, top]. Returns 'full' (every such r certified), 'ok', or ('fail', r)."""
        W['pts'] += 1
        M, S, ok = chain(C, [(p, f), (q, e)])
        sg = S + M; D = 2 * M - sg
        if D <= 0: return ('fail', 'M abundant')
        ab_hi = min((sg - 1) // D, top)
        if ab_hi < lo0: return 'ok'
        if not ok: r = s.find(1, q + 2, ab_hi + 1); return ('fail', r) if r >= 0 else 'ok'
        cert_hi = min((sg - C.c) // D, (S + 1 - 2 * C.c) // C.g)
        cert_lo = max(-(-(M + 2 * C.c - 1) // S) - 1, -(-C.c // M))
        r = s.find(1, q + 2, min(cert_lo, ab_hi + 1))
        if r >= 0: return ('fail', r)
        if cert_hi < ab_hi:
            W['win'] += ab_hi - cert_hi
            r = s.find(1, max(q + 2, cert_hi + 1), ab_hi + 1)
            if r >= 0: return ('fail', r)
        return 'full' if cert_hi >= top else 'ok'
    def line(start, fixedfun, varfun, top):
        """1-D loop: exponent k from start until 'full'."""
        for k in range(start, CAP):
            v = check(*varfun(k), top)
            if v == 'full': return True, k
            if v != 'ok': return False, (varfun(k), v)
        return False, ('cap',)
    topR = top_below(R)
    if topR < 0: return True, 'no r'
    e_s = 1                                                        # rows e < e_s: R_e <= topR
    while True:
        Re = rbound([(q, e_s)], p)
        if Re > topR: break
        t = top_below(Re)
        if t >= 0:
            ok, info = line(1, None, lambda f, e=e_s: (f, e), t)
            if not ok: return False, ('row', e_s, info)
        e_s += 1
        if e_s > CAP: return False, 'ecap'
    f_s = 1
    while True:
        Rf = rbound([(p, f_s)], q)
        if Rf > topR: break
        t = top_below(Rf)
        if t >= 0:
            ok, info = line(e_s, None, lambda e, f=f_s: (f, e), t)
            if not ok: return False, ('col', f_s, info)
        f_s += 1
        if f_s > CAP: return False, 'fcap'
    ok, f_row = line(f_s, None, lambda f: (f, e_s), topR)
    if not ok: return False, ('corner-row', f_row)
    ok, e_col = line(e_s, None, lambda e: (f_s, e), topR)
    if not ok: return False, ('corner-col', e_col)
    for f in range(f_s, f_row):
        for e in range(e_s, e_col):
            v = check(f, e, topR)
            if v not in ('ok', 'full'): return False, ('box', f, e, v)
    return True, (e_s, f_s, f_row, e_col)

def stair(C, p, q, rfix):
    """All (f, e) >= (1, 1) for n p^f q^e (r^1 if rfix, else r free > q)."""
    free_r = rfix is None
    tail = [] if free_r else [(rfix, 1)]
    ordP = lambda fixed, pf: [pf] + fixed                          # chain order p first
    # rows: q^e fixed, p free; columns: p^f fixed, q free
    def rowdef(e): return row_limit_def(C, [(q, e)] + tail, p)
    def coldef(f): return row_limit_def(C, [(p, f)] + tail, q)
    e_inf = 1
    while rowdef(e_inf):
        if e_inf > CAP: return False
        e_inf += 1
    f_inf = 1
    while coldef(f_inf):
        if f_inf > CAP: return False
        f_inf += 1
    for e in range(1, e_inf):                                      # row strips (p free)
        if not strip(C, [(q, e)] + tail, p, q + 2, free_r, lambda fx, pf: [pf] + fx): return False
    for f in range(1, f_inf):                                      # column strips (q free)
        if not strip(C, [(p, f)] + tail, q, q + 2, free_r, lambda fx, qe: [fx[0], qe] + fx[1:]): return False
    def ab(f, e):
        N, S, ok = chain(C, [(p, f), (q, e)] + tail); return ok and C.c <= N and N + C.c <= S
    f_row = f_inf
    while not ab(f_row, e_inf):
        if f_row > CAP: return False
        f_row += 1
    e_col = e_inf
    while not ab(f_inf, e_col):
        if e_col > CAP: return False
        e_col += 1
    for f in range(f_inf, f_row):
        for e in range(e_inf, e_col):
            if not ab(f, e) and not point(C, [(p, f), (q, e)] + tail, free_r): return False
    return True

def decide_q(C, pre, q):
    """Prefix n * pre (exact), next prime q with free exponent e and a free last prime r > q."""
    N, S, _ = chain(C, pre)
    if (S + N) * q <= 2 * N * (q - 1):                             # q limit-deficient: r bounded, 1-D line in e per r
        A, B = (S + N) * q, 2 * N * (q - 1)
        if A == B: return False
        if os.environ.get('BOUNDED') == '1':                       # session 75: same strip, closed-form r-ranges per e
            return strip_fast(C, pre, q, q + 2, lambda fx, qe: fx + [qe])
        R = A // (B - A) + 1; r = q + 2
        k = len(pre)
        while r < R:
            W['rsteps'] += 1
            if isprime(r) and C.n % r:
                if not line(C, pre + [(r, 1)], q, False, lambda fx, qe: fx[:k] + [qe] + fx[k:]): return False
            r += 2
        return True
    for e in range(1, CAP):                                        # exponent loop until abundant with an interval
        N2, S2, ok = chain(C, pre + [(q, e)])
        if ok and C.c <= N2 and N2 + C.c <= S2: return True
        if not point(C, pre + [(q, e)], True): return False
    return False

def decide_qs(C, pre, p):
    """All q > p (r > q) below the prefix n * pre: q loop up to the two-prime tail of the exact prefix."""
    N, S, _ = chain(C, pre)
    if S >= N: return False                                        # abundant prefix without interval: not handled
    Q = p + 2
    while not ((S + N) * (Q + 1) <= 2 * N * (Q - 1)): Q += 2
    q = p + 2
    while q < Q:
        if isprime(q) and C.n % q:
            W['pairs'] += 1
            if not decide_q(C, pre, q): return False
        q += 2
    return True

def decide_p(C, p):
    """Every q > p (and r > q) below p."""
    if not ((C.S + C.n) * p <= 2 * C.n * (p - 1)):                  # not limit-deficient: exponent loop (Lean's fLoop)
        for f in range(1, CAP):
            N, S, ok = chain(C, [(p, f)])
            if ok and C.c <= N and N + C.c <= S: return 'f-loop', []
            if not decide_qs(C, [(p, f)], p): return 'f-loop', [('f', f)]
        return 'f-loop', [('fcap',)]
    # two-prime tail: sigma(n) p (Q+1) <= 2 n (p-1) (Q-1)  ==> no q >= Q (and r > q) gives an abundant n p^f q^e r
    Q = p + 2
    while not ((C.S + C.n) * p * (Q + 1) <= 2 * C.n * (p - 1) * (Q - 1)): Q += 2
    q = p + 2; fails = []
    while q < Q:
        if isprime(q) and C.n % q:
            W['pairs'] += 1; tq = time.time(); wq = dict(W)
            L2n, L2d = (C.S + C.n) * p * q, C.n * (p - 1) * (q - 1)
            if L2n <= 2 * L2d:                                     # r bounded
                if L2n == 2 * L2d: fails.append((q, 'L2=2')); q += 2; continue
                R = L2n // (2 * L2d - L2n) + 1
                if os.environ.get('BOUNDED') == '1':
                    W['triples'] += 1
                    okb, info = stair_bounded(C, p, q, R)
                    if not okb: fails.append((q, 'bounded', info))
                    if os.environ.get('QTRACE') == '1': print('   q=%d R=%d bounded %s %s' % (q, R, okb, info), flush=True)
                    q += 2; continue
                r = q + 2
                while r < R:
                    if isprime(r) and C.n % r:
                        W['triples'] += 1
                        if not stair(C, p, q, r): fails.append((q, r)); break
                    r += 2
            else:
                if not stair(C, p, q, None): fails.append((q, 'free r'))
            if os.environ.get('QTRACE') == '1':
                print('   q=%d L2>2=%s %.2fs %s' % (q, L2n > 2 * L2d, time.time() - tq, {k: W[k] - wq[k] for k in W if W[k] != wq[k]}), flush=True)
        q += 2
    return Q, fails

if __name__ == '__main__':
    a = sys.argv[1:]
    if a[0] == '--plan':
        import subprocess
        out = subprocess.run([sys.executable, '-I', os.path.join(os.path.dirname(os.path.abspath(__file__)), 'subok_cost_probe.py'),
                              '--plan', a[1], a[2], '3', '0', '1', '1', '1', '1'], capture_output=True, text=True).stdout
        line0 = [l for l in out.splitlines() if l.startswith('plan ')][0].split()
        n, S, c, g = int(line0[3]), int(line0[5]), int(line0[9]), int(line0[11]); ps = list(map(int, a[3:]))
        print(' '.join(line0))
    else:
        n, S, c, g = map(int, a[:4]); ps = list(map(int, a[4:]))
    C = Ctx(n, S, c, g)
    if ps == [0]:                        # p = 0: every odd prime p > the prefix's largest prime, up to the three-prime tail
        p0 = max(int(t.split('^')[0]) for t in a[1].split('*')) + 2 if a[0] == '--plan' else 3
        Q3 = p0 + (p0 % 2 == 0)
        while not ((S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1)): Q3 += 2
        ps = [x for x in range(p0, Q3, 2) if isprime(x) and n % x]
        print('three-prime tail Q3 =', Q3, 'primes p:', len(ps), flush=True)
    t_all = time.time(); nf = 0
    for p in ps:
        t = time.time(); w0 = dict(W)
        limdef = (S + n) * p <= 2 * n * (p - 1)
        Q, fails = decide_p(C, p)
        print('p=%d limit-deficient=%s mode/tail Q=%s fails=%s %.1fs work=%s' % (p, limdef, Q, fails[:6],
              time.time() - t, {k: W[k] - w0[k] for k in W}), flush=True)
        nf += bool(fails)
    print('TOTAL p', len(ps), 'failing p', nf, '%.1fs' % (time.time() - t_all), W, flush=True)
