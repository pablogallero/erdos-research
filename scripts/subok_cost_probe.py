# Session 74 (notes/erdos-470.md): cost of the Lean Boolean `subOK` (ErdosResearch/SubsetSumBlock.lean), measured in Python.
# Exact port of pLoop / fLoop / blockOK / qBlock / eLoop / rLoop / eLoop0 / leafOK / lastOK / stepOK / abOK / ppSum / skipB,
# with the SAME short-circuit order as the Lean definitions, plus counters of the work the kernel would do:
#   lastq  = q values scanned by lastOK's List.range B (charged up to the first failing q, else B),
#   eIt / e0It / rIt / qIt / fIt / pIt = iterations of eLoop / eLoop0 / rLoop / qBlock / fLoop / pLoop,
#   skip   = skipB calls (one gcd with P1000 each).
# lastOK is evaluated in closed form (the failing q form at most two integer intervals; n is odd so any even q in
# them fails), checked against the literal loop by SELFTEST=1.
# Python only, decides nothing about #470 (no owf, no search). Usage:
#   python3 -I scripts/subok_cost_probe.py N S c g p0 kp Kf Kq K Kr [BUDGET]
#   python3 -I scripts/subok_cost_probe.py --base 'p^e*p^e*...' p0 kp Kf Kq K Kr [BUDGET]   (exact c, g by bitset; small n)
#   python3 -I scripts/subok_cost_probe.py --plan 'p^e*p^e*p^e' LIMB p0 kp Kf Kq K Kr [BUDGET]  (real prefix; plan4)
#   SELFTEST=1 python3 -I scripts/subok_cost_probe.py
#   kp = -1: smallest three-prime tail; CONT=1: go on after a failing p and list them all.
#   FTRACE=1 prints one line per (p, f) with its cost.
import os, sys, time
from math import gcd

def primes_upto(m):
    s = bytearray([1]) * (m + 1); s[0] = s[1] = 0
    for i in range(2, int(m ** 0.5) + 1):
        if s[i]: s[i * i::i] = bytearray(len(s[i * i::i]))
    return [i for i in range(m + 1) if s[i]]

P1000 = 1
for _p in primes_upto(1000):
    if _p > 2: P1000 *= _p

C = dict(lastq=0, eIt=0, e0It=0, rIt=0, qIt=0, fIt=0, pIt=0, skip=0)
BUDGET = [10 ** 12]

class Budget(Exception): pass

def charge(k, v=1):
    C[k] += v
    if C['lastq'] + 50 * (C['eIt'] + C['e0It'] + C['rIt'] + C['qIt']) > BUDGET[0]: raise Budget()

P31 = 3 * 5 * 7 * 11 * 13 * 17 * 19 * 23 * 29 * 31
_PR = set(primes_upto(10 ** 6))
SMALL = [x for x in primes_upto(97) if x > 2]
SKIP = os.environ.get('SKIP', 'old')   # old = Lean skipB; small = skipB || some odd prime s <= 97, s < q, divides q; gcd2 = skipB || gcd(q, P31) not in {1, q}; oracle = exact
def skipB(q, P=P1000):
    charge('skip')
    if SKIP == 'oracle': return q not in _PR
    if gcd(q, P) != 1 and P % q != 0: return True
    if SKIP == 'gcd2': g_ = gcd(q, P31); return g_ != 1 and g_ != q
    if SKIP == 'small': return any(q % s_ == 0 and s_ < q for s_ in SMALL)
    return False

def ppSum(n, q, S, f):
    s = S
    for _ in range(f): s = S + (n + q * s)
    return s

def stepOK(n, S, c, g, q): return q * g + 2 * c <= S + 1 and n + 2 * c <= (q + 1) * S + 1
def abOK(n, S, c, q, e): N = n * q ** e; return c <= N and N + c <= ppSum(n, q, S, e)

def q_ok(n, S, c, g, q):
    return (q < 2 or n % q == 0 or not (n * q < S + (n + q * S)) or
            (q * g + 2 * c <= S + 1 and n + 2 * c <= (q + 1) * S + 1 and c <= n * q and n * q + c <= S + (n + q * S)))

def lastOK_slow(n, S, c, g, B):
    if not (S < n and n + S < B * (n - S)): return False, 0
    for q in range(B):
        if not q_ok(n, S, c, g, q): return False, q + 1
    return True, B

def cdiv(a, b): return -((-a) // b)

def lastOK(n, S, c, g, B):
    """Closed form of lastOK; returns (value, q values the kernel scans)."""
    if not (S < n and n + S < B * (n - S)): return False, 0
    d = n - S
    hi = min(B, cdiv(S + n, d))          # q < hi: n q abundant (the only q that can fail)
    lo_ok = max(2, cdiv(n + 2 * c - 1, S) - 1 if S > 0 else 10 ** 30, cdiv(c, n) if n else 0)
    hi_ok = min((S + 1 - 2 * c) // g, (S + n - c) // d)   # q <= hi_ok
    bad = []                             # failing intervals inside [2, hi)
    if lo_ok > hi_ok: bad.append((2, hi))
    else:
        bad.append((2, min(lo_ok, hi))); bad.append((max(hi_ok + 1, 2), hi))
    first = None
    for a, b in bad:
        if a >= b: continue
        q = a
        while q < b:                     # stops at the first even q at the latest (n odd) or the first non-divisor
            if not q_ok(n, S, c, g, q):
                first = q if first is None else min(first, q); break
            q += 1
    if first is not None: return False, first + 1
    return True, B

def lastOK_c(n, S, c, g, B):
    v, k = lastOK(n, S, c, g, B); charge('lastq', k); return v

def leafOK(n, S, c, g, e, q):
    if not (q * g + 2 * c <= S + 1 and n + 2 * c <= (q + 1) * S + 1): return False
    N, T = n * q ** e, ppSum(n, q, S, e)
    if c <= N and N + c <= T: return True
    if N <= T: return lastOK_c(N, T, c, g, 1)   # Lean: N - T = 0, x / 0 = 0, B = 1; lastOK then fails on S < n
    return lastOK_c(N, T, c, g, (N + T) // (N - T) + 1)

def eLoop(n, S, c, g, q, e, k):
    while k > 0:
        charge('eIt')
        if stepOK(n, S, c, g, q) and abOK(n, S, c, q, e): return True
        if not leafOK(n, S, c, g, e, q): return False
        e += 1; k -= 1
    return False

def eLoop0(n, S, c, g, q, e, k):
    while k > 0:
        charge('e0It')
        if stepOK(n, S, c, g, q) and abOK(n, S, c, q, e): return True
        if not (ppSum(n, q, S, e) <= n * q ** e): return False
        e += 1; k -= 1
    return False

def rLoop(n, S, c, g, K, q, r, k):
    while k > 0:
        charge('rIt')
        if (S + n) * q * (r + 1) <= 2 * n * (q - 1) * r: return True
        if not (skipB(r) or n % r == 0 or (stepOK(n, S, c, g, r) and eLoop0(n * r, S + (n + r * S), c, g, q, 1, K))):
            return False
        r += 2; k -= 1
    return False

STAT = {}
def qBlock(n, S, c, g, K, Kr, q, k):
    while k > 0:
        charge('qIt')
        if not (skipB(q) or n % q == 0 or eLoop(n, S, c, g, q, 1, K) or rLoop(n, S, c, g, K, q, q + 2, Kr)):
            STAT['qfail'] = q; return False
        q += 2; k -= 1
    return True

def blockOK(n, S, c, g, K, Kr, q0, k):
    Q = q0 + 2 * k
    return q0 % 2 == 1 and 2 <= Q and (S + n) * (Q + 1) <= 2 * n * (Q - 1) and qBlock(n, S, c, g, K, Kr, q0, k)

def min_tail_Q(n, S, q0):
    """Smallest odd Q >= q0 with (S+n)(Q+1) <= 2n(Q-1), or None if n is not deficient."""
    d = 2 * n - (S + n)
    if d <= 0: return None
    Q = max(q0, cdiv(2 * n + S + n, d))
    return Q + (Q % 2 == 0)

def fLoop(n, S, c, g, K, Kr, Kq, p, f, k):
    while k > 0:
        charge('fIt')
        if not stepOK(n, S, c, g, p): STAT['why'] = ('step', p, f); return False
        if abOK(n, S, c, p, f): return True
        N, T = n * p ** f, ppSum(n, p, S, f)
        # Kq: if negative, the adaptive choice "smallest tail Q" (what a generator would emit)
        kq = Kq
        if Kq < 0:
            Q = min_tail_Q(N, T, p + 2)
            if Q is None: STAT['why'] = ('abundant-no-interval', p, f); return False
            kq = (Q - (p + 2)) // 2
        t0 = dict(C)
        ok = blockOK(N, T, c, g, K, Kr, p + 2, kq)
        if os.environ.get('FTRACE') == '1':
            print('  p=%d f=%d sigma/n=%.6f kq=%d ok=%s cost=%s' % (p, f, (N + T) / N, kq, ok,
                  {a: C[a] - t0[a] for a in C if C[a] != t0[a]}), flush=True)
        if not ok: STAT['why'] = ('block', p, f, kq, STAT.get('qfail')); return False
        f += 1; k -= 1
    STAT['why'] = ('ffuel', p); return False

def subOK(n, S, c, g, K, Kr, Kq, Kf, p0, k):
    if k < 0:                            # adaptive: smallest Q with the three-prime tail
        Q = p0
        while not ((S + n) * Q * (Q + 1) <= 2 * n * (Q - 1) * (Q - 1)): Q += 2
        k = (Q - p0) // 2; print('three-prime tail Q =', Q, flush=True)
    Q = p0 + 2 * k
    fails = []
    if not (p0 % 2 == 1 and 2 <= Q and (S + n) * Q * (Q + 1) <= 2 * n * (Q - 1) * (Q - 1)): return 'tail-fails'
    p = p0
    for _ in range(k):
        charge('pIt')
        t0 = dict(C); tt = time.time()
        if not (skipB(p) or n % p == 0):
            ok = fLoop(n, S, c, g, K, Kr, Kq, p, 1, Kf)
            print('p=%d ok=%s %.1fs cost=%s %s' % (p, ok, time.time() - tt,
                  {a: C[a] - t0[a] for a in C if C[a] != t0[a]}, '' if ok else STAT.get('why')), flush=True)
            if not ok:
                fails.append((p, STAT.get('why')))
                if os.environ.get('CONT') != '1': return False
        p += 2
    if fails: print('failing p:', fails); return False
    return True

def sigma_f(fs):
    s = 1
    for p, e in fs: s *= (p ** (e + 1) - 1) // (p - 1)
    return s

def base_cg(fs):
    """Exact smallest c with SS(D n) ⊇ [c, S−c] and the max gap g of SS(D n) (bitset; small n only)."""
    n = 1
    for p, e in fs: n *= p ** e
    D = [d for d in range(1, n) if n % d == 0]
    S = sum(D); bits = 1
    for d in D: bits |= bits << d
    ss = [i for i in range(S + 1) if bits >> i & 1]
    g = max(b - a for a, b in zip(ss, ss[1:]))
    c = 0
    while c <= S - c and any(not (bits >> i & 1) for i in range(c, S - c + 1)): c += 1
    # minimal c: first index from which everything up to S-c is present (symmetric)
    return n, S, c, g

def selftest():
    import random
    rnd = random.Random(74); bad = 0
    for _ in range(20000):
        n = rnd.randrange(3, 4000) | 1; S = rnd.randrange(0, n + 50); c = rnd.randrange(0, 60); g = rnd.randrange(1, 9)
        B = rnd.randrange(0, 300)
        if lastOK(n, S, c, g, B)[0] != lastOK_slow(n, S, c, g, B)[0]: bad += 1
    print('selftest lastOK closed form vs loop: 20000 cases,', bad, 'mismatches')
    return bad == 0

if __name__ == '__main__':
    if os.environ.get('SELFTEST') == '1': sys.exit(0 if selftest() else 1)
    a = sys.argv[1:]
    if a[0] == '--plan':                 # real prefix: (c, g) from session 64's plan4 (base <= LIMB + steps + raises)
        import io, contextlib, textwrap, itertools
        fs = [tuple(map(int, t.split('^'))) for t in a[1].split('*')]; LIMB = int(a[2]); rest = a[3:]
        d_ = os.path.dirname(os.path.abspath(__file__)); sys.argv = ['x', str(LIMB), '0']
        G = {'__file__': os.path.join(d_, 'raise_late_plan.py'), '__name__': 'lib'}
        with contextlib.redirect_stdout(io.StringIO()):
            exec(open(os.path.join(d_, 'raise_late_plan.py')).read(), G)
        src = open(os.path.join(d_, 'subroot_leaf_probe.py')).read()
        body = '    def plan4(f):' + src.split('    def plan4(f):')[1].split('        return out')[0] + '        return out\n'
        G['LIMB'] = LIMB; G['itertools'] = itertools
        exec(textwrap.dedent(body), G)
        P4 = G['plan4'](dict(fs))
        n = 1
        for p_, e_ in fs: n *= p_ ** e_
        S = sigma_f(fs) - n
        if not P4: print('no plan for', a[1]); sys.exit(2)
        c, g = min((c_ * 1000 + g_, (c_, g_)) for c_, g_, *_ in P4)[1]
        print('plan', a[1], 'n', n, 'S', S, 'sigma/n %.6f' % ((S + n) / n), 'c', c, 'g', g, 'plans', len(P4))
    elif a[0] == '--base':
        fs = [tuple(map(int, t.split('^'))) for t in a[1].split('*')]
        n, S, c, g = base_cg(fs); rest = a[2:]
        print('base', a[1], 'n', n, 'S', S, 'c', c, 'g', g)
    else:
        n, S, c, g = map(int, a[:4]); rest = a[4:]
    p0, kp, Kf, Kq, K, Kr = map(int, rest[:6])
    if len(rest) > 6: BUDGET[0] = int(rest[6])
    t = time.time()
    try: res = subOK(n, S, c, g, K, Kr, Kq, Kf, p0, kp)
    except Budget: res = 'BUDGET'
    print('subOK =', res, '%.1fs' % (time.time() - t), C, flush=True)
