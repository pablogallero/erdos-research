# Session 63 (notes/erdos-470.md): leaf census of ONE small sub-tree of the omega=6 search, for a Lean reflective checker.
# Fixes a deficient 4-prime prefix (exact exponents) and replays only the shape of the last two levels of search1/family
# (same pruning bounds, same exponent loop), ASSUMING every pseudoperfect test passes (no pp_Mq / pp_Mqe is run, so this is
# NOT the search and decides nothing). It collects the 5-prime nodes the Lean checker would need as leaves:
#   abundant  -> ppOK list (greedy + exact finish, abundant_greedy_probe.py),
#   deficient -> family plan decider (multi_plan, raise_late_plan.py); #divisors of n is the kernel-cost proxy.
# Env: SKIPAB=1 skips the abundant certificates; DSAMPLE=k tests every k-th deficient node only.
# STARS=1 (with UNIFORM=1) also checks the sixth prime with exponent >= 2.
# J=3 (session 64): PREFIX has 3 primes; leaves are 4/5-prime nodes, all extra primes checked as steps of one M3 certificate.
# Usage: python3 -I scripts/subroot_leaf_probe.py 'p^e*p^e*p^e*p^e' LIMB MAXLEAVES REPO_DIR   (under ulimit -v). Python only.
import os, sys, io, contextlib, time
from math import gcd
PRE, LIMB, MAXL, REPO = sys.argv[1], int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
d = os.path.join(REPO, 'scripts')
sys.argv = ['x', str(LIMB), '0']
g = {'__file__': os.path.join(d, 'raise_late_plan.py'), '__name__': 'lib'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(open(os.path.join(d, 'raise_late_plan.py')).read(), g)
multi_plan, isprime = g['multi_plan'], g['isprime']
allq_slow = g['allq']
def allq_fast(n, c, g_, sg):
    # Same truth value as allq (raise_steps_plan.py), without the loop over every q < sg/(2n-sg): each of allq's
    # conditions is linear in q, so the good q form an interval [lo, hi]; look for the first prime q outside it with
    # n % q != 0 and n q < S + (n + q S) (that last condition is an upper bound on q). Returns [q] or [].
    S = sg - n; end = sg // max(1, 2*n - sg) + 3
    def need(q): return n*q < S + (n + q*S)
    def good(q): return q*g_ + 2*c <= S + 1 and n + 2*c <= (q+1)*S + 1 and c <= n*q and n*q + c <= S + (n + q*S)
    lo, hi = 2, end
    if g_ > 0: hi = min(hi, (S + 1 - 2*c) // g_) if S + 1 - 2*c >= 0 else 1
    if S > 0: lo = max(lo, -((-(n + 2*c - 1)) // S) - 1)
    lo = max(lo, -((-c) // n))
    if n > S: hi = min(hi, (S + n - c) // (n - S)) if S + n - c >= 0 else 1
    elif n == S and S + n - c < 0: hi = 1
    while lo > 2 and good(lo - 1): lo -= 1      # guard the integer rounding: [lo, hi] must be the exact good set
    while lo <= hi and not good(lo): lo += 1
    while hi >= lo and hi + 1 < end and good(hi + 1): hi += 1
    while hi >= lo and not good(hi): hi -= 1
    for q in list(range(2, min(lo, end))) + [None]:
        if q is None: break
        if not need(q): break
        if isprime(q) and n % q: return [q]
    q = max(hi + 1, 2, lo if lo > hi else 2)
    while q < end and need(q):
        if isprime(q) and n % q and not good(q): return [q]
        q += 1
    return []
if os.environ.get('CHECKALLQ') == '1':   # validation against the original loop on small random inputs
    import random as _r
    _r.seed(5)
    for _ in range(20000):
        n = _r.randrange(3, 3000) | 1; sg = _r.randrange(n + 1, 2*n + 2); c = _r.randrange(0, n); gg_ = _r.randrange(1, 50)
        assert bool(allq_slow(n, c, gg_, sg)) == bool(allq_fast(n, c, gg_, sg)), (n, c, gg_, sg)
    print('CHECKALLQ ok 20000', flush=True)
g['allq'] = allq_fast
sys.argv = ['x', '0']
h = {'__name__': 'lib'}
exec(open(os.path.join(d, 'abundant_greedy_probe.py')).read().split('if len(sys.argv) > 3:')[0], h)
greedy = h['greedy']
WIN = 10**4
def sig(p, e): return (p**(e+1) - 1) // (p - 1)
f4 = [tuple(map(int, t.split('^'))) for t in PRE.split('*')]
M4 = S4 = 1
for p, e in f4: M4 *= p**e; S4 *= sig(p, e)
assert S4 < 2*M4, 'prefix must be deficient'
abund, defic = {}, {}
def family_shape(f, M, sigma, un, ud, q0):
    # family() of odd_weird_family.py with every pp test assumed True: returns its value; records the node f
    if un >= 2*ud: return False
    if sigma < 2*M: defic.setdefault(tuple(f), (M, sigma))
    D = 2*M - sigma; qtop = sigma // D
    q = max(q0, qtop + 1)
    while True:
        if un*q < 2*ud*(q-1): return True
        if q > qtop + WIN: return False
        if isprime(q):
            e = 1
            while True:
                s_, pe = sig(q, e), q**e
                if sigma*s_ >= 2*M*pe: break
                if un*s_ >= 2*ud*pe or e > 200: return False
                e += 1
        q += 2
def node(f, M, sigma, un, ud, j, q0):
    if len(abund) + len(defic) >= MAXL: raise StopIteration
    if sigma >= 2*M:
        abund.setdefault(tuple(f), M); return True
    if j == 1: return family_shape(f, M, sigma, un, ud, q0)
    q = q0
    while True:
        a, b = un, ud
        for i in range(j): a *= q + 2*i; b *= q + 2*i - 1
        if a < 2*b: return True
        if isprime(q):
            e = 1
            while True:
                s, pe = sig(q, e), q**e
                an, ad = un*q, ud*(q-1); gg = gcd(an, ad)
                if node(f+[(q, e)], M*pe, sigma*s, an//gg, ad//gg, j-1, q+2): break
                bn, bd = un*s, ud*pe; gg = gcd(bn, bd)
                if not node(f+[(q, e)], M*pe, sigma*s, bn//gg, bd//gg, j-1, q+2): return False
                e += 1
        q += 2
t0 = time.time(); gg = gcd(S4, M4)
try: r = node(f4, M4, S4, S4//gg, M4//gg, int(os.environ.get('J', '2')), max(p for p, _ in f4) + 2); cut = False
except StopIteration: r = None; cut = True
print('prefix', PRE, 'tree shape', r, 'cut at MAXLEAVES' if cut else 'complete', 'abundant', len(abund),
      'deficient', len(defic), 'enum %.1fs' % (time.time() - t0), flush=True)
t = time.time(); aok = 0; alen = []
for f, M in (abund.items() if os.environ.get('SKIPAB') != '1' else []):
    c = greedy(dict(f))
    if c: aok += 1; alen.append(len(c))
    else: print('ABUNDANT-FAIL', f, flush=True)
print('abundant ppOK', aok, '/', len(abund), 'len max', max(alen) if alen else None, '%.1fs' % (time.time() - t), flush=True)
t = time.time(); dok = 0; nd = []
DS = int(os.environ.get('DSAMPLE', '1'))
for f, (M, s) in list(defic.items())[::DS]:
    t1 = time.time(); p = multi_plan(dict(f))
    nd.append(1)
    k = 1
    for _, e in f: k *= e + 1
    if os.environ.get('VERB') == '1': print('node', f, p, 'divisors', k, '%.1fs' % (time.time() - t1), flush=True)
    if p: dok += 1; nd[-1] = k
    else: print('DEFICIENT-UNCOVERED', f, 'divisors', k, '%.1fs' % (time.time() - t1), flush=True)
nd = sorted(x for x in nd if x > 1)
print('deficient covered', dok, '/', len(list(defic)[::DS]), 'divisors median', nd[len(nd)//2] if nd else None,
      'max', nd[-1] if nd else None, '%.1fs' % (time.time() - t), flush=True)
# --- UNIFORM=1 (session 63): one IntervalGap certificate for the 4-prime prefix M4 (base bitset + steps + raises, the
# multi_plan chain without the last-prime test), then the prime-power step by q (conditions on M4, q, c, g only; valid for
# every exponent of q) for EVERY leaf, followed by: abundant leaf -> c <= M5 <= S5 - c (pseudoperfect); deficient leaf ->
# allq empty (no M5 q' weird). If all leaves pass, the whole sub-tree needs ONE kernel computation (the M4 chain) plus
# linear-in-q side conditions, instead of one certificate per leaf.
if os.environ.get('UNIFORM') == '1':
    import itertools
    info, steps_ok, greedy_gap, sigma, sigpp = g['info'], g['steps_ok'], g['greedy_gap'], g['sigma'], g['sigpp']
    def plan4(f):
        ps = sorted(f); out = []
        for e0 in itertools.product(*[[x for x in (0, 1, 2) if x <= f[p]] for p in ps]):
            if not any(e0): continue
            b = 1
            for p, x in zip(ps, e0): b *= p ** x
            if b > LIMB: continue
            s, bits, c, gg = info(b)
            if c is None: continue
            steps = [p for p, x in zip(ps, e0) if x == 0]; raises = [p for p, x in zip(ps, e0) if 0 < x < f[p]]
            for so in (sorted(steps), sorted(steps, reverse=True)):
                if steps_ok(b, sigma(b), f, so, c, gg) is None: continue
                for ro in (raises, raises[::-1]):
                    cur = {p: x for p, x in zip(ps, e0) if x}
                    for q in so: cur[q] = f[q]
                    ok = True
                    for p in ro:
                        m = 1
                        for q, x in cur.items():
                            if q != p: m *= q ** x
                        gB = greedy_gap(m); sgm = sigma(m); sB = sgm - m
                        for e in range(cur[p], f[p]):
                            sA = sgm * sigpp(p, e) - m * p ** e
                            if not (p ** (e + 1) * gB + 2 * c <= sA + 1 and m * p ** e + 2 * c <= p ** (e + 1) * sB + sA + 1):
                                ok = False; break
                        if not ok: break
                        cur[p] = f[p]
                    if ok: out.append((c, gg, b, tuple(so), tuple(ro)))
        return out
    t = time.time(); P4 = plan4(dict(f4)); S4c = S4 - M4
    print('plan4 candidates', len(P4), sorted(set((c, gg) for c, gg, *_ in P4))[:8], '%.1fs' % (time.time() - t), flush=True)
    best = None; stars = [0]
    for c, gg, b, so, ro in P4:
        nbad = []; stepq = 0
        for f, M5 in list(abund.items()) + [(f, v[0]) for f, v in defic.items()]:
            q = f[-1][0]; s5 = sigma(M5) - M5
            # J=3 (session 64): a 3-prime prefix; every extra prime of the leaf is a prime-power step (same c, g)
            Mc, Sc, okst = M4, S4c, True
            for (pq, pe) in f[len(f4):]:
                if not (pq*gg + 2*c <= Sc + 1 and Mc + 2*c <= (pq + 1)*Sc + 1): okst = False; break
                Sc = (Sc + Mc)*sigpp(pq, pe) - Mc*pq**pe; Mc *= pq**pe
            if not okst: nbad.append(('step', f[len(f4):])); continue
            if f in abund:
                if not (c <= M5 <= s5 - c): nbad.append(('abund', f[-1]))
            elif allq_fast(M5, c, gg, s5 + M5): nbad.append(('defic', f[-1]))
            elif os.environ.get('STARS') == '1':
                # sixth prime r with exponent >= 2 (the "star" part of family(); allq only covers r^1): for r > qtop
                # with M5 r^e abundant for some e, the prime-power step by r plus c <= M5 r^e <= sum D - c.
                sg5 = s5 + M5; D5 = 2*M5 - sg5; r = sg5 // D5 + 1; r += (r % 2 == 0)
                while sg5*r >= 2*M5*(r - 1) and r <= sg5 // D5 + WIN:
                    if isprime(r) and M5 % r:
                        e = 2
                        while e <= 200 and sg5*sigpp(r, e) < 2*M5*r**e: e += 1
                        if e <= 200:
                            N = M5*r**e; sN = sg5*sigpp(r, e) - N
                            if not (r*gg + 2*c <= s5 + 1 and M5 + 2*c <= (r + 1)*s5 + 1 and c <= N <= sN - c):
                                nbad.append(('star', f[-1], r, e)); break
                            stars[0] += 1
                    r += 2
        if best is None or len(nbad) < len(best[1]): best = ((c, gg, b, so, ro), nbad)
        if not nbad: break
    if best:
        print('UNIFORM best plan', best[0], 'leaves', len(abund) + len(defic), 'failing', len(best[1]), best[1][:6], 'star leaves checked', stars[0], flush=True)
