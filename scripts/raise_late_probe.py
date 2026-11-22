# Session 57 (notes/erdos-470.md): "late raise". Two parallel step chains with the same step list L:
# on b = m0 p^e0 (bitset; interval c, gaps g) and on m0 (bitset; interval c', gaps gB); then raise p from e0 to its full
# exponent over the LARGE cofactor m = m0 * L (gB is kept by the steps, sums grow). Compared with session 56's
# certify() (raise right after the base) on the same random omega=6 candidates. Python only; not the omega=6 search.
# Usage: python3 scripts/raise_late_probe.py [LIMB]   (run under ulimit -v)
import os, sys, itertools, random
os.environ['SOUND'] = '0'
_src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'raise_step_probe.py')).read()
exec(_src.split("random.seed(1)")[0])

def steps_ok(k, sg, f, order, c, g):
    """prime-power step conditions (interval_properDivisors_mul_prime_pow) along order; returns (k, sg) or None."""
    for q in order:
        S = sg - k
        if not (q * g + 2 * c <= S + 1 and k + 2 * c <= (q + 1) * S + 1):
            return None
        k *= q ** f[q]; sg *= sigpp(q, f[q])
    return k, sg

def greedy_gap(m):
    """gap bound of SS(D m) on [0, sum D m] from sorted proper divisors: max(1, max_i d_i - (d_1+...+d_{i-1})).
    (SS_i = SS_{i-1} u (d_i + SS_{i-1}); only a jump from P_{i-1} up to d_i can open a new gap.)"""
    D = divisors(m)[:-1]; P = 0; G = 1
    for d in D:
        G = max(G, d - P); P += d
    return G

GREEDY = os.environ.get('GREEDY', '0') == '1'

def certify_late(f):
    ps = sorted(f)
    for p in ps:
        others = [q for q in ps if q != p]
        for k in range(1, len(others) + 1):
            for R in itertools.combinations(others, k):
                m0 = 1
                for q in R: m0 *= q ** f[q]
                L = [q for q in others if q not in R]
                if GREEDY:
                    c1 = 0
                elif m0 > LIMB or not L:
                    continue  # (not L: session 56 case)
                else:
                    _, _, c1, _ = info(m0)
                    if c1 is None: continue
                    _, gB = gap0(m0)
                for e0 in range(1, f[p]):
                    b = m0 * p ** e0
                    if b > LIMB: break
                    s, bits, c, g = info(b)
                    if c is None: continue
                    for order in (sorted(L), sorted(L, reverse=True)):
                        if GREEDY:
                            mm = m0
                            for q in L: mm *= q ** f[q]
                            gB = greedy_gap(mm); rb = (mm, sigma(mm))
                        else:
                            rb = steps_ok(m0, sigma(m0), f, order, c1, gB)
                        if rb is None: continue
                        ra = steps_ok(b, sigma(b), f, order, c, g)
                        if ra is None: continue
                        m, sgm = rb; sB = sgm - m
                        good = True
                        for e in range(e0, f[p]):
                            sA = sgm * sigpp(p, e) - m * p ** e
                            if not (p ** (e + 1) * gB + 2 * c <= sA + 1 and
                                    m * p ** e + 2 * c <= p ** (e + 1) * sB + sA + 1):
                                good = False; break
                        if not good: continue
                        N = m * p ** f[p]; S = sgm * sigpp(p, f[p]) - N
                        if c <= N and N + c <= S: return ("late", p, R, e0, order)
    return None

random.seed(1)
primes = [p for p in range(3, 400) if isprime(p)]
tot = c56 = cl = 0; fails = []
for trial in range(400):
    P = sorted(random.sample(primes[:12], 5))
    f = {p: random.choice([1, 1, 2, 2, 3, 4, 6, 10, 15, 20]) for p in P}
    n = 1; sg = 1
    for p, e in f.items(): n *= p ** e; sg *= sigpp(p, e)
    if sg >= 2 * n: continue
    Q = sg // (2 * n - sg)
    qs = [q for q in primes if q > max(P) and q <= Q]
    for q in qs[:5]:
        g2 = dict(f); g2[q] = 1
        tot += 1
        r1 = certify(g2, True)
        c56 += bool(r1)
        r2 = r1 or certify_late(g2)
        cl += bool(r2)
        if r2 and not r1: print("new", g2, r2, flush=True)
        if not r2: fails.append(g2)
print("LIMB", LIMB, "tested", tot, "session56", c56, "with late raise", cl)
for x in fails[:10]: print("fail", x)
