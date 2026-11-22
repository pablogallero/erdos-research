# Session 57 (notes/erdos-470.md): family plans with the LATE raise and the greedy gap bound gB of D(m) (no bitset for m).
# For random deficient 5-prime prefixes f (max exponent >= 6) on which session 56's plan() fails, look for
#   base b = m0 p^e0 (bitset, interval c, gaps g)  --steps L-->  m p^e0  --raise p to f[p] (gB = greedy_gap(m))-->  n
# such that every last prime q is covered by the last-prime decider (allq empty). Prints the plan and #divisors of m.
# Usage: python3 scripts/raise_late_plan.py LIMB [TRIALS]   (run under ulimit -v). Python only; not the omega=6 search.
import os, sys, itertools, random
os.environ['SOUND'] = '0'; os.environ['GREEDY'] = '1'
_d = os.path.dirname(os.path.abspath(__file__))
_src = open(os.path.join(_d, 'raise_late_probe.py')).read()
exec(_src.split("random.seed(1)\nprimes")[0])
_ps = open(os.path.join(_d, 'raise_steps_plan.py')).read()
exec("def plan(f):" + _ps.split("def plan(f):")[1].split("random.seed(2)")[0])
TRIALS = int(sys.argv[2]) if len(sys.argv) > 2 else 3000

def late_plan(f):
    ps = sorted(f); n = 1; sgn = 1
    for p, e in f.items(): n *= p ** e; sgn *= sigpp(p, e)
    best = None
    for p in ps:
        others = [q for q in ps if q != p]
        for k in range(1, len(others) + 1):
            for R in itertools.combinations(others, k):
                m0 = 1
                for q in R: m0 *= q ** f[q]
                L = [q for q in others if q not in R]
                m = m0
                for q in L: m *= q ** f[q]
                gB = greedy_gap(m); sgm = sigma(m); sB = sgm - m
                for e0 in range(1, f[p]):
                    b = m0 * p ** e0
                    if b > LIMB: break
                    s, bits, c, g = info(b)
                    if c is None: continue
                    for order in (sorted(L), sorted(L, reverse=True)):
                        if steps_ok(b, sigma(b), f, order, c, g) is None: continue
                        good = all(p ** (e + 1) * gB + 2 * c <= sgm * sigpp(p, e) - m * p ** e + 1 and
                                   m * p ** e + 2 * c <= p ** (e + 1) * sB + sgm * sigpp(p, e) - m * p ** e + 1
                                   for e in range(e0, f[p]))
                        if not good: continue
                        if allq(n, c, g, sgn): continue
                        nd = len(divisors(m))
                        cand = (nd, b, p, R, e0, tuple(order), c, g, gB)
                        if best is None or cand < best: best = cand
    return best

random.seed(3)
primes = [p for p in range(3, 60) if isprime(p)]
found = tried = old = 0
for t in range(TRIALS):
    P = sorted(random.sample(primes[:8], 5))
    f = {p: random.choice([1, 1, 2, 2, 3, 4, 6, 8, 10]) for p in P}
    n = 1; sgn = 1
    for p, e in f.items(): n *= p ** e; sgn *= sigpp(p, e)
    if sgn >= 2 * n or max(f.values()) < 6: continue
    tried += 1
    r = plan(f)
    if r and r[6] and not allq(n, r[3], r[4], sgn): old += 1; continue
    r2 = late_plan(f)
    if r2: found += 1; print("late-only", f, "plan (ndiv(m), b, p, R, e0, L, c, g, gB) =", r2, flush=True)
print("LIMB", LIMB, "deficient prefixes", tried, "session56 plan", old, "late-only", found)

# --- Multi-raise (session 57, second part): base b = prod p^e0_p (e0_p in {0,1,2}, b <= LIMB, bitset interval),
# steps for the primes with e0_p = 0 (full exponent), then raise every other prime to its full exponent, one prime
# after another (gB = greedy_gap of the current cofactor). Same final family test (allq).
def multi_plan(f):
    ps = sorted(f); n = 1; sgn = 1
    for p, e in f.items(): n *= p ** e; sgn *= sigpp(p, e)
    for e0 in itertools.product(*[[x for x in (0, 1, 2) if x <= f[p]] for p in ps]):
        if not any(e0): continue
        b = 1
        for p, x in zip(ps, e0): b *= p ** x
        if b > LIMB: continue
        s, bits, c, g = info(b)
        if c is None: continue
        steps = [p for p, x in zip(ps, e0) if x == 0]
        raises = [p for p, x in zip(ps, e0) if 0 < x < f[p]]
        for so in (sorted(steps), sorted(steps, reverse=True)):
            st = steps_ok(b, sigma(b), f, so, c, g)
            if st is None: continue
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
                if ok and not allq(n, c, g, sgn):
                    return (b, tuple(so), tuple(ro), c, g)
    return None

if os.environ.get('MULTI') == '1':
    random.seed(3)
    tried = c56 = cl = cm = 0
    for t in range(TRIALS):
        P = sorted(random.sample(primes[:8], 5))
        f = {p: random.choice([1, 1, 2, 2, 3, 4, 6, 8, 10]) for p in P}
        n = 1; sgn = 1
        for p, e in f.items(): n *= p ** e; sgn *= sigpp(p, e)
        if sgn >= 2 * n or max(f.values()) < 6: continue
        tried += 1
        r = plan(f); a = bool(r and r[6] and not allq(n, r[3], r[4], sgn))
        b_ = a or bool(late_plan(f))
        c_ = b_ or bool(multi_plan(f))
        c56 += a; cl += b_; cm += c_
    print("MULTI LIMB", LIMB, "deficient prefixes", tried, "session56", c56, "+late", cl, "+multi", cm)
