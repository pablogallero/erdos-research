# Session 76 (notes/erdos-470.md): brute-force soundness check of plimit_probe.strip_fast (FASTSTRIP=1 / BOUNDED=1), in
# particular its session-75 use in decide_q (q limit-deficient under a non-limit-deficient p). For every strip_fast call that
# returns True (fixed exponents `fixed`, free exponent of `p`, last prime r in [r_lo, R)), enumerate f <= FE and bad primes r
# (odd prime, r not dividing n) in [r_lo, R): every abundant point must carry its own IntervalGap certificate (chain
# order(fixed, (p, f)) -> r). R is never sieved: only the RMAX smallest bad r above r_lo and the RMAX largest below R (found
# by trial division from both ends; the windows that matter sit near R). Also checks that r >= R is never abundant on the
# sampled f (limit bound) for the RMAX bad r just above R. Python only; decides nothing about #470.
# Env: CG=c,g weaker certificate and FORCE=1 (strip_fast forced to True), CHECKCG=c,g (verify only) for mutation tests, RMAX=k (default 200), CALLS=k (every k-th True call), FE (argv).
# Usage: python3 -I scripts/plimit_strip_check.py 'p^e*p^e*p^e' LIMB FE p [p ...]
import os, sys, subprocess
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
plan, limb, FE = sys.argv[1], sys.argv[2], int(sys.argv[3]); ps = list(map(int, sys.argv[4:]))
os.environ['BOUNDED'] = '1'; os.environ['FASTSTRIP'] = '1'
sys.argv = ['x']
import plimit_probe as PL
out = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'subok_cost_probe.py'), '--plan', plan, limb, '3', '0', '1', '1', '1', '1'],
                     capture_output=True, text=True).stdout
l0 = [l for l in out.splitlines() if l.startswith('plan ')][0].split()
n, S, c, g = int(l0[3]), int(l0[5]), int(l0[9]), int(l0[11])
if os.environ.get('CG'): c, g = map(int, os.environ['CG'].split(','))
C = PL.Ctx(n, S, c, g)
calls = []
orig = PL.strip_fast
def spy(C_, fixed, p, r_lo, order):
    res = orig(C_, fixed, p, r_lo, order)
    if os.environ.get('FORCE') == '1': res = True       # mutation test: a decider that always answers True
    calls.append((list(fixed), p, r_lo, order, res)); return res
PL.strip_fast = spy
for p in ps: print('p', p, PL.decide_p(C, p)[1][:4], flush=True)
if os.environ.get('CHECKCG'): c, g = map(int, os.environ['CHECKCG'].split(','))   # mutation: verify with a stricter certificate
RMAX = int(os.environ.get('RMAX', '200')); CALLS = int(os.environ.get('CALLS', '1'))
true_calls = [x for x in calls if x[4]][::CALLS]
def bad(r): return PL.isprime(r) and n % r
tot = ab = unc = above_ab = 0
for fixed, p, r_lo, order, _ in true_calls:
    N0, S0, _ = PL.chain(C, fixed)
    A, B = (S0 + N0) * p, 2 * N0 * (p - 1)
    R = A // (B - A) + 1
    lo, hi, above = [], [], []
    r = r_lo + (r_lo % 2 == 0)
    while r < R and len(lo) < RMAX:
        if bad(r): lo.append(r)
        r += 2
    r = R - 1 - ((R - 1) % 2 == 0)
    while r > (lo[-1] if lo else r_lo - 1) and len(hi) < RMAX:
        if bad(r): hi.append(r)
        r -= 2
    r = R + (R % 2 == 0)
    while len(above) < 20:
        if bad(r): above.append(r)
        r += 2
    rs = sorted(set(lo + hi))
    for f in range(1, FE + 1):
        M, T, _ = PL.chain(C, order(fixed, (p, f)))
        for r in rs + above:
            tot += 1
            if (T + M) * (r + 1) - M * r <= M * r: continue        # n-part times r not abundant
            if r >= R: above_ab += 1; print('ABOVE-R ABUNDANT', fixed, p, f, r, R, flush=True); continue
            ab += 1
            N, T2, ok2 = PL.chain(C, order(fixed, (p, f)) + [(r, 1)])
            if ok2 and c <= N and N + c <= T2: continue
            unc += 1
            if unc < 10: print('UNSOUND', fixed, p, f, r, R, flush=True)
print('strip calls', len(calls), 'true', sum(1 for x in calls if x[4]), 'checked', len(true_calls), 'points', tot,
      'abundant', ab, 'uncertified', unc, 'abundant above R', above_ab, flush=True)
