# Session 75 (notes/erdos-470.md): brute-force soundness check of plimit_probe.stair_bounded (BOUNDED=1). For every pair
# (p, q) on which stair_bounded returns True, enumerate f, e <= FE and every bad prime r in (q, R) (odd prime, r not dividing
# n): each abundant n p^f q^e r must carry its own IntervalGap certificate (chain n -> p^f -> q^e -> r). A violation means the
# staircase logic (limit bounds per row/column, monotonicity) is unsound. Python only; decides nothing about #470.
# Env: CG=c,g override (larger = weaker certificate; used for the mutation test), RMAX=k (k smallest + k largest r per pair), PAIRS=k (every k-th pair) for large prefixes.
# Usage: python3 -I scripts/plimit_bounded_check.py 'p^e*p^e*p^e' LIMB FE [p ...]   (p omitted: every p, as `0` in plimit_probe)
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
if os.environ.get('CG'): c, g = map(int, os.environ['CG'].split(','))   # CG=c,g: weaker (larger) c, g (still sound)
C = PL.Ctx(n, S, c, g)
calls = []
orig = PL.stair_bounded
def spy(C_, p, q, R):
    res = orig(C_, p, q, R); calls.append((p, q, R, res[0])); return res
PL.stair_bounded = spy
if not ps:
    p0 = max(int(t.split('^')[0]) for t in plan.split('*')) + 2
    Q3 = p0 + (p0 % 2 == 0)
    while not ((S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1)): Q3 += 2
    ps = [x for x in range(p0, Q3, 2) if PL.isprime(x) and n % x]
for p in ps: PL.decide_p(C, p)
tot = ab = bad = 0
RMAX = int(os.environ.get('RMAX', '0'))                            # RMAX=k: only the k smallest and k largest r per pair
PAIRS = int(os.environ.get('PAIRS', '0'))                          # PAIRS=k: only every k-th pair returning True
if PAIRS: calls = [x for x in calls if x[3]][::PAIRS]
for p, q, R, okb in calls:
    if not okb: continue
    s = PL.bad_sieve(C, R + 1)
    rs = [r for r in range(q + 2, R) if s[r]]
    if RMAX and len(rs) > 2 * RMAX: rs = rs[:RMAX] + rs[-RMAX:]      # both ends (near R is where the windows are)
    for f in range(1, FE + 1):
        for e in range(1, FE + 1):
            M, T, okc = PL.chain(C, [(p, f), (q, e)])
            for r in rs:
                tot += 1
                if (T + M) * (r + 1) - M * r <= M * r: continue      # not abundant
                ab += 1
                N, T2, ok2 = PL.chain(C, [(p, f), (q, e), (r, 1)])
                if ok2 and c <= N and N + c <= T2: continue
                bad += 1
                if bad < 10: print('UNSOUND', p, f, q, e, r, flush=True)
print('pairs', len(calls), 'true', sum(x[3] for x in calls), 'points', tot, 'abundant', ab, 'uncertified', bad, flush=True)
