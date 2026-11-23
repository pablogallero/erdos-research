# Session 60 (notes/erdos-470.md): multi_plan coverage on deficient 5-prime prefixes shaped like the open omega=6 roots
# (3^E, E >= 17). Usage: python3 -I scripts/highv3_coverage_probe.py LIMB CASES REPO_DIR (under ulimit -v). Python only.
import os, sys, io, contextlib, random, time
LIMB = int(sys.argv[1]); TR = int(sys.argv[2]); REPO = sys.argv[3]
d = os.path.join(REPO, 'scripts'); sys.argv = ['x', str(LIMB), '0']
g = {'__file__': os.path.join(d, 'raise_late_plan.py'), '__name__': 'lib'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(open(os.path.join(d, 'raise_late_plan.py')).read(), g)
multi_plan, sigpp, isprime = g['multi_plan'], g['sigpp'], g['isprime']
def stats(f):
    n = 1; s = 1
    for p, e in f.items(): n *= p**e; s *= sigpp(p, e)
    return n, s
def nextprime(x):
    x += 1
    while not isprime(x): x += 1
    return x
cases = [{3:17,5:24,17:4,257:4,113149:1}]
for f in list(cases):
    t=time.time(); r=multi_plan(f); print('REAL', sorted(f.items()), r, '%.1fs'%(time.time()-t), flush=True)
random.seed(7); P = [p for p in range(7, 400) if isprime(p)]
PR = [p for p in range(3, 300000) if isprime(p)]
while len(cases) < TR:
    f = {3: random.choice([17,18,19,20,25,30])}; f[random.choice([5,5,5,7,11])] = random.randint(1, 30)
    a = random.choice([p for p in P[:7] if p not in f]); f[a] = random.choice([1,2,2,3,4,6])
    b = random.choice([p for p in P if p > a][:25]); f[b] = random.choice([1,1,2,3,4])
    # last prefix prime: the largest one, chosen so that abundance is reachable with one more prime q > it
    n, s = stats(f)
    if s >= 2*n: continue
    lo = max(f) + 1
    cands = [p for p in PR if p >= lo][:400]
    random.shuffle(cands)
    for c in cands:
        f2 = dict(f); f2[c] = random.choice([1,1,1,2])
        n2, s2 = stats(f2)
        Q = nextprime(c)
        if s2 < 2*n2 and s2*(Q+1) >= 2*n2*Q: cases.append(f2); break
cov = 0; t0 = time.time()
for f in cases:
    t = time.time(); r = multi_plan(f); cov += bool(r)
    if not r: print(sorted(f.items()), 'none', r, '%.1fs' % (time.time()-t), flush=True)
print('LIMB', LIMB, 'cases', len(cases), 'covered', cov, 'time %.0fs' % (time.time()-t0))
