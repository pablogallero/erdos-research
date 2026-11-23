# Session 64 (notes/erdos-470.md): how many 4-prime prefixes (= IntervalGap certificates of session 63's uniform
# scheme) one root of the omega=6 search needs. Takes the depth-3 checkpoint keys (f, un, ud, j, q0) of root 3^E,
# samples some, and replays only the SHAPE of search1/family below each (every pseudoperfect test assumed to pass;
# finished roots have nfail 0, so the shape is the real control flow). Counts distinct 4-prime f with j == 2.
# Decides nothing, writes nothing. Usage: python3 -I scripts/m4_count_probe.py E SAMPLE SEED CK.gz [CK2.gz ...]
import sys, gzip, ast, random, time
from math import gcd
E, NS, SEED = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3])
WIN = 10**4
def isprime(n):
    if n < 2: return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0: return n == p
    d, s = n - 1, 0
    while d % 2 == 0: d //= 2; s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1): continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1: break
        else: return False
    return True
def sig(p, e): return (p**(e+1) - 1) // (p - 1)
def family_shape(M, sigma, un, ud, q0):
    if un >= 2*ud: return False
    D = 2*M - sigma; qtop = sigma // D; q = max(q0, qtop + 1)
    q |= 1
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
def node(f, M, sigma, un, ud, j, q0, out, st):
    st[0] += 1
    if sigma >= 2*M: return True
    if j == 1: return family_shape(M, sigma, un, ud, q0)
    if j == 2: out.add(tuple(f))
    q = q0
    while True:
        a, b = un, ud
        for i in range(j): a *= q + 2*i; b *= q + 2*i - 1
        if a < 2*b: return True
        if isprime(q):
            e = 1
            while True:
                s, pe = sig(q, e), q**e
                an, ad = un*q, ud*(q-1); g = gcd(an, ad)
                if node(f+[(q, e)], M*pe, sigma*s, an//g, ad//g, j-1, q+2, out, st): break
                bn, bd = un*s, ud*pe; g = gcd(bn, bd)
                if not node(f+[(q, e)], M*pe, sigma*s, bn//g, bd//g, j-1, q+2, out, st): return False
                e += 1
        q += 2
keys = []
for fn in sys.argv[4:]:
    for l in gzip.open(fn, 'rt'):
        t = ast.literal_eval(l)
        if t[0] and t[0][0] == (3, E) and len(t[0]) == 3: keys.append(t)
random.seed(SEED); smp = random.sample(keys, min(NS, len(keys)))
tot = 0; allf = set()
for f, un, ud, j, q0 in smp:
    M = S = 1
    for p, e in f: M *= p**e; S *= sig(p, e)
    out = set(); st = [0]; t = time.time()
    r = node(list(f), M, S, un, ud, j, q0, out, st)
    tot += len(out); allf |= out
    print(f, j, 'shape', r, 'nodes', st[0], 'M4', len(out), '%.1fs' % (time.time() - t), flush=True)
print('root', E, 'keys(depth3)', len(keys), 'sampled', len(smp), 'M4 total', tot, 'distinct', len(allf),
      'estimate per root ~', round(len(allf) / len(smp) * len(keys)), flush=True)
