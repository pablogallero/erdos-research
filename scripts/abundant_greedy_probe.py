# Session 62 (notes/erdos-470.md): cheap pseudoperfect certificates for ABUNDANT 5-prime prefixes shaped like the open
# omega=6 roots (3^E, E >= 17). Certificate = greedy (largest first) list of distinct proper divisors of n summing to n.
# Usage: python3 -I scripts/abundant_greedy_probe.py CASES [SEED]. Python only (no owf).
import sys, random, time
TR = int(sys.argv[1]); random.seed(int(sys.argv[2]) if len(sys.argv) > 2 else 7)
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
def sigpp(p, e): return (p**(e+1) - 1) // (p - 1)
def stats(f):
    n = s = 1
    for p, e in f.items(): n *= p**e; s *= sigpp(p, e)
    return n, s
def divisors(f):
    ds = [1]
    for p, e in f.items(): ds = [d * p**i for d in ds for i in range(e + 1)]
    return ds
LIM = 1 << 20
def finish(rem, pool):
    # exact subset sum of rem from the distinct numbers in pool (all <= rem), via a big-int bitset; returns a list or None
    pool = [d for d in pool if d <= rem]; reach = [1]
    for d in pool: reach.append(reach[-1] | ((reach[-1] << d) & ((1 << (rem + 1)) - 1)))
    if not (reach[-1] >> rem) & 1: return None
    out = []
    for i in range(len(pool) - 1, -1, -1):
        if not (reach[i] >> rem) & 1: out.append(pool[i]); rem -= pool[i]
    return out
def greedy(f):
    n, _ = stats(f); rem = n; out = []; ds = sorted(divisors(f), reverse=True)
    for i, d in enumerate(ds):
        if rem <= LIM:
            r = finish(rem, [e for e in ds[i:] if e < n][::-1])
            return out + r if r is not None else None
        if d < n and d <= rem: out.append(d); rem -= d
    return out if rem == 0 else None
def node():
    while True:
        f = {3: random.choice([17, 18, 19, 20, 25, 30])}; f[random.choice([5, 5, 5, 7, 11])] = random.randint(1, 30)
        P = [p for p in range(7, 400) if isprime(p) and p not in f]
        a = random.choice(P[:7]); f[a] = random.choice([1, 2, 2, 3, 4, 6])
        b = random.choice([p for p in P if p > a][:25]); f[b] = random.choice([1, 1, 2, 3, 4])
        n, s = stats(f)
        if s >= 2 * n: continue
        # last prefix prime c: random below the abundance threshold s/(2n - s) (so that f + c^1 is abundant)
        hi = min(s // (2 * n - s), 10**7)
        if hi <= max(f): continue
        c = random.randint(max(f) + 1, hi)
        while c <= hi and not (isprime(c) and c not in f): c += 1
        if c > hi: continue
        f2 = dict(f); f2[c] = 1; n2, s2 = stats(f2)
        if s2 >= 2 * n2: return f2
if len(sys.argv) > 3:  # emit the certificate list of the real node (first case) for Lean
    print(greedy({3: 18, 5: 17, 19: 2, 97: 3, 2647: 1})); sys.exit()
cases = [{3: 18, 5: 17, 19: 2, 97: 3, 2647: 1}]
while len(cases) < TR: cases.append(node())
ok = 0; lens = []; t0 = time.time()
for f in cases:
    g = greedy(f)
    if g:
        n, _ = stats(f)
        assert sum(g) == n and len(set(g)) == len(g) and all(n % d == 0 and d < n for d in g)
        ok += 1; lens.append(len(g))
    else: print('FAIL', sorted(f.items()), flush=True)
print('cases', len(cases), 'greedy ok', ok, 'len max', max(lens) if lens else None,
      'len mean %.1f' % (sum(lens) / max(1, len(lens))), 'time %.0fs' % (time.time() - t0))
