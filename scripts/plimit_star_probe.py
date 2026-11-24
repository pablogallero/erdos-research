# Session 76 (notes/erdos-470.md): stars r^h (h >= 2) below a 3-prime prefix, brute force on sampled points. Python only;
# decides nothing about #470.
# Facts used (exact): for M odd, r prime not dividing M, E(h) = sigma(M) sigma(r^h) - 2 M r^h (excess of M r^h) satisfies
# E(h+1) = r E(h) + sigma(M). Hence (a) if M r is abundant AND certified (E(1) >= c, stepOK(M, r)), every M r^h is certified;
# (b) if E(h) >= 1 then E(h+1) >= r + sigma(M) >= c, so only the FIRST abundant h0 can lack a certificate; (c) a star case not
# covered by h = 1 needs M r non-abundant (r D >= sigma, D = 2M - sigma) but sup_h ratio > 2 (r D < 2M): r in [sigma/D,
# sigma/D + 1), i.e. the single candidate r* = ceil(sigma/D). So per deficient point M = n p^f q^e: one r*, one h0, one test.
# This probe enumerates p (argv), every bad q in (p, Q) (Q = two-prime tail, as decide_p), f, e <= FE, and reports the
# r* that are bad primes > q whose first abundant star M r*^h0 is NOT certified (stepOK fails, E(h0) < c, or c > M r*^h0).
# Only limit-deficient p (sigma(n) p <= 2 n (p-1)); the others (decide_p's f-loop) are listed as skipped.
# Usage: python3 -I scripts/plimit_star_probe.py 'p^e*p^e*p^e' LIMB FE p [p ...]   (p = 0: every p, as in plimit_probe)
import os, sys, subprocess, time
sys.dont_write_bytecode = True
HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
plan, limb, FE = sys.argv[1], sys.argv[2], int(sys.argv[3]); ps = list(map(int, sys.argv[4:]))
sys.argv = ['x']
import plimit_probe as PL
out = subprocess.run([sys.executable, '-I', os.path.join(HERE, 'subok_cost_probe.py'), '--plan', plan, limb, '3', '0', '1', '1', '1', '1'],
                     capture_output=True, text=True).stdout
l0 = [l for l in out.splitlines() if l.startswith('plan ')][0].split()
n, S, c, g = int(l0[3]), int(l0[5]), int(l0[9]), int(l0[11])
C = PL.Ctx(n, S, c, g)
def isprime(x):                                                    # Miller-Rabin, deterministic below 3.3e24 (12 prime bases)
    if x < 2 or x % 2 == 0: return x == 2
    for b in (3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41):
        if x % b == 0: return x == b
    d, s_ = x - 1, 0
    while d % 2 == 0: d //= 2; s_ += 1
    for b in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        y = pow(b, d, x)
        if y in (1, x - 1): continue
        for _ in range(s_ - 1):
            y = y * y % x
            if y == x - 1: break
        else: return False
    return True
if ps == [0]:
    p0 = max(int(t.split('^')[0]) for t in plan.split('*')) + 2
    Q3 = p0 + (p0 % 2 == 0)
    while not ((S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1)): Q3 += 2
    ps = [x for x in range(p0, Q3, 2) if PL.isprime(x) and n % x]
t0 = time.time(); pts = defi = cand = cert = unc = 0; ex = []
skipped = []
for p in ps:
    if not ((S + n) * p <= 2 * n * (p - 1)): skipped.append(p); continue   # not limit-deficient: no two-prime tail (f-loop case)
    Q = p + 2
    while not ((S + n) * p * (Q + 1) <= 2 * n * (p - 1) * (Q - 1)): Q += 2
    for q in range(p + 2, Q, 2):
        if not (PL.isprime(q) and n % q): continue
        for f in range(1, FE + 1):
            for e in range(1, FE + 1):
                pts += 1
                M, T, ok = PL.chain(C, [(p, f), (q, e)])
                sg = T + M; D = 2 * M - sg
                if D <= 0: continue
                defi += 1
                r = -(-sg // D)
                if not (r * D < 2 * M) or r <= q or not isprime(r) or M % r == 0: continue
                cand += 1
                h, E, rh = 1, sg * (r + 1) - 2 * M * r, r
                while E <= 0: E = r * E + sg; h += 1; rh *= r
                if ok and PL.step(M, T, c, g, r) and E >= c and c <= M * rh and sg >= c: cert += 1; continue   # sg >= c: fact (b) for h > h0
                unc += 1
                if len(ex) < 8: ex.append((p, f, q, e, r, h, E >= c, PL.step(M, T, c, g, r)))
print('prefix', plan, 'p', len(ps), 'FE', FE, 'points', pts, 'deficient', defi, 'star candidates', cand, 'certified', cert,
      'UNCERTIFIED', unc, 'skipped p (not limit-deficient)', skipped[:10], '%.1fs' % (time.time() - t0), flush=True)
for x in ex: print('  uncertified (p,f,q,e,r,h0,E>=c,step):', x, flush=True)
