# Session 55 (notes/erdos-470.md): how much of the last-prime families the Lean certificate
# (SubsetSumCert.lean: interval step + excess test) covers. Not the omega=6 search.
# Usage: python3 scripts/cert_coverage.py LIM W   (odd deficient M < LIM with omega(M) = W; family = primes
# q > P(M), q not dividing M, with M q abundant, i.e. q <= sigma(M) / (2M - sigma(M)); exponent of q is 1).
import os, sys
_src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'prime_step_check.py')).read()
exec(_src.split("N=int")[0])          # fac, divisors, isprime, info (exact bitsets)
LIM = int(sys.argv[1]); W = int(sys.argv[2])
fam = full = tot = cov_int = cov = 0
for M in range(3, LIM, 2):
    f = fac(M)
    if len(f) != W: continue
    s, bits, c, g = info(M); sig = s + M
    if s >= M: continue
    Q = sig // (2 * M - sig)
    qs = [q for q in range(max(f) + 1, Q + 1) if isprime(q)]
    if not qs: continue
    fam += 1
    if c is None: continue
    ok_int = ok = 0
    for q in qs:
        s2 = s + M + q * s; ex = s2 - M * q          # sum of D(Mq) and the excess
        cond = q * g + 2 * c <= s + 1 and M + 2 * c <= (q + 1) * s + 1 and c <= M * q
        a = cond and M * q + c <= s2
        b = cond and 0 <= ex and (ex >= c or bits[ex] == '1')
        ok_int += a; ok += b
    tot += len(qs); cov_int += ok_int; cov += ok; full += (ok == len(qs))
print("W", W, "LIM", LIM, "families", fam, "fully covered", full, "primes", tot,
      "covered (interval only)", cov_int, "covered (interval + excess)", cov)
