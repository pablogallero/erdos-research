#!/usr/bin/env python3
"""Erdős #470, ω = 6: explicit m with a large closing exponent E0(m) (see notes/root-loop-3.md).

For m coprime to 6 with 3σ(m) > 4m, E0(m) = min{e : 3^e·(3σ(m) − 4m) ≥ σ(m)} is the first exponent of 3
for which 3^e·m is abundant (3^e·m is deficient for every e < E0(m)). Every m with ω(m) = 5 gives
    ROOTTEST=E is False for every E < E0(m)
(the region test 3^≥E would need a pseudoperfect divisor of 3^E·m, which is deficient).

The worst m come from the Fermat primes: (3/4)·∏_{p∈{5,17,257,65537}} p/(p−1) = 1 − 2^-32. With a 5th prime q < 2^32:
    3σ(m)/(4m) = (1 − 2^-32)(1 + 1/q)·∏_p (1 − p^-(e_p+1))    (q to the first power)
and G = 3σ(m)/(4m) − 1 can be made tiny by choosing q close to 2^32 and the exponents so that the losses
∑ p^-(e_p+1) almost cancel G0(q) = (1 − 2^-32)(1 + 1/q) − 1. E0 ≈ log_3(1/(3G)).

Usage: python3 scripts/three_e0_fermat.py [QWINDOW] [EXPMAX]
  scans the primes q in [2^32 − QWINDOW, 2^32) (default 2·10^5) and exponents 1..EXPMAX (default 70)
  of 5, 17, 257, 65537; prints the best m found, verified with exact integer arithmetic.
Env: KF=3 (ω = 5 calibration: Fermat primes 5, 17, 257 and q < 2^16); FREE=5|17 with E3=E (closing exponent of
5 or 17 inside the region 3^≥E, exact 3^E); LO/HI (range of loss sums kept, default 1e-26..1e-13).
This is a LOWER BOUND for sup E0 (a search over one family only), not the supremum.
"""
import os
import sys
from bisect import bisect_left

QW = int(sys.argv[1]) if len(sys.argv) > 1 else 200000
XM = int(sys.argv[2]) if len(sys.argv) > 2 else 70
# KF = number of Fermat primes > 3 in m besides q: 4 for ω = 6 (default), 3 for ω = 5 (calibration)
KF = int(os.environ.get("KF", "4"))
FP = (5, 17, 257, 65537)[:KF]
TW = 1 << (1 << (KF + 1))  # (3/4)·∏ F/(F-1) = 1 - 1/TW;  TW = 2^32 for KF = 4, 2^16 for KF = 3


def isprime(n):
    if n < 2:
        return False
    for p in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        if n % p == 0:
            return n == p
    d, s = n - 1, 0
    while d % 2 == 0:
        d //= 2
        s += 1
    for a in (2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37):
        x = pow(a, d, n)
        if x in (1, n - 1):
            continue
        for _ in range(s - 1):
            x = x * x % n
            if x == n - 1:
                break
        else:
            return False
    return True


def sig(p, e):
    return (p ** (e + 1) - 1) // (p - 1)


# FREE = the prime whose closing exponent is computed (3: the root loop; 5: the loop over 5^b inside the
# region 3^>=E3, i.e. what ROOTTEST=E3 has to go through). The other Fermat primes vary their exponents.
FREE = int(os.environ.get("FREE", "3"))
E3 = int(os.environ.get("E3", "50"))
VAR = [p for p in FP if p != FREE]
LO, HI = float(os.environ.get("LO", "1e-26")), float(os.environ.get("HI", "1e-13"))


def gen(i, s, ex):
    if i == len(VAR):
        sums.append((s, tuple(ex)))
        return
    p = VAR[i]
    for e in range(1, XM + 1):
        x = float(p) ** -(e + 1)
        if s + x <= HI:
            gen(i + 1, s + x, ex + [e])
        if x < LO * 1e-3:
            break


sums = []
base = 0.0 if FREE == 3 else 3.0 ** -(E3 + 1)  # loss of the exact 3^E3 when FREE != 3
gen(0, base, [])
sums.sort()
SV = [s for s, _ in sums]

best = []
q = TW - 1
nq = 0
while q > TW - QW:
    if isprime(q):
        nq += 1
        for h in (1, 2):  # exponent of q
            # G0 = (1 - 2^-32)·σ(q^h)/q^h - 1, numerator computed exactly
            g0 = ((TW - 1) * sig(q, h) - TW * q ** h) / float(TW * q ** h)
            i = bisect_left(SV, g0) - 1
            for k in range(max(0, i - 2), i + 1):
                if k < 0 or k >= len(sums):
                    continue
                s, ex = sums[k]
                best.append((g0 - s, q, h, ex))
        if len(best) > 4000:
            best.sort()
            best = [x for x in best[:200]]
    q -= 2
best.sort()

# exact verification of the candidates: G > 0 and the closing exponent of FREE
out = []
for _, q, h, ex in best[:400]:
    m, sg = q ** h, sig(q, h)
    for p, e in zip(VAR, ex):
        m *= p ** e
        sg *= sig(p, e)
    if FREE == 3:
        D = 3 * sg - 4 * m  # 3^e·m abundant iff 3^e·D >= σ(m)
        if D <= 0:
            continue
        e = 0
        while 3 ** e * D < sg:
            e += 1
    else:  # N = 3^E3·m·FREE^e abundant iff σ(3^E3)σ(m)σ(FREE^e) >= 2·3^E3·m·FREE^e
        A, B = sig(3, E3) * sg, 2 * 3 ** E3 * m
        if A * FREE >= B * (FREE - 1):
            pass
        else:
            continue
        e = 1
        while A * sig(FREE, e) < B * FREE ** e:
            e += 1
            if e > 500:
                break
    out.append((e, q, h, ex))
out.sort(reverse=True)
print("FREE=%d%s: scanned %d primes q in [TW-%d, TW), exponents <= %d, %d loss sums"
      % (FREE, "" if FREE == 3 else " (3^%d exact)" % E3, nq, QW, XM, len(sums)))
print("largest closing exponent of %d found (exact integer check):" % FREE)
for e, q, h, ex in out[:8]:
    print("  %d^%d  m = %s·%d^%d" % (FREE, e, "·".join("%d^%d" % pe for pe in zip(VAR, ex)), q, h))
