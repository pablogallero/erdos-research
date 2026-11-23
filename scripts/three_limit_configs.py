#!/usr/bin/env python3
"""Erdős #470, ω = 6, root loop over the exponent of 3: does it close, and when?

Read-only maths helper (does not run the search, writes nothing). See notes/root-loop-3.md.

For n = 3^a·m (gcd(m, 6) = 1, ω(m) = 5) put ρ(m) = σ(m)/m. Then 3^a·m is abundant iff
    3^a·(3σ(m) − 4m) ≥ σ(m),
so 3^a·m is deficient for every a when ρ(m) < 4/3 (σ(3^a)/3^a < 3/2), and otherwise becomes abundant
from a = E0(m) = ⌈log_3(σ(m)/Δ(m))⌉ on, with Δ(m) = 3σ(m) − 4m ≥ 1. The region test "3^≥E" of the
search can only be True if E ≥ E0(m) for every m it cannot rule out otherwise, so the loop closes iff
sup E0 is finite (modulo pseudoperfect tests), and sup E0 = ∞ iff ρ(m) accumulates at 4/3 from
above, i.e. iff there is a LIMIT CONFIGURATION: ≤ 5 primes p ≥ 5 with exponents in {1, 2, …} ∪ {∞},
at least one ∞, and
    ∏_{e = ∞} p/(p−1) · ∏_{e finite} σ(p^e)/p^e  =  4/3   exactly.
This script enumerates such configurations (exactly), and the closest ones that miss 4/3
(those make the search slow without making it infinite).

Usage: python3 scripts/three_limit_configs.py [PMAX] [EMAX] [NPRIMES]
  PMAX: bound for every prime except the last one, which is solved exactly (default 2000);
  EMAX: largest finite exponent tried (default 4); NPRIMES: max number of primes (default 5).
Exhaustive within those caps (the last prime is not capped); NOT a proof for larger caps.
"""
import sys
from fractions import Fraction as F

PMAX = int(sys.argv[1]) if len(sys.argv) > 1 else 2000
EMAX = int(sys.argv[2]) if len(sys.argv) > 2 else 4
NP = int(sys.argv[3]) if len(sys.argv) > 3 else 5
TARGET = F(4, 3)
INF = None


def isprime(n):
    if n < 2:
        return False
    if n % 2 == 0:
        return n == 2
    i = 3
    while i * i <= n:
        if n % i == 0:
            return False
        i += 2
    return True


PR = [p for p in range(5, PMAX + 1) if isprime(p)]


def fac(p, e):
    return F(p, p - 1) if e is INF else F(p ** (e + 1) - 1, (p - 1) * p ** e)


def last_prime_solutions(t, pmin):
    """all (p, e) with p prime >= pmin, p != 3, and fac(p, e) == t (exact)."""
    out = []
    if t <= 1:
        return out
    # e = ∞: p/(p-1) = t  <=>  p = t/(t-1)
    x = t / (t - 1)
    if x.denominator == 1 and x.numerator >= pmin and isprime(x.numerator):
        out.append((x.numerator, INF))
    # e finite: denominator of t must be p^e (σ(p^e) is coprime to p)
    d = t.denominator
    for e in range(1, 200):
        r = round(d ** (1.0 / e))
        for p in (r - 1, r, r + 1):
            if p >= max(pmin, 5) and p ** e == d and isprime(p) and fac(p, e) == t:
                out.append((p, e))
        if 2 ** e > d:
            break
    return out


sols, near = [], []


def dfs(cfg, val, pidx, left):
    t = TARGET / val
    if t == 1 and cfg:
        if any(e is INF for _, e in cfg):
            sols.append(list(cfg))
        return
    if t < 1 or left == 0:
        return
    pmin = PR[pidx] if pidx < len(PR) else PMAX + 1
    # last prime (or any prime as the last one): solve exactly, no cap
    for p, e in last_prime_solutions(t, pmin):
        c = cfg + [(p, e)]
        if any(x is INF for _, x in c):
            sols.append(c)
    if left == 1:
        # record the closest miss from below with one more prime at its limit
        return
    for i in range(pidx, len(PR)):
        p = PR[i]
        if F(p, p - 1) ** left < t:  # even all-∞ primes >= p cannot reach t
            break
        for e in list(range(1, EMAX + 1)) + [INF]:
            f = fac(p, e)
            nv = val * f
            if nv > TARGET:
                continue
            gap = TARGET - nv
            if gap < TARGET * F(1, 10 ** 4):
                near.append((float(gap / TARGET), cfg + [(p, e)]))
            dfs(cfg + [(p, e)], nv, i + 1, left - 1)


dfs([], F(1), 0, NP)


def show(c):
    return "·".join("%d^%s" % (p, "∞" if e is INF else e) for p, e in c)


print("caps: PMAX=%d EMAX=%d NPRIMES=%d" % (PMAX, EMAX, NP))
print("exact limit configurations (value 4/3, at least one ∞):", len(sols))
for c in sols[:50]:
    print("  ", show(c))
# closest misses from below that use only ∞ exponents (these are the search's worst near-ties)
allinf = sorted((g, c) for g, c in near if all(e is INF for _, e in c) and g > 0)
print("closest all-∞ configurations below 4/3 (relative gap 1 − (3/4)·∏p/(p−1)):")
for g, c in allinf[:12]:
    print("   %.3e  %s" % (g, show(c)))
