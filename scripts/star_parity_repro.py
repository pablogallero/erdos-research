#!/usr/bin/env python3
"""Reproducer for the parity bug in the star loop of `family` (scripts/odd_weird_family.py and .c).

The star loop starts at q = max(q0, qtop + 1) and steps by 2. When qtop is odd, q = qtop + 1 is even and the loop
only visits even numbers: it never tests a prime, and it returns True as soon as the bound U·q/(q−1) < 2 holds.
Every prime in the window (qtop, q_bound] is skipped.

Example (ω = 5, region 3^≥23, from ROOTTEST=23): the family below returns True with 0 star tests, yet
    n = 3^24·5^12·17^6·257^4·65521
is abundant, lies in that family (a multiple of its prefix, last prime 65521 in the window), and no test covers it.
Reads only the repo script (functions only, the search is not run). ~1 s.
Usage: python3 -I scripts/star_parity_repro.py
"""
import os
import sys
from math import gcd

here = os.path.dirname(os.path.abspath(__file__))
src = open(os.path.join(here, "odd_weird_family.py")).read()
src = src[:src.index("k=int(sys.argv[1])")]  # function definitions only
g = {"__name__": "owf_functions"}
exec(src, g)
sig = g["sig"]

f = [(3, 23), (5, 12), (17, 6), (257, 2)]
M = S = 1
for p, e in f:
    M *= p ** e
    S *= sig(p, e)
un, ud = 3 * 5 * 17 * 257, 2 * 4 * 16 * 256  # region bound 3/2·5/4·17/16·257/256 = 2(1 − 2^-16)
d = gcd(un, ud)
un, ud = un // d, ud // d
qtop = S // (2 * M - S)
r = g["family"](f, M, S, un, ud, 259)
print("qtop =", qtop, "(odd)" if qtop % 2 else "(even)", "; family(...) =", r, ";", {k: v for k, v in g["st"].items() if k != "fail"})

n_m = 5 ** 12 * 17 ** 6 * 257 ** 4 * 65521
n_s = sig(5, 12) * sig(17, 6) * sig(257, 4) * 65522
print("3^24·5^12·17^6·257^4·65521 abundant:", sig(3, 24) * n_s >= 2 * 3 ** 24 * n_m,
      "; 3^23·(same) abundant:", sig(3, 23) * n_s >= 2 * 3 ** 23 * n_m)
print("prime 65521 inside the skipped window (qtop, 65535]:", qtop < 65521 <= 65535)
print("BUG REPRODUCED" if r and g["st"]["star"] == 0 and qtop % 2 else "not reproduced")
