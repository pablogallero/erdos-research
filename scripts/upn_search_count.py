"""Node count of the `upnCheck` search (ErdosResearch/UnitaryPerfectFiveOdd.lean), in Python.

Usage: python3 -I scripts/upn_search_count.py R [--ppow]

Searches 2 <= y1 < ... < yR, pairwise coprime, with prod(1 + y) = 2 prod(y), exactly as
`upnCheck` does (the y = L / y >= L+1 split, the ascending-product bound, the linear last step).
With --ppow it also requires every y to be a prime power (`upnCheck` does not do this).
Prints R, the number of nodes, the maximum depth (the fuel needed) and the solutions.
Measured: R=6: 29392 nodes, depth 2087, none (--ppow: 16672). R=7: 20866746 nodes,
solution (3,5,7,13,67,1741,8704) (8704 = 2^9*17 is not a prime power); --ppow: 5787225, none.
"""
import sys
from math import gcd

def asc(L, r):
    p = 1
    for j in range(r):
        p *= L + j
    return p

def ppow(v):
    p = 2
    while p * p <= v and v % p:
        p += 1
    if v % p:
        return True
    while v % p == 0:
        v //= p
    return v == 1

def main():
    r = int(sys.argv[1]); use_pp = '--ppow' in sys.argv
    ok = (lambda v: ppow(v)) if use_pp else (lambda v: True)
    st = {'n': 0, 'depth': 0, 'sol': []}
    def check(P, Q, L, pre, r, d, path):
        st['n'] += 1; st['depth'] = max(st['depth'], d)
        if r == 0:
            if Q == 2 * P:
                st['sol'].append(path)
            return
        if 2 * P <= Q:
            return
        if r == 1:
            dd = 2 * P - Q
            if Q % dd:
                return
            y = Q // dd
            if y >= L and all(gcd(y, p) == 1 for p in pre) and ok(y):
                st['sol'].append(path + [y])
            return
        while Q * asc(L + 1, r) >= 2 * P * asc(L, r):
            if all(gcd(L, p) == 1 for p in pre) and ok(L):
                check(P * L, Q * (1 + L), L + 1, pre + [L], r - 1, d + 1, path + [L])
            L += 1; d += 1; st['n'] += 1; st['depth'] = max(st['depth'], d)
    sys.setrecursionlimit(1000000)
    check(1, 1, 2, [], r, 0, [])
    print(r, st['n'], st['depth'], st['sol'])

main()
