#!/usr/bin/env python3
"""Sampling profile of an odd_weird_family run from its `progress` lines (read-only, no CPU for the search).

The C/Python search prints `progress N FAM SECONDS [(p,e), ...]` to stderr every 200000 nodes. Each line is
a sample of the DFS path at a fixed node interval, so the share of lines whose path starts with a given
prefix = the share of NODES spent below that prefix (a node-count profile per branch, like `perf` samples).

Usage: python3 scripts/roottest_branch_profile.py LOG [LOG ...]
Prints, per depth 1..4, the prefixes (primes + exponents) with most samples; the share of samples whose path
contains the Fermat primes 5, 17, 257 (and 65537); and the node rate per exponent of 5.
"""
import ast
import re
import sys
from collections import Counter

samples = []
for fn in sys.argv[1:]:
    for line in open(fn, errors="replace"):
        m = re.match(r"progress (\d+) (\d+) (\d+) (\[.*\])\s*$", line)
        if m:
            samples.append((int(m.group(1)), int(m.group(3)), ast.literal_eval(m.group(4))))
n = len(samples)
print("samples: %d (= %.1fM nodes at 200k nodes per sample)" % (n, n * 0.2))
if not n:
    sys.exit(0)
for depth in (2, 3, 4):
    c = Counter(tuple(p[:depth]) for _, _, p in samples if len(p) >= depth)
    print("depth %d, top prefixes (share of samples):" % depth)
    for k, v in c.most_common(8):
        print("   %5.1f%%  %s" % (100.0 * v / n, "·".join("%d^%d" % pe for pe in k)))
c = Counter(tuple(p for p, _ in path[1:]) for _, _, path in samples)
print("prime sets below 3 (ignoring exponents), top:")
for k, v in c.most_common(10):
    print("   %5.1f%%  %s" % (100.0 * v / n, ",".join(map(str, k))))
fer = sum(1 for _, _, p in samples if {5, 17, 257} <= {q for q, _ in p})
fer4 = sum(1 for _, _, p in samples if {5, 17, 257, 65537} <= {q for q, _ in p})
f517 = sum(1 for _, _, p in samples if {5, 17} <= {q for q, _ in p})
print("paths containing 5 and 17: %.1f%%; 5, 17, 257: %.1f%%; 5, 17, 257, 65537: %.1f%%"
      % (100.0 * f517 / n, 100.0 * fer / n, 100.0 * fer4 / n))
# node rate per exponent of 5 (only consecutive samples inside the same 5^b)
rate = {}
for (n1, t1, p1), (n2, t2, p2) in zip(samples, samples[1:]):
    if len(p1) > 1 and len(p2) > 1 and p1[1] == p2[1] and p1[1][0] == 5 and t2 > t1:
        b = p1[1][1]
        a = rate.setdefault(b, [0, 0])
        a[0] += n2 - n1
        a[1] += t2 - t1
b5 = Counter(p[1][1] for _, _, p in samples if len(p) > 1 and p[1][0] == 5)
print("exponent b of 5: samples (Mnodes) and node rate where measurable")
for b in sorted(b5):
    r = rate.get(b)
    print("   5^%-3d %6.1f Mnodes  %s" % (b, b5[b] * 0.2, ("%.0f nodes/s" % (r[0] / r[1])) if r else ""))
