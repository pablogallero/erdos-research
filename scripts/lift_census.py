# Session 88 (notes/erdos-470.md): would "lifting" in the prefix exponents make a Lean replay of the omega = 6 search feasible?
# Read-only on a COPY of the gen-1 checkpoint, used only for the SHAPES of the exact deficient 3-prime prefixes (gen-1 has the
# parity bug: not evidence). Python only; decides nothing about #470; never runs owf.
# Usage: python3 -I scripts/lift_census.py CKFILE triples
#        python3 -I scripts/lift_census.py CKFILE flips CAP NS SEED      (pair categories vs the limit ratio L = prod p/(p-1))
#        python3 -I scripts/lift_census.py CKFILE families TH [TH ...]   (exponent e of p FREE iff p^(e+1) >= TH)
import ast, math, random, sys
from fractions import Fraction as Fr
from math import gcd

# Mean kernel seconds per prefix by prime triple (notes/data/lean-cost-census-s87.txt); other triples: 50 s.
COST = {(3, 5, 17): 4600, (3, 5, 19): 780, (3, 5, 23): 180, (3, 5, 29): 84, (3, 5, 31): 43, (3, 7, 11): 56, (3, 7, 13): 45,
        (3, 5, 37): 19, (3, 5, 41): 9, (3, 7, 19): 4, (3, 5, 47): 2}


def sig(p, e): return (p ** (e + 1) - 1) // (p - 1)


def prefixes(ck):
    P = set()
    for line in open(ck):
        line = line.strip()
        if not line.endswith(')'): continue
        try: f, un, ud, j, q0 = ast.literal_eval(line)
        except Exception: continue
        if j != 3 or len(f) != 3: continue
        n = s = 1
        for p, e in f: n *= p ** e; s *= sig(p, e)
        g = gcd(s, n)
        if (un, ud) != (s // g, n // g) or 2 * n <= s: continue      # exact (not region) and deficient
        P.add(tuple(f))
    return P


def sieve(N):
    sv = bytearray([1]) * (N + 1); sv[0] = sv[1] = 0
    for i in range(2, int(N ** .5) + 1):
        if sv[i]: sv[i * i::i] = bytearray(len(sv[i * i::i]))
    return sv


def cats(rho, plo, sv, cap):
    """Pair (p, q) categories at ratio rho = sigma(n)/n, q < cap: pab (n p limit-abundant), bnd (bounded), free (not bounded),
    tail (q >= q-tail, omitted = default). p >= Q3 needs nothing (loop stops)."""
    out = {}
    for p in range(plo, cap):
        if not sv[p]: continue
        if rho * p * (p + 1) <= 2 * (p - 1) ** 2: break
        for q in range(p + 1, cap):
            if not sv[q]: continue
            if rho * p >= 2 * (p - 1): out[(p, q)] = 'pab'
            elif rho * p * (q + 1) <= 2 * (p - 1) * (q - 1): continue
            else: out[(p, q)] = 'free' if rho * p * q >= 2 * (p - 1) * (q - 1) else 'bnd'
    return out


def limit(T):
    L = Fr(1)
    for p in T: L *= Fr(p, p - 1)
    return L


def main():
    P = prefixes(sys.argv[1]); mode = sys.argv[2]
    by = {}
    for f in P: by.setdefault(tuple(p for p, _ in f), []).append(f)
    if mode == 'triples':
        roots = {}
        for f in P: roots.setdefault(f[0][1], set()).add(tuple(p for p, _ in f))
        print('%d exact deficient 3-prime prefixes, %d distinct prime triples; triples per root: %s' % (
            len(P), len(by), {E: len(t) for E, t in sorted(roots.items())}))
        for T, l in sorted(by.items(), key=lambda t: -len(t[1])):
            print(T, len(l), 'L = %.6f' % float(limit(T)))
    elif mode == 'flips':
        cap, ns, seed = map(int, sys.argv[3:6]); sv = sieve(cap); random.seed(seed); bk = {}
        for T, l in sorted(by.items(), key=lambda t: -len(t[1])):
            L = limit(T)
            if L >= 2: continue                              # n eventually abundant: finitely many deficient prefixes
            CL = cats(L, max(T) + 1, sv, cap)
            for f in random.sample(sorted(l), min(ns, len(l))):
                n = s = 1
                for p, e in f: n *= p ** e; s *= sig(p, e)
                rho = Fr(s, n); C = cats(rho, max(T) + 1, sv, cap)
                d = sum(1 for k in set(C) | set(CL) if C.get(k, 'tail') != CL.get(k, 'tail'))
                bk.setdefault(int(math.floor(-math.log10(float((L - rho) / L)))), []).append(d)
        for b in sorted(bk):
            v = sorted(bk[b])
            print('relative gap (L-rho)/L in [1e-%d, 1e-%d): %d prefixes, flipped pairs median %d max %d, zero flips %d' % (
                b + 1, b, len(v), v[len(v) // 2], v[-1], v.count(0)))
    elif mode == 'families':
        per = sum(COST.get(tuple(p for p, _ in f), 50) for f in P)
        for TH in map(int, sys.argv[3:]):
            fam = {}
            for f in P:
                k = tuple((p, 'F' if p ** (e + 1) >= TH else e) for p, e in f); fam[k] = fam.get(k, 0) + 1
            lif = sum(COST.get(tuple(p for p, _ in k), 50) for k in fam)
            print('TH %g: %d prefixes -> %d families (all-free %d); kernel estimate per prefix %.0f h, per family %.0f h (gain %.1fx)'
                  % (TH, len(P), len(fam), sum(all(x == 'F' for _, x in k) for k in fam), per / 3600, lif / 3600, per / lif))


if __name__ == '__main__':
    main()
