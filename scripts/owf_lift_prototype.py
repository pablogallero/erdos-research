#!/usr/bin/env python3
"""PROTOTYPE, NOT ADOPTED (2026-11-23, notes/root-loop-3.md §6): "3^>=E in one tree" by lifting, on top of the
FIXED scripts/odd_weird_family.py. Evidence of the trial only; the workers do not use it.

Usage: [ROOTTEST=E] LIFT=0|1 python3 -I scripts/owf_lift_prototype.py K scripts/odd_weird_family.py
(one core, under timeout: with LIFT=1 several cases do not terminate)
LIFT=0 is the root-by-root search unchanged (reference). LIFT=1 replaces every family whose prefix is
3^(>=E) (region) * M' (all other primes exact) by:
  * a in [E, A): the exact family with 3^a (as a root would do);
  * a >= A, where A = E0(M') if Delta(M') = 3 sigma(M') - 4 M' > 0: one pp test of 3^A M' (all n are multiples);
    otherwise A = first a >= E with Qlim - qtop_a <= WIN (Qlim = 4M'/(-Delta)): the exact family at 3^A for
    q <= qtop_A (abundant there, so the pp test covers every a >= A), and for q in (qtop_A, Qlim] a lifted star
    loop: for each e, a*(q,e) = least a >= A with 3^a Delta(M'q^e) >= sigma(M'q^e); pp test of 3^a* M' q^e;
    stop when a*(e) reaches its strict limit value (then a*(e') = a*(e) for all e' > e, all multiples).
"""
import os, sys, time
from math import gcd

k = int(sys.argv[1])
src = open(sys.argv[2]).read()
src = src[:src.index("k=int(sys.argv[1])")]
g = {"__name__": "owf"}
exec(src, g)
sig, isprime, Pstruct, pp_Mqe, st, WIN = g["sig"], g["isprime"], g["Pstruct"], g["pp_Mqe"], g["st"], g["WIN"]
family0 = g["family"]
st["lift"] = 0; st["liftA"] = 0; st["liftpp"] = 0


def least_a(lo, num, den):
    """least a >= lo with 3^a * num >= den (num > 0)."""
    a = lo
    while 3 ** a * num < den:
        a += 1
    return a


def least_a_strict(lo, num, den):
    a = lo
    while 3 ** a * num <= den:
        a += 1
    return a


def pp_at(a, rest, Mp, Sp, q, e):
    f = [(3, a)] + rest
    M = 3 ** a * Mp
    ps = Pstruct(f, M, sig(3, a) * Sp)
    if ps is None:
        return False
    st["liftpp"] += 1
    if e == 0:  # M itself abundant: pseudoperfect iff M is a subset sum of its proper divisors
        return g["inP"](M, ps)
    return pp_Mqe(q, e, M, ps, f)


REGION3 = [False]
search1_0 = g["search1"]


def search1(f, M, sigma, un, ud, j, q0):
    """node-level lift: inside the region tree of 3 (REGION3), split 3^(>=E) into exact 3^a, a in [E, A), plus
    3^(>=A) with 3^A * base abundant (=> True, as any non-deficient prefix). Sound for any status of the others."""
    if LIFT and REGION3[0] and f and f[0][0] == 3 and sigma < 2 * M:
        E = f[0][1]
        Mp, Sp = M // 3 ** E, sigma // sig(3, E)
        Dl = 3 * Sp - 4 * Mp
        if Dl > 0:
            A = least_a(E, Dl, Sp)
            st["lift"] += 1; st["liftA"] += A - E
            REGION3[0] = False
            try:
                for a in range(E, A):
                    Ma, Sa = 3 ** a * Mp, sig(3, a) * Sp
                    na, da = un * sig(3, a) * 2, ud * 3 ** a * 3
                    d = gcd(na, da)
                    if not g["search"]([(3, a)] + f[1:], Ma, Sa, na // d, da // d, j, q0):
                        return False
            finally:
                REGION3[0] = True
            return True  # region 3^(>=A): base 3^A * base(rest) is abundant
    return search1_0(f, M, sigma, un, ud, j, q0)


def family(f, M, sigma, un, ud, q0):
    if LIFT and REGION3[0] and f and f[0][0] == 3:
        E = f[0][1]
        Mp, Sp = M // 3 ** E, sigma // sig(3, E)
        if un * 2 * Mp == ud * 3 * Sp:  # 3 is a region node, every other prime exact
            return family_lift(f, E, Mp, Sp, q0)
    return family0(f, M, sigma, un, ud, q0)


def exact(a, rest, Mp, Sp):
    M, S = 3 ** a * Mp, sig(3, a) * Sp
    d = gcd(S, M)
    return [(3, a)] + rest, M, S, S // d, M // d


def fam_exact(ff, M, S, un, ud, q0):
    """exact family, skipping it when every completion is deficient (bound with q0/(q0-1) below 2)."""
    if un * q0 < 2 * ud * (q0 - 1):
        st["liftskip"] = st.get("liftskip", 0) + 1
        return True
    return family0(ff, M, S, un, ud, q0)


def family_lift(f, E, Mp, Sp, q0):
    st["lift"] += 1
    rest = f[1:]
    Dl = 3 * Sp - 4 * Mp  # never 0 (3 does not divide Mp)
    if Dl > 0:
        A = least_a(E, Dl, Sp)
        for a in range(E, A):
            if not fam_exact(*exact(a, rest, Mp, Sp), q0):
                return False
        st["liftA"] += A - E
        if not pp_at(A, rest, Mp, Sp, None, 0):
            st["fail"].append(("liftM", f, A)); return False
        return True
    Qlim = 4 * Mp // (-Dl)  # q <= Qlim iff 3 Sp q - 4 Mp (q-1) >= 0
    a = E
    while True:
        ff, M, S, un, ud = exact(a, rest, Mp, Sp)
        qtop = S // (2 * M - S)
        if Qlim - qtop <= WIN:
            break
        if not fam_exact(ff, M, S, un, ud, q0):
            return False
        a += 1
        if a - E > 300:
            st["fail"].append(("liftA", f)); return False
    A = a
    st["liftA"] += A - E
    # exact family at 3^A with its star loop limited to q <= qtop_A (q > qtop_A is done below for every a >= A)
    if not family_qchk_only(ff, M, S, un, ud, q0, qtop):
        return False
    q = max(q0, qtop + 1)
    if q % 2 == 0:
        q += 1
    while q <= Qlim:
        if isprime(q):
            st["star"] += 1
            nl = 3 * Sp * q - 4 * Mp * (q - 1)
            if nl > 0:
                alim = least_a_strict(A, nl, Sp * q)
                e = 1
                while True:
                    s_, pe = sig(q, e), q ** e
                    De = 3 * Sp * s_ - 4 * Mp * pe
                    if De > 0:
                        ae = least_a(A, De, Sp * s_)
                        if not pp_at(ae, rest, Mp, Sp, q, e):
                            st["fail"].append(("liftstar", f, q, e, ae)); return False
                        if ae <= alim:
                            break
                    e += 1
                    if e > 200:
                        st["fail"].append(("liftE", f, q)); return False
        q += 2
    return True


def family_qchk_only(f, M, S, un, ud, q0, qtop):
    """exact family with the star loop removed: only primes q <= qtop (M q abundant) are tested."""
    # Emulate by running the original family with WIN = -inf? Not possible; re-implement the qchk part.
    st["fam"] += 1
    D = 2 * M - S
    ps = Pstruct(f, M, S)
    if ps is None:
        st["fail"].append(("nostruct", f)); return False
    B, c, sp = ps
    if q0 <= qtop:
        C = g["C"]
        if c is None:
            wins = [(q0, qtop)]
        else:
            L = C
            wins = [(q0, min(qtop, L // D + 1)), ((sp - L) // D, (M + L) // D + 1), ((S - L) // D, qtop)]
        seen = set()
        for lo, hi in wins:
            for q in g["primes_in"](max(lo, q0), min(hi, qtop)):
                if q in seen:
                    continue
                seen.add(q); st["qchk"] += 1
                if not g["pp_Mq"](q, M, D, ps):
                    st["fail"].append(("Mq", f, q)); return False
    return True


LIFT = int(os.environ.get("LIFT", "1"))
g["family"] = family
g["search1"] = search1
g.update(k=k, CKDEPTH=3, DONE=set(), CK=None, START3=1, STOP3=0)
st["skip"] = 0
t = time.time(); g["t"] = t
rt = os.environ.get("ROOTTEST")
if rt:
    E = int(rt)
    REGION3[0] = True
    ok = g["search"]([(3, E)], 3 ** E, sig(3, E), 3, 2, k - 1, 5)
    print("ROOTTEST", E, ok, {x: y for x, y in st.items() if x != "fail"}, round(time.time() - t, 1))
else:
    if LIFT:  # one region tree for every power of 3, plus the 3-free part
        REGION3[0] = True
        ok3 = g["search"]([(3, 1)], 3, 4, 3, 2, k - 1, 5)
        REGION3[0] = False
        st["tree3"] = ok3
        ok = ok3 and g["search"]([], 1, 1, 1, 1, k, 5)
    else:
        ok = g["search"]([], 1, 1, 1, 1, k, 3)
    print(k, ok, {x: y for x, y in st.items() if x != "fail"}, round(time.time() - t, 1))
for x in st["fail"][:10]:
    print(x)
