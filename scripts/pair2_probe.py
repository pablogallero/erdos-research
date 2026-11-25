# Session 87 (notes/erdos-470.md): Python twin of Lean `ErdosResearch/SubsetSumPair2.lean` (`pairOK2`, start row er) and a
# parameter finder `find2`. Compares with pair_cert_gen.find (pairOK, er = 1) on every free-r pair below a prefix.
# Usage: python3 -I scripts/pair2_probe.py N S c g PLO PHI QHI    (Python only; decides nothing about #470; no owf)
# e.g. N = 3^16*5^11*19^8, S = 34953892078295791325867031, c = 57, g = 2, 23 287 20000 -> 599 old ok, 1 new ok er=2 (109, 797)
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
sys.dont_write_bytecode = True
import pair_cert_gen as PG
from pair_cert_gen import stepAbOK, stepRowOK, stepPointOK, stepsEnd, ceil_div, point_r1
CAP = 40
def pairOK2(n, S, c, g, p, q, F, fr, er, ec, e0, f0, r1):
    if not (stepAbOK(n, S, c, g, [(p, fr), (q, er)]) and stepAbOK(n, S, c, g, [(p, F), (q, ec)])): return False
    for f in range(1, F):
        if not stepRowOK(n, S, c, g, q, 2, r1(f, 0), e0(f), [(p, f)]): return False
        for e in range(1, e0(f)):
            if not stepPointOK(n, S, c, g, 2, r1(f, e), [(p, f), (q, e)]): return False
    for e in range(1, er):
        if not stepRowOK(n, S, c, g, p, 2, r1(0, e), f0(e), [(q, e)]): return False
        for f in range(F, f0(e)):
            if not stepPointOK(n, S, c, g, 2, r1(f, e), [(p, f), (q, e)]): return False
    for f in range(F, fr):
        for e in range(er, ec):
            if not (stepAbOK(n, S, c, g, [(p, f), (q, e)]) or stepPointOK(n, S, c, g, 2, r1(f, e), [(p, f), (q, e)])):
                return False
    return True
def lim_r1(m, Sm, p):
    if not ((Sm + m) * p < 2 * m * (p - 1)): return None
    num, den = 2 * (Sm + m) * p - 2 * m * (p - 1), 2 * m * (p - 1) - (Sm + m) * p
    return max(0, ceil_div(num, den))
def find2(n, S, c, g, p, q):
    if (S + n) * p * q <= 2 * n * (p - 1) * (q - 1): return None, 'bounded'
    e0t, f0t, r1t = {}, {}, {}
    F = 1
    while True:
        m, Sm = stepsEnd(n, S, [(p, F)]); r = lim_r1(m, Sm, q)
        if r is None: break
        if F > CAP: return None, 'F>CAP'
        e0 = 1
        while not stepRowOK(n, S, c, g, q, 2, r, e0, [(p, F)]):
            e0 += 1
            if e0 > CAP: return None, 'row f'
        e0t[F] = e0; r1t[(F, 0)] = r
        for e in range(1, e0):
            M, T = stepsEnd(n, S, [(p, F), (q, e)])
            if T >= M: return None, 'abundant col point'
            r1t[(F, e)] = point_r1(M, T)
        F += 1
    er = 1
    while True:
        m, Sm = stepsEnd(n, S, [(q, er)]); r = lim_r1(m, Sm, p)
        if r is None: break
        if er > CAP: return None, 'er>CAP'
        f0 = F
        while not stepRowOK(n, S, c, g, p, 2, r, f0, [(q, er)]):
            f0 += 1
            if f0 > CAP: return None, 'row e'
        f0t[er] = f0; r1t[(0, er)] = r
        for f in range(F, f0):
            M, T = stepsEnd(n, S, [(p, f), (q, er)])
            if T >= M: return None, 'abundant row point'
            r1t[(f, er)] = point_r1(M, T)
        er += 1
    fr = F
    while not stepAbOK(n, S, c, g, [(p, fr), (q, er)]):
        fr += 1
        if fr > CAP: return None, 'fr>CAP'
    ec = er
    while not stepAbOK(n, S, c, g, [(p, F), (q, ec)]):
        ec += 1
        if ec > CAP: return None, 'ec>CAP'
    for f in range(F, fr):
        for e in range(er, ec):
            if stepAbOK(n, S, c, g, [(p, f), (q, e)]): continue
            M, T = stepsEnd(n, S, [(p, f), (q, e)])
            if T >= M: return None, 'abundant box point'
            r1t[(f, e)] = point_r1(M, T)
    e0f = lambda f: e0t.get(f, 1); f0f = lambda e: f0t.get(e, 0); r1f = lambda f, e: r1t.get((f, e), 0)
    if not pairOK2(n, S, c, g, p, q, F, fr, er, ec, e0f, f0f, r1f): return None, 'pairOK2 false'
    return (F, fr, er, ec, e0t, f0t, r1t), None
if __name__ == '__main__':
    n, S, c, g, plo, phi, qhi = map(int, sys.argv[1:8])
    tot = {}
    for p in range(plo, phi):
        if not (PG.isprime(p) and n % p): continue
        qt = PG.q_tail(n, S, p)
        if PG.stepAbOK(n, S, c, g, [(p, 1)]): continue
        rg = PG.q_range(n, S, c, g, p)
        for q in range(p + 1, min(qhi, qt) if qt else qhi):
            if not (PG.isprime(q) and n % q) or (rg and rg[0] <= q <= rg[1]): continue
            r1, why1 = PG.find(n, S, c, g, p, q)
            if r1: 
                r2, w2 = find2(n, S, c, g, p, q)
                tot['old ok, new ' + ('ok' if r2 and r2[2] == 1 else str(w2) if not r2 else 'er>1')] = tot.get('old ok, new ' + ('ok' if r2 and r2[2] == 1 else str(w2) if not r2 else 'er>1'), 0) + 1
                continue
            if why1.startswith('bounded'): continue
            r2, w2 = find2(n, S, c, g, p, q)
            k = 'old fail(%s), new %s' % (why1[:12], 'ok er=%d' % r2[2] if r2 else w2)
            tot[k] = tot.get(k, 0) + 1
            if r2: print(p, q, r2[:4], file=sys.stderr)
    print(tot)
