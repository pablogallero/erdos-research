# Session 83 (notes/erdos-470.md): measure the QUADRANT certificate for bounded pairs (p, q) below a prefix n.
# Bounded pair: (S+n) p q < 2 n (p-1)(q-1), i.e. every n p^f q^e is deficient and n p^f q^e r can only be abundant for r below
# a bound that is nondecreasing in (f, e) and eventually constant. quadOK (Lean: ErdosResearch/SubsetSumQuad.lean) checks the
# row invariant of session 81 at ONE corner (f0, e0) and the 2-D limit with one r1; it then holds on the whole quadrant
# f >= f0, e >= e0. The rest of the pair: rows f < f0 (rowOK in q), columns e < e0 (rowOK in p), finitely many points.
# Usage: python3 -I scripts/quad_probe.py N S c g PLO PHI QHI      (Python only; decides nothing about #470; no owf)
#   LEAN=late K0 K1: also print a Lean module with `boundedOK` instances (ErdosResearch/SubsetSumQuad.lean) for the bounded
#   pairs number K0 <= k < K1 (in scan order) below the late prefix (N, S, c, g must be its certificate); NS = Lean namespace.
#   Session 83: NS=SubsetSumQuadGenA ... 0 116 > ErdosResearch/SubsetSumQuadGenA.lean, NS=SubsetSumQuadGenB ... 116 232.
import os, sys
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pair_cert_gen import ppSum_exact, stepsEnd, stepRowOK, stepPointOK, point_r1, ceil_div, isprime, q_tail

CAP = int(os.environ.get('CAP', '40'))


def r1_limit2(n, S, p, q):            # least r1 with (S+n) p q (r1+2) <= 2 (r1+1) n (p-1)(q-1)
    a, b = (S + n) * p * q, 2 * n * (p - 1) * (q - 1)
    if b <= a: return None
    return max(0, ceil_div(2 * a - b, b - a))


def rowInv(m, S, c, g, q, r0, r1, e):
    P = ppSum_exact(m, q, S, e); Me = m * q ** e
    return (r1 * g + 2 * c <= P + 1 and 2 * r1 * Me + c <= (r1 + 1) * (P + Me)
            and (r0 + 2) * Me + 2 * c <= (r0 + 1) * (P + Me) + 1 and c <= Me * r0)


def quadOK(n, S, c, g, p, q, r0, r1, f0, e0):
    if not (1 <= c and n % p and n % q and p != q): return False
    if not (p * g + 2 * c <= S + 1 and n + 2 * c <= (p + 1) * S + 1): return False
    m, Sm = stepsEnd(n, S, [(p, f0)])
    if not (q * g + 2 * c <= Sm + 1 and m + 2 * c <= (q + 1) * Sm + 1): return False
    if not (S + n) * p * q * (r1 + 2) <= 2 * (r1 + 1) * n * (p - 1) * (q - 1): return False
    nq, Sq = stepsEnd(n, S, [(q, e0)])
    return rowInv(nq, Sq, c, g, p, r0, r1, f0)


def row_r1(m, Sm, q):                 # least r1 with the row limit (S+m) q (r1+2) <= 2 (r1+1) m (q-1)
    a, b = (Sm + m) * q, 2 * m * (q - 1)
    if b <= a: return None
    return max(0, ceil_div(2 * a - b, b - a))


def line(n, S, c, g, p, q, f, fmax_pts, lo=1):
    """Row f of the pair (exponent of p fixed = f, e varies): (e-start of rowOK, #points, r1 of the row,
    {e: r1 of the point (f, e)} for lo <= e < start) or None. (Points are listed in the order (p, f), (q, e).)"""
    m, Sm = stepsEnd(n, S, [(p, f)])
    r1 = row_r1(m, Sm, q)
    if r1 is None: return None
    for e0 in range(1, CAP + 1):
        if stepRowOK(n, S, c, g, q, 2, r1, e0, [(p, f)]):
            pts = {}
            for e in range(lo, e0):
                M, T = stepsEnd(n, S, [(p, f), (q, e)])
                pts[e] = point_r1(M, T)
            return e0, max(0, e0 - lo), r1, pts
    return None


def pair(n, S, c, g, p, q):
    r1 = r1_limit2(n, S, p, q)
    if r1 is None: return None, 'not bounded'
    best = None
    for s in range(2, 2 * CAP):
        for f0 in range(1, s):
            e0 = s - f0
            if e0 > CAP or f0 > CAP: continue
            if quadOK(n, S, c, g, p, q, 2, r1, f0, e0):
                best = (f0, e0); break
        if best: break
    if not best: return None, 'no quadrant'
    f0, e0 = best
    cells = 1
    rows, cols = {}, {}
    for f in range(1, f0):           # rows f < f0, all e >= 1
        L = line(n, S, c, g, p, q, f, CAP)
        if L is None: return None, 'row f=%d' % f
        for e, r in L[3].items():
            if not stepPointOK(n, S, c, g, 2, r, [(p, f), (q, e)]): return None, 'point (%d,%d)' % (f, e)
        cells += 1 + L[1]; rows[f] = L
    for e in range(1, e0):           # columns e < e0, f >= f0 (rowOK in p from f-start; points f0 <= f < start)
        L = line(n, S, c, g, q, p, e, CAP, lo=f0)
        if L is None: return None, 'col e=%d' % e
        for f, r in L[3].items():
            if not stepPointOK(n, S, c, g, 2, r, [(p, f), (q, e)]): return None, 'point (%d,%d)' % (f, e)
        cells += 1 + L[1]; cols[e] = L
    return (f0, e0, r1, cells, rows, cols), 'ok'


def main():
    n, S, c, g, plo, phi, qhi = map(int, sys.argv[1:8])
    Q3 = 2
    while not (S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1): Q3 += 1
    phi = min(phi, Q3)
    tot = ok = cells = 0; fails = {}; quads = {}; found = []
    for p in range(plo, phi):
        if not (isprime(p) and n % p): continue
        qt = q_tail(n, S, p)
        for q in range(p + 1, min(qhi, qt) if qt else qhi):
            if not (isprime(q) and n % q): continue
            if r1_limit2(n, S, p, q) is None: continue
            tot += 1
            res, why = pair(n, S, c, g, p, q)
            if res is None:
                fails[why.split('=')[0]] = fails.get(why.split('=')[0], 0) + 1
                if sum(fails.values()) <= 5: print('FAIL p=%d q=%d: %s' % (p, q, why), file=sys.stderr)
                continue
            ok += 1; cells += res[3]; k = res[:2]; quads[k] = quads.get(k, 0) + 1
            found.append((p, q, res))
    print('Q3 %d; bounded pairs below the q-tails %d: certified %d (total cells %d), failed %s' % (Q3, tot, ok, cells, fails), file=sys.stderr)
    print('quadrant corners (f0, e0): %s' % dict(sorted(quads.items(), key=lambda t: -t[1])[:10]), file=sys.stderr)
    if os.environ.get('LEAN') in ('late', 'real'):
        k0, k1 = map(int, sys.argv[8:10])
        print(emit(found[k0:k1], k0, ' '.join(sys.argv[1:10])), end='')


LATE = (3 ** 3 * 23 * 13 ** 10 * 17 ** 2 * 11, 256030928920159929, 2295, 5)
# LEAN=real: the real prefix 3^16*5^11*19^8 with its generated certificate (ErdosResearch/OddWeirdPrefixIG.lean)
DESC = {'late': '3^3·23·13^10·17^2·11` (late prefix)', 'real': '3^16·5^11·19^8` (a real prefix of the search)'}
PREFIXES = {'late': (LATE, 'lateN', 'ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix', 'ErdosResearch.SubsetSumQuad'),
            'real': ((3 ** 16 * 5 ** 11 * 19 ** 8, 34953892078295791325867031, 57, 2), '(3 ^ 16 * 5 ^ 11 * 19 ^ 8)',
                     'ErdosResearch.OddWeirdPrefixIG.intervalGap_real', 'ErdosResearch.OddWeirdPrefixIG')}


def r1fun(f0, e0, rows, cols):
    """Lean `fun f e => ...` for the r1 table of `boundedOK`."""
    items = []
    for f, L in sorted(rows.items()):
        items.append(('f = %d ∧ e = 0' % f, L[2]))
        items += [('f = %d ∧ e = %d' % (f, e), r) for e, r in sorted(L[3].items())]
    for e, L in sorted(cols.items()):
        items.append(('f = 0 ∧ e = %d' % e, L[2]))
        items += [('f = %d ∧ e = %d' % (f, e), r) for f, r in sorted(L[3].items())]
    body = '0'
    for cond, r in reversed(items):
        body = 'if %s then %d else %s' % (cond, r, body)
    return 'fun f e => ' + body


def tabfun(d):
    body = '0'
    for k, v in sorted(d.items(), reverse=True):
        body = 'if x = %d then %d else %s' % (k, v, body)
    return 'fun x => ' + body


def emit(found, k0, args):
    ns = os.environ.get('NS', 'SubsetSumQuadGen')
    (pn, pS, pc, pg), nexp, ig, imp = PREFIXES[os.environ['LEAN']]
    out = ['module', '', 'public import ErdosResearch.SubsetSumQuad'] + (['public import %s' % imp] if imp != 'ErdosResearch.SubsetSumQuad' else []) + ['', '@[expose] public section', '', '/-!',
           '# Generated: whole bounded pairs below one prefix (`boundedOK`)', '',
           'Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 83).', '',
           'GENERATED by `NS=%s LEAN=%s python3 -I scripts/quad_probe.py %s` (do not edit by hand). Each theorem: no' % (ns, os.environ['LEAN'], args),
           '`n·p^f·q^e·r` is weird for ALL `f, e ≥ 1` and every prime `r ∤ n·p^f·q^e`, for one bounded pair `(p, q)` below the',
           'prefix `n = %s. Elementary; not a new result on #470.' % DESC[os.environ['LEAN']], '-/', '',
           'set_option Elab.async false', '', 'namespace ErdosResearch.%s' % ns, '',
           'open ErdosResearch.SubsetSumQuad', '']
    for i, (p, q, (f0, e0, r1, cells, rows, cols)) in enumerate(found):
        e0r = {f: L[0] for f, L in rows.items()}
        f0c = {e: L[0] for e, L in cols.items()}
        out += ['/-- Bounded pair `(%d, %d)`: quadrant from `(%d, %d)` (`r₁ = %d`), %d cells. -/' % (p, q, f0, e0, r1, cells),
                'theorem not_weird_%d_%d {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)' % (p, q),
                '    (hrM : ¬ r ∣ %s * %d ^ f * %d ^ e) : ¬ (%s * %d ^ f * %d ^ e * r).Weird :=' % (nexp, p, q, nexp, p, q),
                '  not_weird_of_boundedOK (S := %d) (c := %d) (g := %d) (r1q := %d) (f₀ := %d) (e₀ := %d)' % (pS, pc, pg, r1, f0, e0),
                '    (e0r := %s) (f0c := %s)' % (tabfun(e0r), tabfun(f0c)),
                '    (r1 := %s)' % r1fun(f0, e0, rows, cols),
                '    (by norm_num) (by norm_num) %s (by norm_num) (by norm_num)' % ig,
                '    (by decide +kernel) hf he hr hrM', '']
    out += ['end ErdosResearch.%s' % ns, '']
    return '\n'.join(out)



if __name__ == '__main__':
    main()
