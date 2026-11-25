# Session 85 (notes/erdos-470.md): measure what STAR versions (6th prime as r^h, h >= 2) of the row / quadrant / tail
# certificates need, below the late prefix (the 276 leaves of sessions 82-83 cover r^1 only).
# Facts used (session 76/77, Lean SubsetSumStar.star_prime_unique): at a deficient point N with sigma = sigma(N), D = 2N - sigma,
# the only prime r with N r NOT abundant but some N r^h abundant is r* = ceil(sigma / D). Along a row N_e = m x^e, sigma_e/N_e
# increases strictly to rho = sigma(m) x / (m (x-1)), so r*_e is nondecreasing and stabilises at r_inf = ceil(L),
# L = rho / (2 - rho) (row limit-deficient: rho < 2).
# For each line (row of a pairOK leaf, row/column of a boundedOK leaf) this reports:
#   transient points  e >= start with r*_e != r_inf (each would need its own star test, like pointStarOK);
#   r_inf: prime and coprime?  If so the line becomes a 2-D staircase in (e, h): first abundant h_e (nonincreasing in e),
#   its limit h_inf, whether every corner is certified (c <= N, N + c <= T, step conditions for r_inf), and whether the
#   rows h < h_inf are limit-deficient in x (then they need nothing).
# Also: deficient POINTS of the leaves (pointStarOK-style test), quadrant star candidates (distinct r* on a box), and the
# star q-tail Q* with (S+n) p Q^2 <= 2 n (p-1) (Q-1)^2 (factor Q/(Q-1) for r^h instead of (Q+1)/Q).
# Python only; indicative; decides nothing about #470; never runs owf.
# Usage: python3 -I scripts/star_row_probe.py            (late prefix, all leaves)
#   ROWSTAR=1: also check the Lean Booleans `rowStarOK` / `quadStarOK` (ErdosResearch/SubsetSumRowStar.lean) on every row,
#   column and quadrant of the leaves: candidate R = r1 + 1 even, R | prefix, skipS R (odd primes < 100), or the corner
#   (line start, R^2) certified by stepAbOK. Prints the counts per branch; any FAIL is listed.
import os, sys
from fractions import Fraction
sys.dont_write_bytecode = True
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from pair_cert_gen import (ppSum_exact, stepsEnd, stepsOK, ceil_div, isprime, q_range, q_tail, find, stepAbOK, LATE)
from quad_probe import pair as qpair, r1_limit2

FUEL = int(os.environ.get('FUEL', '60'))
EMAX = int(os.environ.get('EMAX', '400'))


def rstar(M, T):                      # T = sum of proper divisors, M deficient (T < M)
    sig, D = T + M, M - T
    return ceil_div(sig, D)


def star_cert(M, T, c, g, r):
    """pointStarOK-style test of the star-only prime r at the point (M, T): step conditions, then the first abundant
    exponent h (if any within FUEL) must be certified. Returns (ok, h) ; h None = never abundant within FUEL."""
    if not (r * g + 2 * c <= T + 1 and M + 2 * c <= (r + 1) * T + 1): return False, -1
    Th, Nh = T, M
    for h in range(1, FUEL + 1):
        Th, Nh = T + (M + r * Th), r * Nh      # ppSum recursion
        if Nh < Th: return (c <= Nh and Nh + c <= Th), h
    return False, None


def relevant(r, M):
    return r > 2 and r % 2 == 1 and M % r != 0 and isprime(r)


def line(n, S, c, g, pre, x, start, stats, tag):
    """Line N_e = m x^e (m = n * pre), e >= start."""
    m, Sm = stepsEnd(n, S, pre)
    sig_m = Sm + m
    rho = Fraction(sig_m * x, m * (x - 1))
    if rho >= 2: stats['notlimit'] += 1; return
    L = rho / (2 - rho)
    rinf = -((-L.numerator) // L.denominator)
    e = start; trans = 0; tfail = 0
    while True:
        M, T = stepsEnd(m, Sm, [(x, e)])
        if T >= M: stats['abundant_on_line'] += 1; return
        r = rstar(M, T)
        if r == rinf: break
        if relevant(r, M):
            trans += 1
            ok, _ = star_cert(M, T, c, g, r)
            if not ok: tfail += 1
        e += 1
        if e > start + EMAX: stats['nostab'] += 1; return
    stats['lines'] += 1; stats['trans'] += trans; stats['trans_fail'] += tfail
    stats['maxtrans'] = max(stats['maxtrans'], trans)
    if not relevant(rinf, m * x):
        stats['rinf_irrelevant'] += 1; return
    stats['rinf_prime'] += 1
    # staircase in (e, h) for r = rinf, from e = start: first abundant h_e
    hs = []; bad = 0
    for k in range(start, e + 25):
        M, T = stepsEnd(m, Sm, [(x, k)])
        ok, h = star_cert(M, T, c, g, rinf)
        hs.append(h)
        if not ok and h is not None: bad += 1
    hinf = hs[-1]
    stats['rinf_cornerfail'] += bad
    if hinf is None: stats['rinf_never'] += 1; return
    # rows h < hinf of the prefix m * rinf^h must be limit-deficient in x (else some (e, h) corner is missing)
    for h in range(1, hinf):
        mh, Sh = stepsEnd(m, Sm, [(rinf, h)])
        if not ((Sh + mh) * x < 2 * mh * (x - 1)):
            stats['rinf_row_notlimit'] += 1
            if stats['rinf_row_notlimit'] <= 3: print('  %s: row h=%d of r_inf=%d not limit-deficient' % (tag, h, rinf), file=sys.stderr)
            break
    stats['hinf_max'] = max(stats['hinf_max'], hinf)
    stats['corners'] += len(set(hs))


def point(n, S, c, g, pre, stats):
    M, T = stepsEnd(n, S, pre)
    if T >= M: return
    r = rstar(M, T)
    if not relevant(r, M):
        stats['pt_irrelevant'] += 1
        if r % 2 == 1 and r > 2:          # odd candidate: session 84's pointStarOK has no skipS / R | M branch
            stats['pt_odd_nonprime'] += 1
            if not star_cert(M, T, c, g, r)[0]:
                stats['pt_odd_nonprime_firstfail'] += 1
                if M % r == 0 or any(2 <= s < r and r % s == 0 for s in SKIP): stats['pt_odd_nonprime_firstfail_skipdiv'] += 1
        return
    ok, h = star_cert(M, T, c, g, r)
    stats['pt'] += 1
    if not ok: stats['pt_fail'] += 1


SKIP = [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97]


def star_branch(n, S, c, g, pre, corner, r1):
    """Branch of rowStarOK / quadStarOK that holds for the candidate R = r1 + 1 ('FAIL' if none)."""
    m = stepsEnd(n, S, pre)[0]
    R = r1 + 1
    if R % 2 == 0 and R > 2: return 'even'
    if m % R == 0: return 'div'
    if len(corner) >= 1 and R == corner[-1][0] and corner[-1][1] >= 1 and len(pre) == 1: return 'R=q'   # rowStarOK only
    if any(2 <= s < R and R % s == 0 for s in SKIP): return 'skip'
    if stepAbOK(n, S, c, g, corner + [(R, 2)]): return 'corner'
    return 'FAIL'


def rowstar(n, S, c, g, Q3):
    from pair_cert_gen import stepRowOK
    from quad_probe import quadOK
    cnt = {}
    def add(k, tag):
        cnt[k] = cnt.get(k, 0) + 1
        if k.endswith('FAIL'): print('  rowstar FAIL %s' % (tag,), file=sys.stderr)
    for p in range(29, Q3):
        if not (isprime(p) and n % p) or stepAbOK(n, S, c, g, [(p, 1)]): continue
        rg = q_range(n, S, c, g, p); qt = q_tail(n, S, p)
        for q in range(p + 1, qt):
            if not (isprime(q) and n % q) or (rg and rg[0] <= q <= rg[1]): continue
            if r1_limit2(n, S, p, q) is not None:
                res, _ = qpair(n, S, c, g, p, q); f0, e0, r1, cells, rows, cols = res
                assert quadOK(n, S, c, g, p, q, 2, r1, f0, e0)
                add('quad ' + star_branch(n, S, c, g, [], [(p, f0), (q, e0)], r1), (p, q))
                for f, L in rows.items():
                    assert stepRowOK(n, S, c, g, q, 2, L[2], L[0], [(p, f)])
                    add('row ' + star_branch(n, S, c, g, [(p, f)], [(p, f), (q, L[0])], L[2]), (p, q, 'row', f))
                for e, L in cols.items():
                    assert stepRowOK(n, S, c, g, p, 2, L[2], L[0], [(q, e)])
                    add('row ' + star_branch(n, S, c, g, [(q, e)], [(q, e), (p, L[0])], L[2]), (p, q, 'col', e))
            else:
                res, _ = find(n, S, c, g, p, q); F, fr, ec, e0t, r1t = res
                for f in range(1, F):
                    add('row ' + star_branch(n, S, c, g, [(p, f)], [(p, f), (q, e0t[f])], r1t[(f, 0)]), (p, q, 'row', f))
    print('rowStarOK / quadStarOK branches: %s' % dict(sorted(cnt.items())))


def main():
    n, S, c, g = LATE
    keys = ['lines', 'trans', 'trans_fail', 'maxtrans', 'notlimit', 'abundant_on_line', 'nostab', 'rinf_irrelevant',
            'rinf_prime', 'rinf_cornerfail', 'rinf_never', 'rinf_row_notlimit', 'hinf_max', 'corners', 'pt', 'pt_fail',
            'pt_irrelevant', 'pt_odd_nonprime', 'pt_odd_nonprime_firstfail', 'pt_odd_nonprime_firstfail_skipdiv', 'quad', 'quad_distinct_max', 'quad_fail']
    st = {k: 0 for k in keys}
    Q3 = 2
    while not (S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1): Q3 += 1
    Q3s = 2
    while not (S + n) * Q3s * Q3s * Q3s <= 2 * n * (Q3s - 1) ** 3: Q3s += 1
    print('three-prime tail Q3 = %d (r^1); star version (Q/(Q-1))^3 needs Q3* = %d' % (Q3, Q3s), file=sys.stderr)
    npairs = nbounded = 0; tails = []
    for p in range(29, Q3):
        if not (isprime(p) and n % p): continue
        if stepAbOK(n, S, c, g, [(p, 1)]): continue
        rg = q_range(n, S, c, g, p); qt = q_tail(n, S, p)
        A, B = 2 * n * (p - 1), (S + n) * p
        Qs = p + 1
        while not B * Qs * Qs <= A * (Qs - 1) ** 2: Qs += 1
        tails.append((p, qt, Qs))
        for q in range(p + 1, qt):
            if not (isprime(q) and n % q): continue
            if rg and rg[0] <= q <= rg[1]: continue
            if r1_limit2(n, S, p, q) is not None:          # bounded pair
                res, why = qpair(n, S, c, g, p, q)
                if res is None: print('bounded FAIL', p, q, why, file=sys.stderr); continue
                nbounded += 1
                f0, e0, r1, cells, rows, cols = res
                for f, Lr in rows.items():
                    line(n, S, c, g, [(p, f)], q, Lr[0], st, 'p=%d q=%d row f=%d' % (p, q, f))
                    for e in Lr[3]: point(n, S, c, g, [(p, f), (q, e)], st)
                for e, Lc in cols.items():
                    line(n, S, c, g, [(q, e)], p, Lc[0], st, 'p=%d q=%d col e=%d' % (p, q, e))
                    for f in Lc[3]: point(n, S, c, g, [(p, f), (q, e)], st)
                # quadrant f >= f0, e >= e0: distinct r* on a box
                vals = set(); fail = 0
                for f in range(f0, f0 + 8):
                    for e in range(e0, e0 + 8):
                        M, T = stepsEnd(n, S, [(p, f), (q, e)])
                        r = rstar(M, T)
                        if relevant(r, M) and r not in vals:
                            ok, _ = star_cert(M, T, c, g, r)
                            if not ok: fail += 1
                        vals.add(r)
                st['quad'] += 1; st['quad_fail'] += fail
                st['quad_distinct_max'] = max(st['quad_distinct_max'], len(vals))
                continue
            res, why = find(n, S, c, g, p, q)
            if res is None: print('pair FAIL', p, q, why, file=sys.stderr); continue
            npairs += 1
            F, fr, ec, e0t, r1t = res
            for f in range(1, F):
                line(n, S, c, g, [(p, f)], q, e0t[f], st, 'p=%d q=%d row f=%d' % (p, q, f))
                for e in range(1, e0t[f]): point(n, S, c, g, [(p, f), (q, e)], st)
            for (f, e) in r1t:
                if e >= 1 and f >= F: point(n, S, c, g, [(p, f), (q, e)], st)
    print('pairOK leaves %d, boundedOK leaves %d' % (npairs, nbounded))
    print('q-tails (p, Q for r^1, Q* for r^h): %s' % tails)
    for k in keys: print('%s %d' % (k, st[k]))
    if os.environ.get('ROWSTAR') == '1': rowstar(n, S, c, g, Q3)


if __name__ == '__main__':
    main()
