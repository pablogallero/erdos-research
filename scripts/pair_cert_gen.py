# Session 82 (notes/erdos-470.md): parameter search + Lean emitter for `pairOK` (ErdosResearch/SubsetSumPair.lean).
# Exact Python port of the Lean Booleans stepsOK / ppSum / stepsEnd / pointOK / rowOK / stepAbOK / pairOK (r0 = 2), so a
# pair accepted here makes `pairOK ... = true` by `decide +kernel` (the kernel re-checks; nothing here is trusted).
# Decides nothing about #470 and runs no search (no owf).
# Usage:
#   python3 -I scripts/pair_cert_gen.py N S c g PLO PHI QHI [MAXPAIRS]     -> DRY report (shapes, failures) for primes
#        PLO <= p < PHI, p < q < QHI, p, q not dividing N
#   LEAN=late ... same, and prints a Lean module (to stdout) with one theorem per found pair, below the late prefix
#        (N must be 3^3*23*13^10*17^2*11 with its certificate S = 256030928920159929, c = 2295, g = 5)
#   RANGES=1: n p abundant (`stepAbOK`), a `q_tail` Q (no work for q >= Q), one `rangeOK` q-range per p (Lean SubsetSumPairRange) first, `pairOK` only for the pairs left over
#   SELFTEST=1: python3 -I scripts/pair_cert_gen.py  -> reproduces the two hand-made instances of session 81
import os, sys

CAP = int(os.environ.get('CAP', '60'))
QCAP = int(os.environ.get('QCAP', str(10 ** 100)))


def ppSum_exact(n, q, S, f):          # same recursion as Lean: ppSum (f+1) = S0 + (n + q * ppSum f)
    t = S
    for _ in range(f):
        t = S + (n + q * t)
    return t


def stepsEnd(n, S, l):
    for (q, f) in l:
        n, S = n * q ** f, ppSum_exact(n, q, S, f)
    return n, S


def stepsOK(c, g, n, S, l):
    for (q, f) in l:
        if not (n % q != 0 and q * g + 2 * c <= S + 1 and n + 2 * c <= (q + 1) * S + 1):
            return False
        n, S = n * q ** f, ppSum_exact(n, q, S, f)
    return True


def pointOK(M, S, c, g, r0, r1):
    return (S < M and S + M <= (r1 + 1) * (M - S) and r1 * g + 2 * c <= S + 1 and r1 * (M - S) + c <= S + M
            and M + 2 * c <= (r0 + 1) * S + 1 and c <= M * r0)


def rowOK(m, S, c, g, q, r0, r1, e0):
    P = ppSum_exact(m, q, S, e0); Me = m * q ** e0
    return (1 <= c and m % q != 0 and q * g + 2 * c <= S + 1 and m + 2 * c <= (q + 1) * S + 1
            and (S + m) * q * (r1 + 2) <= 2 * (r1 + 1) * m * (q - 1) and r1 * g + 2 * c <= P + 1
            and 2 * r1 * Me + c <= (r1 + 1) * (P + Me) and (r0 + 2) * Me + 2 * c <= (r0 + 1) * (P + Me) + 1
            and c <= Me * r0)


def stepAbOK(n, S, c, g, l):
    if not stepsOK(c, g, n, S, l): return False
    M, T = stepsEnd(n, S, l)
    return c <= M and M + c <= T


def stepPointOK(n, S, c, g, r0, r1, l):
    if not stepsOK(c, g, n, S, l): return False
    M, T = stepsEnd(n, S, l)
    return pointOK(M, T, c, g, r0, r1)


def stepRowOK(n, S, c, g, q, r0, r1, e0, l):
    if not stepsOK(c, g, n, S, l): return False
    M, T = stepsEnd(n, S, l)
    return rowOK(M, T, c, g, q, r0, r1, e0)


def pairOK(n, S, c, g, p, q, F, fr, ec, e0, r1):
    if not (stepAbOK(n, S, c, g, [(p, fr), (q, 1)]) and stepAbOK(n, S, c, g, [(p, F), (q, ec)])): return False
    for f in range(1, F):
        if not stepRowOK(n, S, c, g, q, 2, r1(f, 0), e0(f), [(p, f)]): return False
        for e in range(1, e0(f)):
            if not stepPointOK(n, S, c, g, 2, r1(f, e), [(p, f), (q, e)]): return False
    for f in range(F, fr):
        for e in range(1, ec):
            if not (stepAbOK(n, S, c, g, [(p, f), (q, e)]) or stepPointOK(n, S, c, g, 2, r1(f, e), [(p, f), (q, e)])):
                return False
    return True


def ceil_div(a, b): return -(-a // b)


def point_r1(M, T):                   # least r1 with S + M <= (r1 + 1)(M - S)  (the other tests are upper bounds on r1)
    return max(0, ceil_div(T + M, M - T) - 1)


def find(n, S, c, g, p, q):
    """Parameters (F, fr, ec, e0 table, r1 table) with pairOK = true, or (None, reason)."""
    if (S + n) * p * q <= 2 * n * (p - 1) * (q - 1):
        return None, 'bounded pair (L2 <= 2: every column limit-deficient; stair_bounded, not pairOK)'
    e0t, r1t = {}, {}
    F = 1
    while True:                       # columns f < F: n p^f limit-deficient in q (strictly)
        m, Sm = stepsEnd(n, S, [(p, F)])
        if not ((Sm + m) * q < 2 * m * (q - 1)): break
        if F > CAP: return None, 'F>CAP'
        num, den = 2 * (Sm + m) * q - 2 * m * (q - 1), 2 * m * (q - 1) - (Sm + m) * q
        r1row = max(0, ceil_div(num, den))
        e0 = 1
        while not stepRowOK(n, S, c, g, q, 2, r1row, e0, [(p, F)]):
            e0 += 1
            if e0 > CAP: return None, 'row f=%d' % F
        e0t[F] = e0; r1t[(F, 0)] = r1row
        for e in range(1, e0):
            M, T = stepsEnd(n, S, [(p, F), (q, e)])
            if T >= M: return None, 'abundant point in limit column f=%d e=%d' % (F, e)
            r1t[(F, e)] = point_r1(M, T)
        F += 1
    mq, Sq = stepsEnd(n, S, [(q, 1)])
    if (Sq + mq) * p <= 2 * mq * (p - 1):
        return None, 'shape e_inf >= 2 (row e = 1 limit-deficient in p; not pairOK)'
    fr = F
    while not stepAbOK(n, S, c, g, [(p, fr), (q, 1)]):
        fr += 1
        if fr > CAP: return None, 'fr>CAP'
    ec = 1
    while not stepAbOK(n, S, c, g, [(p, F), (q, ec)]):
        ec += 1
        if ec > CAP: return None, 'ec>CAP'
    for f in range(F, fr):
        for e in range(1, ec):
            if stepAbOK(n, S, c, g, [(p, f), (q, e)]): continue
            M, T = stepsEnd(n, S, [(p, f), (q, e)])
            if T >= M: return None, 'abundant box point without interval f=%d e=%d' % (f, e)
            r1t[(f, e)] = point_r1(M, T)
    e0f = lambda f: e0t.get(f, 1)
    r1f = lambda f, e: r1t.get((f, e), 0)
    if not pairOK(n, S, c, g, p, q, F, fr, ec, e0f, r1f): return None, 'pairOK false (r1 window / step conditions)'
    return (F, fr, ec, e0t, r1t), None


def q_range(n, S, c, g, p):
    """Largest [q0, q1] (q0 > p) with rangeOK true (Lean SubsetSumPairRange), or None. q1 capped at QCAP."""
    if not stepsOK(c, g, n, S, [(p, 1)]): return None
    m, T = stepsEnd(n, S, [(p, 1)])
    q0 = max(p + 1, ceil_div(m + 2 * c - 1, T) - 1 if m + 2 * c - 1 > T else 0, ceil_div(c, m))
    q1 = (T + 1 - 2 * c) // g
    if m > T: q1 = min(q1, (T + m - c) // (m - T))
    q1 = min(q1, QCAP)
    if q1 < q0: return None
    assert rangeOK(n, S, c, g, p, q0, q1)
    return q0, q1


def q_tail(n, S, p):
    """Least Q > p with (S+n) p (Q+1) <= 2n(p-1)(Q-1) (Lean not_weird_qtail), or None if n p^f is not limit-deficient."""
    A, B = 2 * n * (p - 1), (S + n) * p
    if A <= B: return None
    Q = max(p + 1, ceil_div(A + B, A - B))          # (Q+1) B <= (Q-1) A  <=>  Q (A - B) >= A + B
    assert B * (Q + 1) <= A * (Q - 1)
    return Q


def rangeOK(n, S, c, g, p, q0, q1):
    if not stepsOK(c, g, n, S, [(p, 1)]): return False
    m, T = stepsEnd(n, S, [(p, 1)])
    return q1 * g + 2 * c <= T + 1 and m + 2 * c <= (q0 + 1) * T + 1 and c <= m * q0 and m * q1 + c <= T + (m + q1 * T)


def isprime(x):
    if x < 2: return False
    if x % 2 == 0: return x == 2
    d = 3
    while d * d <= x:
        if x % d == 0: return False
        d += 2
    return True


def lean_fun_e0(e0t):
    s = '1'
    for f in sorted(e0t, reverse=True): s = 'if f = %d then %d else %s' % (f, e0t[f], s)
    return 'fun f => ' + s


def lean_fun_r1(r1t):
    s = '0'
    for (f, e) in sorted(r1t, reverse=True): s = 'if f = %d ∧ e = %d then %d else %s' % (f, e, r1t[(f, e)], s)
    return 'fun f e => ' + s


LATE = (3 ** 3 * 23 * 13 ** 10 * 17 ** 2 * 11, 256030928920159929, 2295, 5)
LATE_LEAN = '3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11'


def emit(found, ranges, abps, tails):
    out = ['module', '', 'public import ErdosResearch.SubsetSumPair', 'public import ErdosResearch.SubsetSumPairRange', '',
           '@[expose] public section', '',
           '/-!', '# Generated `pairOK` / `rangeOK` instances below the late prefix (session 82)', '',
           'GENERATED by `scripts/pair_cert_gen.py` (`LEAN=late`, `RANGES=1`); do not edit by hand. With',
           '`n = %s`: each `pair` theorem says no `n·p^f·q^e·r` is weird (all `f, e ≥ 1`, every prime `r`);' % LATE_LEAN,
           'each `ab` theorem says no `n·p^f·m` is weird (all `f, m ≥ 1`: `n p` is pseudoperfect);',
           'each `qtail` theorem says no `n·p^f·q^e·r` is weird (all `f, e`) for primes `q, r ≥ Q`;',
           'each `range` theorem says no `n·p^f·q^e·m` is weird (all `f, e, m ≥ 1`) for every prime `q` in a range.',
           'Reference: <https://www.erdosproblems.com/470>; see `notes/erdos-470.md` (session 82).',
           'Elementary; new only as a formalisation.', '-/', '',
           'namespace ErdosResearch.SubsetSumPairGen', '',
           'open ErdosResearch.SubsetSumPair ErdosResearch.SubsetSumPairRange', '']
    for p in abps:
        out += ['theorem not_weird_late_ab_%d {f m : ℕ} (hf : 1 ≤ f) (hm : 0 < m) :' % p,
                '    ¬ (%s * %d ^ f * m).Weird :=' % (LATE_LEAN, p),
                '  not_weird_of_stepAbOK_single (S := %d) (c := %d) (g := %d) (by norm_num) (by norm_num)' % LATE[1:],
                '    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by decide +kernel) hf hm', '']
    for (p, Q) in tails:
        out += ['theorem not_weird_late_qtail_%d {f q e r : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ %s * %d ^ f)' % (p, LATE_LEAN, p),
                '    (hr : r.Prime) (hrn : ¬ r ∣ %s * %d ^ f * q ^ e) (hQq : %d ≤ q) (hQr : %d ≤ r) :' % (LATE_LEAN, p, Q, Q),
                '    ¬ (%s * %d ^ f * q ^ e * r).Weird :=' % (LATE_LEAN, p),
                '  not_weird_qtail (S := %d) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix.1' % LATE[1],
                '    (by norm_num) (by norm_num) hq hqn hr hrn (by norm_num) hQq hQr (by norm_num)', '']
    for (p, (q0, q1)) in ranges:
        out += ['theorem not_weird_late_range_%d {q f e m : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ %s * %d)' % (p, LATE_LEAN, p),
                '    (hq₀ : %d ≤ q) (hq₁ : q ≤ %d) (hf : 1 ≤ f) (he : 1 ≤ e) (hm : 0 < m) :' % (q0, q1),
                '    ¬ (%s * %d ^ f * q ^ e * m).Weird :=' % (LATE_LEAN, p),
                '  not_weird_of_rangeOK (S := %d) (c := %d) (g := %d) (by norm_num) (by norm_num)' % LATE[1:],
                '    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by decide +kernel) hq hqn hq₀ hq₁',
                '    hf he hm', '']
    for (p, q, (F, fr, ec, e0t, r1t)) in found:
        out += ['theorem not_weird_late_pair_%d_%d {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)' % (p, q),
                '    (hrM : ¬ r ∣ %s * %d ^ f * %d ^ e) :' % (LATE_LEAN, p, q),
                '    ¬ (%s * %d ^ f * %d ^ e * r).Weird :=' % (LATE_LEAN, p, q),
                '  not_weird_of_pairOK (S := %d) (c := %d) (g := %d) (F := %d) (fr := %d) (ec := %d)' % (LATE[1], LATE[2], LATE[3], F, fr, ec),
                '    (e0 := %s)' % lean_fun_e0(e0t),
                '    (r1 := %s)' % lean_fun_r1(r1t),
                '    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num)',
                '    (by norm_num) (by decide +kernel) hf he hr hrM', '']
    out += ['end ErdosResearch.SubsetSumPairGen', '']
    return '\n'.join(out)


def main():
    if os.environ.get('SELFTEST') == '1':
        n, S, c, g = LATE
        ok1 = pairOK(n, S, c, g, 37, 307, 2, 2, 1, lambda f: 3, lambda f, e: 7196 if e == 0 else 6686 if e == 1 else 7195)
        ok2 = pairOK(n, S, c, g, 41, 167, 1, 2, 2, lambda f: 1, lambda f, e: 472739)
        r1, r2 = find(n, S, c, g, 37, 307), find(n, S, c, g, 41, 167)
        print('selftest hand-made', ok1, ok2, 'found', r1[0] is not None, r2[0] is not None)
        sys.exit(0 if ok1 and ok2 and r1[0] and r2[0] else 1)
    a = sys.argv[1:]
    n, S, c, g, plo, phi, qhi = map(int, a[:7]); maxpairs = int(a[7]) if len(a) > 7 else 10 ** 9
    lean = os.environ.get('LEAN') == 'late'
    if lean and (n, S, c, g) != LATE: sys.exit('LEAN=late needs the late prefix certificate')
    use_ranges = os.environ.get('RANGES') == '1'
    found, fails, shapes, ranges, nranged, abps, tails = [], {}, {}, [], 0, [], []
    if use_ranges:                    # p >= Q3 is covered by the three-prime tail (Lean not_weird_ptail)
        Q3 = 2
        while not (S + n) * Q3 * (Q3 + 1) <= 2 * n * (Q3 - 1) * (Q3 - 1): Q3 += 1
        print('three-prime tail Q3 = %d (p >= Q3 needs nothing)' % Q3, file=sys.stderr)
        phi = min(phi, Q3)
    for p in range(plo, phi):
        if not (isprime(p) and n % p): continue
        if use_ranges and stepAbOK(n, S, c, g, [(p, 1)]):   # n p pseudoperfect: every q at once, no upper bound
            abps.append(p); continue
        rg = q_range(n, S, c, g, p) if use_ranges else None
        if rg: ranges.append((p, rg))
        qt = q_tail(n, S, p) if use_ranges else None
        if qt: tails.append((p, qt))
        if use_ranges and (qt is None or qt > qhi): print('WARNING p=%d: q-tail %s above QHI, pairs not all scanned' % (p, qt), file=sys.stderr)
        for q in range(p + 1, min(qhi, qt) if qt else qhi):
            if not (isprime(q) and n % q): continue
            if len(found) >= maxpairs: break
            if rg and rg[0] <= q <= rg[1]:
                nranged += 1; continue
            res, why = find(n, S, c, g, p, q)
            if res is None:
                fails[why.split(' f=')[0]] = fails.get(why.split(' f=')[0], 0) + 1
                if len(fails) and sum(fails.values()) <= 5: print('FAIL p=%d q=%d: %s' % (p, q, why), file=sys.stderr)
                continue
            F, fr, ec, e0t, r1t = res
            k = (F, fr, ec); shapes[k] = shapes.get(k, 0) + 1
            found.append((p, q, res))
    if use_ranges: print('p with n p abundant (all q) %s; ranges %d (one per p), pairs covered by ranges %d; q-tails %d, largest Q %s'
                         % (abps, len(ranges), nranged, len(tails), max((t[1] for t in tails), default=None)), file=sys.stderr)
    print('pairs certified %d, failed %d %s' % (len(found), sum(fails.values()), fails), file=sys.stderr)
    print('shapes (F, fr, ec): %s' % dict(sorted(shapes.items(), key=lambda t: -t[1])[:12]), file=sys.stderr)
    if lean: print(emit(found, ranges, abps, tails), end='')


if __name__ == '__main__':
    main()
