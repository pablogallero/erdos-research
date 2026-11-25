# Session 83 (notes/erdos-470.md): a Lean `IntervalGap` certificate for ONE given prefix, e.g. the real 3-prime prefix
# 3^16*5^11*19^8 of the omega = 6 search (session 82, item 4). Uses multi_plan (scripts/raise_late_plan.py): bitset base,
# prime-power steps, then raises over cofactors with a greedy gap bound -- the same certificate pieces as
# scripts/late_cert_gen.py, but it stops at the IntervalGap (no lastOK), so it can feed the pair layer (pairOK/rangeOK/...).
# Usage: python3 -I scripts/prefix_ig_gen.py LIMB NAME 'p^e*q^f*...' [more 'NAME=prefix' ...] > ErdosResearch/OddWeirdPrefixIG.lean
#   e.g.  python3 -I scripts/prefix_ig_gen.py 100000 real '3^16*5^11*19^8'
# Python only; it does NOT run the omega = 6 search.
import os, sys, io, contextlib

LIMB = int(sys.argv[1])
jobs = [(sys.argv[i], sys.argv[i + 1]) for i in range(2, len(sys.argv), 2)]
_d = os.path.dirname(os.path.abspath(__file__))
sys.argv = [sys.argv[0], str(LIMB), '0']
_g = {'__file__': os.path.join(_d, 'raise_late_plan.py'), '__name__': 'late_plan_lib'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(open(os.path.join(_d, 'raise_late_plan.py')).read(), _g)
multi_plan, divisors, sigma, greedy_gap = (_g[k] for k in ('multi_plan', 'divisors', 'sigma', 'greedy_gap'))


def val(n, p):
    e = 0
    while n % p == 0:
        n //= p; e += 1
    return e


def prodOfl(fs):
    r = 1
    for p, e in fs:
        r *= p ** e
    return r


def parse(s):
    f = {}
    for t in s.split('*'):
        p, _, e = t.partition('^')
        f[int(p)] = int(e or 1)
    return f


def nexpr(f):
    return ' * '.join(f'{p} ^ {e}' if e > 1 else f'{p}' for p, e in sorted(f.items()))


def lean_pairs(xs):
    return '[' + ', '.join(f'({a}, {e})' for a, e in xs) + ']'


def build(f):
    pl = multi_plan(f)
    if not pl:
        sys.exit(f'no plan for {f}')
    b, so, ro, c, g = pl
    ps = sorted(f)
    cur = {p: val(b, p) for p in ps if b % p == 0}
    fsb = [(p, cur[p]) for p in sorted(cur)]
    steps = [(q, f[q]) for q in so]
    for q, e in steps:
        cur[q] = e
    N = prodOfl(f.items())
    raises = []
    for p in ro:
        fsM = [(q, x) for q, x in sorted(cur.items()) if q != p]
        m = prodOfl(fsM)
        e0 = cur[p]
        SA = sigma(m * p ** e0) - m * p ** e0
        SB = sigma(m) - m
        Snew = sigma(m * p ** f[p]) - m * p ** f[p]
        raises.append((p, fsM, e0, f[p] - e0, greedy_gap(m), SB, SA, Snew, len(divisors(m))))
        cur[p] = f[p]
    assert all(cur.get(p) == f[p] for p in ps)
    return dict(f=f, b=b, fsb=fsb, steps=steps, c=c, g=g, raises=raises, N=N, S=sigma(N) - N)


def emit(i, d):
    out = []
    ne = nexpr(d['f'])
    r = d['raises']
    out.append(f"/-- Factorisation of the base `{d['b']}` of prefix `{i}`. -/\n"
               f"def fsb_{i} : List (ℕ × ℕ) := {lean_pairs(d['fsb'])}\n")
    for j, x in enumerate(r):
        out.append(f"/-- Cofactor of raise {j + 1} of prefix `{i}` (prime `{x[0]}`, {x[8]} divisors). -/\n"
                   f"def fs_{i}_{j} : List (ℕ × ℕ) := {lean_pairs(x[1])}\n")
    st = lean_pairs(d['steps'])

    def thm(name, conj):
        out.append(f"theorem {name} :\n    " + " ∧\n    ".join(conj) + " := by\n  decide +kernel\n")
    lb = f"(baseList fsb_{i})"
    base = [f"baseOK fsb_{i} = true", f"prodOf fsb_{i} = {d['b']}",
            f"intervalOKB (ssBits {lb}) {d['c']} {lb}.sum = true", f"gapOKB (ssBits {lb}) {d['g']} {lb}.sum = true",
            f"stepsOK {d['c']} {d['g']} {d['b']} {lb}.sum {st} = true"]
    if r:
        p, fsM, e0, *_x = r[0]
        base.append(f"stepsEnd {d['b']} {lb}.sum {st} = (prodOf fs_{i}_0 * {p} ^ {e0}, {r[0][6]})")
    else:
        base.append(f"stepsEnd {d['b']} {lb}.sum {st} = ({ne}, {d['S']})")
    thm(f"cert_{i}_base", base)
    for j, (p, fsM, e0, kk, gB, SB, SA, Sn, _nd) in enumerate(r):
        nxt = f"prodOf fs_{i}_{j + 1} * {r[j + 1][0]} ^ {r[j + 1][2]}" if j + 1 < len(r) else ne
        thm(f"cert_{i}_gap{j}", [f"gapCertM fs_{i}_{j} {gB} {SB} = true"])
        thm(f"cert_{i}_raise{j}", [f"raiseOK (prodOf fs_{i}_{j}) {p} {e0} {d['c']} {gB} {SB} {SA} {kk} = true",
                                   f"raiseSum (prodOf fs_{i}_{j}) {p} {e0} {SB} {SA} {kk} = {Sn}",
                                   f"prodOf fs_{i}_{j} * {p} ^ ({e0} + {kk}) = {nxt}",
                                   f"0 < prodOf fs_{i}_{j}", f"prodOf fs_{i}_{j} % {p} ≠ 0"])
    pf = [f"  obtain ⟨hbo, hpb, hI, hG, hst, hend⟩ := cert_{i}_base",
          f"  obtain ⟨hl, hnd⟩ := baseList_properDivisors (by norm_num [fsb_{i}]) hbo",
          f"  have h0 := intervalGap_of_bitsB (baseList fsb_{i}) hl hnd hI hG",
          "  rw [hpb] at h0",
          f"  have hs := intervalGap_of_stepsOK (by norm_num) {st} _ _ (by norm_num) (by norm_num) hst h0",
          "  rw [hend] at hs"]
    for j, (p, *_rest) in enumerate(r):
        pf += [f"  obtain ⟨h{j}ok, h{j}rs, h{j}n, h{j}m0, h{j}mp⟩ := cert_{i}_raise{j}",
               f"  obtain ⟨hSB{j}, hgB{j}⟩ := gap_properDivisors_of_gapCertM (by norm_num [fs_{i}_{j}]) cert_{i}_gap{j}",
               f"  have hr{j} := intervalGap_raise h{j}m0 (by norm_num) (fun h => h{j}mp (Nat.mod_eq_zero_of_dvd h))",
               f"    (by norm_num) hs hSB{j} hgB{j} h{j}ok",
               f"  rw [h{j}rs, h{j}n] at hr{j}",
               "  clear hs",
               f"  have hs := hr{j}"]
    pf.append("  exact hs")
    desc = (f"base `{d['b']}`, steps {', '.join(f'`{q}^{e}`' for q, e in d['steps']) or 'none'}, "
            f"raises {', '.join(f'`{x[0]}` to `{x[0]}^{x[2] + x[3]}`' for x in r) or 'none'}")
    out.append(f"/-- **Interval + gap certificate** for the proper divisors of `{ne}`: every `x ∈ [{d['c']}, S − {d['c']}]`"
               f" is a subset sum, gaps ≤ `{d['g']}` ({desc}). -/\n"
               f"theorem intervalGap_{i} : IntervalGap ({ne}) {d['S']} {d['c']} {d['g']} := by\n" + "\n".join(pf) + "\n")
    return "\n".join(out)


HEADER = '''module

public import ErdosResearch.SubsetSumLate
public import ErdosResearch.SubsetSumDivsDesc
public import ErdosResearch.SubsetSumBitsFast

@[expose] public section

/-!
# Generated: interval + gap certificates for real prefixes of the omega = 6 search

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 83).

GENERATED by `scripts/prefix_ig_gen.py {args}` (do not edit by hand). Each theorem is an `IntervalGap` for the proper
divisors of one prefix (bitset base, prime-power steps, raises with a greedy gap bound), the input that the pair layer
(`pairOK`, `rangeOK`, `not_weird_qtail`) needs. Elementary; not a new result on #470.
-/

set_option Elab.async false

namespace ErdosResearch.OddWeirdPrefixIG

open ErdosResearch.SubsetSumCert ErdosResearch.SubsetSumRaise ErdosResearch.SubsetSumSteps
  ErdosResearch.SubsetSumGreedy ErdosResearch.SubsetSumLate ErdosResearch.SubsetSumDivsDesc
  ErdosResearch.SubsetSumBitsFast

'''

parts = []
for name, s in jobs:
    d = build(parse(s))
    print(f"{name}: {s} plan b={d['b']} steps={d['steps']} raises={[x[0] for x in d['raises']]} "
          f"c={d['c']} g={d['g']} maxdiv={max([x[8] for x in d['raises']] or [0])}", file=sys.stderr)
    parts.append(emit(name, d))
args = ' '.join([str(LIMB)] + [f"{a} '{b}'" for a, b in jobs])
print(HEADER.replace('{args}', args) + "\n".join(parts) + "\nend ErdosResearch.OddWeirdPrefixIG")
