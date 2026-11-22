# Session 58 (notes/erdos-470.md): turn multi-raise plans (scripts/raise_late_plan.py, multi_plan) into Lean instances
#   no  N · q  weird  (q prime, q ∤ N)
# for random deficient 5-prime prefixes N (the same random family as `MULTI=1 raise_late_plan.py`). Each instance is one
# `decide +kernel` certificate (bitset base, stepsOK, per raise: gapCertM + raiseOK, then lastOK) and a short proof
# using intervalGap_of_bits / intervalGap_of_stepsOK / intervalGap_raise / not_weird_mul_prime_of_lastOK.
# Usage: python3 scripts/late_cert_gen.py LIMB COUNT MAXDIV MAXB > ErdosResearch/OddWeirdPlans.lean   (run under ulimit -v)
#   LIMB: bitset base bound; COUNT: instances; MAXDIV: max #divisors of a raise cofactor; MAXB: max lastOK bound B.
# Python only; it does NOT run the omega = 6 search.
import os, sys, io, contextlib, random

LIMB, COUNT, MAXDIV, MAXB = (int(x) for x in sys.argv[1:5])
_d = os.path.dirname(os.path.abspath(__file__))
sys.argv = [sys.argv[0], str(LIMB), '0']
_g = {'__file__': os.path.join(_d, 'raise_late_plan.py'), '__name__': 'late_plan_lib'}
with contextlib.redirect_stdout(io.StringIO()):
    exec(open(os.path.join(_d, 'raise_late_plan.py')).read(), _g)
multi_plan, divisors, sigma, sigpp, greedy_gap, info, isprime = (
    _g[k] for k in ('multi_plan', 'divisors', 'sigma', 'sigpp', 'greedy_gap', 'info', 'isprime'))


def val(n, p):
    e = 0
    while n % p == 0:
        n //= p; e += 1
    return e


def build(f, pl):
    """Returns the data of one instance, or None if it is outside the size limits."""
    b, so, ro, c, g = pl
    ps = sorted(f)
    cur = {p: val(b, p) for p in ps if b % p == 0}
    fsb = [(p, cur[p]) for p in sorted(cur)]
    steps = [(q, f[q]) for q in so]
    for q, e in steps:
        cur[q] = e
    N = 1
    for p in ps:
        N *= p ** f[p]
    raises = []
    for p in ro:
        m = 1
        for q, x in cur.items():
            if q != p:
                m *= q ** x
        fsM = [(q, x) for q, x in sorted(cur.items()) if q != p]
        nd = len(divisors(m))
        if nd > MAXDIV:
            return None
        e0 = cur[p]
        SA = sigma(m * p ** e0) - m * p ** e0
        SB = sigma(m) - m
        gB = greedy_gap(m)
        kk = f[p] - e0
        Snew = sigma(m * p ** f[p]) - m * p ** f[p]
        raises.append((p, fsM, e0, kk, gB, SB, SA, Snew))
        cur[p] = f[p]
    assert all(cur[p] == f[p] for p in ps)
    Sfin = sigma(N) - N
    if not Sfin < N:
        return None
    B = (N + Sfin) // (N - Sfin) + 1
    if B > MAXB:
        return None
    # MINDIV (env, default 0): keep only instances whose largest raise cofactor has more than MINDIV divisors (timing tests)
    if max(len(divisors(prodOfl(x[1]))) for x in raises) <= int(os.environ.get('MINDIV', '0')):
        return None
    # lastOK in Python (same Boolean as Lean)
    for q in range(2, B):
        if N % q == 0 or not (N * q < Sfin + (N + q * Sfin)):
            continue
        if not (q * g + 2 * c <= Sfin + 1 and N + 2 * c <= (q + 1) * Sfin + 1 and c <= N * q
                and N * q + c <= Sfin + (N + q * Sfin)):
            return None
    return dict(f=f, b=b, fsb=fsb, steps=steps, c=c, g=g, raises=raises, N=N, S=Sfin, B=B)


def prodOfl(fs):
    r = 1
    for p, e in fs:
        r *= p ** e
    return r


def nexpr(f):
    return ' * '.join(f'{p} ^ {e}' if e > 1 else f'{p}' for p, e in sorted(f.items()))


def lean_list(xs):
    return '[' + ', '.join(str(x) for x in xs) + ']'


def lean_pairs(xs):
    return '[' + ', '.join(f'({a}, {e})' for a, e in xs) + ']'


def emit(i, d):
    out = []
    ne = nexpr(d['f'])
    r = d['raises']
    out.append(f"/-- Factorisation of the base `{d['b']}` (its proper divisors are `baseList fsb{i}`). -/\n"
               f"def fsb{i} : List (ℕ × ℕ) := {lean_pairs(d['fsb'])}\n")
    for j, (p, fsM, e0, kk, gB, SB, SA, Sn) in enumerate(r):
        out.append(f"/-- Cofactor of raise {j + 1} (prime `{p}`). -/\ndef fs{i}_{j} : List (ℕ × ℕ) := {lean_pairs(fsM)}\n")
    st = lean_pairs(d['steps'])
    # One declaration per group (the kernel keeps every term of a `decide`; one big conjunction runs out of memory
    # on cofactors with ~1000 divisors).
    def thm(name, conj):
        out.append(f"theorem {name} :\n    " + " ∧\n    ".join(conj) + " := by\n  decide +kernel\n")
    lb = f"(baseList fsb{i})"
    base = [f"baseOK fsb{i} = true", f"prodOf fsb{i} = {d['b']}",
            f"intervalOKB (ssBits {lb}) {d['c']} {lb}.sum = true", f"gapOKB (ssBits {lb}) {d['g']} {lb}.sum = true",
            f"stepsOK {d['c']} {d['g']} {d['b']} {lb}.sum {st} = true"]
    if r:
        p, fsM, e0, kk, gB, SB, SA, Sn = r[0]
        base.append(f"stepsEnd {d['b']} {lb}.sum {st} = (prodOf fs{i}_0 * {p} ^ {e0}, {SA})")
    else:
        base.append(f"stepsEnd {d['b']} {lb}.sum {st} = ({ne}, {d['S']})")
    thm(f"cert{i}_base", base)
    for j, (p, fsM, e0, kk, gB, SB, SA, Sn) in enumerate(r):
        nxt = f"prodOf fs{i}_{j + 1} * {r[j + 1][0]} ^ {r[j + 1][2]}" if j + 1 < len(r) else ne
        thm(f"cert{i}_gap{j}", [f"gapCertM fs{i}_{j} {gB} {SB} = true"])
        thm(f"cert{i}_raise{j}", [f"raiseOK (prodOf fs{i}_{j}) {p} {e0} {d['c']} {gB} {SB} {SA} {kk} = true",
                                  f"raiseSum (prodOf fs{i}_{j}) {p} {e0} {SB} {SA} {kk} = {Sn}",
                                  f"prodOf fs{i}_{j} * {p} ^ ({e0} + {kk}) = {nxt}",
                                  f"0 < prodOf fs{i}_{j}", f"prodOf fs{i}_{j} % {p} ≠ 0"])
    thm(f"cert{i}_last", [f"lastOK ({ne}) {d['S']} {d['c']} {d['g']} {d['B']} = true"])
    pf = [f"  obtain ⟨hbo, hpb, hI, hG, hst, hend⟩ := cert{i}_base",
          f"  obtain ⟨hl, hnd⟩ := baseList_properDivisors (by norm_num [fsb{i}]) hbo",
          f"  have h0 := intervalGap_of_bitsB (baseList fsb{i}) hl hnd hI hG",
          "  rw [hpb] at h0",
          f"  have hs := intervalGap_of_stepsOK (by norm_num) {st} _ _ (by norm_num) (by norm_num) hst h0",
          "  rw [hend] at hs"]
    for j, (p, *_rest) in enumerate(r):
        pf += [f"  obtain ⟨h{j}ok, h{j}rs, h{j}n, h{j}m0, h{j}mp⟩ := cert{i}_raise{j}",
               f"  obtain ⟨hSB{j}, hgB{j}⟩ := gap_properDivisors_of_gapCertM (by norm_num [fs{i}_{j}]) cert{i}_gap{j}",
               f"  have hr{j} := intervalGap_raise h{j}m0 (by norm_num) (fun h => h{j}mp (Nat.mod_eq_zero_of_dvd h))",
               f"    (by norm_num) hs hSB{j} hgB{j} h{j}ok",
               f"  rw [h{j}rs, h{j}n] at hr{j}",
               f"  clear hs",
               f"  have hs := hr{j}"]
    pf.append(f"  exact not_weird_mul_prime_of_lastOK (by norm_num) (by norm_num) hs cert{i}_last hq hqn")
    desc = (f"base `{d['b']}` (`c = {d['c']}`, `g = {d['g']}`), steps {', '.join(f'`{q}^{e}`' for q, e in d['steps']) or 'none'}, "
            f"raises {', '.join(f'`{p}` to `{p}^{e0 + kk}`' for p, _f, e0, kk, *_x in r) or 'none'}, last primes `q < {d['B']}`")
    out.append(f"/-- **No `{ne} · q` is weird** (`q` prime, `q ∤` prefix): {desc}. -/\n"
               f"theorem not_weird_{i} {{q : ℕ}} (hq : q.Prime) (hqn : ¬ q ∣ {ne}) :\n"
               f"    ¬ ({ne} * q).Weird := by\n" + "\n".join(pf) + "\n")
    return "\n".join(out)


HEADER = '''module

public import ErdosResearch.SubsetSumLate
public import ErdosResearch.SubsetSumLastOK
public import ErdosResearch.SubsetSumDivsDesc
public import ErdosResearch.SubsetSumBitsFast

@[expose] public section

/-!
# Generated: odd-weird families certified by multi-raise plans

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 58).

GENERATED by `scripts/late_cert_gen.py {args}` (do not edit by hand). Each instance says that no `N · q`
(`q` prime, `q ∤ N`) is weird, for one deficient 5-prime prefix `N` drawn from the same random family as
`MULTI=1 scripts/raise_late_plan.py`: a bitset base, prime-power steps (`stepsOK`), raises over cofactors with a
greedy gap bound (`gapCertM`, `intervalGap_raise`), and all last primes at once (`lastOK`).
These are random test prefixes, not the prefixes of the omega = 6 search. Elementary; not a new result on #470.
-/

set_option Elab.async false

namespace ErdosResearch.OddWeirdPlans

open ErdosResearch.SubsetSumCert ErdosResearch.SubsetSumRaise ErdosResearch.SubsetSumSteps
  ErdosResearch.SubsetSumGreedy ErdosResearch.SubsetSumLate ErdosResearch.SubsetSumLastOK
  ErdosResearch.SubsetSumDivsDesc ErdosResearch.SubsetSumBitsFast

'''

DRY = os.environ.get('DRY') == '1'   # DRY=1: only count (prefixes tried / with a plan / emitted), no Lean output
tried = planned = 0
random.seed(3)
primes = [p for p in range(3, 60) if isprime(p)]
done = 0
parts = []
seen = set()
for t in range(3000):
    if done >= COUNT:
        break
    P = sorted(random.sample(primes[:8], 5))
    f = {p: random.choice([1, 1, 2, 2, 3, 4, 6, 8, 10]) for p in P}
    n = 1; sgn = 1
    for p, e in f.items():
        n *= p ** e; sgn *= sigpp(p, e)
    if sgn >= 2 * n or max(f.values()) < 6 or n in seen:
        continue
    tried += 1
    pl = multi_plan(f)
    if not pl or not pl[2]:
        continue
    planned += 1
    d = build(f, pl)
    if d is None:
        continue
    seen.add(n)
    if not DRY:
        parts.append(emit(done, d))
    done += 1
    print(f"instance {done - 1}: f={f} plan={pl} B={d['B']}", file=sys.stderr, flush=True)
print(f"deficient prefixes {tried}, multi-raise plans {planned}, emitted {done}", file=sys.stderr)
if DRY:
    sys.exit(0)
print(HEADER.replace('{args}', f'{LIMB} {COUNT} {MAXDIV} {MAXB}') + "\n".join(parts) + "\nend ErdosResearch.OddWeirdPlans")
