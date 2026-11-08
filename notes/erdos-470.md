# Erdős #470: odd weird numbers ($10)

Statement (erdosproblems.com/470, checked 2026-11-08): `n` is *weird* if `σ(n) ≥ 2n` and `n` is not
pseudoperfect. (i) Are there odd weird numbers? (ii) Are there infinitely many primitive weird
numbers? The $10 is for (i) (Guy B2). Lean: `FormalConjectures/ErdosProblems/470.lean` uses
Mathlib's `Nat.Weird` (abundant ∧ ¬ pseudoperfect). Both parts are still `sorry` there, as are the
variants `odd_weird_10_pow_21` (Fang) and the Liddy–Riedl variant.

## Why switch from #1052 (decision of 2026-11-08, session 8)

Session 7 concluded that something new on #1052 needs ≥ 9 odd primes (Wall 1988 covers ≤ 8), which
is far beyond search (k = 7 alone is 12.9M nodes). I re-filtered the teorth/erdosproblems
`problems.yaml` (downloaded 2026-11-08): **54** open/falsifiable prize problems. Almost all of them are
deep analytic, combinatorial or geometric problems. The elementary ones are:
- #470 ($10): 2 comments, none mathematical; one user "currently working on" it; formal statement present.
- #647 (£25 ≈ $44): crowded (18 comments, 4 users working on it), and it is a search for one
  `n > 24` that Erdős himself thought very doubtful. Dropped.
- #708, #710, #711: asymptotic questions; #711 has partial progress by van Doorn 2026. Not
  elementary-finite.

#470 has the same "exclude small ω" structure as #1052, so the session 1–7 method transfers.

## What is known (literature)

- Benkoski–Erdős 1974, Math. Comp. 28, 617–623 (zbMATH Zbl 0279.10005, confirmed): weird numbers
  have positive density.
- Fang, arXiv:2207.12906 (abstract read; LaTeX source skimmed): no odd weird number below `10^21`.
  Also none below `10^28` with abundance below `10^14`. The method is a tree search on `pred(N) = N/(largest prime)`.
- Liddy & Riedl 2018, *An algorithm to determine all odd primitive abundant numbers with d prime
  divisors*, Honors Research Projects 728, Univ. of Akron (cited by erdosproblems.com and
  formal-conjectures): an odd weird number has ≥ 6 distinct prime factors. **Not read** (not on
  zbMATH / OpenAlex; ideaexchange.uakron.edu is not one of my sources).
- Amato–Hasler–Melfi–Parton, J. Number Theory 2019 (Zbl 1437.11167; arXiv:1802.07178): primitive
  abundant numbers counted by Ω; odd PANs counted up to Ω = 8.
- Hisamoto, arXiv:2607.25278 (2026, main theorem read): abundancy index > 633 ⇒ semiperfect. It does
  not help with odd numbers, whose abundancy is small for small ω.
- OpenAlex lists a Zenodo deposit (2026) titled "Non-existence of odd weird numbers: a complete
  proof". It is not peer-reviewed, the site still lists #470 as open, and I did not read it. Ignored.

## Feasibility of something new: "no odd weird number with ω = 6"

Reduction: an odd weird `n` is a multiple of an odd primitive non-deficient `m`, and `m` must itself
be weird (a multiple of a pseudoperfect number is pseudoperfect). So "ω ≥ 7" ⇔ every odd primitive
abundant number with ω = 6 is pseudoperfect (with ω ≤ 5 handled by Liddy–Riedl).
- My count (`/tmp` Python, not committed): odd primitive abundant numbers with ω = 3: **8**; with
  ω = 4: **576**. The ω = 5 run did not finish within a few minutes in naive Python.
- Growth is doubly exponential: the last prime `q` ranges up to `σ(M)/(2M − σ(M))` for the deficient
  prefix `M`, which is astronomically large when `σ(M)/M` is close to 2.
- Useful idea for the last prime (mine, not checked against Liddy–Riedl): for `m = Mq` with `q` prime,
  larger than every prime factor of `M`, and `q ∤ M`, `m` is pseudoperfect if and only if
  `∃ k ≥ 1` with `M − k` a subset sum of the proper divisors of `M` and `kq` a subset sum of the
  divisors of `M` (since `kq ≤ σ(M) < 2M`). That handles all `q` for a fixed `M` with one
  subset-sum table, but the number of prefixes `M` with ω = 5 is still enormous.
- Verdict: ω = 6 needs a serious C/GMP computation (days, uncertain), and it cannot be checked in
  Lean. **Not attempted this session.**

## Session 8 (2026-11-08): proved, failed, next step

**Proved (Lean; no sorry; axioms `propext`, `Classical.choice`, `Quot.sound`; `lake build` OK, 7360
jobs; module ~10 s):** `ErdosResearch/OddWeird.lean`
- `sigma_mul_prod_sub_one_le`: `σ(n)·∏_{p|n}(p−1) ≤ n·∏_{p|n} p` for every `n`.
- `deficient_of_odd_of_card_primeFactors_le_two`, `not_weird_of_odd_of_card_primeFactors_le_two`:
  an odd number with ω ≤ 2 is deficient, so it is not weird.
- Classical (trivial). It is a base for the next cases, not a new result.

**Failed:** two `omega` calls (fixed by naming the hypotheses and giving `s.card = 1/2` explicitly).

**Next step (in order):**
1. ω = 3 in Lean: an odd abundant `n` with ω = 3 is a multiple of one of the 8 odd PANs with ω = 3
   (smallest 945 = 3³·5·7). Prove each one is pseudoperfect with an explicit subset (`decide`), plus
   "multiple of a pseudoperfect is pseudoperfect" (scale the subset). The finiteness/enumeration
   step can reuse the sorted-factor bounds from `UnitaryPerfectFinite.lean`.
2. Write a fast enumerator (C or optimised Python) and count odd PANs with ω = 5. That shows whether
   ω = 6 (new) is within reach at all, using the last-prime subset-sum reduction above.
3. If ω = 6 is out of reach (likely), the realistic deliverable is formalising Liddy–Riedl (ω ≤ 5)
   in Lean, which is a `sorry` in formal-conjectures. Publishing anything needs Pablo's approval.

## Daily summary (2026-11-08, session 8)

- **Approaches tried:** (a) re-filtering all open prize problems in order to switch; (b) literature on
  #470 (erdosproblems.com, arXiv, zbMATH, OpenAlex; Semantic Scholar answered "429 Too Many
  Requests"); (c) counting odd primitive abundant numbers by ω; (d) Lean base for #470.
- **What failed and why:** nothing new on #1052 is reachable by search (Wall 1988), hence the switch.
  The naive ω = 5 count is too slow in Python. ω = 6 (a new result) looks infeasible without a
  large, unverifiable computation.
- **Advances:** in Lean, without `sorry`: odd ω ≤ 2 ⇒ deficient ⇒ not weird, and the general bound
  `σ(n)/n ≤ ∏ p/(p−1)`. Classical. No new mathematical result.
- **Quota consumed:** one `lean-research` session. I can't see the exact token count from inside
  the session; PGAL should take it from its own accounting. About 10 network queries (GitHub raw,
  erdosproblems.com, arXiv, zbMATH, OpenAlex), 3 compilations of the module and 1 full `lake build`.
  Mathlib came from the cache and was not compiled. No money spent.
