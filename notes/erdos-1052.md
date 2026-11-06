# Erdős #1052: unitary perfect numbers ($10)

Statement (erdosproblems.com/1052, Guy B3): `d` is a unitary divisor of `n` if `d ∣ n` and
`gcd(d, n/d) = 1`. `n` is *unitary perfect* if it is the sum of its unitary divisors other
than `n`, i.e. `σ*(n) = 2n`. **Are there only finitely many?** Prize: $10 (Carlitz, Erdős,
Subbarao, as reported by Guy), and Subbarao adds 10 cents for each new example.
Five are known: 6, 60, 90, 87360 and 146361946186458562560000.

Lean statement: `FormalConjectures/ErdosProblems/1052.lean` (formal-conjectures), copied
as-is into `ErdosResearch/UnitaryPerfect.lean` (as `def`s, without `sorry`).

## Why this problem (decision of 2026-11-05)

#43 is resolved (`erdos-43-status.md`). I filtered the teorth/erdosproblems table for
problems that are open, have a prize and a formal-conjectures statement: 44 of them. To
measure prior attention I looked at the comments on erdosproblems.com, who is marked as
"currently working on", AI attempts (mehmetmars7/Erdosproblems-llm-hunter) and arXiv.

| # | prize | comments | working on it | AI attempts | why not / why yes |
|---|---|---|---|---|---|
| 39 | $500 | 0 | nobody | 5 | infinite Sidon set with `N^{1/2−ε}`: Ruzsa's exponent (√2−1) has stood since 1998; deep |
| 41 | $500 | 0 | nobody | 5 | `B_3` liminf: only even `h` is known (Chen 1996); deep |
| 50 | $250 | 0 | nobody | 12 | singular distribution of φ(n)/n: real analysis that is hard to formalise |
| 241 | $100 | 3 | nobody | 3 | sharp constant for `B_3`; the best bound (White 2024) is nearly optimal *within* Green's method |
| 1191 | $1000 | 0 | nobody | 1 | strengthens #39; deep |
| **1052** | **$10** | **0** | **nobody** | **3** | **elementary, finite cases checkable in Lean, natural partial results** |

All of the above have been through the mass AI sweeps (llm-hunter covers every problem).
None of them has "little attention" in an absolute sense. I pick #1052 because it is the only
one where an incremental partial result (more odd prime factors excluded, cases with `k`
odd primes classified) is realistic and fits Lean well. Caveat: Lean attention exists.
AlphaProof proved `even_of_isUnitaryPerfect` in a fork of formal-conjectures, and someone
has a proof of the fifth example in another fork. Neither is a solution.

## What is known (literature)

Checked on arXiv on 2026-11-05:
- arXiv:2605.20475 (T. Maciejewski, May 2026), *Bounded-box reductions in the
  Subbarao–Warren problem*. **It does not prove finiteness.** It eliminates "impostor
  kernels" for `1 ≤ a ≤ 10000` (with `2^a ∥ n`) and reduces what remains to a set `H_even` of
  `m` such that every prime factor of `2^m + 1` is "3-Higgs", bounding `|H_even ∩ [2, 50000]| ≤ 272`.
  **Read in full in session 2 (LaTeX source from arXiv); see "Reading of arXiv:2605.20475" below.**
- Nothing else on arXiv about unitary perfect *integers* (only polynomials over `F_2`/`F_4`).

Bibliographic existence **checked on zbMATH Open on 2026-11-06** (title search "unitary perfect").
The contents were not read; the journals are not reachable:
- Subbarao–Warren, *Unitary perfect numbers*, Can. Math. Bull. 9 (1966) 147–153, Zbl 0139.26901:
  definition, the first four, no odd ones.
- Wall, *The fifth unitary perfect number*, Can. Math. Bull. 18 (1975) 115–122, Zbl 0312.10004.
- Frey, *On unitary perfect numbers*, Elem. Math. 33 (1978) 95–96, Zbl 0382.10004. (The content
  "if `3 ∤ n`, at least 144 odd prime factors" is from memory and **not checked**.)
- Goto, *Upper bounds for unitary perfect numbers and unitary harmonic numbers*, Rocky Mt. J.
  Math. 37 (2007) 1557–1576, Zbl 1141.11006. (The content "`n < 2^{2^k}` with `k` odd prime
  factors" is from memory and **not checked**.)
- Also listed: Subbarao–Cook–Newberry–Weber, Delta 3 (1972), Zbl 0251.10007; DeBoer, *Non-existence
  of certain unitary perfect numbers*, Pi Mu Epsilon J. 9 (1993), Zbl 0805.11006; He Bo, J. Guizhou
  Norm. Univ. 23 (2005), Zbl 1128.11302. Not read.
- Wall 1988 ("at least 9 odd prime factors") and Graham 1989 ("squarefree odd part ⇒ 6, 60,
  87360; some prime > 2^15") are cited like this in arXiv:2605.20475. zbMATH has entries
  Zbl 0657.10003 (1988) and Zbl 0678.10004 (1989), but their metadata is hidden ("contents
  unavailable due to conflicting licenses"), so I **cannot confirm** that they are these papers.
  The paper also cites Hagis for `ω(n) ≥ 7`; I have not checked that.

## Reading of arXiv:2605.20475 (session 2)

What it claims as rigorous: the 3-filter elimination of five "impostor kernels" for
`a ≤ 10000`; the bounds `|H_even ∩ [2,40000]| ≤ 201` and `|H_even ∩ [2,50000]| ≤ 272`; the reduction
of finiteness of `H_even` to `m = 2p`; a thinness theorem via Ford. It explicitly says it does
**not** prove finiteness. Everything that is conditional (H1, H2, several conjectures) is
labelled as such.

**Gap I found (my reading, not checked by anyone else):** the whole link from UPNs to `H_even`
goes through Proposition 1.1, "every prime divisor of a UPN is 3-Higgs". The proof as written
does not work:
- It uses `q ∣ p − 1 ∣ p^e + 1`, but `p^e + 1 ≡ 2 (mod p − 1)`, so `p − 1 ∤ p^e + 1` once
  `p > 3`. (The divisibility that does hold is `p + 1 ∣ p^e + 1` for odd `e`.)
- It gets the exponent caps `v_q(p−1) ≤ 3` from "the kernel exponents in the box enforce this".
  That is circular for a general UPN.
- I do not see why, say, 17 (with `17 − 1 = 2^4`, so not 3-Higgs) could not divide a UPN.
So filter N, and with it `H_even`, are about the 3-Higgs constraint, which is not proved to hold
for UPNs. The paper's results do not constrain UPNs unless that proposition gets a correct proof.
**Consequence for us:** do not build on `H_even`. The paper's frontier is not a reliable target
for a partial result. Per the rules I do not contact the author.

## Session 1 (2026-11-05): proved, failed, next step

**Proved in Lean** (`ErdosResearch/UnitaryPerfect.lean`, compiles without `sorry`, axioms
only `propext`, `Classical.choice`, `Quot.sound`):
- `isUnitaryPerfect_iff`: the formal-conjectures definition ⇔ `σ*(n) = 2n ∧ n > 0`.
- `usigma_mul`: `σ*` is multiplicative on coprime arguments.
- `usigma_prime_pow`: `σ*(p^e) = 1 + p^e`.
- `even_of_isUnitaryPerfect`: every unitary perfect number is even (known; AlphaProof
  also has it).
- `eq_six_of_isUnitaryPerfect_of_card_primeFactors_le_two`: with at most one odd prime
  factor, the only one is 6 (known, elementary).
- The five known examples. The last two (87360 and the 24-digit one) go through
  multiplicativity and take seconds. In formal-conjectures the 87360 one is `stop` ("too slow")
  and the fifth is `sorry` in the main repo.

**None of this is mathematically new.** It is the base for the cases that come next.

**Failed / lessons:**
- `set x := …` followed by `omega`: omega unfolds the definition and fails. Fix: `clear_value`
  after collecting the facts you need.
- `usigma_split` had to be stated with the explicit type after `set`, otherwise the hypothesis
  keeps `n.factorization p` and later `rw` calls do not match.
- `decide` on the definition is fine up to 90; for larger numbers, use multiplicativity.

**Next step at the end of session 1 (superseded; see session 2):** read arXiv:2605.20475; classify
the case with two odd primes; formalise finiteness for fixed `k`; then look for something new.

## Session 2 (2026-11-06): proved, failed, next step

**Done:**
- Read arXiv:2605.20475 in full (LaTeX source; the PDF cannot be rendered here). There is a gap
  in its Proposition 1.1 (see above). Decision: do not use `H_even`.
- Checked on zbMATH that the classical references exist (list above).
- **Lean** (`ErdosResearch/UnitaryPerfect.lean`, `lake build` OK, no `sorry`, axioms only
  `propext`, `Classical.choice`, `Quot.sound`):
  - `exists_split_of_dvd`: `m = p^e · r` with `p ∤ r` and `ω(r) = ω(m) − 1` (general; reusable
    for any `k`).
  - `arith_sorted`, `arith_two_odd`: `(1+2^a)(1+P)(1+Q) = 2^{a+1}PQ` with `P ≠ Q` odd and `> 1`
    ⇒ `2^a P Q ∈ {60, 90}`. The argument: `a ≥ 3` is impossible by a size bound; for `a = 1` it
    reduces to `(P−3)(Q−3) = 12`, and for `a = 2` to `(3P−5)(3Q−5) = 40`.
  - `eq_sixty_or_ninety_of_isUnitaryPerfect_of_card_primeFactors_eq_three`.
  - `isUnitaryPerfect_of_card_primeFactors_le_three_iff`: with at most two odd prime factors,
    the UPNs are exactly `6, 60, 90`.
- **Not new mathematically** (Subbarao–Warren 1966). It is new only as a formalisation, as far as
  I know; formal-conjectures has only the statement.

**Failed / lessons:**
- `nlinarith` could not do the bound `2XPQ > (1+X)(1+P)(1+Q)` for `X ≥ 8, P ≥ 3, Q ≥ 5` directly,
  even with product hints. Fix: shift the variables (`X = x+8`, `P = p+3`, `Q = q+5`), then
  `ring_nf`, and then `nlinarith` with the nonnegative monomials `xp, xq, pq, xpq`. Since every
  coefficient is positive, it closes at once. Reuse this trick for `k = 3`.
- The PDF reader needs `pdftoppm` (not installed). Use the arXiv source at `arxiv.org/e-print/ID`.

**Next step (in order):**
1. `k = 3` odd prime factors: prove that there is **no** UPN (87360 has 4). Same scheme, using
   `exists_split_of_dvd` twice. The arithmetic needs more cases. Use the 2-adic balance:
   `v₂((1+P)(1+Q)(1+R)) = a + 1`, so `a ≥ 2`, together with the bound
   `∏(1+1/x) = 2`. Before writing it, do it by hand or with a small script to get the finite
   list of `(a, P)` cases.
2. Better than case-by-case: a general lemma "`n` has `k` odd prime factors ⇒ `2^k ∣ σ*(m)` ⇒
   `a ≥ k − 1`" and a "smallest prime power is bounded" lemma. They are the building blocks of a
   formal finiteness theorem for fixed `k` (Goto-type), which would be a substantial formal
   result.
3. Honest assessment: a mathematically new result (beyond Wall's ≥ 9 odd components) needs a
   computer search far beyond what can be certified in Lean in a session. The realistic
   deliverable is the formalisation (`k ≤ 3` or `k ≤ 4` classified; finiteness for fixed `k`).
   Formal-conjectures could take that, but I will not publish it without Pablo's approval.

## Daily summary (2026-11-05)

- **Approaches tried:** (a) status check of #43 on erdosproblems.com, arXiv and
  formal-conjectures → resolved, so dropped; (b) choice of #1052 from the teorth table
  (prize, Lean statement, little attention); (c) Lean base for #1052: definition equivalence,
  multiplicativity of `σ*`, parity, the case with ≤ 1 odd prime factor, the five known examples.
- **What failed and why:** `set` + `omega` (omega unfolds the definition; fixed with
  `clear_value`); `decide` on large examples (too slow; replaced by multiplicativity +
  `norm_num`). The two-odd-primes classification was not reached in this session.
- **Advances:** formal base compiled without `sorry` or added axioms. No mathematically new
  result.
- **Quota consumed:** one `lean-research` session (2 h limit), within budget. The exact token
  count is not visible from inside the session, so it is not reported here; PGAL should take it
  from its own accounting. No money spent, no Mathlib build (cache only), AWS priority untouched.

## Daily summary (2026-11-06)

- **Approaches tried:** (a) full reading of arXiv:2605.20475; (b) checking the references on
  zbMATH; (c) Lean classification of the case with two odd primes.
- **What failed and why:** the PDF route (no renderer; I used the LaTeX source). Direct
  `nlinarith` on the size bound (it needed shifted variables). The 2026 paper does not work as
  a base, because its Prop. 1.1 has a gap.
- **Advances:** UPNs with at most two odd prime factors = `{6, 60, 90}`, in Lean without `sorry`.
  It is known mathematically. No new mathematical result yet.
- **Quota consumed:** one `lean-research` session. Exact tokens are not visible from inside, so
  PGAL should take them from its own accounting. About 5 builds of the repo file (Mathlib from
  cache, never compiled). No money spent.

## Not verified

- **Task #49 / PART 1 / `docs/cost-analysis.md`:** the email says PART 1 is done in
  `docs/cost-analysis.md`. That file does **not** exist in this repo (there is no `docs/`
  directory) and the GitHub API gives 404 when looking for it elsewhere. The reference to task
  #49 and to PART 1 is therefore **not verified**.
- General web search (no egress beyond lean-lang, erdosproblems and arXiv).
- Wall / Frey / Goto: on 2026-11-06 I confirmed on zbMATH that the papers exist. Their exact
  *contents* (bounds) are still from memory or second-hand via arXiv:2605.20475. Wall 1988 and
  Graham 1989 are not confirmed.
- The gap in Prop. 1.1 of arXiv:2605.20475 is my own reading. Nobody else has checked it.
