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
- **Graham 1989 confirmed second-hand on 2026-11-06:** the zbMATH review of DeBoer 1993
  (Zbl 0805.11006) says that S. W. Graham, Fibonacci Q. 27 (1989) 317–322, Zbl 0678.10004, showed
  that 6, 60 and 87360 are the only UPNs `2^m s` with `s` odd and squarefree. It also says that DeBoer
  shows 90 is the only one of the form `2^m 3^2 s` (`s` squarefree, coprime to 6).
  The review of Subbarao–Cook–Newberry–Weber 1972 is empty, so its content is unknown.
- Wall 1988 ("at least 9 odd prime factors") and Graham 1989 ("squarefree odd part ⇒ 6, 60,
  87360; some prime > 2^15") are cited like this in arXiv:2605.20475. zbMATH has entries
  Zbl 0657.10003 (1988) and Zbl 0678.10004 (1989), but their metadata is hidden ("contents
  unavailable due to conflicting licenses"), so I **cannot confirm** that they are these papers.
  The paper also cites Hagis for `ω(n) ≥ 7`; I have not checked that.
- **Wall 1988 confirmed on zbMATH on 2026-11-08** (session 5): the *review* of Zbl 0657.10003 is
  visible even though the metadata is hidden. It says that the fifth UPN is `N = 2^18 · 5^4 · Q`,
  with `Q` a squarefree product of ten odd primes, and that "if n is a unitary perfect number
  which exceeds N then n is divisible by at least nine distinct odd primes" (review by P. Hagis
  jun.). Together with Wall 1975 (Zbl 0312.10004, whose review says the paper proves there are
  no UPNs between 87360 and N; that part is cut off in the API text, so it is second-hand), a
  sixth UPN has ≥ 9 odd prime factors. So "≤ 8 odd prime factors ⇒ one of the known four" is
  classical. The review of Zbl 0625.10003
  (1987, same hidden metadata) states that a sixth UPN has an odd prime power `p^e`
  with … (cut off). Not read further.

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

**Next step at the end of session 2 (step 1 done in session 3; see below):**
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

## Session 3 (2026-11-06): proved, failed, next step

**Proved in Lean** (`lake build` OK, 7355 jobs, 0 warnings, no `sorry`; `#print axioms` gives only
`propext`, `Classical.choice`, `Quot.sound`):
- `ErdosResearch/UnitaryPerfect.lean`:
  - `arith3_sorted`, `arith_three_odd`, `not_isUnitaryPerfect_of_card_primeFactors_eq_four`:
    **there is no UPN with exactly 3 odd prime factors.**
  - `isUnitaryPerfect_of_card_primeFactors_le_four_iff`: ≤ 3 odd prime factors ⇒ `{6, 60, 90}`.
- `ErdosResearch/UnitaryPerfectFourOdd.lean` (new):
  - `exists_sorted_factors`: for `n ≠ 0`, the prime-power factors `p^{v_p(n)}` form a strictly
    increasing, pairwise coprime list of numbers `> 1`, of length `ω(n)`, with product `n` and
    `∏(1+y) = σ*(n)`. It is general and reusable for any `k`.
  - `arith_sorted_5` (generated proof, 12 lemmas): if `1 < y₁ < … < y₅` are pairwise coprime and
    `∏(1+yᵢ) = 2∏yᵢ`, then `∏yᵢ = 87360`.
  - `eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five`: **the only UPN with exactly 4 odd
    prime factors is 87360.**
  - `isUnitaryPerfect_of_card_primeFactors_le_five_iff`: **≤ 4 odd prime factors ⇒ exactly
    `{6, 60, 90, 87360}`.**
- **Not new mathematically.** It is consistent with Graham 1989 and with Wall 1988's "a sixth UPN
  has ≥ 9 odd prime factors" (cited second-hand). I could not check who first proved the
  ≤ 4 classification; it is probably Subbarao–Warren 1966 or SCNW 1972. As far as I know it is
  new *as a formalisation*: formal-conjectures has only the statement and the examples.

**Method (reusable for any `k`):** `scripts/upn_case_tree.py M TARGET SPLIT` generates the case
tree, and `python3 -I scripts/upn_case_tree.py 5 87360 2` reproduces the generated section exactly.
Sort *all* prime-power factors, including `2^a`, as `y₁ < … < y_M`. At each level, either:
- a size bound `yᵢ ≥ B`: shift the remaining variables to `B, B+1, …`. Then
  `2∏y − ∏(1+y)` has nonnegative coefficients, so `linarith` closes it with the monomial hints
  `0 ≤ z·z'·…`;
- or one of the finitely many values below `B`: prune a value at once (`norm_num` on `Nat.Coprime`) if it shares a factor with an earlier `yⱼ`;
- the last variable: the equation is linear, so `omega` decides it.
Parity and "power of two" are not needed; coprimality alone kills the spurious integer solutions:
- 4 factors: `(3,5,8,9)`, `(2,5,11,54)`, …;
- 5 factors: `(3,5,9,11,32)`, `(3,5,9,16,17)`, … (26 non-coprime ones);
- the only coprime 5-factor solution is `(3,5,7,13,64)`.

**Failed / lessons:**
- With only the odd primes as variables (as in the `k = 3` proof), the `k = 4` tree does not
  terminate. `3,5,7,9` already give `∏(1+1/p) ≈ 2.03 > 2`, so no size bound on `a` exists, and
  87360 has `a = 6`. Fix: put `2^a` into the sorted list like any other factor.
- One lemma with the whole tree runs out of heartbeats (200000 per declaration). Fix: one lemma
  per `(y₁, y₂)` prefix.
- `nlinarith` on 4–5 shifted variables with 11–26 hints runs out of heartbeats. Fix:
  `linarith` with the same hints, which is enough because its parser treats monomials as atoms. It
  is much faster, and no `ring_nf` is needed first.
- `rw [← h]` to permute the factors of the equation fails (the pattern does not match). Use
  `convert h using 1 <;> ring`.
- Naming a script `enum.py` shadows the stdlib module `enum` when it runs from that directory.

**Measured for the next `k`:**
- 5 odd primes (6 factors), coprimality pruning only: 4144 linear leaves, 2596 bounds and 15913
  gcd-pruned branches. **No coprime solution**, so no UPN with exactly 5 odd prime factors (by
  computation, not yet in Lean).
- That is ~120× the 4-odd tree, which compiles in ~70 s. As is, it would be ~1–2 h of
  compilation and a ~100k-line file: too much for the CI (60-minute timeout).
- With parity + power-of-two pruning but no gcd pruning it is worse: 12370 leaves.

**Next step (in order):**
1. `k = 5` (no UPN with exactly 5 odd prime factors), in Lean. Make the tree smaller first. Ideas:
   - combine gcd pruning with "at most one even factor, and it is a power of 2". For Lean, add
     the hypothesis that exactly one `yᵢ` is even and pass `2 ∣ yᵢ → yᵢ = 2^a` as data;
   - replace the explicit `rcases` over long ranges with `interval_cases` + `first | omega |
     norm_num at …`;
   - check in a scratch file (`lake env lean`) how long one `(y₁, y₂)` lemma takes before
     generating them all;
   - if it stays > 30 min, split it into several files so they compile in parallel in the CI.
2. A uniform version: one theorem `card primeFactors = M ⇒ …` that uses `exists_sorted_factors`
   for each generated `arith_sorted_M`. The `k ≤ 3` cases could be redone this way and simplified.
3. Honest assessment (unchanged): with `k ≤ 4`, and `k = 5` if it gets done, this only reproduces
   classical results. Something mathematically new would be beyond Wall's ≥ 9 odd prime factors,
   which needs `k = 5…8` (out of reach with this tree). The deliverable is the formalisation.
   Formal-conjectures could take it, but I will not publish it without Pablo's approval.

## Session 4 (2026-11-06): proved, failed, next step

**Proved (Lean; no sorry; axioms `propext`, `Classical.choice`, `Quot.sound` only; `lake build`
OK, 7356 jobs, ~45 s, new module ~34 s):** `ErdosResearch/UnitaryPerfectFiveOdd.lean`
- `upnCheck`: a Boolean search over `y₁ < ⋯ < y_r`, pairwise coprime, coprime to a prefix
  `pre`, with entries `≥ L`. It returns `true` only if `Q · ∏(1+y) = 2P · ∏y` has no
  solution. Its steps: `2P ≤ Q` ⇒ none; one variable ⇒ linear (`y = Q/(2P−Q)`); a bound
  `Q·(L+1)⋯(L+r) < 2P·L⋯(L+r−1)` ⇒ none; otherwise split into `y₁ = L` (pruned by gcd) or
  `y₁ ≥ L+1`.
- `upnCheck_sound`: the soundness proof, once and for all (induction on the fuel). The key
  lemma is `prod_succ_mul_le`: for sorted entries `≥ L`,
  `∏(1+y) · L⋯(L+r−1) ≤ ∏y · (L+1)⋯(L+r)`.
- `upnCheck_six : upnCheck 5000 1 1 2 [] 6 = true := by decide +kernel`. The kernel evaluates it
  in ~30 s (29392 nodes, depth 2087, using GMP arithmetic on `Nat`). This is reflection, not
  `native_decide`, so no extra axiom.
- `not_isUnitaryPerfect_of_card_primeFactors_eq_six`: **there is no UPN with exactly 5 odd prime
  factors.**
- `isUnitaryPerfect_of_card_primeFactors_le_six_iff`: **ω(n) ≤ 6 ⇒ n ∈ {6, 60, 90, 87360}.**
- `scripts/upn_search_count.py R [--ppow]`: the same search in Python, used to count nodes before
  running it in the kernel.
- **Not new mathematically.** It is implied by Wall 1988 (≥ 9 odd prime factors for a sixth UPN,
  cited second-hand). It is new only as a formalisation.

**Decision and why:** I dropped the session 3 plan (shrinking the generated `linarith` tree)
in favour of reflection. A ~120× bigger tree meant a ~100k-line file and 1–2 h of compilation.
With reflection the proof is ~200 lines and 30 s. The bound "ratio ≤ ∏(L+1+j)/(L+j)" (because
`(1+y)/y` decreases) is much simpler to prove in general than the positivity of polynomial
coefficients used by the old generator. The old tree for k = 4 stays as it is: it works, and
there was no reason to touch it.

**Failed / lessons:**
- First version of the checker: the `2P ≤ Q` branch returned `true`, which is **unsound** when
  `P = Q = 0` (`0 = 0`). The soundness proof would not close, and that is how I found it. Fix:
  return `0 < Q`.
- `rw [hq]` with `hq : Q = …` also rewrites the `Q` inside the denominator. Use
  `Nat.div_eq_of_eq_mul_left` / `Nat.mod_eq_zero_of_dvd` directly.
- **k = 6 (7 factors) is not feasible with this checker as is.** With coprimality only it needs
  20.9M nodes, and it finds the spurious solution `(3,5,7,13,67,1741,8704)`, where
  `8704 = 2⁹·17` is not a prime power. With prime-power pruning it needs 5.8M nodes and finds no
  solution. At ~1000 nodes/s in the kernel that is ≥ 1.5 h, over the CI limit (60 min).

**Next step (in order):**
1. k = 6 (7 factors). Shrink the search before giving it to the kernel:
   (a) 2-adic constraint: `1 + 2^a` is odd and every `1 + p^e` is even, so
   `a + 1 = Σ v₂(1 + pᵢ^eᵢ) ≥ k`, i.e. the even factor is `≥ 2^{k−1}`. Also, each `pᵢ^eᵢ ≡ 3
   (mod 4)` contributes `v₂ ≥ 2`;
   (b) a prime-power check in the checker (`IsPrimePow`, by trial division with fuel);
   (c) with two variables left, use `(dy − Q)(dz − Q) = Q(Q + d)` (`d = 2P − Q`) instead of walking
   `y` up to its bound. Measure each idea with `scripts/upn_search_count.py` first. Aim for
   < 1M nodes. If it does not fit, split by `y₁` into several modules.
2. Optional: redo k ≤ 4 with `upnCheck` (an extension that returns the solutions, to allow
   87360) and remove the ~900 generated lines. This is cosmetic, low priority.
3. Honest assessment (unchanged): reaching k = 8 would reproduce Wall 1988 by computation, and
   it is not new. Something new would need k ≥ 9, which a naive search cannot reach. The value
   is the formalisation. formal-conjectures could take it, but only with Pablo's approval.

## Session 5 (2026-11-08): proved, failed, next step

**Proved (Lean; no sorry; axioms `propext`, `Classical.choice`, `Quot.sound` only; `lake build`
OK, 7357 jobs; new module ~41 s):** `ErdosResearch/UnitaryPerfectSixOdd.lean`
- **No UPN has exactly 6 odd prime factors** (`not_isUnitaryPerfect_of_card_primeFactors_eq_seven`).
- `isUnitaryPerfect_of_card_primeFactors_le_seven_iff`: **ω(n) ≤ 7 ⇒ n ∈ {6, 60, 90, 87360}.**
- **Not new mathematically.** Wall 1988 (now confirmed on zbMATH, see the literature section)
  gives ≥ 9 odd prime factors for a sixth UPN. New only as a formalisation.

**How (and why it fits when the session 4 plan did not):** a new reflective checker `fchk`,
which treats `2^a` separately instead of as one more sorted variable:
1. *2-adic bound* (`two_pow_le_of_eq`): each `1 + qᵢ` is even and `∏ qᵢ` is odd, so
   `2^k ∣ 2^{a+1}`, i.e. `2^a ≥ 2^{k−1} = 32`. This is the decisive pruning: without it (A0 = 1)
   the same search needs 11.9M nodes; with it, 5447.
2. *"free" state* (`2^a` not placed yet): walk `L` by 1; odd `L` → branch `y = L` (gcd pruning;
   `2 ∈ pre` makes everything odd); even `L` → branch `2^a = L` if `L` is a power of 2 and
   `≥ 32` (`isPow2From`). The bound uses stride 2 for the odd variables (`ascProd2`,
   `prod2_succ_mul_le`) and `(1+E)/E ≤ (1+M')/M'` with `M' = max(L, 32)` for the power of two.
3. *"placed" state*: the rest is the session 4 `upnCheck`, reused as is (its soundness lemma is
   applied directly).
4. *Last odd variable while `2^a` is still free*: no walk. `2^a ∣ Q(1+y)` (since `2^a ⟂ 1+2^a`) and
   `min(y, 2^a)·(2P−Q) ≤ 3Q` (`min_bound`) give `2^a ≤ Q(1 + 3Q/(2P−Q))` (`pow_le_bound`), so
   the checker loops over the powers of two (`powLoop`) and solves for `y` linearly (`candOk`).
- `fchk 5000 1 1 32 2 [2] 6 = true` by `decide +kernel`: 5447 nodes + 7779 loop steps, depth 1794.
- Sanity checks (`#eval` in a scratch file): `fchk … 4 = false` (it finds 87360 = 2⁶·3·5·7·13)
  and `fchk … 2 = false` (60, 90), so the checker is not vacuously `true`. `fchk … 3/5/6 = true`.
- `scripts/upn_search_hybrid.py K [A0]`: the same search in Python, used to count nodes.

**Failed / lessons:**
- *Odd variables only, with `a` eliminated by the 2-adic valuation* (first idea): the target
  ratio is then an interval `[2^k/(1+2^{k−1}), 2)` instead of a number, and once the partial
  ratio enters the interval the bound never prunes, so the walk does not terminate (Python
  looped for k = 6). Making `2^a` an explicit, specially-handled variable fixes it.
- First hybrid version missed 60 = 2²·3·5: the power-of-two branch was only tested at `L+1` after
  choosing `y = L`, which skips `4` between `3` and `5`. Fixed by walking `L` by 1 in the free
  state and testing parity. The small cases k = 1, 2, 4 (which must find 6; 60, 90; 87360)
  caught it.
- Prime-power pruning and the 2-adic check in the "placed" state barely help (462k vs 463k nodes
  before the `powLoop` change), so they were left out of the Lean checker.
- `rw [← heq]` fails when the goal has a permuted product. Rewrite the goal into the exact
  form with `show … = … by ring` first.
- A careless `sed` on `ErdosResearch.lean` replaced every import line. I restored it with
  `git checkout` and appended the one import. Edit that file with an append, not `sed`.

**k = 7 (8 factors), measured in Python, not feasible yet:** 12.9M nodes + 4.9M loop steps. Of
those, 8.6M nodes are in the "placed" state with two odd variables left and 0.66M in the "free"
state with two odd variables left. With two variables left the equation is
`(dy − Q)(dz − Q) = Q(Q + d) = 2PQ` (`d = 2P − Q`), and `P`, `Q` are products of known
factors. Replacing that walk by an enumeration of the divisors of `2PQ` gives ~0.8M nodes +
0.55M divisors + 4.9M loop steps (estimate; it counts `d(2PQ)/2` per node). The kernel speed
here is roughly 2–3 ms per node, so that is still several hours.

**Next step (in order):**
1. k = 7 needs ~10× fewer kernel steps than the divisor estimate. Options, to measure in Python
   first: (a) start `powLoop` at `max(L, 2^{k−1})` instead of 1 (most of the 4.9M loop steps
   are below that); (b) divisors of `2PQ` for two variables left, in both states (needs a
   verified divisor enumeration from a known factorisation: carry the prime factorisation of
   `P` and `Q` along the search); (c) measure the real kernel time per node on a k = 7 sub-tree
   (fix `y₁ = 3`) before writing anything. If it stays > 30 min, split by `y₁` into modules.
2. Honest assessment (updated): k ≤ 8 is exactly Wall 1988 (now confirmed). A *new* result would
   need either k ≥ 9 odd prime factors (out of reach for any search like this; Wall's own proof
   is not a plain enumeration) or a structural statement, e.g. finiteness for fixed k (Goto 2007
   proves `n < 2^{2^k}`, from memory, **not checked**). The realistic deliverable is still the
   formalisation, now ω ≤ 7, which nobody has in Lean (formal-conjectures only states #1052).
   Submitting it anywhere needs Pablo's approval.
3. Optional/cosmetic: redo k ≤ 4 with `fchk` (it returns `false` exactly when a solution exists,
   so for k = 2, 4 a variant that collects solutions would be needed) and drop ~900 generated
   lines.

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

## Daily summary (2026-11-06, session 3)

- **Approaches tried:** (a) the `k = 3` case with the odd primes as variables and `a` bounded by
  size, generated by a script; (b) the same scheme for `k = 4` (it does not terminate, because `a`
  is not bounded); (c) sorting all prime-power factors including `2^a`, pruned only by
  coprimality, which works for `k = 4`; (d) counting the `k = 5` tree.
- **What failed and why:** see "Failed / lessons" in session 3. In short: an unbounded `a` with
  odd-only variables, the heartbeat limit for one big lemma, `nlinarith` being too slow with many
  hints, and `rw` not matching a permuted product.
- **Advances:** in Lean without `sorry`: no UPN with 3 odd prime factors; the only one with 4 is
  87360; so `ω(n) ≤ 5 ⇒ n ∈ {6, 60, 90, 87360}`. Graham 1989 confirmed second-hand via zbMATH. No
  new mathematical result.
- **Quota consumed:** one `lean-research` session. I cannot see exact tokens from inside the
  session, so PGAL should take them from its own accounting. About 15 compilations (scratch files
  + `lake build`), Mathlib from cache only, never compiled. Two zbMATH queries. No money spent.

## Daily summary (2026-11-06, session 4)

- **Approaches tried:** (a) a reflective checker `upnCheck` + its soundness proof + `decide
  +kernel` for k = 5 odd primes; (b) measuring k = 6 in Python (coprimality only, and with
  prime-power pruning).
- **What failed and why:** the first checker was unsound for `P = Q = 0` (the soundness proof
  caught it). k = 6 needs 5.8M nodes even with prime-power pruning, too many for the kernel within
  the CI.
- **Advances:** no UPN with exactly 5 odd prime factors, so `ω(n) ≤ 6 ⇒ n ∈ {6, 60, 90, 87360}`.
  In Lean, without `sorry`, with standard axioms only. Known mathematically (Wall 1988,
  second-hand). No new mathematical result.
- **Quota consumed:** one `lean-research` session. I cannot see exact tokens from inside the
  session (PGAL should use its own accounting). About 8 compilations, Mathlib from cache only,
  never compiled. Python counts: ~35 s for k = 6 and a few minutes with `--ppow`. No network
  queries. No money spent.

## Daily summary (2026-11-08, session 5)

- **Approaches tried:** (a) odd-only search with `a` eliminated 2-adically (does not terminate:
  interval target); (b) hybrid search with `2^a` as a special variable, the 2-adic lower bound
  `2^a ≥ 2^{k−1}`, stride-2 bounds and a loop over powers of two for the last odd variable,
  formalised as `fchk` + soundness proof + `decide +kernel`; (c) Python estimates for k = 7,
  including divisor enumeration for the two-variable step; (d) zbMATH check of Wall 1988.
- **What failed and why:** (a) see above; the first hybrid version skipped a power of two
  between consecutive odd candidates (caught by the k = 2 test); k = 7 is still ~13M nodes,
  hours in the kernel.
- **Advances:** in Lean, without `sorry`, standard axioms only: no UPN with exactly 6 odd prime
  factors, so `ω(n) ≤ 7 ⇒ n ∈ {6, 60, 90, 87360}`. Kernel check ~30 s. Wall 1988 is now confirmed
  on zbMATH, and it already implies this, so **no new mathematical result**. New only as a
  formalisation.
- **Quota consumed:** one `lean-research` session. I cannot see exact tokens from inside the
  session (PGAL should use its own accounting). About 5 compilations of the new module plus two
  full `lake build`s (Mathlib from cache, never compiled). Python runs: ~2 min in total, plus one
  k = 6 run of the abandoned odd-only search that did not terminate (killed by timeout, ~2 min).
  One zbMATH query. No money spent.

## Not verified

- **Task #49 / PART 1 / `docs/cost-analysis.md`:** the email says PART 1 is done in
  `docs/cost-analysis.md`. That file does **not** exist in this repo (there is no `docs/`
  directory) and the GitHub API gives 404 when looking for it elsewhere. The reference to task
  #49 and to PART 1 is therefore **not verified**.
- General web search (no egress beyond lean-lang, erdosproblems and arXiv).
- Wall / Frey / Goto: on 2026-11-06 I confirmed on zbMATH that the papers exist. Wall 1988
  (≥ 9 odd prime factors) is confirmed by its zbMATH review (session 5). Frey's and Goto's
  bounds are still from memory, and Graham 1989 is only second-hand (via DeBoer's review).
- The gap in Prop. 1.1 of arXiv:2605.20475 is my own reading. Nobody else has checked it.
- Who first proved "≤ 4 odd prime factors ⇒ {6, 60, 90, 87360}": zbMATH has no review of
  Subbarao–Warren 1966 or of SCNW 1972. "No UPN with 5 odd prime factors" is now checked in Lean (session 4).
