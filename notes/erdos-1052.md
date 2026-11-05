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
  **Read it in full before calling anything about the 2-adic structure new.**
- Nothing else on arXiv about unitary perfect *integers* (only polynomials over `F_2`/`F_4`).

From memory, **not checked against the source** (journals not reachable):
- Subbarao–Warren (1966): definition, the first four, no odd ones.
- Wall (1975): the fifth, 146361946186458562560000.
- Wall (1988, Fibonacci Quart.): a new unitary perfect number has at least 9 odd prime factors.
- Frey (1978): if `3 ∤ n`, then `n` has at least 144 odd prime factors (approximate).
- Goto (2007): `n < 2^{2^k}` if `n` has `k` odd prime factors (so finitely many for each `k`).

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

**Next step (in order):**
1. Read arXiv:2605.20475 in full and write down what it proves and what it leaves open.
2. Lean: the classification with exactly two odd prime factors (`{60, 90}`). Equation
   `(1+2^a)(1+p^e)(1+q^f) = 2^{a+1} p^e q^f`. Goal: a general lemma "`n` with `k` odd prime
   factors ⇒ `2^k ∣ σ*(n)` ⇒ `a ≥ k − 1`", useful for every `k`.
3. Formalise the finiteness for fixed `k` (Subbarao/Goto). That would be a substantial formal
   result even though it is known.
4. Only then look for a new partial result: extend Wall's bound (≥ 9 odd prime factors) or
   close cases of `H_even` from the 2026 paper. Before calling it new, check the literature
   again.
