module

public import Mathlib

@[expose] public section

/-!
# Unitary perfect numbers with few prime factors, and odd weird numbers with few prime factors

Statements only. The proofs are in `Solution.lean`, which imports the development in
`ErdosResearch/`.

A *unitary divisor* of `n` is a divisor `d` with `gcd(d, n / d) = 1`. A *unitary perfect number*
is a positive `n` equal to the sum of its unitary divisors other than `n` itself. Erdős Problem
1052 asks whether there are only finitely many. The known ones are 6, 60, 90, 87360 and
146361946186458562560000. The definitions below are copied verbatim from
`ErdosResearch/UnitaryPerfect.lean`, where they follow google-deepmind/formal-conjectures
(`ErdosProblems/1052.lean`).

A number is *weird* if it is abundant but not pseudoperfect (`Nat.Weird` in Mathlib). Erdős
Problem 470 asks whether an odd weird number exists.

`ω(n)` is written `n.primeFactors.card` (the number of distinct prime factors).
-/

namespace ErdosResearch.Erdos1052

/-- A proper unitary divisor of $n$ is a divisor $d$ of $n$
such that $d$ is coprime to $n/d$, and $d < n$. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- A number $n > 0$ is a unitary perfect number if it is the sum of its proper unitary
divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

end ErdosResearch.Erdos1052

namespace ErdosResearch.Palomar

open ErdosResearch.Erdos1052

/-- **Classification for `ω(n) ≤ 7`.** The unitary perfect numbers with at most seven distinct
prime factors are exactly `6`, `60`, `90` and `87360`. (Known: Wall 1988 shows that every
unitary perfect number other than the five known ones has at least nine odd prime factors.) -/
theorem isUnitaryPerfect_iff_of_card_primeFactors_le_seven {n : ℕ}
    (hcard : n.primeFactors.card ≤ 7) :
    IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 := by
  sorry

/-- **Finiteness for fixed `ω`.** For every `k`, there are only finitely many unitary perfect
numbers with exactly `k` distinct prime factors. (Known: Subbarao–Warren 1966, Goto 2007.) -/
theorem finite_isUnitaryPerfect_of_card_primeFactors_eq (k : ℕ) :
    {n : ℕ | IsUnitaryPerfect n ∧ n.primeFactors.card = k}.Finite := by
  sorry

/-- **No odd weird number with `ω(n) ≤ 4`.** An odd number with at most four distinct prime
factors is not weird. (Known: Liddy–Riedl 2018 show that an odd weird number has at least six
distinct prime factors.) -/
theorem not_weird_of_odd_of_card_primeFactors_le_four {n : ℕ} (hn : Odd n)
    (hcard : n.primeFactors.card ≤ 4) : ¬ n.Weird := by
  sorry

end ErdosResearch.Palomar
