module

public import Mathlib

@[expose] public section

/-!
# Palomar Challenge: unitary perfect numbers (Erdős #1052) and odd weird numbers (Erdős #470)

The statements below use Mathlib only. The definitions are spelled out inline, so a reader does not
need to trust any project-specific definition.

* A *unitary perfect number* is an `n > 0` equal to the sum of its proper unitary divisors, i.e.
  the divisors `d < n` of `n` with `gcd(d, n/d) = 1`. This is the definition used for Erdős
  Problem 1052 in `google-deepmind/formal-conjectures` (`FormalConjectures/ErdosProblems/1052.lean`).
* A number is *weird* if it is abundant but not pseudoperfect (`Nat.Weird` in Mathlib, the same
  notion as in `FormalConjectures/ErdosProblems/470.lean`).

Results (proved in `Solution.lean`):

1. `finite_unitaryPerfect_card_primeFactors_eq`: for every `k`, only finitely many unitary perfect
   numbers have exactly `k` distinct prime factors.
2. `unitaryPerfect_iff_of_card_primeFactors_le_seven`: a number with at most seven distinct prime
   factors is unitary perfect iff it is `6`, `60`, `90` or `87360`.
3. `not_weird_of_odd_of_card_primeFactors_le_four`: an odd number with at most four distinct prime
   factors is not weird.

All three are known mathematically (Subbarao–Warren 1966, Wall 1988, Goto 2007 for unitary perfect
numbers; Liddy–Riedl 2018 for odd weird numbers). They are new only as formalisations.
-/

namespace ErdosResearch.Palomar

/-- For every `k`, only finitely many unitary perfect numbers have exactly `k` distinct prime
factors. Here `n` is unitary perfect iff `n > 0` and `n` is the sum of the divisors `d` of `n`
with `1 ≤ d < n` and `gcd(d, n/d) = 1`. -/
theorem finite_unitaryPerfect_card_primeFactors_eq (k : ℕ) :
    {n : ℕ | ((∑ d ∈ Finset.Ico 1 n with d ∣ n ∧ d.Coprime (n / d), d) = n ∧ 0 < n) ∧
      n.primeFactors.card = k}.Finite := by
  sorry

/-- A natural number with at most seven distinct prime factors is unitary perfect iff it is
`6`, `60`, `90` or `87360`. -/
theorem unitaryPerfect_iff_of_card_primeFactors_le_seven {n : ℕ}
    (hcard : n.primeFactors.card ≤ 7) :
    ((∑ d ∈ Finset.Ico 1 n with d ∣ n ∧ d.Coprime (n / d), d) = n ∧ 0 < n) ↔
      n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 := by
  sorry

/-- An odd natural number with at most four distinct prime factors is not weird
(abundant but not pseudoperfect). -/
theorem not_weird_of_odd_of_card_primeFactors_le_four {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card ≤ 4) : ¬ n.Weird := by
  sorry

end ErdosResearch.Palomar
