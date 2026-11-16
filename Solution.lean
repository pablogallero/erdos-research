module

public import ErdosResearch

@[expose] public section

/-!
# Proofs of the statements in `Challenge.lean`

Same names and types as in `Challenge.lean`. The definitions `properUnitaryDivisors` and
`IsUnitaryPerfect` come from `ErdosResearch/UnitaryPerfect.lean`, with the same bodies as in the
Challenge; the proofs are in `ErdosResearch/UnitaryPerfectSixOdd.lean`,
`ErdosResearch/UnitaryPerfectFinite.lean` and `ErdosResearch/OddWeirdFour.lean`.
-/

namespace ErdosResearch.Palomar

open ErdosResearch.Erdos1052

theorem isUnitaryPerfect_iff_of_card_primeFactors_le_seven {n : ℕ}
    (hcard : n.primeFactors.card ≤ 7) :
    IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 :=
  isUnitaryPerfect_of_card_primeFactors_le_seven_iff hcard

theorem finite_isUnitaryPerfect_of_card_primeFactors_eq (k : ℕ) :
    {n : ℕ | IsUnitaryPerfect n ∧ n.primeFactors.card = k}.Finite :=
  finite_isUnitaryPerfect_card_primeFactors_eq k

theorem not_weird_of_odd_of_card_primeFactors_le_four {n : ℕ} (hn : Odd n)
    (hcard : n.primeFactors.card ≤ 4) : ¬ n.Weird :=
  Erdos470Research.not_weird_of_odd_of_card_primeFactors_le_four hn hcard

end ErdosResearch.Palomar
