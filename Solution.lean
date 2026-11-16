module

public import Mathlib
public import ErdosResearch

@[expose] public section

/-!
# Palomar Solution

Proofs of the statements in `Challenge.lean`, taken from the `ErdosResearch` library:

* `ErdosResearch.Erdos1052.finite_isUnitaryPerfect_card_primeFactors_eq`
  (`ErdosResearch/UnitaryPerfectFinite.lean`);
* `ErdosResearch.Erdos1052.isUnitaryPerfect_of_card_primeFactors_le_seven_iff`
  (`ErdosResearch/UnitaryPerfectSixOdd.lean`);
* `Erdos470Research.not_weird_of_odd_of_card_primeFactors_le_four`
  (`ErdosResearch/OddWeirdFour.lean`).

`ErdosResearch.Erdos1052.IsUnitaryPerfect` unfolds to the inline condition of the Challenge.
-/

namespace ErdosResearch.Palomar

theorem finite_unitaryPerfect_card_primeFactors_eq (k : ℕ) :
    {n : ℕ | ((∑ d ∈ Finset.Ico 1 n with d ∣ n ∧ d.Coprime (n / d), d) = n ∧ 0 < n) ∧
      n.primeFactors.card = k}.Finite :=
  Erdos1052.finite_isUnitaryPerfect_card_primeFactors_eq k

theorem unitaryPerfect_iff_of_card_primeFactors_le_seven {n : ℕ}
    (hcard : n.primeFactors.card ≤ 7) :
    ((∑ d ∈ Finset.Ico 1 n with d ∣ n ∧ d.Coprime (n / d), d) = n ∧ 0 < n) ↔
      n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 :=
  Erdos1052.isUnitaryPerfect_of_card_primeFactors_le_seven_iff hcard

theorem not_weird_of_odd_of_card_primeFactors_le_four {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card ≤ 4) : ¬ n.Weird :=
  Erdos470Research.not_weird_of_odd_of_card_primeFactors_le_four hn h

end ErdosResearch.Palomar
