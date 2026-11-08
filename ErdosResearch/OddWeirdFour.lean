import ErdosResearch.OddWeirdFourChunks

/-!
# Erdős Problem 470: an odd number with at most four distinct prime factors is not weird

* `OddWeirdFourData.lean`: 584 odd primitive abundant numbers (8 with three prime factors, 576
  with four), each with a pseudoperfectness certificate (`certs_ok`, checked by the kernel).
* `OddWeirdFourCore.lean`: the checker `chk` and its soundness (`chk_sound` and combinators).
* `OddWeirdFourChunks.lean` (generated): the search for four odd primes, split into chunks, giving
  `sound_top : Sound R0 1 1 4 3 0`.

Here `sound_top` is applied to the sorted prime factors of `n`.

Classical: Liddy and Riedl (2018) show that an odd weird number has at least six distinct prime
factors. New only as a formalisation.
-/

namespace Erdos470Research

open ArithmeticFunction

set_option maxRecDepth 100000 in
theorem certs_ok : panCerts.all certOK = true := by decide +kernel

lemma good_R0 : Good 1 R0 := good_certs panCerts certs_ok

lemma ppow_fsOf_sort {n : ℕ} (hn : n ≠ 0) :
    ppow (fsOf (n.primeFactors.sort (· ≤ ·)) n.factorization) = n := by
  have hnd := (n.primeFactors.sort_sorted_lt).nodup
  have h1 : ppow (fsOf (n.primeFactors.sort (· ≤ ·)) n.factorization) =
      ((n.primeFactors.sort (· ≤ ·)).map fun p => p ^ n.factorization p).prod := by
    simp [ppow, fsOf, Function.comp_def]
  rw [h1, ← List.prod_toFinset _ hnd, Finset.sort_toFinset]
  conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
  rw [Finsupp.prod, Nat.support_factorization]

/-- An odd abundant number with exactly four distinct prime factors is pseudoperfect. -/
theorem pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_four {n : ℕ} (hn : Odd n)
    (hab : n.Abundant) (h : n.primeFactors.card = 4) : n.Pseudoperfect := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  set ps := n.primeFactors.sort (· ≤ ·)
  have hmem : ∀ p ∈ ps, p.Prime ∧ 3 ≤ p ∧ p % 2 = 1 ∧ ¬ p ∣ 1 ∧ 1 ≤ n.factorization p := by
    intro p hp
    rw [Finset.mem_sort] at hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hodd : p % 2 = 1 := by
      rcases hpp.eq_two_or_odd with h2 | h2
      · rw [h2] at hdvd
        exact absurd (Nat.odd_iff.mp hn) (by rw [Nat.dvd_iff_mod_eq_zero] at hdvd; omega)
      · exact h2
    refine ⟨hpp, by have := hpp.two_le; omega, hodd, hpp.not_dvd_one, ?_⟩
    exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp
      (by rwa [Nat.support_factorization]))
  have key := sound_top 1 1 ps n.factorization good_R0 (dvd_refl 1) one_pos (by simp) le_rfl
    rfl (by simp [ps, h]) (Finset.sort_sorted_lt _) hmem (by simp)
  rw [one_mul, ppow_fsOf_sort hn0] at key
  rcases key with hσ | hps
  · exact absurd (abundant_iff_sigma.mp hab) (by omega)
  · exact hps

/-- An odd number with exactly four distinct prime factors is not weird. -/
theorem not_weird_of_odd_of_card_primeFactors_eq_four {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card = 4) : ¬ n.Weird := fun ⟨hab, hps⟩ =>
  hps (pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_four hn hab h)

/-- An odd number with at most four distinct prime factors is not weird. -/
theorem not_weird_of_odd_of_card_primeFactors_le_four {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card ≤ 4) : ¬ n.Weird := by
  rcases Nat.lt_or_ge n.primeFactors.card 4 with h' | h'
  · exact not_weird_of_odd_of_card_primeFactors_le_three hn (by omega)
  · exact not_weird_of_odd_of_card_primeFactors_eq_four hn (by omega)

end Erdos470Research
