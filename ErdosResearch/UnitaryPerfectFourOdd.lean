import ErdosResearch.UnitaryPerfect

/-!
# Erdős Problem 1052: unitary perfect numbers with four odd prime factors

* `exists_sorted_factors`: the prime-power factors `p ^ v_p(n)` of `n ≠ 0`, as a strictly
  increasing, pairwise coprime list with product `n` and `∏ (1 + y) = σ*(n)`.
* `arith_sorted_5`: if `1 < y₁ < ⋯ < y₅` are pairwise coprime and
  `∏ (1 + yᵢ) = 2 ∏ yᵢ`, then `∏ yᵢ = 87360`. Parity and "power of two" are not used; only the
  order and coprimality are.
* `eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five`: the only unitary perfect number
  with exactly four odd prime factors is `87360 = 2^6 · 3 · 5 · 7 · 13`.
* `isUnitaryPerfect_of_card_primeFactors_le_five_iff`: with at most four odd prime factors, the
  unitary perfect numbers are exactly `6, 60, 90, 87360`.

All of this is known mathematically (see `notes/erdos-1052.md`); it is new only as a
formalisation.

## How `arith_sorted_5` is proved (generated proof)

The case tree was produced by a script (`notes/erdos-1052.md` describes it). At each level the
smallest remaining factor `yᵢ` is either a size bound or one of finitely many values:
* bound `yᵢ ≥ B`: shift every remaining variable to its lower bound (`yⱼ = zⱼ + B + (j - i)`).
  Then `2 ∏ y - ∏ (1 + y)` is a polynomial in the `z`s with nonnegative coefficients and a
  positive constant term, so `linarith` closes it once the monomials `0 ≤ z * z' * …` are
  given;
* a value with a common factor with an earlier `yⱼ`: `norm_num` on the coprimality hypothesis;
* the last variable: the equation is linear in it, so `omega` decides it.
The integer solutions that are not pairwise coprime, such as `(3, 5, 9, 11, 32)` or
`(3, 5, 9, 16, 17)`, are cut by coprimality. The only coprime one is `(3, 5, 7, 13, 64)`.
The tree is split into one lemma per `(y₁, y₂)` prefix to stay within the heartbeat limit.
-/

namespace ErdosResearch.Erdos1052

open Finset

/-- The prime-power factors `p ^ v_p(n)` of `n ≠ 0`, sorted: a strictly increasing list of
pairwise coprime numbers `> 1`, of length `ω(n)`, with product `n` and `∏ (1 + y) = σ*(n)`. -/
lemma exists_sorted_factors {n : ℕ} (hn : n ≠ 0) :
    ∃ l : List ℕ, l.Sorted (· < ·) ∧ l.length = n.primeFactors.card ∧ (∀ y ∈ l, 1 < y) ∧
      l.Pairwise Nat.Coprime ∧ l.prod = n ∧ (l.map (1 + ·)).prod = usigma n := by
  set f : ℕ → ℕ := fun p => p ^ n.factorization p with hf
  have hinj : Set.InjOn f n.primeFactors := by
    intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hq' := Nat.prime_of_mem_primeFactors hq
    have hvp : 0 < n.factorization p :=
      hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    have hdvd : p ∣ q ^ n.factorization q := by
      have : p ∣ f p := dvd_pow_self p hvp.ne'
      rwa [hpq] at this
    exact (Nat.prime_dvd_prime_iff_eq hp' hq').1 (hp'.dvd_of_dvd_pow hdvd)
  set s := n.primeFactors.image f with hs
  refine ⟨s.sort (· ≤ ·), s.sort_sorted_lt, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_sort, card_image_of_injOn hinj]
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.1 ((mem_sort _).1 hy)
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact Nat.one_lt_pow (hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).ne'
      hp'.one_lt
  · refine (s.sort_sorted_lt).imp_of_mem ?_
    intro x y hx hy hxy
    obtain ⟨p, hp, rfl⟩ := mem_image.1 ((mem_sort _).1 hx)
    obtain ⟨q, hq, rfl⟩ := mem_image.1 ((mem_sort _).1 hy)
    have hpq : p ≠ q := by rintro rfl; exact hxy.ne rfl
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq
  · have : (s.sort (· ≤ ·)).prod = ∏ y ∈ s, y := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id', ← Finset.sort_eq (· ≤ ·) s,
        Multiset.prod_coe]
    rw [this, prod_image hinj]
    conv_rhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rfl
  · have : ((s.sort (· ≤ ·)).map (1 + ·)).prod = ∏ y ∈ s, (1 + y) := by
      rw [Finset.prod_eq_multiset_prod, ← Finset.sort_eq (· ≤ ·) s, Multiset.map_coe,
        Multiset.prod_coe]
    rw [this, prod_image hinj, Nat.multiplicative_factorization usigma
      (fun _ _ h => usigma_mul h) usigma_one hn]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.support_factorization] at hp
    show 1 + p ^ n.factorization p = usigma (p ^ n.factorization p)
    rw [usigma_prime_pow (Nat.prime_of_mem_primeFactors hp)
      ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp))]

section Generated

set_option linter.unusedVariables false

lemma arith_sorted_5_2_3 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 2) (e2 : y2 =
          3) :
    False := by
  subst e1 e2
  linarith [Nat.zero_le (y3 * y4), Nat.zero_le (y3 * y5), Nat.zero_le (y4 * y5), Nat.zero_le (y3 *
      y4 * y5)]

lemma arith_sorted_5_2_5 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 2) (e2 : y2 =
          5) :
    False := by
  subst e1 e2
  rcases (show y3 = 6 ∨ y3 = 7 ∨ y3 = 8 ∨ y3 = 9 ∨ y3 = 10 ∨ y3 = 11 ∨ y3 = 12 ∨ y3 = 13 ∨ y3 = 14 ∨
      y3 = 15 ∨ y3 = 16 ∨ y3 = 17 ∨ y3 = 18 ∨ y3 = 19 ∨ y3 = 20 ∨ y3 = 21 ∨ y3 = 22 ∨ y3 = 23 ∨ y3 =
      24 ∨ y3 = 25 ∨ y3 = 26 ∨ y3 = 27 ∨ 28 ≤ y3 by omega) with rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | hb
  · norm_num at c1_3
  · linarith [Nat.zero_le (y4 * y5)]
  · norm_num at c1_3
  · linarith [Nat.zero_le (y4 * y5)]
  · norm_num at c1_3
  · rcases (show y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4
      = 20 ∨ y4 = 21 ∨ y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ y4 = 29
      ∨ y4 = 30 ∨ y4 = 31 ∨ y4 = 32 ∨ y4 = 33 ∨ y4 = 34 ∨ y4 = 35 ∨ y4 = 36 ∨ y4 = 37 ∨ y4 = 38 ∨ y4
      = 39 ∨ y4 = 40 ∨ y4 = 41 ∨ y4 = 42 ∨ y4 = 43 ∨ y4 = 44 ∨ y4 = 45 ∨ y4 = 46 ∨ y4 = 47 ∨ y4 = 48
      ∨ y4 = 49 ∨ y4 = 50 ∨ y4 = 51 ∨ y4 = 52 ∨ y4 = 53 ∨ y4 = 54 ∨ y4 = 55 ∨ y4 = 56 ∨ y4 = 57 ∨ y4
      = 58 ∨ y4 = 59 ∨ y4 = 60 ∨ y4 = 61 ∨ y4 = 62 ∨ y4 = 63 ∨ y4 = 64 ∨ y4 = 65 ∨ y4 = 66 ∨ y4 = 67
      ∨ y4 = 68 ∨ y4 = 69 ∨ y4 = 70 ∨ y4 = 71 ∨ y4 = 72 ∨ y4 = 73 ∨ y4 = 74 ∨ y4 = 75 ∨ y4 = 76 ∨ y4
      = 77 ∨ y4 = 78 ∨ y4 = 79 ∨ y4 = 80 ∨ y4 = 81 ∨ y4 = 82 ∨ y4 = 83 ∨ y4 = 84 ∨ y4 = 85 ∨ y4 = 86
      ∨ y4 = 87 ∨ y4 = 88 ∨ y4 = 89 ∨ y4 = 90 ∨ y4 = 91 ∨ y4 = 92 ∨ y4 = 93 ∨ y4 = 94 ∨ y4 = 95 ∨ y4
      = 96 ∨ y4 = 97 ∨ y4 = 98 ∨ y4 = 99 ∨ y4 = 100 ∨ y4 = 101 ∨ y4 = 102 ∨ y4 = 103 ∨ y4 = 104 ∨ y4
      = 105 ∨ y4 = 106 ∨ y4 = 107 ∨ y4 = 108 ∨ 109 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain rfl : y5 = 1044 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · obtain rfl : y5 = 648 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 384 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 252 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 164 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain rfl : y5 = 144 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 109 := ⟨y4 - 109, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 110 := ⟨y5 - 110, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ y4
      = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ y4 = 29 ∨ y4 = 30 ∨ y4 = 31
      ∨ y4 = 32 ∨ y4 = 33 ∨ y4 = 34 ∨ y4 = 35 ∨ y4 = 36 ∨ y4 = 37 ∨ y4 = 38 ∨ y4 = 39 ∨ y4 = 40 ∨ y4
      = 41 ∨ y4 = 42 ∨ y4 = 43 ∨ y4 = 44 ∨ y4 = 45 ∨ y4 = 46 ∨ y4 = 47 ∨ y4 = 48 ∨ y4 = 49 ∨ y4 = 50
      ∨ y4 = 51 ∨ y4 = 52 ∨ y4 = 53 ∨ y4 = 54 ∨ y4 = 55 ∨ y4 = 56 ∨ y4 = 57 ∨ y4 = 58 ∨ y4 = 59 ∨ y4
      = 60 ∨ y4 = 61 ∨ y4 = 62 ∨ y4 = 63 ∨ 64 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 714 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 90 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · obtain rfl : y5 = 84 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 64 := by omega
      norm_num at c1_5
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 64 := ⟨y4 - 64, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 65 := ⟨y5 - 65, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · norm_num at c2_3
  · norm_num at c1_3
  · rcases (show y4 = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4
      = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ y4 = 29 ∨ y4 = 30 ∨ y4 = 31 ∨ y4 = 32 ∨ y4 = 33 ∨ y4 = 34 ∨ y4 = 35
      ∨ y4 = 36 ∨ y4 = 37 ∨ y4 = 38 ∨ y4 = 39 ∨ y4 = 40 ∨ 41 ≤ y4 by omega) with rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 594 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain rfl : y5 = 84 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 54 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 41 := ⟨y4 - 41, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 42 := ⟨y5 - 42, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 20 ∨ y4 = 21 ∨ y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27 ∨ y4
      = 28 ∨ y4 = 29 ∨ y4 = 30 ∨ y4 = 31 ∨ y4 = 32 ∨ y4 = 33 ∨ y4 = 34 ∨ y4 = 35 ∨ y4 = 36 ∨ 37 ≤ y4
      by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · obtain rfl : y5 = 132 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain rfl : y5 = 56 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 37 := ⟨y4 - 37, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 38 := ⟨y5 - 38, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ y4 = 29 ∨ y4
      = 30 ∨ y4 = 31 ∨ y4 = 32 ∨ y4 = 33 ∨ 34 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 34 := ⟨y4 - 34, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 35 := ⟨y5 - 35, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ y4 = 29 ∨ y4 = 30 ∨ 31 ≤ y4 by
      omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 31 := ⟨y4 - 31, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 32 := ⟨y5 - 32, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · norm_num at c2_3
  · norm_num at c1_3
  · rcases (show y4 = 28 ∨ 29 ≤ y4 by omega) with rfl | hb
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 29 := ⟨y4 - 29, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 30 := ⟨y5 - 30, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 28 := ⟨y3 - 28, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 29 := ⟨y4 - 29, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 30 := ⟨y5 - 30, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_2_7 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 2) (e2 : y2 =
          7) :
    False := by
  subst e1 e2
  rcases (show y3 = 8 ∨ y3 = 9 ∨ y3 = 10 ∨ y3 = 11 ∨ y3 = 12 ∨ y3 = 13 ∨ y3 = 14 ∨ y3 = 15 ∨ y3 = 16
      ∨ y3 = 17 ∨ y3 = 18 ∨ 19 ≤ y3 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | hb
  · norm_num at c1_3
  · rcases (show y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4
      = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27
      ∨ y4 = 28 ∨ y4 = 29 ∨ y4 = 30 ∨ y4 = 31 ∨ y4 = 32 ∨ y4 = 33 ∨ y4 = 34 ∨ y4 = 35 ∨ y4 = 36 ∨ y4
      = 37 ∨ y4 = 38 ∨ y4 = 39 ∨ y4 = 40 ∨ 41 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain rfl : y5 = 160 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · obtain rfl : y5 = 104 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c3_4
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 41 := ⟨y4 - 41, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 42 := ⟨y5 - 42, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4
      = 20 ∨ y4 = 21 ∨ y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨ y4 = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ 29 ≤ y4
      by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 384 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain rfl : y5 = 32 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 29 := ⟨y4 - 29, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 30 := ⟨y5 - 30, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ y4
      = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ 25 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · obtain rfl : y5 = 64 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 25 := ⟨y4 - 25, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 26 := ⟨y5 - 26, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ 22 ≤ y4 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 22 := ⟨y4 - 22, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 23 := ⟨y5 - 23, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 18 ∨ y4 = 19 ∨ 20 ≤ y4 by omega) with rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 20 := ⟨y4 - 20, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 21 := ⟨y5 - 21, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 19 := ⟨y3 - 19, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 20 := ⟨y4 - 20, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 21 := ⟨y5 - 21, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_2_9 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 2) (e2 : y2 =
          9) :
    False := by
  subst e1 e2
  rcases (show y3 = 10 ∨ y3 = 11 ∨ y3 = 12 ∨ y3 = 13 ∨ y3 = 14 ∨ y3 = 15 ∨ 16 ≤ y3 by omega) with
      rfl | rfl | rfl | rfl | rfl | rfl | hb
  · norm_num at c1_3
  · rcases (show y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4
      = 20 ∨ 21 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 21 := ⟨y4 - 21, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 22 := ⟨y5 - 22, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ 18 ≤ y4 by omega) with rfl | rfl | rfl |
      rfl | hb
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c1_4
    · omega
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 18 := ⟨y4 - 18, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 19 := ⟨y5 - 19, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · norm_num at c2_3
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 16 := ⟨y3 - 16, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 17 := ⟨y4 - 17, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 18 := ⟨y5 - 18, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_2_11 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 2) (e2 : y2 =
          11) :
    False := by
  subst e1 e2
  rcases (show y3 = 12 ∨ y3 = 13 ∨ 14 ≤ y3 by omega) with rfl | rfl | hb
  · norm_num at c1_3
  · rcases (show y4 = 14 ∨ 15 ≤ y4 by omega) with rfl | hb
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 15 := ⟨y4 - 15, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 16 := ⟨y5 - 16, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 14 := ⟨y3 - 14, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 15 := ⟨y4 - 15, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 16 := ⟨y5 - 16, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_3_4 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 3) (e2 : y2 =
          4) :
    False := by
  subst e1 e2
  rcases (show y3 = 5 ∨ y3 = 6 ∨ y3 = 7 ∨ y3 = 8 ∨ y3 = 9 ∨ y3 = 10 ∨ y3 = 11 ∨ y3 = 12 ∨ y3 = 13 ∨
      y3 = 14 ∨ y3 = 15 ∨ 16 ≤ y3 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      | rfl | rfl | hb
  · linarith [Nat.zero_le (y4 * y5)]
  · norm_num at c1_3
  · rcases (show y4 = 8 ∨ y4 = 9 ∨ y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 =
      16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ y4 = 22 ∨ y4 = 23 ∨ y4 = 24 ∨ y4 = 25 ∨
      y4 = 26 ∨ y4 = 27 ∨ y4 = 28 ∨ y4 = 29 ∨ y4 = 30 ∨ y4 = 31 ∨ y4 = 32 ∨ y4 = 33 ∨ y4 = 34 ∨ y4 =
      35 ∨ y4 = 36 ∨ y4 = 37 ∨ y4 = 38 ∨ y4 = 39 ∨ y4 = 40 ∨ 41 ≤ y4 by omega) with rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · obtain rfl : y5 = 160 := by omega
      norm_num at c2_5
    · norm_num at c1_4
    · obtain rfl : y5 = 104 := by omega
      norm_num at c2_5
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · norm_num at c3_4
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 41 := ⟨y4 - 41, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 42 := ⟨y5 - 42, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c2_3
  · norm_num at c1_3
  · norm_num at c2_3
  · rcases (show y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4
      = 20 ∨ 21 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 21 := ⟨y4 - 21, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 22 := ⟨y5 - 22, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 = 17 ∨ 18 ≤ y4 by omega) with rfl | rfl | rfl |
      rfl | hb
    · norm_num at c2_4
    · norm_num at c1_4
    · norm_num at c2_4
    · omega
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 18 := ⟨y4 - 18, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 19 := ⟨y5 - 19, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c2_3
  · norm_num at c1_3
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 16 := ⟨y3 - 16, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 17 := ⟨y4 - 17, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 18 := ⟨y5 - 18, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_3_5 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 3) (e2 : y2 =
          5) :
    False := by
  subst e1 e2
  rcases (show y3 = 6 ∨ y3 = 7 ∨ y3 = 8 ∨ y3 = 9 ∨ y3 = 10 ∨ y3 = 11 ∨ y3 = 12 ∨ 13 ≤ y3 by omega)
      with rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
  · norm_num at c1_3
  · rcases (show y4 = 8 ∨ y4 = 9 ∨ y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 =
      16 ∨ y4 = 17 ∨ y4 = 18 ∨ y4 = 19 ∨ y4 = 20 ∨ y4 = 21 ∨ 22 ≤ y4 by omega) with rfl | rfl | rfl
      | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | hb
    · omega
    · norm_num at c1_4
    · norm_num at c2_4
    · obtain rfl : y5 = 384 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · obtain rfl : y5 = 64 := by omega
      exact hne (by norm_num)
    · norm_num at c3_4
    · norm_num at c1_4
    · obtain rfl : y5 = 34 := by omega
      norm_num at c4_5
    · omega
    · norm_num at c1_4
    · omega
    · norm_num at c2_4
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 22 := ⟨y4 - 22, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 23 := ⟨y5 - 23, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · rcases (show y4 = 9 ∨ y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ y4 = 13 ∨ y4 = 14 ∨ y4 = 15 ∨ y4 = 16 ∨ y4 =
      17 ∨ y4 = 18 ∨ 19 ≤ y4 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      rfl | hb
    · norm_num at c1_4
    · norm_num at c2_4
    · obtain rfl : y5 = 54 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c3_4
    · norm_num at c1_4
    · norm_num at c3_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 19 := ⟨y4 - 19, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 20 := ⟨y5 - 20, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · norm_num at c2_3
  · rcases (show y4 = 12 ∨ y4 = 13 ∨ 14 ≤ y4 by omega) with rfl | rfl | hb
    · norm_num at c1_4
    · omega
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 14 := ⟨y4 - 14, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 15 := ⟨y5 - 15, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 13 := ⟨y3 - 13, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 14 := ⟨y4 - 14, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 15 := ⟨y5 - 15, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_3_7 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 3) (e2 : y2 =
          7) :
    False := by
  subst e1 e2
  rcases (show y3 = 8 ∨ y3 = 9 ∨ 10 ≤ y3 by omega) with rfl | rfl | hb
  · rcases (show y4 = 9 ∨ y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ 13 ≤ y4 by omega) with rfl | rfl | rfl | rfl
      | hb
    · norm_num at c1_4
    · norm_num at c3_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 13 := ⟨y4 - 13, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 14 := ⟨y5 - 14, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 10 := ⟨y3 - 10, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 11 := ⟨y4 - 11, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 12 := ⟨y5 - 12, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_3_8 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 3) (e2 : y2 =
          8) :
    False := by
  subst e1 e2
  rcases (show y3 = 9 ∨ 10 ≤ y3 by omega) with rfl | hb
  · norm_num at c1_3
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 10 := ⟨y3 - 10, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 11 := ⟨y4 - 11, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 12 := ⟨y5 - 12, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_4_5 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 4) (e2 : y2 =
          5) :
    False := by
  subst e1 e2
  rcases (show y3 = 6 ∨ y3 = 7 ∨ y3 = 8 ∨ y3 = 9 ∨ 10 ≤ y3 by omega) with rfl | rfl | rfl | rfl | hb
  · norm_num at c1_3
  · rcases (show y4 = 8 ∨ y4 = 9 ∨ y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ 13 ≤ y4 by omega) with rfl | rfl |
      rfl | rfl | rfl | hb
    · norm_num at c1_4
    · obtain rfl : y5 = 20 := by omega
      norm_num at c1_5
    · norm_num at c1_4
    · omega
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 13 := ⟨y4 - 13, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 14 := ⟨y5 - 14, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · norm_num at c1_3
  · rcases (show y4 = 10 ∨ 11 ≤ y4 by omega) with rfl | hb
    · norm_num at c1_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 11 := ⟨y4 - 11, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 12 := ⟨y5 - 12, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 10 := ⟨y3 - 10, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 11 := ⟨y4 - 11, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 12 := ⟨y5 - 12, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5_5_6 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) (hne : ¬y1 * y2 * y3 * y4 * y5 = 87360) (e1 : y1 = 5) (e2 : y2 =
          6) :
    False := by
  subst e1 e2
  rcases (show y3 = 7 ∨ 8 ≤ y3 by omega) with rfl | hb
  · rcases (show y4 = 8 ∨ 9 ≤ y4 by omega) with rfl | hb
    · norm_num at c2_4
    · obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 9 := ⟨y4 - 9, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 10 := ⟨y5 - 10, by omega⟩
      linarith [Nat.zero_le (z4 * z5)]
  · obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 8 := ⟨y3 - 8, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 9 := ⟨y4 - 9, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 10 := ⟨y5 - 10, by omega⟩
    linarith [Nat.zero_le (z3 * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z3 *
        z4 * z5)]

lemma arith_sorted_5 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) :
    y1 * y2 * y3 * y4 * y5 = 87360 := by
  by_contra hne
  rcases (show y1 = 2 ∨ y1 = 3 ∨ y1 = 4 ∨ y1 = 5 ∨ 6 ≤ y1 by omega) with rfl | rfl | rfl | rfl | hb
  · rcases (show y2 = 3 ∨ y2 = 4 ∨ y2 = 5 ∨ y2 = 6 ∨ y2 = 7 ∨ y2 = 8 ∨ y2 = 9 ∨ y2 = 10 ∨ y2 = 11 ∨
      y2 = 12 ∨ 13 ≤ y2 by omega) with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
      hb
    · exact arith_sorted_5_2_3 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · exact arith_sorted_5_2_5 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · exact arith_sorted_5_2_7 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · exact arith_sorted_5_2_9 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · exact arith_sorted_5_2_11 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · obtain ⟨z2, rfl⟩ : ∃ z, y2 = z + 13 := ⟨y2 - 13, by omega⟩
      obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 14 := ⟨y3 - 14, by omega⟩
      obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 15 := ⟨y4 - 15, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 16 := ⟨y5 - 16, by omega⟩
      linarith [Nat.zero_le (z2 * z3), Nat.zero_le (z2 * z4), Nat.zero_le (z2 * z5), Nat.zero_le (z3
          * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z2 * z3 * z4),
          Nat.zero_le (z2 * z3 * z5), Nat.zero_le (z2 * z4 * z5), Nat.zero_le (z3 * z4 * z5),
          Nat.zero_le (z2 * z3 * z4 * z5)]
  · rcases (show y2 = 4 ∨ y2 = 5 ∨ y2 = 6 ∨ y2 = 7 ∨ y2 = 8 ∨ 9 ≤ y2 by omega) with rfl | rfl | rfl
      | rfl | rfl | hb
    · exact arith_sorted_5_3_4 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · exact arith_sorted_5_3_5 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · exact arith_sorted_5_3_7 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · exact arith_sorted_5_3_8 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · obtain ⟨z2, rfl⟩ : ∃ z, y2 = z + 9 := ⟨y2 - 9, by omega⟩
      obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 10 := ⟨y3 - 10, by omega⟩
      obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 11 := ⟨y4 - 11, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 12 := ⟨y5 - 12, by omega⟩
      linarith [Nat.zero_le (z2 * z3), Nat.zero_le (z2 * z4), Nat.zero_le (z2 * z5), Nat.zero_le (z3
          * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z2 * z3 * z4),
          Nat.zero_le (z2 * z3 * z5), Nat.zero_le (z2 * z4 * z5), Nat.zero_le (z3 * z4 * z5),
          Nat.zero_le (z2 * z3 * z4 * z5)]
  · rcases (show y2 = 5 ∨ y2 = 6 ∨ 7 ≤ y2 by omega) with rfl | rfl | hb
    · exact arith_sorted_5_4_5 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · norm_num at c1_2
    · obtain ⟨z2, rfl⟩ : ∃ z, y2 = z + 7 := ⟨y2 - 7, by omega⟩
      obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 8 := ⟨y3 - 8, by omega⟩
      obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 9 := ⟨y4 - 9, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 10 := ⟨y5 - 10, by omega⟩
      linarith [Nat.zero_le (z2 * z3), Nat.zero_le (z2 * z4), Nat.zero_le (z2 * z5), Nat.zero_le (z3
          * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z2 * z3 * z4),
          Nat.zero_le (z2 * z3 * z5), Nat.zero_le (z2 * z4 * z5), Nat.zero_le (z3 * z4 * z5),
          Nat.zero_le (z2 * z3 * z4 * z5)]
  · rcases (show y2 = 6 ∨ 7 ≤ y2 by omega) with rfl | hb
    · exact arith_sorted_5_5_6 h1 hlt1 hlt2 hlt3 hlt4 c1_2 c1_3 c1_4 c1_5 c2_3 c2_4 c2_5 c3_4 c3_5
        c4_5 h hne rfl rfl
    · obtain ⟨z2, rfl⟩ : ∃ z, y2 = z + 7 := ⟨y2 - 7, by omega⟩
      obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 8 := ⟨y3 - 8, by omega⟩
      obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 9 := ⟨y4 - 9, by omega⟩
      obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 10 := ⟨y5 - 10, by omega⟩
      linarith [Nat.zero_le (z2 * z3), Nat.zero_le (z2 * z4), Nat.zero_le (z2 * z5), Nat.zero_le (z3
          * z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z2 * z3 * z4),
          Nat.zero_le (z2 * z3 * z5), Nat.zero_le (z2 * z4 * z5), Nat.zero_le (z3 * z4 * z5),
          Nat.zero_le (z2 * z3 * z4 * z5)]
  · obtain ⟨z1, rfl⟩ : ∃ z, y1 = z + 6 := ⟨y1 - 6, by omega⟩
    obtain ⟨z2, rfl⟩ : ∃ z, y2 = z + 7 := ⟨y2 - 7, by omega⟩
    obtain ⟨z3, rfl⟩ : ∃ z, y3 = z + 8 := ⟨y3 - 8, by omega⟩
    obtain ⟨z4, rfl⟩ : ∃ z, y4 = z + 9 := ⟨y4 - 9, by omega⟩
    obtain ⟨z5, rfl⟩ : ∃ z, y5 = z + 10 := ⟨y5 - 10, by omega⟩
    linarith [Nat.zero_le (z1 * z2), Nat.zero_le (z1 * z3), Nat.zero_le (z1 * z4), Nat.zero_le (z1 *
        z5), Nat.zero_le (z2 * z3), Nat.zero_le (z2 * z4), Nat.zero_le (z2 * z5), Nat.zero_le (z3 *
        z4), Nat.zero_le (z3 * z5), Nat.zero_le (z4 * z5), Nat.zero_le (z1 * z2 * z3), Nat.zero_le
        (z1 * z2 * z4), Nat.zero_le (z1 * z2 * z5), Nat.zero_le (z1 * z3 * z4), Nat.zero_le (z1 * z3
        * z5), Nat.zero_le (z1 * z4 * z5), Nat.zero_le (z2 * z3 * z4), Nat.zero_le (z2 * z3 * z5),
        Nat.zero_le (z2 * z4 * z5), Nat.zero_le (z3 * z4 * z5), Nat.zero_le (z1 * z2 * z3 * z4),
        Nat.zero_le (z1 * z2 * z3 * z5), Nat.zero_le (z1 * z2 * z4 * z5), Nat.zero_le (z1 * z3 * z4
        * z5), Nat.zero_le (z2 * z3 * z4 * z5), Nat.zero_le (z1 * z2 * z3 * z4 * z5)]

end Generated
/-- The only unitary perfect number with exactly four odd prime factors is `87360`. -/
theorem eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five {n : ℕ}
    (h : IsUnitaryPerfect n) (hcard : n.primeFactors.card = 5) : n = 87360 := by
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  obtain ⟨l, hsort, hlen, hgt, hcop, hprod, hsig⟩ := exists_sorted_factors hpos.ne'
  rw [hcard] at hlen
  rcases l with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨y6, l⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  simp only [List.Sorted, List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hsort hcop
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hgt
  simp only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil, mul_one] at hprod hsig
  obtain ⟨⟨hlt1, -, -, -⟩, ⟨hlt2, -, -⟩, ⟨hlt3, -⟩, hlt4⟩ := hsort
  obtain ⟨⟨c12, c13, c14, c15⟩, ⟨c23, c24, c25⟩, ⟨c34, c35⟩, c45⟩ := hcop
  have heq : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5 := by
    have := hsig.trans (hs.trans (congrArg (2 * ·) hprod.symm))
    convert this using 1 <;> ring
  rw [← hprod]
  have := arith_sorted_5 hgt.1 hlt1 hlt2 hlt3 hlt4.1 c12 c13 c14 c15 c23 c24 c25 c34 c35
    c45.1 heq
  rw [← this]; ring

/-- Classification of unitary perfect numbers with at most five prime factors (i.e. at most four
odd prime factors): they are exactly `6`, `60`, `90` and `87360`. -/
theorem isUnitaryPerfect_of_card_primeFactors_le_five_iff {n : ℕ}
    (hcard : n.primeFactors.card ≤ 5) :
    IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 := by
  constructor
  · intro h
    rcases (show n.primeFactors.card ≤ 4 ∨ n.primeFactors.card = 5 by omega) with h4 | h5
    · rcases (isUnitaryPerfect_of_card_primeFactors_le_four_iff h4).1 h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five h h5)))
  · rintro (rfl | rfl | rfl | rfl)
    exacts [isUnitaryPerfect_6, isUnitaryPerfect_60, isUnitaryPerfect_90, isUnitaryPerfect_87360]

end ErdosResearch.Erdos1052
