import Mathlib

/-!
# Erdős Problem 470: odd weird numbers (first steps)

Reference: <https://www.erdosproblems.com/470> (prize: $10, reported by Guy, B2).

A number is *weird* if it is abundant but not pseudoperfect (`Nat.Weird` in Mathlib, the same
definition used by `FormalConjectures/ErdosProblems/470.lean`). The open question
`erdos_470.parts.i` asks whether an odd weird number exists. Liddy and Riedl (2018) showed that
an odd weird number has at least 6 distinct prime factors. Fang (2022) showed there is none below
`10^21`.

What is proved here (classical and elementary; see `notes/erdos-470.md`):
* `sigma_mul_prod_sub_one_le`: `σ(n) · ∏_{p ∣ n} (p - 1) ≤ n · ∏_{p ∣ n} p` for every `n`
  (that is, the abundancy index is at most `∏ p/(p-1)`).
* `deficient_of_odd_of_card_primeFactors_le_two`: an odd `n ≠ 0` with at most two distinct prime
  factors is deficient (`σ(n)/n ≤ (3/2)(5/4) = 15/8 < 2`).
* `not_weird_of_odd_of_card_primeFactors_le_two`: so it is not weird.
-/

namespace Erdos470Research

open ArithmeticFunction Finset

/-- `(p - 1) · σ(p^k) ≤ p^k · p`, the prime-power case of the abundancy bound. -/
lemma sub_one_mul_sigma_prime_pow_le {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (p - 1) * σ 1 (p ^ k) ≤ p ^ k * p := by
  rw [sigma_one_apply_prime_pow hp]
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by have := hp.one_lt; omega⟩
  simp only [Nat.add_sub_cancel]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ]
    nlinarith [ih]

/-- The abundancy index of `n` is at most `∏_{p ∣ n} p / (p - 1)`, stated in `ℕ`. -/
theorem sigma_mul_prod_sub_one_le (n : ℕ) :
    σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤ n * ∏ p ∈ n.primeFactors, p := by
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  have hσ : σ 1 n = ∏ p ∈ n.primeFactors, σ 1 (p ^ n.factorization p) := by
    rw [isMultiplicative_sigma.multiplicative_factorization (σ 1) hn, Finsupp.prod,
      Nat.support_factorization]
  have hn' : n = ∏ p ∈ n.primeFactors, p ^ n.factorization p := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn]
    rw [Finsupp.prod, Nat.support_factorization]
  calc σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)
      = ∏ p ∈ n.primeFactors, ((p - 1) * σ 1 (p ^ n.factorization p)) := by
        rw [hσ, ← Finset.prod_mul_distrib]
        exact Finset.prod_congr rfl fun _ _ => mul_comm _ _
    _ ≤ ∏ p ∈ n.primeFactors, (p ^ n.factorization p * p) :=
        Finset.prod_le_prod' fun p hp => sub_one_mul_sigma_prime_pow_le (Nat.prime_of_mem_primeFactors hp) _
    _ = n * ∏ p ∈ n.primeFactors, p := by
        rw [Finset.prod_mul_distrib, ← hn']

/-- For a set of at most two odd primes, `8 · ∏ p ≤ 15 · ∏ (p - 1)`. -/
lemma eight_mul_prod_le {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p ≠ 2) (hcard : s.card ≤ 2) :
    8 * ∏ p ∈ s, p ≤ 15 * ∏ p ∈ s, (p - 1) := by
  have h3 : ∀ p ∈ s, 3 ≤ p := by
    intro p hp
    have h2 : 2 ≤ p := (hs p hp).1.two_le
    have hne : p ≠ 2 := (hs p hp).2
    omega
  rcases Nat.lt_or_ge s.card 2 with h | h
  · rcases Nat.lt_or_ge s.card 1 with h' | h'
    · rw [Nat.lt_one_iff, Finset.card_eq_zero] at h'
      subst h'; simp
    · obtain ⟨p, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
      have := h3 p (by simp)
      simp only [Finset.prod_singleton]
      omega
  · obtain ⟨p, q, hpq, rfl⟩ := Finset.card_eq_two.mp (show s.card = 2 by omega)
    have hp := h3 p (by simp)
    have hq := h3 q (by simp)
    have hpo := (hs p (by simp)).1.eq_one_or_self_of_dvd 2
    have hqo := (hs q (by simp)).1.eq_one_or_self_of_dvd 2
    have hp2 : p % 2 = 1 := by
      rcases Nat.even_or_odd p with ⟨k, hk⟩ | ⟨k, hk⟩
      · have := hpo ⟨k, by omega⟩; omega
      · omega
    have hq2 : q % 2 = 1 := by
      rcases Nat.even_or_odd q with ⟨k, hk⟩ | ⟨k, hk⟩
      · have := hqo ⟨k, by omega⟩; omega
      · omega
    rw [Finset.prod_pair hpq, Finset.prod_pair hpq]
    obtain ⟨a, rfl⟩ : ∃ a, p = a + 3 := ⟨p - 3, by omega⟩
    obtain ⟨b, rfl⟩ : ∃ b, q = b + 3 := ⟨q - 3, by omega⟩
    simp only [show ∀ x, x + 3 - 1 = x + 2 from fun x => rfl]
    -- one of `a, b` is at least 2, because `p ≠ q` are both odd
    rcases Nat.lt_or_ge a 2 with ha | ha
    · have hb : 2 ≤ b := by omega
      nlinarith
    · nlinarith

/-- An odd number with at most two distinct prime factors is deficient. -/
theorem deficient_of_odd_of_card_primeFactors_le_two {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card ≤ 2) : n.Deficient := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  have hs : ∀ p ∈ n.primeFactors, p.Prime ∧ p ≠ 2 := fun p hp => by
    refine ⟨Nat.prime_of_mem_primeFactors hp, ?_⟩
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hn) (even_iff_two_dvd.mpr (Nat.dvd_of_mem_primeFactors hp))
  have h1 := sigma_mul_prod_sub_one_le n
  have h2 := eight_mul_prod_le hs h
  have hpos : 0 < ∏ p ∈ n.primeFactors, (p - 1) :=
    Finset.prod_pos fun p hp => by have := (hs p hp).1.two_le; omega
  -- `8 σ(n) ∏(p-1) ≤ 8 n ∏ p ≤ 15 n ∏(p-1)`, so `8 σ(n) ≤ 15 n < 16 n`.
  have h3 : 8 * σ 1 n ≤ 15 * n := by
    have : 8 * σ 1 n * ∏ p ∈ n.primeFactors, (p - 1) ≤
        15 * n * ∏ p ∈ n.primeFactors, (p - 1) := by
      calc 8 * σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)
          = 8 * (σ 1 n * ∏ p ∈ n.primeFactors, (p - 1)) := by ring
        _ ≤ 8 * (n * ∏ p ∈ n.primeFactors, p) := Nat.mul_le_mul_left _ h1
        _ = n * (8 * ∏ p ∈ n.primeFactors, p) := by ring
        _ ≤ n * (15 * ∏ p ∈ n.primeFactors, (p - 1)) := Nat.mul_le_mul_left _ h2
        _ = 15 * n * ∏ p ∈ n.primeFactors, (p - 1) := by ring
    exact Nat.le_of_mul_le_mul_right this hpos
  have hσ : σ 1 n = ∑ i ∈ n.properDivisors, i + n := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  have : 0 < n := Nat.pos_of_ne_zero hn0
  unfold Nat.Deficient
  omega

/-- An odd number with at most two distinct prime factors is not weird. -/
theorem not_weird_of_odd_of_card_primeFactors_le_two {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card ≤ 2) : ¬ n.Weird := by
  rintro ⟨ha, -⟩
  have hd := deficient_of_odd_of_card_primeFactors_le_two hn h
  unfold Nat.Abundant at ha
  unfold Nat.Deficient at hd
  omega

end Erdos470Research
