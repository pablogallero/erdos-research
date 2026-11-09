import Mathlib

/-!
# Erdős Problem 470: certificates for the last prime factor

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 11).

In the search for odd weird numbers with `ω = K`, the last (largest) prime `q` of `n = M q` ranges
over a huge interval for a fixed prefix `M`. `scripts/odd_weird_family.py` decides all those `q`
at once with the criteria below. Here are the general facts behind them (classical and elementary;
they are building blocks for a Lean version of that search, not a new result):

* `pseudoperfect_of_compl`: `n > 0` is pseudoperfect as soon as some set of proper divisors of `n`
  sums to `σ(n) - 2n` (its complement then sums to `n`).
* `pseudoperfect_mul_prime`: if `q` is prime, `q ∤ M`, `A` is a set of proper divisors of `M` with
  sum `M - k`, and `B` is a set of divisors of `M` with sum `k q`, then `M q` is pseudoperfect.
  This is the subset `B ∪ q·A`.
* `pseudoperfect_mul_prime_of_sum_divisors`: if `q` is prime, `q ∤ M`, `M > 0`, and some set of
  divisors of `M` sums to `σ(Mq) - 2Mq`, then `Mq` is pseudoperfect. This is the test the script
  applies first, with `σ(Mq) - 2Mq = σ(M) - (2M - σ(M)) q`.
-/

namespace Erdos470Research

open ArithmeticFunction Finset

/-- Complement certificate: a set of proper divisors with sum `∑ properDivisors n - n`. -/
theorem pseudoperfect_of_compl {n : ℕ} (hn : 0 < n) {X : Finset ℕ} (hX : X ⊆ n.properDivisors)
    (hsum : ∑ i ∈ X, i + n = ∑ i ∈ n.properDivisors, i) : n.Pseudoperfect := by
  refine ⟨hn, n.properDivisors \ X, sdiff_subset, ?_⟩
  have h : ∑ i ∈ n.properDivisors \ X, i + ∑ i ∈ X, i = ∑ i ∈ n.properDivisors, i :=
    sum_sdiff hX
  omega

/-- The last-prime criterion (sufficient direction): the subset `B ∪ q·A`. -/
theorem pseudoperfect_mul_prime {M q k : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) (hM : 0 < M)
    {A B : Finset ℕ} (hA : A ⊆ M.properDivisors) (hB : B ⊆ M.divisors) (hk : k ≤ M)
    (hAsum : ∑ i ∈ A, i = M - k) (hBsum : ∑ i ∈ B, i = k * q) : (M * q).Pseudoperfect := by
  have hq1 : 1 < q := hq.one_lt
  have hMq : M < M * q := lt_mul_of_one_lt_right hM hq1
  refine ⟨by positivity, B ∪ A.image (· * q), ?_, ?_⟩
  · intro x hx
    rcases mem_union.mp hx with hx | hx
    · obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (hB hx)
      exact Nat.mem_properDivisors.mpr
        ⟨Dvd.dvd.mul_right hdvd q, lt_of_le_of_lt (Nat.le_of_dvd hM hdvd) hMq⟩
    · obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
      obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp (hA hi)
      exact Nat.mem_properDivisors.mpr
        ⟨Nat.mul_dvd_mul_right hdvd q, Nat.mul_lt_mul_of_pos_right hlt (by omega)⟩
  · have hdisj : Disjoint B (A.image (· * q)) := by
      rw [disjoint_left]
      intro x hxB hxA
      obtain ⟨i, -, rfl⟩ := mem_image.mp hxA
      obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (hB hxB)
      exact hqM (Dvd.dvd.trans (Dvd.intro_left i rfl) hdvd)
    rw [sum_union hdisj, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_right (by omega) h),
      ← sum_mul, hAsum, hBsum, ← add_mul, Nat.add_sub_cancel' hk]

/-- `σ(Mq) = σ(M) (q + 1)` for a prime `q ∤ M`, written with proper divisors:
`∑ properDivisors (Mq) = (∑ properDivisors M + M) (q + 1) - Mq`. -/
theorem sum_properDivisors_mul_prime {M q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M) :
    ∑ i ∈ (M * q).properDivisors, i + M * q = (∑ i ∈ M.properDivisors, i + M) * (q + 1) := by
  have hcop : Nat.Coprime M q := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hq).mpr hqM))
  have h1 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := M * q)
  have h2 := Nat.sum_divisors_eq_sum_properDivisors_add_self (n := M)
  have hs : σ 1 (M * q) = σ 1 M * σ 1 q := isMultiplicative_sigma.map_mul_of_coprime hcop
  rw [sigma_one_apply, sigma_one_apply, sigma_one_apply, hq.sum_divisors] at hs
  rw [← h1, ← h2, hs]

/-- The test applied first by `scripts/odd_weird_family.py`: some divisors of `M` sum to
`σ(Mq) - 2Mq`. -/
theorem pseudoperfect_mul_prime_of_sum_divisors {M q : ℕ} (hq : q.Prime) (hqM : ¬ q ∣ M)
    (hM : 0 < M) {X : Finset ℕ} (hX : X ⊆ M.divisors)
    (hsum : ∑ i ∈ X, i + 2 * (M * q) = (∑ i ∈ M.properDivisors, i + M) * (q + 1)) :
    (M * q).Pseudoperfect := by
  have hq1 : 1 < q := hq.one_lt
  have hMq : M < M * q := lt_mul_of_one_lt_right hM hq1
  refine pseudoperfect_of_compl (X := X) (by positivity) ?_ ?_
  · intro x hx
    obtain ⟨hdvd, -⟩ := Nat.mem_divisors.mp (hX hx)
    exact Nat.mem_properDivisors.mpr
      ⟨Dvd.dvd.mul_right hdvd q, lt_of_le_of_lt (Nat.le_of_dvd hM hdvd) hMq⟩
  · have := sum_properDivisors_mul_prime hq hqM
    omega

/-- Sanity check: `945 = 135 · 7` is pseudoperfect via the last-prime test. Here `σ(945) - 2·945
= 30 = 27 + 3`, a sum of divisors of `135`. -/
example : (135 * 7).Pseudoperfect := by
  refine pseudoperfect_mul_prime_of_sum_divisors (X := {27, 3}) (by norm_num) (by norm_num)
    (by norm_num) ?_ ?_
  · intro x hx
    simp only [mem_insert, mem_singleton] at hx
    rcases hx with rfl | rfl <;> decide
  · decide

end Erdos470Research
