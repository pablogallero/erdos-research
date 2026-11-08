import Mathlib
import ErdosResearch.OddWeird

/-!
# Erdős Problem 470: no odd weird number with three distinct prime factors

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md`.

What is proved here (classical; Liddy–Riedl 2018 prove the stronger `ω ≥ 6`):
* `Nat.Pseudoperfect.of_dvd`: a positive multiple of a pseudoperfect number is pseudoperfect.
* The eight odd primitive abundant numbers with `ω = 3`
  (`945, 1575, 2205, 7425, 78975, 131625, 342225, 570375`) are pseudoperfect, with explicit subsets.
* `pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_three`: an odd abundant number with
  exactly three distinct prime factors is pseudoperfect.
* `not_weird_of_odd_of_card_primeFactors_le_three`: an odd number with `ω ≤ 3` is not weird.

Method: write `n = p^a q^b r^c` with `p < q < r`. From `σ(n)/n < ∏ p/(p-1)` and abundance we get
`p = 3`, `q = 5`, `r ∈ {7, 11, 13}`. Then the exponents `(a, b, c)` either dominate the exponents
of one of the eight primitive abundant numbers (so `n` is a multiple of it), or they lie in a
"box" where `σ(n) ≤ 2n` (fixed exponents use the exact value of `σ(p^e)`, free exponents the bound
`σ(p^e)/p^e < p/(p-1)`).
-/

namespace Erdos470Research

open ArithmeticFunction Finset

/-- A positive multiple of a pseudoperfect number is pseudoperfect: scale the subset. -/
theorem _root_.Nat.Pseudoperfect.of_dvd {m n : ℕ} (hm : m.Pseudoperfect) (h : m ∣ n)
    (hn : 0 < n) : n.Pseudoperfect := by
  obtain ⟨-, s, hs, hsum⟩ := hm
  obtain ⟨k, rfl⟩ := h
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  refine ⟨hn, s.image (· * k), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hx
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp (hs hi)
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right hdvd k,
      Nat.mul_lt_mul_of_pos_right hlt hk⟩
  · rw [Finset.sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_right hk hxy),
      ← Finset.sum_mul, hsum]

/-! ### The eight odd primitive abundant numbers with three prime factors -/

lemma pseudoperfect_945 : Nat.Pseudoperfect (3 ^ 3 * 5 ^ 1 * 7 ^ 1) := by
  refine ⟨by norm_num, {315, 189, 135, 105, 63, 45, 35, 27, 21, 9, 1}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_1575 : Nat.Pseudoperfect (3 ^ 2 * 5 ^ 2 * 7 ^ 1) := by
  refine ⟨by norm_num, {525, 315, 225, 175, 105, 75, 63, 45, 35, 9, 3}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_2205 : Nat.Pseudoperfect (3 ^ 2 * 5 ^ 1 * 7 ^ 2) := by
  refine ⟨by norm_num, {735, 441, 315, 245, 147, 105, 63, 49, 45, 35, 21, 3, 1}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_7425 : Nat.Pseudoperfect (3 ^ 3 * 5 ^ 2 * 11 ^ 1) := by
  refine ⟨by norm_num, {2475, 1485, 825, 675, 495, 297, 275, 225, 165, 135, 99, 75, 55, 45, 33,
    27, 25, 11, 3}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_78975 : Nat.Pseudoperfect (3 ^ 5 * 5 ^ 2 * 13 ^ 1) := by
  refine ⟨by norm_num, {26325, 15795, 8775, 6075, 5265, 3159, 2925, 2025, 1755, 1215, 1053, 975,
    675, 585, 405, 351, 325, 243, 225, 195, 135, 117, 81, 75, 65, 45, 39, 27, 25, 15, 5}, ?_,
    by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_131625 : Nat.Pseudoperfect (3 ^ 4 * 5 ^ 3 * 13 ^ 1) := by
  refine ⟨by norm_num, {43875, 26325, 14625, 10125, 8775, 5265, 4875, 3375, 2925, 2025, 1755,
    1625, 1125, 1053, 975, 675, 585, 405, 375, 325, 225, 195, 117}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_342225 : Nat.Pseudoperfect (3 ^ 4 * 5 ^ 2 * 13 ^ 2) := by
  refine ⟨by norm_num, {114075, 68445, 38025, 26325, 22815, 13689, 12675, 8775, 7605, 5265, 4563,
    4225, 2925, 2535, 2025, 1755, 1521, 1053, 975, 845, 675, 585, 507, 225, 117}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

lemma pseudoperfect_570375 : Nat.Pseudoperfect (3 ^ 3 * 5 ^ 3 * 13 ^ 2) := by
  refine ⟨by norm_num, {190125, 114075, 63375, 43875, 38025, 22815, 21125, 14625, 12675, 8775,
    7605, 4875, 4563, 4225, 3375, 2925, 2535, 1755, 1625, 1521, 1125, 975, 845, 675, 585, 507,
    375, 351, 325, 117, 1}, ?_, by rfl⟩
  simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff, Nat.mem_properDivisors]
  norm_num

/-! ### Exponent analysis for `n = 3^a 5^b r^c` -/

/-- Combine three ratio bounds `X/U ≤ u₁/u₂`, … into `XYZ ≤ 2UVW`. -/
lemma box {X Y Z U V W u₁ u₂ v₁ v₂ w₁ w₂ : ℕ} (hx : X * u₂ ≤ U * u₁) (hy : Y * v₂ ≤ V * v₁)
    (hz : Z * w₂ ≤ W * w₁) (hc : u₁ * v₁ * w₁ ≤ 2 * (u₂ * v₂ * w₂)) (hpos : 0 < u₂ * v₂ * w₂) :
    X * Y * Z ≤ 2 * (U * V * W) := by
  have h1 := Nat.mul_le_mul (Nat.mul_le_mul hx hy) hz
  have h2 : X * Y * Z * (u₂ * v₂ * w₂) ≤ 2 * (U * V * W) * (u₂ * v₂ * w₂) :=
    calc X * Y * Z * (u₂ * v₂ * w₂) = X * u₂ * (Y * v₂) * (Z * w₂) := by ring
      _ ≤ U * u₁ * (V * v₁) * (W * w₁) := h1
      _ = (U * V * W) * (u₁ * v₁ * w₁) := by ring
      _ ≤ (U * V * W) * (2 * (u₂ * v₂ * w₂)) := Nat.mul_le_mul_left _ hc
      _ = 2 * (U * V * W) * (u₂ * v₂ * w₂) := by ring
  exact Nat.le_of_mul_le_mul_right h2 hpos

/-- Free exponent: `σ(p^e) · (p - 1) ≤ p^e · p`. -/
lemma free {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) * (p - 1) ≤ p ^ e * p := by
  rw [mul_comm]; exact sub_one_mul_sigma_prime_pow_le hp e

/-- Fixed exponent: the trivial bound `σ(p^e) · p^e ≤ p^e · σ(p^e)`. -/
lemma fixed (p e : ℕ) : σ 1 (p ^ e) * p ^ e ≤ p ^ e * σ 1 (p ^ e) := le_of_eq (mul_comm _ _)

lemma sigma_pow_eq {p : ℕ} (hp : p.Prime) (e : ℕ) : σ 1 (p ^ e) = ∑ i ∈ range (e + 1), p ^ i :=
  sigma_one_apply_prime_pow hp

lemma s3 (e : ℕ) : σ 1 (3 ^ e) = ∑ i ∈ range (e + 1), 3 ^ i := sigma_pow_eq Nat.prime_three e
lemma s5 (e : ℕ) : σ 1 (5 ^ e) = ∑ i ∈ range (e + 1), 5 ^ i := sigma_pow_eq Nat.prime_five e
lemma s7 (e : ℕ) : σ 1 (7 ^ e) = ∑ i ∈ range (e + 1), 7 ^ i := sigma_pow_eq (by norm_num) e
lemma s11 (e : ℕ) : σ 1 (11 ^ e) = ∑ i ∈ range (e + 1), 11 ^ i := sigma_pow_eq (by norm_num) e
lemma s13 (e : ℕ) : σ 1 (13 ^ e) = ∑ i ∈ range (e + 1), 13 ^ i := sigma_pow_eq (by norm_num) e

lemma dvd3 {a b c a₀ b₀ c₀ r : ℕ} (ha : a₀ ≤ a) (hb : b₀ ≤ b) (hc : c₀ ≤ c) :
    3 ^ a₀ * 5 ^ b₀ * r ^ c₀ ∣ 3 ^ a * 5 ^ b * r ^ c :=
  Nat.mul_dvd_mul (Nat.mul_dvd_mul (pow_dvd_pow 3 ha) (pow_dvd_pow 5 hb)) (pow_dvd_pow r hc)

lemma pos3 (a b c r : ℕ) (hr : 0 < r) : 0 < 3 ^ a * 5 ^ b * r ^ c := by positivity

lemma case_seven {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : 2 * (3 ^ a * 5 ^ b * 7 ^ c) < σ 1 (3 ^ a) * σ 1 (5 ^ b) * σ 1 (7 ^ c)) :
    (3 ^ a * 5 ^ b * 7 ^ c).Pseudoperfect := by
  have hpos := pos3 a b c 7 (by norm_num)
  rcases Nat.lt_or_ge a 2 with ha' | ha'
  · obtain rfl : a = 1 := by omega
    have := box (fixed 3 1) (free Nat.prime_five b) (free (by norm_num : Nat.Prime 7) c)
      (by simp only [s3, Finset.sum_range_succ]; norm_num) (by norm_num)
    omega
  rcases Nat.lt_or_ge 1 b with hb' | hb'
  · exact pseudoperfect_1575.of_dvd (dvd3 ha' hb' hc) hpos
  obtain rfl : b = 1 := by omega
  rcases Nat.lt_or_ge 1 c with hc' | hc'
  · exact pseudoperfect_2205.of_dvd (dvd3 ha' hb hc') hpos
  obtain rfl : c = 1 := by omega
  rcases Nat.lt_or_ge 2 a with ha'' | ha''
  · exact pseudoperfect_945.of_dvd (dvd3 ha'' hb hc) hpos
  obtain rfl : a = 2 := by omega
  simp only [s3, s5, s7, Finset.sum_range_succ] at h
  norm_num at h

lemma case_eleven {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : 2 * (3 ^ a * 5 ^ b * 11 ^ c) < σ 1 (3 ^ a) * σ 1 (5 ^ b) * σ 1 (11 ^ c)) :
    (3 ^ a * 5 ^ b * 11 ^ c).Pseudoperfect := by
  have hpos := pos3 a b c 11 (by norm_num)
  have p11 : Nat.Prime 11 := by norm_num
  rcases Nat.lt_or_ge a 3 with ha' | ha'
  · obtain rfl | rfl : a = 1 ∨ a = 2 := by omega
    · have := box (fixed 3 1) (free Nat.prime_five b) (free p11 c)
        (by simp only [s3, Finset.sum_range_succ]; norm_num) (by norm_num)
      omega
    · have := box (fixed 3 2) (free Nat.prime_five b) (free p11 c)
        (by simp only [s3, Finset.sum_range_succ]; norm_num) (by norm_num)
      omega
  rcases Nat.lt_or_ge 1 b with hb' | hb'
  · exact pseudoperfect_7425.of_dvd (dvd3 ha' hb' hc) hpos
  obtain rfl : b = 1 := by omega
  have := box (free Nat.prime_three a) (fixed 5 1) (free p11 c)
    (by simp only [s5, Finset.sum_range_succ]; norm_num) (by norm_num)
  omega

lemma case_thirteen {a b c : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b) (hc : 1 ≤ c)
    (h : 2 * (3 ^ a * 5 ^ b * 13 ^ c) < σ 1 (3 ^ a) * σ 1 (5 ^ b) * σ 1 (13 ^ c)) :
    (3 ^ a * 5 ^ b * 13 ^ c).Pseudoperfect := by
  have hpos := pos3 a b c 13 (by norm_num)
  have p13 : Nat.Prime 13 := by norm_num
  rcases Nat.lt_or_ge a 3 with ha' | ha'
  · obtain rfl | rfl : a = 1 ∨ a = 2 := by omega
    · have := box (fixed 3 1) (free Nat.prime_five b) (free p13 c)
        (by simp only [s3, Finset.sum_range_succ]; norm_num) (by norm_num)
      omega
    · have := box (fixed 3 2) (free Nat.prime_five b) (free p13 c)
        (by simp only [s3, Finset.sum_range_succ]; norm_num) (by norm_num)
      omega
  rcases Nat.lt_or_ge b 2 with hb' | hb'
  · obtain rfl : b = 1 := by omega
    have := box (free Nat.prime_three a) (fixed 5 1) (free p13 c)
      (by simp only [s5, Finset.sum_range_succ]; norm_num) (by norm_num)
    omega
  rcases Nat.lt_or_ge a 4 with ha'' | ha''
  · -- `a = 3`
    obtain rfl : a = 3 := by omega
    rcases Nat.lt_or_ge b 3 with hb'' | hb''
    · obtain rfl : b = 2 := by omega
      have := box (fixed 3 3) (fixed 5 2) (free p13 c)
        (by simp only [s3, s5, Finset.sum_range_succ]; norm_num) (by norm_num)
      omega
    rcases Nat.lt_or_ge 1 c with hc' | hc'
    · exact pseudoperfect_570375.of_dvd (dvd3 le_rfl hb'' hc') hpos
    obtain rfl : c = 1 := by omega
    have := box (fixed 3 3) (free Nat.prime_five b) (fixed 13 1)
      (by simp only [s3, s13, Finset.sum_range_succ]; norm_num) (by norm_num)
    omega
  · -- `a ≥ 4`
    rcases Nat.lt_or_ge 1 c with hc' | hc'
    · exact pseudoperfect_342225.of_dvd (dvd3 ha'' hb' hc') hpos
    obtain rfl : c = 1 := by omega
    rcases Nat.lt_or_ge 2 b with hb'' | hb''
    · exact pseudoperfect_131625.of_dvd (dvd3 ha'' hb'' hc) hpos
    obtain rfl : b = 2 := by omega
    rcases Nat.lt_or_ge 4 a with ha''' | ha'''
    · exact pseudoperfect_78975.of_dvd (dvd3 ha''' hb' hc) hpos
    obtain rfl : a = 4 := by omega
    simp only [s3, s5, s13, Finset.sum_range_succ] at h
    norm_num at h

/-! ### The primes must be `3, 5` and `r ∈ {7, 11, 13}` -/

/-- `∏ (x+1) ≤ 2 ∏ x` when `4 ≤ x`, `6 ≤ y`, `8 ≤ z`. -/
lemma prime_bound₁ {x y z : ℕ} (hx : 4 ≤ x) (hy : 6 ≤ y) (hz : 8 ≤ z) :
    (x + 1) * (y + 1) * (z + 1) ≤ 2 * (x * y * z) := by
  have h1 : 4 * (x + 1) ≤ 5 * x := by omega
  have h2 : 6 * (y + 1) ≤ 7 * y := by omega
  have h3 : 8 * (z + 1) ≤ 9 * z := by omega
  have := Nat.mul_le_mul (Nat.mul_le_mul h1 h2) h3
  have h0 : 0 ≤ x * y * z := Nat.zero_le _
  nlinarith

/-- `3 · (y+1) · (z+1) ≤ 2 · (2 y z)` when `6 ≤ y`, `8 ≤ z`. -/
lemma prime_bound₂ {y z : ℕ} (hy : 6 ≤ y) (hz : 8 ≤ z) :
    (2 + 1) * (y + 1) * (z + 1) ≤ 2 * (2 * y * z) := by
  have h2 : 6 * (y + 1) ≤ 7 * y := by omega
  have h3 : 8 * (z + 1) ≤ 9 * z := by omega
  have := Nat.mul_le_mul h2 h3
  nlinarith

/-- Sort a three-element finset. -/
lemma exists_sorted_three {s : Finset ℕ} (h : s.card = 3) :
    ∃ p q r, p < q ∧ q < r ∧ s = {p, q, r} := by
  obtain ⟨x, y, z, hxy, hxz, hyz, rfl⟩ := Finset.card_eq_three.mp h
  rcases lt_or_gt_of_ne hxy with h1 | h1 <;> rcases lt_or_gt_of_ne hxz with h2 | h2 <;>
    rcases lt_or_gt_of_ne hyz with h3 | h3
  · exact ⟨x, y, z, h1, h3, rfl⟩
  · exact ⟨x, z, y, h2, h3, by ext; simp; tauto⟩
  · omega
  · exact ⟨z, x, y, h2, h1, by ext; simp; tauto⟩
  · exact ⟨y, x, z, h1, h2, by ext; simp; tauto⟩
  · omega
  · exact ⟨y, z, x, h3, h2, by ext; simp; tauto⟩
  · exact ⟨z, y, x, h3, h1, by ext; simp; tauto⟩

lemma abundant_iff_sigma {n : ℕ} : n.Abundant ↔ 2 * n < σ 1 n := by
  rw [Nat.Abundant, sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-- An odd abundant number with exactly three distinct prime factors is pseudoperfect. -/
theorem pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_three {n : ℕ} (hn : Odd n)
    (hab : n.Abundant) (h : n.primeFactors.card = 3) : n.Pseudoperfect := by
  have hn0 : n ≠ 0 := by rintro rfl; simp at hn
  obtain ⟨p, q, r, hpq, hqr, hs⟩ := exists_sorted_three h
  have mem : ∀ x ∈ ({p, q, r} : Finset ℕ), x.Prime ∧ x % 2 = 1 ∧ 1 ≤ n.factorization x := by
    intro x hx
    rw [← hs] at hx
    have hxp := Nat.prime_of_mem_primeFactors hx
    have hxd := Nat.dvd_of_mem_primeFactors hx
    refine ⟨hxp, ?_, hxp.factorization_pos_of_dvd hn0 hxd⟩
    rcases hxp.eq_two_or_odd with rfl | h2
    · exact absurd (even_iff_two_dvd.mpr hxd) (Nat.not_even_iff_odd.mpr hn)
    · exact h2
  obtain ⟨hp, hp2, ha⟩ := mem p (by simp)
  obtain ⟨hq, hq2, hb⟩ := mem q (by simp)
  obtain ⟨hr, hr2, hc⟩ := mem r (by simp)
  set a := n.factorization p
  set b := n.factorization q
  set c := n.factorization r
  have hn_eq : n = p ^ a * q ^ b * r ^ c := by
    conv_lhs => rw [← Nat.factorization_prod_pow_eq_self hn0]
    rw [Finsupp.prod, Nat.support_factorization, hs,
      Finset.prod_insert (by simp; omega), Finset.prod_insert (by simp; omega),
      Finset.prod_singleton, mul_assoc]
  have cop : ∀ {x y : ℕ}, x.Prime → y.Prime → x ≠ y → ∀ i j, Nat.Coprime (x ^ i) (y ^ j) :=
    fun hx hy hxy i j => ((Nat.coprime_primes hx hy).mpr hxy).pow i j
  have hσ : σ 1 n = σ 1 (p ^ a) * σ 1 (q ^ b) * σ 1 (r ^ c) := by
    rw [hn_eq, isMultiplicative_sigma.map_mul_of_coprime
        (Nat.Coprime.mul_left (cop hp hr (by omega) a c) (cop hq hr (by omega) b c)),
      isMultiplicative_sigma.map_mul_of_coprime (cop hp hq (by omega) a b)]
  have habσ := abundant_iff_sigma.mp hab
  rw [hσ, hn_eq] at habσ
  -- the prime bound `2 (p-1)(q-1)(r-1) < p q r`
  have hprime : 2 * ((p - 1) * (q - 1) * (r - 1)) < p * q * r := by
    by_contra hcon
    push_neg at hcon
    have := box (free hp a) (free hq b) (free hr c) hcon
      (Nat.mul_pos (Nat.mul_pos (by have := hp.two_le; omega) (by have := hq.two_le; omega))
        (by have := hr.two_le; omega))
    omega
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  obtain ⟨x, rfl⟩ : ∃ x, p = x + 1 := ⟨p - 1, by omega⟩
  obtain ⟨y, rfl⟩ : ∃ y, q = y + 1 := ⟨q - 1, by omega⟩
  obtain ⟨z, rfl⟩ : ∃ z, r = z + 1 := ⟨r - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hprime
  -- `p = 3`
  obtain rfl : x = 2 := by
    by_contra hx
    have := prime_bound₁ (x := x) (y := y) (z := z) (by omega) (by omega) (by omega)
    omega
  -- `q = 5`
  obtain rfl : y = 4 := by
    by_contra hy
    have := prime_bound₂ (y := y) (z := z) (by omega) (by omega)
    omega
  -- `r ≤ 13`
  have hz : z < 15 := by
    by_contra hz
    omega
  have hz' : z = 6 ∨ z = 10 ∨ z = 12 := by
    interval_cases z <;> first | omega | (exfalso; revert hr; norm_num)
  rw [hn_eq]
  rcases hz' with rfl | rfl | rfl
  · exact case_seven ha hb hc habσ
  · exact case_eleven ha hb hc habσ
  · exact case_thirteen ha hb hc habσ

/-- An odd number with exactly three distinct prime factors is not weird. -/
theorem not_weird_of_odd_of_card_primeFactors_eq_three {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card = 3) : ¬ n.Weird := fun ⟨hab, hps⟩ =>
  hps (pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_three hn hab h)

/-- An odd number with at most three distinct prime factors is not weird. -/
theorem not_weird_of_odd_of_card_primeFactors_le_three {n : ℕ} (hn : Odd n)
    (h : n.primeFactors.card ≤ 3) : ¬ n.Weird := by
  rcases Nat.lt_or_ge n.primeFactors.card 3 with h' | h'
  · exact not_weird_of_odd_of_card_primeFactors_le_two hn (by omega)
  · exact not_weird_of_odd_of_card_primeFactors_eq_three hn (by omega)

end Erdos470Research
