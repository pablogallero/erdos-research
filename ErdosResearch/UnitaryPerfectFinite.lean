import ErdosResearch.UnitaryPerfectFourOdd

/-!
# Erdős #1052: finitely many unitary perfect numbers with a fixed number of prime factors

For every `k`, there are only finitely many unitary perfect numbers `n` with `ω(n) = k`
(`finite_isUnitaryPerfect_card_primeFactors_eq`). Consequently Erdős #1052 is equivalent to
the boundedness of `ω` on unitary perfect numbers (`erdos_1052_statement_iff_bddAbove`).

This is classical (the Dickson-type argument; see `notes/erdos-1052.md`); it is new here only as
a formalisation, uniform in `k`, unlike the case-by-case classifications in the other files.

Proof. Write `n = y₁ ⋯ y_k` with `y₁ < ⋯ < y_k` its prime-power factors. Then
`∏ (1 + 1/yᵢ) = σ*(n)/n = 2`. For a sorted list with product `t` and length `m + 1`, the smallest
element `y` satisfies `1 < t ≤ (1 + 1/y)^{m+1} ≤ 1 + (2^{m+1} - 1)/y`, so `y ≤ 2^{m+1}/(t - 1)`;
the rest is a sorted list of length `m` with product `t / (1 + 1/y)`. Induction on `m`
(generalising `t`) shows that the set of such lists is finite.
-/

namespace ErdosResearch.Erdos1052

/-- The factor `1 + 1/y` (as a rational). -/
def ff (y : ℕ) : ℚ := 1 + 1 / (y : ℚ)

/-- Sorted lists of positive integers of length `m` with `∏ (1 + 1/y) = t`. -/
def GoodList (m : ℕ) (t : ℚ) : Set (List ℕ) :=
  {l | l.length = m ∧ l.Sorted (· < ·) ∧ (∀ y ∈ l, 0 < y) ∧ (l.map ff).prod = t}

lemma ff_pos (y : ℕ) : 0 < ff y := by
  unfold ff; positivity

lemma one_lt_ff {y : ℕ} (hy : 0 < y) : 1 < ff y := by
  unfold ff
  have : (0 : ℚ) < y := by exact_mod_cast hy
  have : 0 < 1 / (y : ℚ) := by positivity
  linarith

lemma ff_le_ff {y b : ℕ} (hy : 0 < y) (hyb : y ≤ b) : ff b ≤ ff y := by
  unfold ff
  have h1 : (0 : ℚ) < y := by exact_mod_cast hy
  have h2 : (y : ℚ) ≤ b := by exact_mod_cast hyb
  have := one_div_le_one_div_of_le h1 h2
  linarith

lemma one_le_prod_ff : ∀ l : List ℕ, (∀ b ∈ l, 0 < b) → 1 ≤ (l.map ff).prod
  | [], _ => by simp
  | b :: l, h => by
    rw [List.map_cons, List.prod_cons]
    have h1 := one_lt_ff (h b (by simp))
    have h2 := one_le_prod_ff l (fun c hc => h c (by simp [hc]))
    nlinarith

lemma prod_ff_le_pow {y : ℕ} (hy : 0 < y) :
    ∀ l : List ℕ, (∀ b ∈ l, y ≤ b) → (l.map ff).prod ≤ ff y ^ l.length
  | [], _ => by simp
  | b :: l, h => by
    rw [List.map_cons, List.prod_cons, List.length_cons, pow_succ']
    have h1 := ff_le_ff hy (h b (by simp))
    have h2 := prod_ff_le_pow hy l (fun c hc => h c (by simp [hc]))
    have h3 := one_le_prod_ff l (fun c hc => lt_of_lt_of_le hy (h c (by simp [hc])))
    have h4 := ff_pos b
    have h5 : (0 : ℚ) ≤ ff y ^ l.length := by have := ff_pos y; positivity
    calc ff b * (l.map ff).prod ≤ ff y * (l.map ff).prod := by nlinarith
      _ ≤ ff y * ff y ^ l.length := by have := ff_pos y; nlinarith

/-- `(1 + x)^n ≤ 1 + (2^n - 1) x` for `0 ≤ x ≤ 1` (convexity). -/
lemma one_add_pow_le {x : ℚ} (h0 : 0 ≤ x) (h1 : x ≤ 1) :
    ∀ n : ℕ, (1 + x) ^ n ≤ 1 + (2 ^ n - 1) * x
  | 0 => by simp
  | n + 1 => by
    have ih := one_add_pow_le h0 h1 n
    have h2 : (1 : ℚ) ≤ 2 ^ n := one_le_pow₀ (by norm_num)
    rw [pow_succ, pow_succ]
    calc (1 + x) ^ n * (1 + x) ≤ (1 + (2 ^ n - 1) * x) * (1 + x) := by
          apply mul_le_mul_of_nonneg_right ih; linarith
      _ ≤ 1 + (2 ^ n * 2 - 1) * x := by nlinarith [mul_nonneg h0 (sub_nonneg.2 h1)]

/-- The smallest element is bounded in terms of the target and the length. -/
lemma le_bound {y : ℕ} {m : ℕ} {t : ℚ} (hy : 0 < y) (ht : t ≤ ff y ^ (m + 1))
    (ht1 : ff y ≤ t) : y ≤ ⌈(2 : ℚ) ^ (m + 1) / (t - 1)⌉₊ := by
  have hy' : (1 : ℚ) ≤ y := by exact_mod_cast hy
  have hx0 : (0 : ℚ) ≤ 1 / (y : ℚ) := by positivity
  have hx1 : 1 / (y : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hy'
  have hb := one_add_pow_le hx0 hx1 (m + 1)
  have hfy : 1 < ff y := one_lt_ff hy
  have htpos : 0 < t - 1 := by linarith
  have key : t - 1 ≤ (2 ^ (m + 1) - 1) * (1 / (y : ℚ)) := by
    unfold ff at ht; linarith
  have key2 : (y : ℚ) * (t - 1) ≤ 2 ^ (m + 1) := by
    have hyq : (0 : ℚ) < y := by linarith
    have : (y : ℚ) * (t - 1) ≤ (y : ℚ) * ((2 ^ (m + 1) - 1) * (1 / (y : ℚ))) :=
      mul_le_mul_of_nonneg_left key hyq.le
    have e : (y : ℚ) * ((2 ^ (m + 1) - 1) * (1 / (y : ℚ))) = 2 ^ (m + 1) - 1 := by
      field_simp
    linarith
  have : (y : ℚ) ≤ (2 : ℚ) ^ (m + 1) / (t - 1) := by
    rw [le_div_iff₀ htpos]; exact key2
  exact_mod_cast this.trans (Nat.le_ceil _)

theorem goodList_finite : ∀ (m : ℕ) (t : ℚ), (GoodList m t).Finite
  | 0, t => by
    refine (Set.finite_singleton ([] : List ℕ)).subset ?_
    rintro l ⟨hl, -, -, -⟩
    simp [List.length_eq_zero_iff.1 hl]
  | m + 1, t => by
    set B := ⌈(2 : ℚ) ^ (m + 1) / (t - 1)⌉₊
    refine (Set.Finite.biUnion (Finset.range (B + 1)).finite_toSet
      (fun y _ => (goodList_finite m (t / ff y)).image (List.cons y))).subset ?_
    rintro l ⟨hl, hs, hpos, hprod⟩
    obtain _ | ⟨y, l'⟩ := l
    · simp at hl
    simp only [List.length_cons, Nat.add_right_cancel_iff] at hl
    rw [List.sorted_cons] at hs
    rw [List.map_cons, List.prod_cons] at hprod
    have hy : 0 < y := hpos y (by simp)
    have hpos' : ∀ b ∈ l', 0 < b := fun b hb => hpos b (by simp [hb])
    have hge := one_le_prod_ff l' hpos'
    have hle := prod_ff_le_pow hy l' (fun b hb => (hs.1 b hb).le)
    rw [hl] at hle
    have hfy := ff_pos y
    have hyB : y ≤ B := by
      apply le_bound hy
      · rw [← hprod, pow_succ']; exact mul_le_mul_of_nonneg_left hle hfy.le
      · rw [← hprod]; nlinarith
    simp only [Set.mem_iUnion, Set.mem_image, Finset.coe_range, Set.mem_Iio]
    refine ⟨y, by omega, l', ⟨hl, hs.2, hpos', ?_⟩, rfl⟩
    rw [← hprod]; field_simp

lemma prod_map_ff : ∀ l : List ℕ, (∀ y ∈ l, 0 < y) →
    (l.map ff).prod * (l.prod : ℚ) = ((l.map (1 + ·)).prod : ℕ)
  | [], _ => by simp
  | y :: l, h => by
    have ih := prod_map_ff l (fun b hb => h b (by simp [hb]))
    have hy : (y : ℚ) ≠ 0 := by have := h y (by simp); positivity
    simp only [List.map_cons, List.prod_cons, Nat.cast_mul, Nat.cast_add, Nat.cast_one] at ih ⊢
    rw [← ih]; unfold ff; field_simp; ring

/-- **For each `k`, only finitely many unitary perfect numbers have exactly `k` distinct prime
factors.** -/
theorem finite_isUnitaryPerfect_card_primeFactors_eq (k : ℕ) :
    {n | IsUnitaryPerfect n ∧ n.primeFactors.card = k}.Finite := by
  refine ((goodList_finite k 2).image List.prod).subset ?_
  rintro n ⟨hn, hk⟩
  obtain ⟨hs, hn0⟩ := isUnitaryPerfect_iff.1 hn
  obtain ⟨l, hsort, hlen, hgt, -, hprod, hsig⟩ := exists_sorted_factors hn0.ne'
  have hpos : ∀ y ∈ l, 0 < y := fun y hy => lt_trans Nat.zero_lt_one (hgt y hy)
  refine ⟨l, ⟨hlen.trans hk, hsort, hpos, ?_⟩, hprod⟩
  have e := prod_map_ff l hpos
  rw [hsig, hs, hprod] at e
  have : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
  push_cast at e
  field_simp at e
  linarith

/-- Only finitely many unitary perfect numbers have at most `K` distinct prime factors. -/
theorem finite_isUnitaryPerfect_card_primeFactors_le (K : ℕ) :
    {n | IsUnitaryPerfect n ∧ n.primeFactors.card ≤ K}.Finite := by
  refine (Set.Finite.biUnion (Finset.range (K + 1)).finite_toSet
    (fun k _ => finite_isUnitaryPerfect_card_primeFactors_eq k)).subset ?_
  rintro n ⟨hn, hK⟩
  simp only [Set.mem_iUnion, Finset.coe_range, Set.mem_Iio, Set.mem_setOf_eq]
  exact ⟨_, by omega, hn, rfl⟩

/-- **Erdős #1052 is equivalent to a uniform bound on the number of distinct prime factors of a
unitary perfect number.** -/
theorem erdos_1052_statement_iff_bddAbove :
    erdos_1052_statement ↔ ∃ K, ∀ n, IsUnitaryPerfect n → n.primeFactors.card ≤ K := by
  constructor
  · intro h
    obtain ⟨K, hK⟩ := (h.image fun n => n.primeFactors.card).bddAbove
    exact ⟨K, fun n hn => hK ⟨n, hn, rfl⟩⟩
  · rintro ⟨K, hK⟩
    exact (finite_isUnitaryPerfect_card_primeFactors_le K).subset fun n hn => ⟨hn, hK n hn⟩

end ErdosResearch.Erdos1052
