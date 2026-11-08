import ErdosResearch.UnitaryPerfectFinite

/-!
# Erdős #1052: an explicit bound for unitary perfect numbers with `k` prime factors

`IsUnitaryPerfect n → n ≤ 2 ^ (k * 2 ^ k)` where `k = ω(n)`
(`le_two_pow_of_isUnitaryPerfect`).

This is classical: Goto (2007, Zbl 1141.11006) proves the sharper `n < 2 ^ (2 ^ k)`. It is new
here only as a formalisation; it makes the finiteness in `UnitaryPerfectFinite.lean` explicit.

Proof. Track the target `t = b / a` of the remaining product `∏ (1 + 1/yᵢ)` with `a, b ∈ ℕ`.
If the remaining sorted list has smallest element `y` and length `n`, then `b ≥ a + 1` and the
convexity bound gives `y (t - 1) ≤ 2^n - 1`, hence `y < 2^n a`. Passing to the rest replaces `a`
by `a (1 + y) ≤ 2^n a²`, and induction gives `a ∏ (1 + yᵢ) ≤ (2^n a)^(2^n)`.
-/

namespace ErdosResearch.Erdos1052

/-- One step: the smallest element `y` satisfies `y < 2^n a` when the target is `b / a`. -/
lemma lt_two_pow_mul {y a b : ℕ} (l : List ℕ) (hy : 0 < y) (ha : 0 < a)
    (hge : ∀ z ∈ l, y ≤ z) (hpos : ∀ z ∈ l, 0 < z)
    (h : (a : ℚ) * (ff y * (l.map ff).prod) = b) : y < 2 ^ (l.length + 1) * a := by
  set n := l.length + 1
  have hle := prod_ff_le_pow hy l hge
  have hone := one_le_prod_ff l hpos
  have hfy := one_lt_ff hy
  have haq : (0 : ℚ) < a := by exact_mod_cast ha
  have hyq : (1 : ℚ) ≤ y := by exact_mod_cast hy
  -- `b > a`, hence `b ≥ a + 1`
  have hba : (a : ℚ) < b := by
    have h1 : 1 < ff y * (l.map ff).prod := by nlinarith
    rw [← h]; nlinarith
  have hba' : (a : ℚ) + 1 ≤ b := by
    have : a < b := by exact_mod_cast hba
    exact_mod_cast this
  -- `b ≤ a (1 + 1/y)^n ≤ a (1 + (2^n - 1)/y)`
  have hx0 : (0 : ℚ) ≤ 1 / (y : ℚ) := by positivity
  have hx1 : 1 / (y : ℚ) ≤ 1 := by rw [div_le_one (by linarith)]; exact hyq
  have hc := one_add_pow_le hx0 hx1 n
  have hb : (b : ℚ) ≤ a * (1 + (2 ^ n - 1) * (1 / (y : ℚ))) := by
    have h1 : ff y * (l.map ff).prod ≤ ff y ^ n := by
      simp only [n, pow_succ']
      exact mul_le_mul_of_nonneg_left hle (by linarith)
    have h2 : ff y ^ n ≤ 1 + (2 ^ n - 1) * (1 / (y : ℚ)) := by unfold ff; exact hc
    rw [← h]; exact mul_le_mul_of_nonneg_left (h1.trans h2) haq.le
  -- so `y ≤ a (2^n - 1)`
  have key : (y : ℚ) ≤ a * (2 ^ n - 1) := by
    have hyp : (0 : ℚ) < y := by linarith
    have e : (a : ℚ) * (1 + (2 ^ n - 1) * (1 / (y : ℚ))) = a + a * (2 ^ n - 1) / y := by
      field_simp
    rw [e] at hb
    have : 1 ≤ (a : ℚ) * (2 ^ n - 1) / y := by linarith
    rwa [one_le_div hyp] at this
  have key' : (y : ℚ) < 2 ^ n * a := by nlinarith
  exact_mod_cast key'

/-- The explicit bound on sorted lists with target `b / a`. -/
theorem mul_prod_le : ∀ (l : List ℕ) (a b : ℕ), l.Sorted (· < ·) → (∀ y ∈ l, 0 < y) → 0 < a →
    (a : ℚ) * (l.map ff).prod = b →
    a * (l.map (1 + ·)).prod ≤ (2 ^ l.length * a) ^ (2 ^ l.length)
  | [], a, _, _, _, _, _ => by simp
  | y :: l, a, b, hs, hpos, ha, h => by
    rw [List.sorted_cons] at hs
    have hy : 0 < y := hpos y (by simp)
    have hpos' : ∀ z ∈ l, 0 < z := fun z hz => hpos z (by simp [hz])
    rw [List.map_cons, List.prod_cons] at h
    have hlt := lt_two_pow_mul l hy ha (fun z hz => (hs.1 z hz).le) hpos' h
    -- induction hypothesis with `a' = a (1 + y)`, `b' = b y`
    have h' : ((a * (1 + y) : ℕ) : ℚ) * (l.map ff).prod = (b * y : ℕ) := by
      have hyq : (y : ℚ) ≠ 0 := by exact_mod_cast hy.ne'
      push_cast
      rw [← h]; unfold ff; field_simp; ring
    have ih := mul_prod_le l (a * (1 + y)) (b * y) hs.2 hpos' (by positivity) h'
    set n := l.length
    simp only [List.map_cons, List.prod_cons, List.length_cons]
    have hy1 : 1 + y ≤ 2 ^ (n + 1) * a := by omega
    calc a * ((1 + y) * (l.map (1 + ·)).prod) = a * (1 + y) * (l.map (1 + ·)).prod := by ring
      _ ≤ (2 ^ n * (a * (1 + y))) ^ 2 ^ n := ih
      _ ≤ ((2 ^ (n + 1) * a) ^ 2) ^ 2 ^ n := by
          apply Nat.pow_le_pow_left
          calc 2 ^ n * (a * (1 + y)) ≤ 2 ^ (n + 1) * (a * (2 ^ (n + 1) * a)) := by
                apply Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega))
                exact Nat.mul_le_mul_left _ hy1
            _ = (2 ^ (n + 1) * a) ^ 2 := by ring
      _ = (2 ^ (n + 1) * a) ^ 2 ^ (n + 1) := by rw [← pow_mul, pow_succ 2 n, mul_comm (2 ^ n)]

lemma list_prod_le_prod_one_add : ∀ l : List ℕ, l.prod ≤ (l.map (1 + ·)).prod
  | [] => by simp
  | y :: l => by
    simp only [List.prod_cons, List.map_cons]
    exact Nat.mul_le_mul (by omega) (list_prod_le_prod_one_add l)

/-- **A unitary perfect number with `k` distinct prime factors is at most `2^(k·2^k)`.**
(Goto 2007 has the sharper `n < 2^(2^k)`.) -/
theorem le_two_pow_of_isUnitaryPerfect {n : ℕ} (hn : IsUnitaryPerfect n) :
    n ≤ 2 ^ (n.primeFactors.card * 2 ^ n.primeFactors.card) := by
  obtain ⟨hs, hn0⟩ := isUnitaryPerfect_iff.1 hn
  obtain ⟨l, hsort, hlen, hgt, -, hprod, hsig⟩ := exists_sorted_factors hn0.ne'
  have hpos : ∀ y ∈ l, 0 < y := fun y hy => lt_trans Nat.zero_lt_one (hgt y hy)
  have h2 : ((1 : ℕ) : ℚ) * (l.map ff).prod = ((2 : ℕ) : ℚ) := by
    have e := prod_map_ff l hpos
    rw [hsig, hs, hprod] at e
    have : (n : ℚ) ≠ 0 := by exact_mod_cast hn0.ne'
    push_cast at e ⊢
    field_simp at e
    linarith
  have hb := mul_prod_le l 1 2 hsort hpos one_pos h2
  rw [one_mul, mul_one, hlen, ← pow_mul] at hb
  have := (list_prod_le_prod_one_add l).trans hb
  rwa [hprod] at this

/-- The explicit form of `finite_isUnitaryPerfect_card_primeFactors_eq`. -/
theorem isUnitaryPerfect_card_primeFactors_eq_subset (k : ℕ) :
    {n | IsUnitaryPerfect n ∧ n.primeFactors.card = k} ⊆ Set.Iic (2 ^ (k * 2 ^ k)) := by
  rintro n ⟨hn, rfl⟩
  exact le_two_pow_of_isUnitaryPerfect hn

end ErdosResearch.Erdos1052
