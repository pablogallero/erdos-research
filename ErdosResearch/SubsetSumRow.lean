module

public import ErdosResearch.SubsetSumStairPoint

@[expose] public section

/-!
# A limit row of the staircase: every exponent `e ≥ e₀` and every last prime at once

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 81).

Fix a point `m` (e.g. `m = n p^f`) with an `IntervalGap m S c g` certificate and a prime `q ∤ m` that is
*limit-deficient* with margin: `σ(m) q (r₁ + 2) ≤ 2 (r₁ + 1) m (q − 1)`. Then every `M_e = m q^e` is deficient and
`σ(M_e) ≤ (r₁ + 1)(2 M_e − σ(M_e))`, so `M_e r` can only be abundant for `r ≤ r₁`. With `T_e = σ(M_e)`,
`T_{e+1} = q T_e + σ(m)` and `M_{e+1} = q M_e`, so the remaining conditions of `pointOK`
(`2 r₁ M + c ≤ (r₁ + 1) T`, `(r₀ + 2) M + 2c ≤ (r₀ + 1) T + 1`, `r₁ g + 2c ≤ S + 1`, `c ≤ M r₀`) propagate from `e`
to `e + 1`. The step conditions of `q` do not depend on `e`. So one Boolean `rowOK`, checked at `e₀` only, gives
`¬ (m q^e r).Weird` for EVERY `e ≥ e₀` and every prime `r ≥ r₀`, `r ∤ m q^e`.

Instances below the late prefix `n = 3^3·23·13^10·17^2·11`: the row `n·37·307^e` for every `e ≥ 1`
(`not_weird_late_prefix_row_all`), and with the pseudoperfect corner `n·37²·307` (`not_weird_of_upset`) the WHOLE pair
`(37, 307)`: no `n·37^f·307^e·r` is weird for any `f, e ≥ 1` and prime `r` (`not_weird_late_prefix_pair_all`).

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumRow

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPoint ErdosResearch.SubsetSumStairPoint

/-- The Boolean of a limit row (`m`, `∑ D m = S`, prime `q`, exponents `e ≥ e₀`, last primes `r ≥ r₀`). -/
def rowOK (m S c g q r₀ r₁ e₀ : ℕ) : Bool :=
  decide (1 ≤ c) && decide (m % q ≠ 0) && decide (q * g + 2 * c ≤ S + 1) &&
    decide (m + 2 * c ≤ (q + 1) * S + 1) &&
    decide ((S + m) * q * (r₁ + 2) ≤ 2 * (r₁ + 1) * m * (q - 1)) &&
    decide (r₁ * g + 2 * c ≤ ppSum m q S e₀ + 1) &&
    decide (2 * r₁ * (m * q ^ e₀) + c ≤ (r₁ + 1) * (ppSum m q S e₀ + m * q ^ e₀)) &&
    decide ((r₀ + 2) * (m * q ^ e₀) + 2 * c ≤ (r₀ + 1) * (ppSum m q S e₀ + m * q ^ e₀) + 1) &&
    decide (c ≤ m * q ^ e₀ * r₀)

/-- `T_{e+1} = q T_e + σ(m)` for `T_e = ppSum m q S e + m q^e`. -/
theorem total_succ (m q S e : ℕ) :
    ppSum m q S (e + 1) + m * q ^ (e + 1) = q * (ppSum m q S e + m * q ^ e) + (S + m) := by
  simp only [ppSum, pow_succ]; ring

/-- The limit inequality bounds every `T_e`: `(r₁ + 2) T_e < 2 (r₁ + 1) m q^e`. -/
theorem total_lt_of_limit {m q S r₁ : ℕ} (hm : 0 < m) (hq : 2 ≤ q)
    (hlim : (S + m) * q * (r₁ + 2) ≤ 2 * (r₁ + 1) * m * (q - 1)) (e : ℕ) :
    (r₁ + 2) * (ppSum m q S e + m * q ^ e) < 2 * (r₁ + 1) * (m * q ^ e) := by
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by omega⟩
  have hx := ErdosResearch.SubsetSumFifthLoop.ppSum_exact' m (q' + 2) S e
  have hq1 : q' + 2 - 1 = q' + 1 := by omega
  rw [hq1] at hlim
  rw [pow_succ] at hx
  set T := ppSum m (q' + 2) S e + m * (q' + 2) ^ e
  set x := (q' + 2) ^ e
  -- `T (q' + 1) + σ = σ (q' + 2) x`
  have h1 : T * (q' + 1) + (S + m) = (S + m) * (q' + 2) * x := by
    have e1 : T * (q' + 2) = T * (q' + 1) + T := by ring
    have e2 : (S + m) * (x * (q' + 2)) = (S + m) * (q' + 2) * x := by ring
    rw [e1, e2] at hx; omega
  have h2 : (S + m) * (q' + 2) * (r₁ + 2) * x ≤ 2 * (r₁ + 1) * m * (q' + 1) * x :=
    Nat.mul_le_mul_right x hlim
  have h3 : (r₁ + 2) * T * (q' + 1) < 2 * (r₁ + 1) * (m * x) * (q' + 1) := by
    have hσ : 0 < S + m := by omega
    have h1' : (r₁ + 2) * (T * (q' + 1)) + (r₁ + 2) * (S + m) = (r₁ + 2) * ((S + m) * (q' + 2) * x) := by
      rw [← h1]; ring
    have h4 : 0 < (r₁ + 2) * (S + m) := Nat.mul_pos (by omega) hσ
    linarith
  exact Nat.lt_of_mul_lt_mul_right h3

/-- The conditions that propagate along the row (from `e` to `e + 1`). -/
def rowInv (m S c g q r₀ r₁ e : ℕ) : Prop :=
  r₁ * g + 2 * c ≤ ppSum m q S e + 1 ∧
    2 * r₁ * (m * q ^ e) + c ≤ (r₁ + 1) * (ppSum m q S e + m * q ^ e) ∧
    (r₀ + 2) * (m * q ^ e) + 2 * c ≤ (r₀ + 1) * (ppSum m q S e + m * q ^ e) + 1 ∧
    c ≤ m * q ^ e * r₀

theorem rowInv_succ {m S c g q r₀ r₁ e : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q) (h : rowInv m S c g q r₀ r₁ e) :
    rowInv m S c g q r₀ r₁ (e + 1) := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  have hT := total_succ m q S e
  set T := ppSum m q S e + m * q ^ e
  set M := m * q ^ e
  have hM : m * q ^ (e + 1) = q * M := by rw [pow_succ]; ring
  have hS1 : ppSum m q S (e + 1) = S + (m + q * ppSum m q S e) := rfl
  simp only [rowInv]
  rw [hT, hM]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hS1]; linarith [Nat.le_mul_of_pos_left (ppSum m q S e) hq]
  · linarith [Nat.mul_le_mul_left q h2, Nat.le_mul_of_pos_left c hq, Nat.zero_le ((r₁ + 1) * (S + m))]
  · have key : 2 * c + q ≤ 2 * c * q + 1 := by
      obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
      obtain ⟨q', rfl⟩ : ∃ q', q = q' + 1 := ⟨q - 1, by omega⟩
      ring_nf; omega
    linarith [Nat.mul_le_mul_left q h3, Nat.zero_le ((r₀ + 1) * (S + m))]
  · linarith [Nat.mul_le_mul_left q h4, Nat.le_mul_of_pos_left c hq]

theorem rowInv_of_le {m S c g q r₀ r₁ e₀ : ℕ} (hc : 1 ≤ c) (hq : 1 ≤ q) (h : rowInv m S c g q r₀ r₁ e₀) :
    ∀ e, e₀ ≤ e → rowInv m S c g q r₀ r₁ e := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => exact h
  | succ e _ ih => exact rowInv_succ hc hq ih

/-- **Limit row.** `IntervalGap m S c g` + `rowOK` ⇒ for every `e ≥ e₀` and every prime `r ≥ r₀` with
`r ∤ m q^e`, `m q^e r` is not weird. -/
theorem not_weird_of_rowOK {m S c g q r₀ r₁ e₀ e r : ℕ} (hm : 0 < m) (hg : 1 ≤ g)
    (h : IntervalGap m S c g) (hq : q.Prime) (hok : rowOK m S c g q r₀ r₁ e₀ = true) (he : e₀ ≤ e)
    (hr : r.Prime) (hrM : ¬ r ∣ m * q ^ e) (hr₀ : r₀ ≤ r) : ¬ (m * q ^ e * r).Weird := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, hqm⟩, hs1⟩, hs2⟩, hlim⟩, i1⟩, i2⟩, i3⟩, i4⟩ := hok
  have hqm' : ¬ q ∣ m := fun hd => hqm (Nat.mod_eq_zero_of_dvd hd)
  have hIG := ErdosResearch.SubsetSumUniform.intervalGap_mul_prime_pow hm hg h hq hqm' hs1 hs2 e
  obtain ⟨j1, j2, j3, j4⟩ := rowInv_of_le hc hq.one_lt.le ⟨i1, i2, i3, i4⟩ e he
  have hlt := total_lt_of_limit hm hq.two_le hlim e
  refine not_weird_mul_prime_of_pointOK (r₁ := r₁) (Nat.mul_pos hm (pow_pos hq.pos e)) hg hIG ?_ hr hrM hr₀
  simp only [pointOK, Bool.and_eq_true, decide_eq_true_eq]
  set S' := ppSum m q S e
  set M := m * q ^ e
  have hSM : S' < M := by
    by_contra hc'
    have := Nat.mul_le_mul_left (r₁ + 2) (Nat.le_of_not_lt hc')
    linarith
  obtain ⟨D, hD⟩ : ∃ D, M = S' + D := ⟨M - S', by omega⟩
  have hD' : M - S' = D := by omega
  rw [hD']
  rw [hD] at hlt j2 j3 j4 ⊢
  refine ⟨⟨⟨⟨⟨by omega, by linarith⟩, j1⟩, by linarith⟩, by linarith⟩, j4⟩

/-- Row after prime-power steps from a prefix certificate: `stepsOK` along `l`, then `rowOK` at the end point. -/
def stepRowOK (n S c g q r₀ r₁ e₀ : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  stepsOK c g n S l && rowOK (stepsEnd n S l).1 (stepsEnd n S l).2 c g q r₀ r₁ e₀

theorem not_weird_of_stepRowOK {n S c g q r₀ r₁ e₀ e r : ℕ} {l : List (ℕ × ℕ)} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hpr : ∀ s ∈ l, s.1.Prime) (hq : q.Prime)
    (hok : stepRowOK n S c g q r₀ r₁ e₀ l = true) (he : e₀ ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ (stepsEnd n S l).1 * q ^ e) (hr₀ : r₀ ≤ r) :
    ¬ ((stepsEnd n S l).1 * q ^ e * r).Weird := by
  simp only [stepRowOK, Bool.and_eq_true] at hok
  exact not_weird_of_rowOK (stepsEnd_pos l n S hn hpr) hg (intervalGap_of_stepsOK hg l n S hn hpr hok.1 h)
    hq hok.2 he hr hrM hr₀

/-- **Instance (limit row).** Below the late prefix `n = 3^3·23·13^10·17^2·11` (certificate `(c, g) = (2295, 5)`),
`p = 37` with `f = 1` and `q = 307`: for EVERY `e ≥ 3` and every prime `r ∤ n·37·307^e`, `n·37·307^e·r` is not
weird (`r₁ = 7196` bounds the abundant range of `r` on the whole row). -/
theorem not_weird_late_prefix_row {e r : ℕ} (he : 3 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ e) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ e * r).Weird :=
  not_weird_of_stepRowOK (S := 256030928920159929) (c := 2295) (g := 5) (q := 307) (r₀ := 2) (r₁ := 7196)
    (e₀ := 3) (l := [(37, 1)]) (by norm_num) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; norm_num) (by norm_num)
    (by decide +kernel) he hr hrM hr.two_le

/-- The point `e = 2` of the same row (session-80 style, `r₁ = 7195`). -/
theorem not_weird_late_prefix_row_two {r : ℕ} (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ 2) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ 2 * r).Weird :=
  not_weird_of_stepPointOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 7195)
    (l := [(37, 1), (307, 2)]) (by norm_num) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; norm_num)
    (by decide +kernel) hr hrM hr.two_le

/-- **The whole row.** For `n = 3^3·23·13^10·17^2·11`: no `n·37·307^e·r` is weird, for EVERY `e ≥ 1` and every prime
`r ∤ n·37·307^e` (`e = 1`: session 80's point; `e = 2`: one point; `e ≥ 3`: the limit row). -/
theorem not_weird_late_prefix_row_all {e r : ℕ} (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ e) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ e * r).Weird := by
  rcases (show e = 1 ∨ e = 2 ∨ 3 ≤ e by omega) with rfl | rfl | h3
  · exact not_weird_late_prefix_pair_point hr hrM
  · exact not_weird_late_prefix_row_two hr hrM
  · exact not_weird_late_prefix_row h3 hr hrM

/-- The corner `(f, e) = (2, 1)` of the pair `(37, 307)` is abundant and pseudoperfect (two steps, then the interval
contains the number). -/
theorem pseudoperfect_late_prefix_corner :
    (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 2 * 307 ^ 1).Pseudoperfect :=
  pseudoperfect_of_stepAbOK (S := 256030928920159929) (c := 2295) (g := 5) (l := [(37, 2), (307, 1)])
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; norm_num)
    (by decide +kernel)

/-- **A whole pair of the staircase.** For `n = 3^3·23·13^10·17^2·11`: no `n·37^f·307^e·r` is weird, for ALL
`f, e ≥ 1` and every prime `r ∤ n·37^f·307^e`. Row `f = 1` is deficient for every `e` (points `e = 1, 2` and the limit
row `e ≥ 3`); for `f ≥ 2` the corner `(2, 1)` is pseudoperfect and covers the whole up-set. -/
theorem not_weird_late_prefix_pair_all {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 307 ^ e) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 307 ^ e * r).Weird := by
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | h2
  · exact not_weird_late_prefix_row_all he hr hrM
  · exact not_weird_of_upset (by norm_num) (by norm_num) pseudoperfect_late_prefix_corner h2 he hr.pos

end ErdosResearch.SubsetSumRow
