module

public import ErdosResearch.SubsetSumStairPoint
public import ErdosResearch.SubsetSumUniform
public import ErdosResearch.SubsetSumFifthLoop

@[expose] public section

/-!
# All trivial pairs `(p, q)` with `q` in a range, from one Boolean

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 82).

Session 82 (`scripts/pair_cert_gen.py`) found that below the late prefix almost every free-`r` pair has the trivial
shape `(F, f_r, e_c) = (1, 1, 1)`: the corner `n p q` is already abundant with an interval, so the whole up-set
`f, e ≥ 1` is pseudoperfect (1439 of 1460 pairs with `p < 400`, `q < 5000`). Emitting one `pairOK` per pair costs
≈ 0.3 s of kernel each. Here the step `n ↦ n p` is taken once and the session-63 range lemma
(`pseudoperfect_mul_prime_of_range`, four end inequalities, linear in `q`) covers every prime `q ∈ [q₀, q₁]` at once.

* `rangeOK n S c g p q₀ q₁`: the Boolean (step condition for `p`, then the four end inequalities at `n p`).
* `not_weird_of_stepAbOK_single`: `n p` abundant with an interval covers every `q`.
* `not_weird_qtail`: for a fixed `p`, `σ(n) p (Q+1) ≤ 2n(p−1)(Q−1)` ⇒ no `n p^f q^e r` with primes `q, r ≥ Q` is weird
  (all `f, e`): the bounded pairs with `q ≥ Q` need no work at all.
* `not_weird_of_rangeOK`: no `n p^f q^e m` is weird, for all `f, e ≥ 1`, `m ≥ 1` and every prime `q ∈ [q₀, q₁]`
  with `q ∤ n p`.

Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumPairRange

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumStairPoint

/-- The Boolean of a `q`-range of trivial pairs over the prime `p`. -/
def rangeOK (n S c g p q₀ q₁ : ℕ) : Bool :=
  stepsOK c g n S [(p, 1)] &&
    decide (q₁ * g + 2 * c ≤ (stepsEnd n S [(p, 1)]).2 + 1) &&
    decide ((stepsEnd n S [(p, 1)]).1 + 2 * c ≤ (q₀ + 1) * (stepsEnd n S [(p, 1)]).2 + 1) &&
    decide (c ≤ (stepsEnd n S [(p, 1)]).1 * q₀) &&
    decide ((stepsEnd n S [(p, 1)]).1 * q₁ + c ≤
      (stepsEnd n S [(p, 1)]).2 + ((stepsEnd n S [(p, 1)]).1 + q₁ * (stepsEnd n S [(p, 1)]).2))

theorem stepsEnd_single (n S p : ℕ) : (stepsEnd n S [(p, 1)]).1 = n * p := by simp [stepsEnd]

/-- **A whole `q`-range of trivial pairs.** -/
theorem not_weird_of_rangeOK {n S c g p q₀ q₁ q f e m : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hp : p.Prime) (hok : rangeOK n S c g p q₀ q₁ = true) (hq : q.Prime)
    (hqn : ¬ q ∣ n * p) (hq₀ : q₀ ≤ q) (hq₁ : q ≤ q₁) (hf : 1 ≤ f) (he : 1 ≤ e) (hm : 0 < m) :
    ¬ (n * p ^ f * q ^ e * m).Weird := by
  simp only [rangeOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hs, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  have hpr : ∀ s ∈ [(p, 1)], s.1.Prime := by simp [hp]
  have hI := intervalGap_of_stepsOK hg [(p, 1)] n S hn hpr hs h
  have hpos : 0 < (stepsEnd n S [(p, 1)]).1 := by rw [stepsEnd_single]; exact Nat.mul_pos hn hp.pos
  have hqn' : ¬ q ∣ (stepsEnd n S [(p, 1)]).1 := by rwa [stepsEnd_single]
  have hpp := SubsetSumUniform.pseudoperfect_mul_prime_of_range hpos hg hI hq hqn' hq₀ hq₁ h1 h2 h3 h4
  rw [stepsEnd_single] at hpp
  exact not_weird_of_upset (f₀ := 1) (e₀ := 1) hp.pos hq.pos (by simpa using hpp) hf he hm

/-- **Abundant single step.** If `n p` is already abundant with an interval (`stepAbOK` on `[(p, 1)]`), it is
pseudoperfect, so no `n p^f m` (`f, m ≥ 1`) is weird: every `q` (with no upper bound) is covered at once. -/
theorem not_weird_of_stepAbOK_single {n S c g p f m : ℕ} (hn : 0 < n) (hg : 1 ≤ g) (h : IntervalGap n S c g)
    (hp : p.Prime) (hok : stepAbOK n S c g [(p, 1)] = true) (hf : 1 ≤ f) (hm : 0 < m) :
    ¬ (n * p ^ f * m).Weird := by
  have hpr : ∀ s ∈ [(p, 1)], s.1.Prime := by simp [hp]
  have hpp := pseudoperfect_of_stepAbOK hn hg h hpr hok
  rw [stepsEnd_single] at hpp
  have hd : n * p ∣ n * p ^ f * m :=
    Dvd.dvd.mul_right (mul_dvd_mul_left n (by simpa using pow_dvd_pow p hf)) m
  have hpos : 0 < n * p ^ f * m := Nat.mul_pos (Nat.mul_pos hn (pow_pos hp.pos f)) hm
  exact fun hw => hw.2 (hpp.of_dvd hd hpos)

/-- `σ(n p^f) (p − 1) ≤ σ(n) p^(f+1)` in `ppSum` form. -/
theorem ppSum_ratio (n p S f : ℕ) (hp : 2 ≤ p) :
    (ppSum n p S f + n * p ^ f) * (p - 1) ≤ (S + n) * (p ^ f * p) := by
  have hx := ErdosResearch.SubsetSumFifthLoop.ppSum_exact' n p S f
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by omega⟩
  rw [pow_succ] at hx
  have h : p' + 2 - 1 = p' + 1 := by omega
  rw [h]
  nlinarith [hx]

/-- **`q`-tail for a fixed `p`.** -/
theorem not_weird_qtail {n S p Q f q e r : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q.Prime) (hqn : ¬ q ∣ n * p ^ f) (hr : r.Prime)
    (hrn : ¬ r ∣ n * p ^ f * q ^ e) (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hQr : Q ≤ r)
    (hσ : (S + n) * p * (Q + 1) ≤ 2 * n * (p - 1) * (Q - 1)) : ¬ (n * p ^ f * q ^ e * r).Weird := by
  have hm : 0 < n * p ^ f := Nat.mul_pos hn (pow_pos hp.pos f)
  refine ErdosResearch.SubsetSumFifthLoop.not_weird_tail hm (ppSum_eq hn hp hpn hS f) hq hqn hr hrn hQ hQq hQr ?_
  have h1 := ppSum_ratio n p S f hp.two_le
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  refine Nat.le_of_mul_le_mul_right ?_ hp1
  calc (ppSum n p S f + n * p ^ f) * (Q + 1) * (p - 1)
      = (ppSum n p S f + n * p ^ f) * (p - 1) * (Q + 1) := by ring
    _ ≤ (S + n) * (p ^ f * p) * (Q + 1) := Nat.mul_le_mul_right _ h1
    _ = p ^ f * ((S + n) * p * (Q + 1)) := by ring
    _ ≤ p ^ f * (2 * n * (p - 1) * (Q - 1)) := Nat.mul_le_mul_left _ hσ
    _ = 2 * (n * p ^ f) * (Q - 1) * (p - 1) := by ring

end ErdosResearch.SubsetSumPairRange
