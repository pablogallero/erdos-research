module

public import ErdosResearch.SubsetSumRow
public import ErdosResearch.SubsetSumPairRange

@[expose] public section

/-!
# A limit quadrant of a bounded pair: every `f ≥ f₀`, `e ≥ e₀` and every last prime at once

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 83).

Fix a prefix `n` with `IntervalGap n S c g` and two primes `p ≠ q` not dividing `n`. The pair is *bounded* when
`σ(n) p q < 2 n (p − 1)(q − 1)`: then every `n p^f q^e` is deficient and `n p^f q^e r` can only be abundant for `r`
below a bound that is nondecreasing in `(f, e)` and bounded, hence constant (`= r₁`) on some quadrant.

The row invariant of session 81 (`rowInv`, conditions at the end `r₁`) propagates along `e` (`rowInv_succ`). Since
`∑ D(n p^f q^e)` is symmetric in `(p, f)` and `(q, e)`, it also propagates along `f`: check it once at the corner of
`n q^{e₀}` with the prime `p` and exponent `f₀`. The 2-D limit `σ(n) p q (r₁ + 2) ≤ 2 (r₁ + 1) n (p − 1)(q − 1)` gives
the row limit of every `n p^f` (`ppSum_ratio`), and the step conditions of `q` at `n p^{f₀}` carry over to `f ≥ f₀`.
So one Boolean `quadOK`, checked at the corner only, gives `¬ (n p^f q^e r).Weird` for EVERY `f ≥ f₀`, `e ≥ e₀` and
every prime `r ≥ r₀`, `r ∤ n p^f q^e` (`not_weird_of_quadOK`).

With rows `f < f₀` (`rowOK` in `q`) and columns `e < e₀` (`rowOK` in `p`) this closes a whole bounded pair; Python
(`scripts/quad_probe.py`) finds such a cover for all 232 bounded pairs below the late prefix and all 2507 below the real
prefix `3^16·5^11·19^8`. Instance: the bounded pair `(53, 151)` below the late prefix is closed (`not_weird_late_prefix_53_151`).

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumQuad

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumRow ErdosResearch.SubsetSumStairPoint

/-- The Boolean of a limit quadrant (prefix `n`, `∑ D n = S`, primes `p`, `q`, corner `(f₀, e₀)`, last primes in
`[r₀, ∞)`, end `r₁` of the abundant range of `r` on the whole quadrant). -/
def quadOK (n S c g p q r₀ r₁ f₀ e₀ : ℕ) : Bool :=
  decide (1 ≤ c) && decide (n % p ≠ 0) && decide (n % q ≠ 0) && decide (p ≠ q) &&
    decide (p * g + 2 * c ≤ S + 1) && decide (n + 2 * c ≤ (p + 1) * S + 1) &&
    decide (q * g + 2 * c ≤ ppSum n p S f₀ + 1) &&
    decide (n * p ^ f₀ + 2 * c ≤ (q + 1) * ppSum n p S f₀ + 1) &&
    decide ((S + n) * p * q * (r₁ + 2) ≤ 2 * (r₁ + 1) * n * (p - 1) * (q - 1)) &&
    decide (r₁ * g + 2 * c ≤ ppSum (n * q ^ e₀) p (ppSum n q S e₀) f₀ + 1) &&
    decide (2 * r₁ * (n * q ^ e₀ * p ^ f₀) + c ≤
      (r₁ + 1) * (ppSum (n * q ^ e₀) p (ppSum n q S e₀) f₀ + n * q ^ e₀ * p ^ f₀)) &&
    decide ((r₀ + 2) * (n * q ^ e₀ * p ^ f₀) + 2 * c ≤
      (r₀ + 1) * (ppSum (n * q ^ e₀) p (ppSum n q S e₀) f₀ + n * q ^ e₀ * p ^ f₀) + 1) &&
    decide (c ≤ n * q ^ e₀ * p ^ f₀ * r₀)

theorem ppSum_le_succ (n p S f : ℕ) (hp : 1 ≤ p) : ppSum n p S f ≤ ppSum n p S (f + 1) := by
  show ppSum n p S f ≤ S + (n + p * ppSum n p S f)
  have := Nat.le_mul_of_pos_left (ppSum n p S f) hp
  omega

theorem ppSum_mono {n p S f₀ : ℕ} (hp : 1 ≤ p) : ∀ f, f₀ ≤ f → ppSum n p S f₀ ≤ ppSum n p S f := by
  intro f hf
  induction f, hf using Nat.le_induction with
  | base => exact le_rfl
  | succ f _ ih => exact ih.trans (ppSum_le_succ n p S f hp)

/-- The second step condition of `q` carries over from `n p^f` to `n p^(f+1)`. -/
theorem step2_succ {n S c p q f : ℕ} (hc : 1 ≤ c) (hp : 1 ≤ p)
    (h : n * p ^ f + 2 * c ≤ (q + 1) * ppSum n p S f + 1) :
    n * p ^ (f + 1) + 2 * c ≤ (q + 1) * ppSum n p S (f + 1) + 1 := by
  have hS1 : ppSum n p S (f + 1) = S + (n + p * ppSum n p S f) := rfl
  have hM : n * p ^ (f + 1) = p * (n * p ^ f) := by rw [pow_succ]; ring
  rw [hS1, hM]
  have key : 2 * c + p ≤ 2 * c * p + 1 := by
    obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
    obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
    ring_nf; omega
  have h2 := Nat.mul_le_mul_left p h
  have e1 : (q + 1) * (S + (n + p * ppSum n p S f)) = (q + 1) * (S + n) + p * ((q + 1) * ppSum n p S f) := by ring
  rw [e1]
  nlinarith [Nat.zero_le ((q + 1) * (S + n))]

theorem step2_mono {n S c p q f₀ : ℕ} (hc : 1 ≤ c) (hp : 1 ≤ p)
    (h : n * p ^ f₀ + 2 * c ≤ (q + 1) * ppSum n p S f₀ + 1) :
    ∀ f, f₀ ≤ f → n * p ^ f + 2 * c ≤ (q + 1) * ppSum n p S f + 1 := by
  intro f hf
  induction f, hf using Nat.le_induction with
  | base => exact h
  | succ f _ ih => exact step2_succ hc hp ih

/-- The 2-D limit gives the row limit of `n p^f` in `q`. -/
theorem row_limit {n S p q r₁ : ℕ} (hp : 2 ≤ p)
    (hlim : (S + n) * p * q * (r₁ + 2) ≤ 2 * (r₁ + 1) * n * (p - 1) * (q - 1)) (f : ℕ) :
    (ppSum n p S f + n * p ^ f) * q * (r₁ + 2) ≤ 2 * (r₁ + 1) * (n * p ^ f) * (q - 1) := by
  have hr := ErdosResearch.SubsetSumPairRange.ppSum_ratio n p S f hp
  have hp1 : 0 < p - 1 := by omega
  refine Nat.le_of_mul_le_mul_right ?_ hp1
  calc (ppSum n p S f + n * p ^ f) * q * (r₁ + 2) * (p - 1)
      = (ppSum n p S f + n * p ^ f) * (p - 1) * (q * (r₁ + 2)) := by ring
    _ ≤ (S + n) * (p ^ f * p) * (q * (r₁ + 2)) := Nat.mul_le_mul_right _ hr
    _ = (S + n) * p * q * (r₁ + 2) * p ^ f := by ring
    _ ≤ 2 * (r₁ + 1) * n * (p - 1) * (q - 1) * p ^ f := Nat.mul_le_mul_right _ hlim
    _ = 2 * (r₁ + 1) * (n * p ^ f) * (q - 1) * (p - 1) := by ring

/-- `∑ D(n p^f q^e)` computed in either order. -/
theorem ppSum_swap {n S p q : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S) (hp : p.Prime) (hq : q.Prime)
    (hpn : ¬ p ∣ n) (hqn : ¬ q ∣ n) (hpq : p ≠ q) (f e : ℕ) :
    ppSum (n * p ^ f) q (ppSum n p S f) e = ppSum (n * q ^ e) p (ppSum n q S e) f := by
  have hqp : ¬ q ∣ n * p ^ f := fun h => by
    rcases (Nat.Prime.dvd_mul hq).1 h with h | h
    · exact hqn h
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow h)).symm
  have hpq' : ¬ p ∣ n * q ^ e := fun h => by
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · exact hpn h
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hp hq).1 (hp.dvd_of_dvd_pow h))
  have h1 := ppSum_eq (Nat.mul_pos hn (pow_pos hp.pos f)) hq hqp (ppSum_eq hn hp hpn hS f) e
  have h2 := ppSum_eq (Nat.mul_pos hn (pow_pos hq.pos e)) hp hpq' (ppSum_eq hn hq hqn hS e) f
  have hx : n * p ^ f * q ^ e = n * q ^ e * p ^ f := by ring
  rw [← h1, ← h2, hx]

/-- **Limit quadrant.** `IntervalGap n S c g` + `quadOK` ⇒ for every `f ≥ f₀`, `e ≥ e₀` and every prime `r ≥ r₀`
with `r ∤ n p^f q^e`, `n p^f q^e r` is not weird. -/
theorem not_weird_of_quadOK {n S c g p q r₀ r₁ f₀ e₀ f e r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hp : p.Prime) (hq : q.Prime)
    (hok : quadOK n S c g p q r₀ r₁ f₀ e₀ = true) (hf : f₀ ≤ f) (he : e₀ ≤ e)
    (hr : r.Prime) (hrM : ¬ r ∣ n * p ^ f * q ^ e) (hr₀ : r₀ ≤ r) : ¬ (n * p ^ f * q ^ e * r).Weird := by
  simp only [quadOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, hpn⟩, hqn⟩, hpq⟩, hp1⟩, hp2⟩, hq1⟩, hq2⟩, hlim⟩, i1⟩, i2⟩, i3⟩, i4⟩ := hok
  have hpn' : ¬ p ∣ n := fun hd => hpn (Nat.mod_eq_zero_of_dvd hd)
  have hqn' : ¬ q ∣ n := fun hd => hqn (Nat.mod_eq_zero_of_dvd hd)
  have hIG := ErdosResearch.SubsetSumUniform.intervalGap_mul_prime_pow hn hg h hp hpn' hp1 hp2 f
  -- the row invariant of `n q^{e₀}` along `p`, carried from `f₀` to `f`
  obtain ⟨j1, j2, j3, j4⟩ := rowInv_of_le hc hp.one_lt.le ⟨i1, i2, i3, i4⟩ f hf
  have hsw := ppSum_swap hn h.1 hp hq hpn' hqn' hpq f e₀
  have hx : n * q ^ e₀ * p ^ f = n * p ^ f * q ^ e₀ := by ring
  rw [← hsw] at j1 j2 j3
  rw [hx] at j2 j3 j4
  have hqm : (n * p ^ f) % q ≠ 0 := by
    intro h0
    have hd := Nat.dvd_of_mod_eq_zero h0
    rcases (Nat.Prime.dvd_mul hq).1 hd with hd | hd
    · exact hqn' hd
    · exact hpq ((Nat.prime_dvd_prime_iff_eq hq hp).1 (hq.dvd_of_dvd_pow hd)).symm
  have hrow : rowOK (n * p ^ f) (ppSum n p S f) c g q r₀ r₁ e₀ = true := by
    simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨⟨⟨⟨⟨⟨⟨⟨hc, hqm⟩, ?_⟩, step2_mono hc hp.one_lt.le hq2 f hf⟩, ?_⟩, j1⟩, j2⟩, j3⟩, j4⟩
    · exact le_trans hq1 (Nat.add_le_add_right (ppSum_mono hp.one_lt.le f hf) 1)
    · have := row_limit hp.two_le hlim f
      calc (ppSum n p S f + n * p ^ f) * q * (r₁ + 2) ≤ 2 * (r₁ + 1) * (n * p ^ f) * (q - 1) := this
        _ = 2 * (r₁ + 1) * (n * p ^ f) * (q - 1) := rfl
  exact not_weird_of_rowOK (Nat.mul_pos hn (pow_pos hp.pos f)) hg hIG hq hrow he hr hrM hr₀

/-- The late prefix `n = 3^3·23·13^10·17^2·11` (certificate `(c, g) = (2295, 5)`). -/
abbrev lateN : ℕ := 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11

/-- **A whole bounded pair.** Below the late prefix, the pair `(53, 151)` is bounded
(`σ(n)·53·151 < 2n·52·150`). No `n·53^f·151^e·r` is weird, for ALL `f, e ≥ 1` and every prime `r ∤ n·53^f·151^e`:
the point `(1, 1)` (`r₁ = 208`), the row `f = 1, e ≥ 2` (`r₁ = 210`), the column `e = 1, f ≥ 2` (`r₁ = 225`) and the
quadrant `f, e ≥ 2` (`r₁ = 227`). -/
theorem not_weird_late_prefix_53_151 {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ lateN * 53 ^ f * 151 ^ e) : ¬ (lateN * 53 ^ f * 151 ^ e * r).Weird := by
  have hIG := ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
  rcases (show f = 1 ∨ 2 ≤ f by omega) with rfl | hf2 <;> rcases (show e = 1 ∨ 2 ≤ e by omega) with rfl | he2
  · exact ErdosResearch.SubsetSumStairPoint.not_weird_of_stepPointOK (S := 256030928920159929) (c := 2295)
      (g := 5) (r₀ := 2) (r₁ := 208) (l := [(53, 1), (151, 1)]) (by norm_num) (by norm_num) hIG
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; norm_num)
      (by decide +kernel) hr hrM hr.two_le
  · exact not_weird_of_stepRowOK (S := 256030928920159929) (c := 2295) (g := 5) (q := 151) (r₀ := 2)
      (r₁ := 210) (e₀ := 2) (l := [(53, 1)]) (by norm_num) (by norm_num) hIG
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; norm_num) (by norm_num)
      (by decide +kernel) he2 hr hrM hr.two_le
  · have hc : lateN * 53 ^ f * 151 ^ 1 = lateN * 151 ^ 1 * 53 ^ f := by ring
    rw [hc] at hrM ⊢
    exact not_weird_of_stepRowOK (S := 256030928920159929) (c := 2295) (g := 5) (q := 53) (r₀ := 2)
      (r₁ := 225) (e₀ := 2) (l := [(151, 1)]) (by norm_num) (by norm_num) hIG
      (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; norm_num) (by norm_num)
      (by decide +kernel) hf2 hr hrM hr.two_le
  · exact not_weird_of_quadOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 227)
      (f₀ := 2) (e₀ := 2) (by norm_num) (by norm_num) hIG (by norm_num) (by norm_num) (by decide +kernel)
      hf2 he2 hr hrM hr.two_le

/-- The Boolean of a whole bounded pair: the quadrant `f ≥ f₀, e ≥ e₀` (`quadOK`, end `r1q`), rows `f < f₀` (limit row
in `q` from `e0r f`, points `e < e0r f`), columns `e < e₀` (limit row in `p` from `f0c e`, points `f₀ ≤ f < f0c e`).
`r1 f 0` / `r1 0 e` are the ends of row `f` / column `e`, `r1 f e` (`f, e ≥ 1`) the end of the point `(f, e)`. -/
def boundedOK (n S c g p q r1q f₀ e₀ : ℕ) (e0r f0c : ℕ → ℕ) (r1 : ℕ → ℕ → ℕ) : Bool :=
  quadOK n S c g p q 2 r1q f₀ e₀ &&
    (List.range' 1 (f₀ - 1)).all (fun f =>
      stepRowOK n S c g q 2 (r1 f 0) (e0r f) [(p, f)] &&
        (List.range' 1 (e0r f - 1)).all (fun e => stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)])) &&
    (List.range' 1 (e₀ - 1)).all (fun e =>
      stepRowOK n S c g p 2 (r1 0 e) (f0c e) [(q, e)] &&
        (List.range' f₀ (f0c e - f₀)).all (fun f => stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)]))

/-- **A whole bounded pair from one Boolean.** -/
theorem not_weird_of_boundedOK {n S c g p q r1q f₀ e₀ f e r : ℕ} {e0r f0c : ℕ → ℕ} {r1 : ℕ → ℕ → ℕ}
    (hn : 0 < n) (hg : 1 ≤ g) (h : IntervalGap n S c g) (hp : p.Prime) (hq : q.Prime)
    (hok : boundedOK n S c g p q r1q f₀ e₀ e0r f0c r1 = true) (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ n * p ^ f * q ^ e) : ¬ (n * p ^ f * q ^ e * r).Weird := by
  simp only [boundedOK, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at hok
  obtain ⟨⟨hquad, hrows⟩, hcols⟩ := hok
  have hpq : ∀ s ∈ [(p, f), (q, e)], s.1.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hp, hq⟩
  have hpt : ∀ r₁, stepPointOK n S c g 2 r₁ [(p, f), (q, e)] = true → ¬ (n * p ^ f * q ^ e * r).Weird :=
    fun r₁ hpo => ErdosResearch.SubsetSumStairPoint.not_weird_of_stepPointOK hn hg h hpq hpo hr hrM hr.two_le
  by_cases hff : f < f₀
  · obtain ⟨hrow, hpts⟩ := hrows f ⟨hf, by omega⟩
    by_cases he0 : e < e0r f
    · exact hpt _ (hpts e ⟨he, by omega⟩)
    · have hp1 : ∀ s ∈ [(p, f)], s.1.Prime := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hp
      exact not_weird_of_stepRowOK hn hg h hp1 hq hrow (by omega) hr hrM hr.two_le
  · by_cases hee : e < e₀
    · obtain ⟨hcol, hpts⟩ := hcols e ⟨he, by omega⟩
      by_cases hf0 : f < f0c e
      · exact hpt _ (hpts f ⟨by omega, by omega⟩)
      · have hq1 : ∀ s ∈ [(q, e)], s.1.Prime := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hq
        have hx : n * q ^ e * p ^ f = n * p ^ f * q ^ e := by ring
        have hrM' : ¬ r ∣ (stepsEnd n S [(q, e)]).1 * p ^ f := by
          show ¬ r ∣ n * q ^ e * p ^ f
          rw [hx]; exact hrM
        have := not_weird_of_stepRowOK hn hg h hq1 hp hcol (by omega) hr hrM' hr.two_le
        change ¬ (n * q ^ e * p ^ f * r).Weird at this
        rwa [hx] at this
    · exact not_weird_of_quadOK hn hg h hp hq hquad (by omega) (by omega) hr hrM hr.two_le

/-- The pair `(53, 151)` again, from one Boolean (`f₀ = e₀ = 2`, row `f = 1` from `e = 2`, column `e = 1` from `f = 2`). -/
theorem not_weird_late_prefix_53_151' {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ lateN * 53 ^ f * 151 ^ e) : ¬ (lateN * 53 ^ f * 151 ^ e * r).Weird :=
  not_weird_of_boundedOK (S := 256030928920159929) (c := 2295) (g := 5) (r1q := 227) (f₀ := 2) (e₀ := 2)
    (e0r := fun _ => 2) (f0c := fun _ => 2)
    (r1 := fun f e => if f = 0 then 225 else if e = 0 then 210 else 208)
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by norm_num)
    (by decide +kernel) hf he hr hrM

end ErdosResearch.SubsetSumQuad
