module

public import ErdosResearch.SubsetSumPointStar
public import ErdosResearch.SubsetSumRow
public import ErdosResearch.SubsetSumStrip
public import ErdosResearch.SubsetSumQuad

@[expose] public section

/-!
# A limit row, every last prime power at once (stars `r^k` on a whole row)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 85).

Session 81's `rowOK m S c g q r₀ r₁ e₀` decides `m q^e r` for every `e ≥ e₀` and every prime `r ≥ r₀`. At every point
`M = m q^e` of the row it gives session 79's `pointOK M _ c g r₀ r₁` with the SAME `r₁` (`pointOK_of_rowOK`). As in
session 84, every prime `r ≠ r₁ + 1` is then decided for every power `r^k` (`not_weird_pow_of_pointOK`: `r ≤ r₁` is
certified at `k = 1` and stays certified; `r ≥ r₁ + 2` is never abundant). So only ONE candidate `R = r₁ + 1` is left,
for the whole row. The Python measurement `scripts/star_row_probe.py` (late prefix: 755 lines) shows that the star-only
prime of every point of a row is already `⌈L⌉` = `r₁ + 1` at the start `e₀` (0 transient points). `rowStarOK` then
needs one of:
* `R` even and `> 2`, or `R ∣ m` or `R = q` (excluded by `r ∤ m q^e`), or `skipS R L` (composite);
* `stepAbOK m S c g [(q, e₀), (R, 2)]`: the corner `m q^{e₀} R²` is pseudoperfect, so every `m q^e R^k` with `e ≥ e₀`
  and `k ≥ 2` is not weird (`not_weird_of_upset`); `k = 1` is `rowOK`.

`not_weird_of_rowStarOK`: `¬ (m q^e r^k).Weird` for every `e ≥ e₀`, every prime `r ≥ r₀` with `r ∤ m q^e`, and every
`k ≥ 1`; `not_weird_of_stepRowStarOK` is the same after a list of prime-power steps.

Quadrants (session 83's `quadOK`, bounded pairs) work the same way: `quadOK` gives a `rowOK` for every prefix `n p^f`
(`f ≥ f₀`) with the quadrant's `r₁` (`rowOK_of_quadOK`), and `quadStarOK` adds the same candidate test with the corner
`n p^{f₀} q^{e₀} R²` (`not_weird_of_quadStarOK`). Python (late prefix, `scripts/star_row_probe.py ROWSTAR=1`): the
Booleans hold on all 755 rows/columns and all 232 quadrants of sessions 82–83. Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumRowStar

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPoint ErdosResearch.SubsetSumStairPoint
  ErdosResearch.SubsetSumPointStar ErdosResearch.SubsetSumRow ErdosResearch.SubsetSumStrip ErdosResearch.SubsetSumQuad

/-- `pointOK` decides every prime power `M r^k` except possibly the candidate `r = r₁ + 1`, which is left to `hcand`. -/
theorem not_weird_pow_of_pointOK {M S c g r₀ r₁ r k : ℕ} (hM : 0 < M) (hg : 1 ≤ g)
    (h : IntervalGap M S c g) (hok : pointOK M S c g r₀ r₁ = true) (hr : r.Prime) (hrM : ¬ r ∣ M)
    (hr₀ : r₀ ≤ r) (hk : 1 ≤ k) (hcand : r = r₁ + 1 → ¬ (M * r ^ k).Weird) : ¬ (M * r ^ k).Weird := by
  by_cases hR : r = r₁ + 1
  · exact hcand hR
  simp only [pointOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hSM, hab⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  have hsum := ppSum_eq hM hr hrM h.1 k
  have hr1 : 1 ≤ r := hr.one_lt.le
  rintro ⟨habund, hnot⟩
  unfold Nat.Abundant at habund
  rw [hsum] at habund
  have finish : r * g + 2 * c ≤ S + 1 → c ≤ M * r ^ k → M * r ^ k + c ≤ ppSum M r S k → False := by
    intro s1 c1 c2
    have e3 : (r₀ + 1) * S ≤ (r + 1) * S := Nat.mul_le_mul_right S (by omega)
    exact hnot (ErdosResearch.SubsetSumUniform.pseudoperfect_mul_prime_pow_of_intervalGap hM hg h hr hrM s1
      (by omega) k c1 c2)
  obtain ⟨D, rfl⟩ : ∃ D, M = S + D := ⟨M - S, by omega⟩
  have hD : S + D - S = D := by omega
  rw [hD] at hab h2
  rcases Nat.lt_or_ge r (r₁ + 1) with hlt | hge
  · have e1 : r * g ≤ r₁ * g := Nat.mul_le_mul_right g (by omega)
    have e2 : r * D ≤ r₁ * D := Nat.mul_le_mul_right D (by omega)
    have e4 : (S + D) * r₀ ≤ (S + D) * r := Nat.mul_le_mul_left _ hr₀
    have c1 : c ≤ (S + D) * r ^ 1 := by rw [pow_one]; omega
    have c2 : (S + D) * r ^ 1 + c ≤ ppSum (S + D) r S 1 := by
      simp only [pow_one, ppSum]
      have : (S + D) * r = r * S + r * D := by ring
      omega
    obtain ⟨j, rfl⟩ : ∃ j, k = 1 + j := ⟨k - 1, by omega⟩
    obtain ⟨d1, d2⟩ := cert_mono hr1 c1 c2 j
    exact finish (by omega) d1 d2
  rcases Nat.eq_or_lt_of_le hge with heq | hfar
  · exact hR heq.symm
  · obtain ⟨a, rfl⟩ : ∃ a, r = a + 1 := ⟨r - 1, by omega⟩
    have hAD : 2 * S + D ≤ a * D := by
      have : (r₁ + 1) * D ≤ a * D := Nat.mul_le_mul_right D (by omega)
      omega
    have hinv : (S + ((S + D) + (a + 1) * S)) * a + (S + (S + D)) ≤ (S + D) * (a + 1) * a := by
      have := Nat.mul_le_mul_left a hAD
      nlinarith
    have := not_abundant_of_far hinv (by omega) k hk
    omega

/-- Every point of a `rowOK` row satisfies `pointOK` with the row's `r₁`. -/
theorem pointOK_of_rowOK {m S c g q r₀ r₁ e₀ e : ℕ} (hm : 0 < m) (hq : q.Prime)
    (hok : rowOK m S c g q r₀ r₁ e₀ = true) (he : e₀ ≤ e) :
    pointOK (m * q ^ e) (ppSum m q S e) c g r₀ r₁ = true := by
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hc, _⟩, _⟩, _⟩, hlim⟩, i1⟩, i2⟩, i3⟩, i4⟩ := hok
  obtain ⟨j1, j2, j3, j4⟩ := rowInv_of_le hc hq.one_lt.le ⟨i1, i2, i3, i4⟩ e he
  have hlt := total_lt_of_limit hm hq.two_le hlim e
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
  exact ⟨⟨⟨⟨⟨by omega, by linarith⟩, j1⟩, by linarith⟩, by linarith⟩, j4⟩

/-- `rowOK` plus the row's single star-only candidate `R = r₁ + 1`. -/
def rowStarOK (m S c g q r₀ r₁ e₀ : ℕ) (L : List ℕ) : Bool :=
  rowOK m S c g q r₀ r₁ e₀ &&
    ((decide ((r₁ + 1) % 2 = 0) && decide (2 < r₁ + 1)) || decide (m % (r₁ + 1) = 0) || skipS (r₁ + 1) L ||
      stepAbOK m S c g [(q, e₀), (r₁ + 1, 2)] || (decide (r₁ + 1 = q) && decide (1 ≤ e₀)))

/-- **A whole limit row, every last prime power.** -/
theorem not_weird_of_rowStarOK {m S c g q r₀ r₁ e₀ e r k : ℕ} {L : List ℕ} (hm : 0 < m) (hg : 1 ≤ g)
    (h : IntervalGap m S c g) (hq : q.Prime) (hok : rowStarOK m S c g q r₀ r₁ e₀ L = true) (he : e₀ ≤ e)
    (hr : r.Prime) (hrM : ¬ r ∣ m * q ^ e) (hr₀ : r₀ ≤ r) (hk : 1 ≤ k) : ¬ (m * q ^ e * r ^ k).Weird := by
  simp only [rowStarOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hrow, hstar⟩ := hok
  have hrow' := hrow
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hqm⟩, hs1⟩, hs2⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hrow'
  have hqm' : ¬ q ∣ m := fun hd => hqm (Nat.mod_eq_zero_of_dvd hd)
  have hIG := ErdosResearch.SubsetSumUniform.intervalGap_mul_prime_pow hm hg h hq hqm' hs1 hs2 e
  refine not_weird_pow_of_pointOK (Nat.mul_pos hm (pow_pos hq.pos e)) hg hIG (pointOK_of_rowOK hm hq hrow he)
    hr hrM hr₀ hk ?_
  rintro rfl
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    rw [pow_one]
    exact not_weird_of_rowOK hm hg h hq hrow he hr hrM hr₀
  rcases hstar with (((⟨hev, h2lt⟩ | hdiv) | hskip) | hab) | ⟨hRq, he₀⟩
  · exact absurd (hr.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev)) (by omega)
  · exact absurd (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hdiv) _) hrM
  · rw [prime_imp_not_skipS hr] at hskip
    exact absurd hskip (by decide)
  · have hpr : ∀ s ∈ [(q, e₀), (r₁ + 1, 2)], s.1.Prime := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hq, hr⟩
    have hps := pseudoperfect_of_stepAbOK hm hg h hpr hab
    have hend : (stepsEnd m S [(q, e₀), (r₁ + 1, 2)]).1 = m * q ^ e₀ * (r₁ + 1) ^ 2 := rfl
    rw [hend] at hps
    have := not_weird_of_upset (m := 1) hq.pos hr.pos hps he hk2 one_pos
    simpa using this
  · have hdq : r₁ + 1 ∣ m * q ^ e := by
      rw [hRq]; exact Dvd.dvd.mul_left (dvd_pow_self q (by omega : e ≠ 0)) m
    exact absurd hdq hrM

/-- Star row after prime-power steps from a prefix certificate. -/
def stepRowStarOK (n S c g q r₀ r₁ e₀ : ℕ) (L : List ℕ) (l : List (ℕ × ℕ)) : Bool :=
  stepsOK c g n S l && rowStarOK (stepsEnd n S l).1 (stepsEnd n S l).2 c g q r₀ r₁ e₀ L

/-- **A whole limit row below a prefix, every last prime power.** -/
theorem not_weird_of_stepRowStarOK {n S c g q r₀ r₁ e₀ e r k : ℕ} {L : List ℕ} {l : List (ℕ × ℕ)} (hn : 0 < n)
    (hg : 1 ≤ g) (h : IntervalGap n S c g) (hpr : ∀ s ∈ l, s.1.Prime) (hq : q.Prime)
    (hok : stepRowStarOK n S c g q r₀ r₁ e₀ L l = true) (he : e₀ ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ (stepsEnd n S l).1 * q ^ e) (hr₀ : r₀ ≤ r) (hk : 1 ≤ k) :
    ¬ ((stepsEnd n S l).1 * q ^ e * r ^ k).Weird := by
  simp only [stepRowStarOK, Bool.and_eq_true] at hok
  exact not_weird_of_rowStarOK (stepsEnd_pos l n S hn hpr) hg (intervalGap_of_stepsOK hg l n S hn hpr hok.1 h)
    hq hok.2 he hr hrM hr₀ hk

/-- **Instance (prime candidate).** Below the late prefix `n = 3^3·23·13^10·17^2·11`, the row `n·37·349^e` (`e ≥ 2`,
from session 82's `pairOK (37, 349)`, `r₁ = 1878`): the candidate `R = 1879` is prime, `n·37·349²·1879²` is
pseudoperfect, so no `n·37·349^e·r^k` is weird, for every `e ≥ 2`, every prime `r`, every `k ≥ 1`. -/
theorem not_weird_late_prefix_37_349_row_pow {e r k : ℕ} (he : 2 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 349 ^ e) (hk : 1 ≤ k) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 349 ^ e * r ^ k).Weird :=
  not_weird_of_stepRowStarOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 1878) (e₀ := 2)
    (L := []) (l := [(37, 1)]) (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; norm_num) (by norm_num)
    (by decide +kernel) he hr hrM hr.two_le hk

/-- **Instance (composite candidate).** The row `n·37·307^e` (`e ≥ 3`, session 81, `r₁ = 7196`): `R = 7197 = 3·2399`
is skipped by `skipS`, so no `n·37·307^e·r^k` is weird for `e ≥ 3`, every prime `r`, every `k ≥ 1`. -/
theorem not_weird_late_prefix_37_307_row_pow {e r k : ℕ} (he : 3 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ e) (hk : 1 ≤ k) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ e * r ^ k).Weird :=
  not_weird_of_stepRowStarOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 7196) (e₀ := 3)
    (L := [3]) (l := [(37, 1)]) (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; norm_num) (by norm_num)
    (by decide +kernel) he hr hrM hr.two_le hk

/-- `quadOK` gives a `rowOK` (along `q`, from `e₀`) for every prefix `n p^f` with `f ≥ f₀` and the same `r₁`. -/
theorem rowOK_of_quadOK {n S c g p q r₀ r₁ f₀ e₀ f : ℕ} (hn : 0 < n) (h : IntervalGap n S c g) (hp : p.Prime)
    (hq : q.Prime) (hok : quadOK n S c g p q r₀ r₁ f₀ e₀ = true) (hf : f₀ ≤ f) :
    rowOK (n * p ^ f) (ppSum n p S f) c g q r₀ r₁ e₀ = true := by
  simp only [quadOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hc, hpn⟩, hqn⟩, hpq⟩, _⟩, _⟩, hq1⟩, hq2⟩, hlim⟩, i1⟩, i2⟩, i3⟩, i4⟩ := hok
  have hpn' : ¬ p ∣ n := fun hd => hpn (Nat.mod_eq_zero_of_dvd hd)
  have hqn' : ¬ q ∣ n := fun hd => hqn (Nat.mod_eq_zero_of_dvd hd)
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
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq]
  refine ⟨⟨⟨⟨⟨⟨⟨⟨hc, hqm⟩, ?_⟩, step2_mono hc hp.one_lt.le hq2 f hf⟩, ?_⟩, j1⟩, j2⟩, j3⟩, j4⟩
  · exact le_trans hq1 (Nat.add_le_add_right (ppSum_mono hp.one_lt.le f hf) 1)
  · exact row_limit hp.two_le hlim f

/-- `quadOK` plus the quadrant's single star-only candidate `R = r₁ + 1`. -/
def quadStarOK (n S c g p q r₀ r₁ f₀ e₀ : ℕ) (L : List ℕ) : Bool :=
  quadOK n S c g p q r₀ r₁ f₀ e₀ &&
    ((decide ((r₁ + 1) % 2 = 0) && decide (2 < r₁ + 1)) || decide (n % (r₁ + 1) = 0) || skipS (r₁ + 1) L ||
      stepAbOK n S c g [(p, f₀), (q, e₀), (r₁ + 1, 2)])

/-- **A whole quadrant of a bounded pair, every last prime power.** -/
theorem not_weird_of_quadStarOK {n S c g p q r₀ r₁ f₀ e₀ f e r k : ℕ} {L : List ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hp : p.Prime) (hq : q.Prime)
    (hok : quadStarOK n S c g p q r₀ r₁ f₀ e₀ L = true) (hf : f₀ ≤ f) (he : e₀ ≤ e)
    (hr : r.Prime) (hrM : ¬ r ∣ n * p ^ f * q ^ e) (hr₀ : r₀ ≤ r) (hk : 1 ≤ k) :
    ¬ (n * p ^ f * q ^ e * r ^ k).Weird := by
  simp only [quadStarOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨hquad, hstar⟩ := hok
  have hrow := rowOK_of_quadOK hn h hp hq hquad hf
  have hquad' := hquad
  simp only [quadOK, Bool.and_eq_true, decide_eq_true_eq] at hquad'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, hpn⟩, _⟩, _⟩, hp1⟩, hp2⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hquad'
  have hpn' : ¬ p ∣ n := fun hd => hpn (Nat.mod_eq_zero_of_dvd hd)
  have hIG := ErdosResearch.SubsetSumUniform.intervalGap_mul_prime_pow hn hg h hp hpn' hp1 hp2 f
  have hm : 0 < n * p ^ f := Nat.mul_pos hn (pow_pos hp.pos f)
  have hrow' := hrow
  simp only [rowOK, Bool.and_eq_true, decide_eq_true_eq] at hrow'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨_, hqm⟩, hs1⟩, hs2⟩, _⟩, _⟩, _⟩, _⟩, _⟩ := hrow'
  have hqm' : ¬ q ∣ n * p ^ f := fun hd => hqm (Nat.mod_eq_zero_of_dvd hd)
  have hIG2 := ErdosResearch.SubsetSumUniform.intervalGap_mul_prime_pow hm hg hIG hq hqm' hs1 hs2 e
  refine not_weird_pow_of_pointOK (Nat.mul_pos hm (pow_pos hq.pos e)) hg hIG2 (pointOK_of_rowOK hm hq hrow he)
    hr hrM hr₀ hk ?_
  rintro rfl
  rcases Nat.lt_or_ge k 2 with hk1 | hk2
  · obtain rfl : k = 1 := by omega
    rw [pow_one]
    exact not_weird_of_quadOK hn hg h hp hq hquad hf he hr hrM hr₀
  rcases hstar with ((⟨hev, h2lt⟩ | hdiv) | hskip) | hab
  · exact absurd (hr.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev)) (by omega)
  · exact absurd (Dvd.dvd.mul_right (Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero hdiv) _) _) hrM
  · rw [prime_imp_not_skipS hr] at hskip
    exact absurd hskip (by decide)
  · have hpr : ∀ s ∈ [(p, f₀), (q, e₀), (r₁ + 1, 2)], s.1.Prime := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]
      exact ⟨hp, hq, hr⟩
    have hps := pseudoperfect_of_stepAbOK hn hg h hpr hab
    have hend : (stepsEnd n S [(p, f₀), (q, e₀), (r₁ + 1, 2)]).1 = n * p ^ f₀ * q ^ e₀ * (r₁ + 1) ^ 2 := rfl
    rw [hend] at hps
    have hpos : 0 < n * p ^ f * q ^ e * (r₁ + 1) ^ k :=
      Nat.mul_pos (Nat.mul_pos hm (pow_pos hq.pos e)) (pow_pos (by omega) k)
    have hd : n * p ^ f₀ * q ^ e₀ * (r₁ + 1) ^ 2 ∣ n * p ^ f * q ^ e * (r₁ + 1) ^ k :=
      mul_dvd_mul (mul_dvd_mul (mul_dvd_mul_left n (pow_dvd_pow p hf)) (pow_dvd_pow q he)) (pow_dvd_pow _ hk2)
    exact fun hw => hw.2 (hps.of_dvd hd hpos)

/-- **Instance (quadrant, prime candidate).** Below the late prefix, the bounded pair `(37, 449)`: quadrant `f ≥ 5`,
`e ≥ 3`, `r₁ = 2266`; `R = 2267` is prime and the corner `n·37⁵·449³·2267²` is pseudoperfect. -/
theorem not_weird_late_prefix_37_449_quad_pow {f e r k : ℕ} (hf : 5 ≤ f) (he : 3 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ lateN * 37 ^ f * 449 ^ e) (hk : 1 ≤ k) : ¬ (lateN * 37 ^ f * 449 ^ e * r ^ k).Weird :=
  not_weird_of_quadStarOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 2266) (f₀ := 5) (e₀ := 3)
    (L := []) (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num)
    (by norm_num) (by decide +kernel) hf he hr hrM hr.two_le hk

/-- **Instance (quadrant, composite candidate).** The bounded pair `(37, 389)`: quadrant `f ≥ 5`, `e ≥ 3`,
`r₁ = 10324`; `R = 10325 = 5²·7·59` is skipped. -/
theorem not_weird_late_prefix_37_389_quad_pow {f e r k : ℕ} (hf : 5 ≤ f) (he : 3 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ lateN * 37 ^ f * 389 ^ e) (hk : 1 ≤ k) : ¬ (lateN * 37 ^ f * 389 ^ e * r ^ k).Weird :=
  not_weird_of_quadStarOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 10324) (f₀ := 5)
    (e₀ := 3) (L := [5]) (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by norm_num) (by norm_num) (by decide +kernel) hf he hr hrM hr.two_le hk

end ErdosResearch.SubsetSumRowStar
