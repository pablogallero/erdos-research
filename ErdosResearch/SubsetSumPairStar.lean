module

public import ErdosResearch.SubsetSumRowStar
public import ErdosResearch.SubsetSumPair

@[expose] public section

/-!
# Whole pairs with a star: every last prime power `r^k`

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 85).

Star versions of session 81's `pairOK` and session 83's `boundedOK`: the same lists, with `stepRowOK` → `stepRowStarOK`,
`quadOK` → `quadStarOK` (`SubsetSumRowStar`) and `stepPointOK` → `stepPointStarOK` (`SubsetSumPointStar`). Abundant
corners need no change (`not_weird_of_upset` allows any cofactor). Python (`scripts/star_row_probe.py ROWSTAR=1`, late
prefix): the row/quadrant Booleans hold on all 755 lines and 232 quadrants, and the point test (`firstOK`) holds at all
307 deficient points with an odd candidate (92 prime, 215 composite). Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumPairStar

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumStairPoint ErdosResearch.SubsetSumPointStar
  ErdosResearch.SubsetSumRowStar ErdosResearch.SubsetSumQuad

/-- Star version of `pairOK`. -/
def pairStarOK (n S c g p q F fr ec : ℕ) (e0 : ℕ → ℕ) (r1 : ℕ → ℕ → ℕ) (L : List ℕ) (fuel : ℕ) : Bool :=
  stepAbOK n S c g [(p, fr), (q, 1)] && stepAbOK n S c g [(p, F), (q, ec)] &&
    (List.range' 1 (F - 1)).all (fun f =>
      stepRowStarOK n S c g q 2 (r1 f 0) (e0 f) L [(p, f)] &&
        (List.range' 1 (e0 f - 1)).all (fun e => stepPointStarOK n S c g 2 (r1 f e) fuel [(p, f), (q, e)])) &&
    (List.range' F (fr - F)).all (fun f => (List.range' 1 (ec - 1)).all (fun e =>
      stepAbOK n S c g [(p, f), (q, e)] || stepPointStarOK n S c g 2 (r1 f e) fuel [(p, f), (q, e)]))

/-- **A whole pair, every last prime power.** -/
theorem not_weird_of_pairStarOK {n S c g p q F fr ec f e r k fuel : ℕ} {e0 : ℕ → ℕ} {r1 : ℕ → ℕ → ℕ}
    {L : List ℕ} (hn : 0 < n) (hg : 1 ≤ g) (h : IntervalGap n S c g) (hp : p.Prime) (hq : q.Prime)
    (hok : pairStarOK n S c g p q F fr ec e0 r1 L fuel = true) (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ n * p ^ f * q ^ e) (hk : 1 ≤ k) : ¬ (n * p ^ f * q ^ e * r ^ k).Weird := by
  simp only [pairStarOK, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true] at hok
  obtain ⟨⟨⟨hc1, hc2⟩, hcol⟩, hbox⟩ := hok
  have hpq : ∀ s ∈ [(p, f), (q, e)], s.1.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hp, hq⟩
  have hpt : ∀ r₁, stepPointStarOK n S c g 2 r₁ fuel [(p, f), (q, e)] = true →
      ¬ (n * p ^ f * q ^ e * r ^ k).Weird :=
    fun r₁ hpo => not_weird_of_stepPointStarOK hn hg h hpq hpo hr hrM hr.two_le hk
  have hcorner : ∀ f₀ e₀, stepAbOK n S c g [(p, f₀), (q, e₀)] = true → f₀ ≤ f → e₀ ≤ e →
      ¬ (n * p ^ f * q ^ e * r ^ k).Weird := fun f₀ e₀ ha h1 h2 => by
    have hpq' : ∀ s ∈ [(p, f₀), (q, e₀)], s.1.Prime := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hp, hq⟩
    exact not_weird_of_upset hp.pos hq.pos (pseudoperfect_of_stepAbOK hn hg h hpq' ha) h1 h2 (pow_pos hr.pos k)
  by_cases hfF : f < F
  · obtain ⟨hrow, hpts⟩ := hcol f ⟨hf, by omega⟩
    by_cases he0 : e < e0 f
    · exact hpt _ (hpts e ⟨he, by omega⟩)
    · have hp1 : ∀ s ∈ [(p, f)], s.1.Prime := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hp
      exact not_weird_of_stepRowStarOK hn hg h hp1 hq hrow (by omega) hr hrM hr.two_le hk
  · by_cases hfr : fr ≤ f
    · exact hcorner fr 1 hc1 hfr he
    · by_cases hec : ec ≤ e
      · exact hcorner F ec hc2 (by omega) hec
      · rcases hbox f ⟨by omega, by omega⟩ e ⟨he, by omega⟩ with ha | hpo
        · exact hcorner f e ha le_rfl le_rfl
        · exact hpt _ hpo

/-- Star version of `boundedOK`. -/
def boundedStarOK (n S c g p q r1q f₀ e₀ : ℕ) (e0r f0c : ℕ → ℕ) (r1 : ℕ → ℕ → ℕ) (L : List ℕ) (fuel : ℕ) :
    Bool :=
  quadStarOK n S c g p q 2 r1q f₀ e₀ L &&
    (List.range' 1 (f₀ - 1)).all (fun f =>
      stepRowStarOK n S c g q 2 (r1 f 0) (e0r f) L [(p, f)] &&
        (List.range' 1 (e0r f - 1)).all (fun e => stepPointStarOK n S c g 2 (r1 f e) fuel [(p, f), (q, e)])) &&
    (List.range' 1 (e₀ - 1)).all (fun e =>
      stepRowStarOK n S c g p 2 (r1 0 e) (f0c e) L [(q, e)] &&
        (List.range' f₀ (f0c e - f₀)).all (fun f => stepPointStarOK n S c g 2 (r1 f e) fuel [(p, f), (q, e)]))

/-- **A whole bounded pair, every last prime power.** -/
theorem not_weird_of_boundedStarOK {n S c g p q r1q f₀ e₀ f e r k fuel : ℕ} {e0r f0c : ℕ → ℕ}
    {r1 : ℕ → ℕ → ℕ} {L : List ℕ} (hn : 0 < n) (hg : 1 ≤ g) (h : IntervalGap n S c g) (hp : p.Prime)
    (hq : q.Prime) (hok : boundedStarOK n S c g p q r1q f₀ e₀ e0r f0c r1 L fuel = true) (hf : 1 ≤ f)
    (he : 1 ≤ e) (hr : r.Prime) (hrM : ¬ r ∣ n * p ^ f * q ^ e) (hk : 1 ≤ k) :
    ¬ (n * p ^ f * q ^ e * r ^ k).Weird := by
  simp only [boundedStarOK, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1] at hok
  obtain ⟨⟨hquad, hrows⟩, hcols⟩ := hok
  have hpq : ∀ s ∈ [(p, f), (q, e)], s.1.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hp, hq⟩
  have hpt : ∀ r₁, stepPointStarOK n S c g 2 r₁ fuel [(p, f), (q, e)] = true →
      ¬ (n * p ^ f * q ^ e * r ^ k).Weird :=
    fun r₁ hpo => not_weird_of_stepPointStarOK hn hg h hpq hpo hr hrM hr.two_le hk
  by_cases hff : f < f₀
  · obtain ⟨hrow, hpts⟩ := hrows f ⟨hf, by omega⟩
    by_cases he0 : e < e0r f
    · exact hpt _ (hpts e ⟨he, by omega⟩)
    · have hp1 : ∀ s ∈ [(p, f)], s.1.Prime := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hp
      exact not_weird_of_stepRowStarOK hn hg h hp1 hq hrow (by omega) hr hrM hr.two_le hk
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
        have := not_weird_of_stepRowStarOK hn hg h hq1 hp hcol (by omega) hr hrM' hr.two_le hk
        change ¬ (n * q ^ e * p ^ f * r ^ k).Weird at this
        rwa [hx] at this
    · exact not_weird_of_quadStarOK hn hg h hp hq hquad (by omega) (by omega) hr hrM hr.two_le hk

/-- **Instance (pair).** The pair `(37, 307)` below the late prefix (session 81's `not_weird_late_prefix_pairOK`), now
for every power: no `n·37^f·307^e·r^k` is weird (`f, e, k ≥ 1`, `r` prime). Row candidate `7197 = 3·2399` (skipS),
point candidates `6687` (`firstOK`) and `7196` (even). -/
theorem not_weird_late_prefix_pairStarOK {f e r k : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 307 ^ e) (hk : 1 ≤ k) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 307 ^ e * r ^ k).Weird :=
  not_weird_of_pairStarOK (S := 256030928920159929) (c := 2295) (g := 5) (F := 2) (fr := 2) (ec := 1)
    (e0 := fun _ => 3) (r1 := fun _ e => if e = 0 then 7196 else if e = 1 then 6686 else 7195) (L := [3]) (fuel := 4)
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by norm_num)
    (by decide +kernel) hf he hr hrM hk

/-- **Instance (bounded pair).** The pair `(53, 151)` (session 83's `not_weird_late_prefix_53_151'`), now for every
power: no `n·53^f·151^e·r^k` is weird (`f, e, k ≥ 1`, `r` prime). -/
theorem not_weird_late_prefix_53_151_star {f e r k : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ lateN * 53 ^ f * 151 ^ e) (hk : 1 ≤ k) : ¬ (lateN * 53 ^ f * 151 ^ e * r ^ k).Weird :=
  not_weird_of_boundedStarOK (S := 256030928920159929) (c := 2295) (g := 5) (r1q := 227) (f₀ := 2) (e₀ := 2)
    (e0r := fun _ => 2) (f0c := fun _ => 2)
    (r1 := fun f e => if f = 0 then 225 else if e = 0 then 210 else 208) (L := [3, 5, 7, 11, 13]) (fuel := 8)
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by norm_num)
    (by decide +kernel) hf he hr hrM hk

end ErdosResearch.SubsetSumPairStar
