module

public import ErdosResearch.SubsetSumRow

@[expose] public section

/-!
# A whole pair `(p, q)` of the staircase from one Boolean (shape `e_inf = 1`)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 81).

Below a prefix `n` with `IntervalGap n S c g`, the staircase decider (`scripts/plimit_probe.py`, `stair`) closes a pair of
primes `(p, q)` with a free last prime `r`. Session 81 measured the shapes `(e_inf, f_inf)` on real prefixes: almost all
pairs have `e_inf = 1` (no limit row in `e`). For that shape, with `F = f_inf`:

* columns `f < F` (`n p^f` limit-deficient in `q`): finitely many points `e < e₀(f)` (`stepPointOK`) and the limit row
  `e ≥ e₀(f)` (`stepRowOK`);
* two pseudoperfect corners `(f_r, 1)` and `(F, e_c)` (`stepAbOK`), whose up-sets cover `f ≥ f_r` and `f ≥ F, e ≥ e_c`;
* the finite box `[F, f_r) × [1, e_c)`, point by point (abundant with interval, or deficient with `pointOK`).

`pairOK` is that Boolean (the per-point `r₁` come from a table `r1`), and `not_weird_of_pairOK` gives
`¬ (n p^f q^e r).Weird` for ALL `f, e ≥ 1` and every prime `r ≥ 2`, `r ∤ n p^f q^e`. Stars `r^h` (`h ≥ 2`) are not covered.
Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumPair

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPoint ErdosResearch.SubsetSumStairPoint
  ErdosResearch.SubsetSumRow

/-- The Boolean of a pair of shape `e_inf = 1`. `r1 f e` is the `r₁` of the deficient point `(f, e)`; `r1 f 0` and
`e0 f` are the `r₁` and the start of the limit row of column `f < F`. -/
def pairOK (n S c g p q F fr ec : ℕ) (e0 : ℕ → ℕ) (r1 : ℕ → ℕ → ℕ) : Bool :=
  stepAbOK n S c g [(p, fr), (q, 1)] && stepAbOK n S c g [(p, F), (q, ec)] &&
    (List.range' 1 (F - 1)).all (fun f =>
      stepRowOK n S c g q 2 (r1 f 0) (e0 f) [(p, f)] &&
        (List.range' 1 (e0 f - 1)).all (fun e => stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)])) &&
    (List.range' F (fr - F)).all (fun f => (List.range' 1 (ec - 1)).all (fun e =>
      stepAbOK n S c g [(p, f), (q, e)] || stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)]))

theorem stepsEnd_two (n S p f q e : ℕ) : (stepsEnd n S [(p, f), (q, e)]).1 = n * p ^ f * q ^ e := rfl

theorem stepsEnd_one (n S p f : ℕ) : (stepsEnd n S [(p, f)]).1 = n * p ^ f := rfl

/-- **A whole pair.** -/
theorem not_weird_of_pairOK {n S c g p q F fr ec f e r : ℕ} {e0 : ℕ → ℕ} {r1 : ℕ → ℕ → ℕ} (hn : 0 < n)
    (hg : 1 ≤ g) (h : IntervalGap n S c g) (hp : p.Prime) (hq : q.Prime)
    (hok : pairOK n S c g p q F fr ec e0 r1 = true) (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ n * p ^ f * q ^ e) : ¬ (n * p ^ f * q ^ e * r).Weird := by
  simp only [pairOK, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true] at hok
  obtain ⟨⟨⟨hc1, hc2⟩, hcol⟩, hbox⟩ := hok
  have hpq : ∀ s ∈ [(p, f), (q, e)], s.1.Prime := by
    simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hp, hq⟩
  have hpt : ∀ r₁, stepPointOK n S c g 2 r₁ [(p, f), (q, e)] = true → ¬ (n * p ^ f * q ^ e * r).Weird :=
    fun r₁ hpo => not_weird_of_stepPointOK hn hg h hpq hpo hr hrM hr.two_le
  have hab : stepAbOK n S c g [(p, f), (q, e)] = true → ¬ (n * p ^ f * q ^ e * r).Weird := fun ha =>
    not_weird_of_upset (f₀ := f) (e₀ := e) hp.pos hq.pos (pseudoperfect_of_stepAbOK hn hg h hpq ha) le_rfl le_rfl
      hr.pos
  have hcorner : ∀ f₀ e₀, stepAbOK n S c g [(p, f₀), (q, e₀)] = true → f₀ ≤ f → e₀ ≤ e →
      ¬ (n * p ^ f * q ^ e * r).Weird := fun f₀ e₀ ha h1 h2 => by
    have hpq' : ∀ s ∈ [(p, f₀), (q, e₀)], s.1.Prime := by
      simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; exact ⟨hp, hq⟩
    exact not_weird_of_upset hp.pos hq.pos (pseudoperfect_of_stepAbOK hn hg h hpq' ha) h1 h2 hr.pos
  by_cases hfF : f < F
  · obtain ⟨hrow, hpts⟩ := hcol f ⟨hf, by omega⟩
    by_cases he0 : e < e0 f
    · exact hpt _ (hpts e ⟨he, by omega⟩)
    · have hp1 : ∀ s ∈ [(p, f)], s.1.Prime := by
        simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hp
      exact not_weird_of_stepRowOK hn hg h hp1 hq hrow (by omega) hr hrM hr.two_le
  · by_cases hfr : fr ≤ f
    · exact hcorner fr 1 hc1 hfr he
    · by_cases hec : ec ≤ e
      · exact hcorner F ec hc2 (by omega) hec
      · rcases hbox f ⟨by omega, by omega⟩ e ⟨he, by omega⟩ with ha | hpo
        · exact hab ha
        · exact hpt _ hpo

/-- **Instance.** The pair `(37, 307)` below the late prefix (session 81, `not_weird_late_prefix_pair_all`) again, now
from one Boolean: `F = 2`, corners `(2, 1)` and `(2, 1)`, column `f = 1` with points `e = 1, 2` and the row from `e₀ = 3`. -/
theorem not_weird_late_prefix_pairOK {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 307 ^ e) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 307 ^ e * r).Weird :=
  not_weird_of_pairOK (S := 256030928920159929) (c := 2295) (g := 5) (F := 2) (fr := 2) (ec := 1)
    (e0 := fun _ => 3) (r1 := fun _ e => if e = 0 then 7196 else if e = 1 then 6686 else 7195)
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by norm_num)
    (by decide +kernel) hf he hr hrM

/-- **Instance (another shape).** The pair `(41, 167)` below the late prefix: no limit column (`F = 1`), corners
`(2, 1)` and `(1, 2)`, and one deficient box point `(1, 1)` with `r₁ = 472739`. So no `n·41^f·167^e·r` is weird
(`f, e ≥ 1`, `r` prime). Found by a throwaway scan (`/tmp`), checked here by the kernel. -/
theorem not_weird_late_prefix_pairOK_41_167 {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 41 ^ f * 167 ^ e) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 41 ^ f * 167 ^ e * r).Weird :=
  not_weird_of_pairOK (S := 256030928920159929) (c := 2295) (g := 5) (F := 1) (fr := 2) (ec := 2)
    (e0 := fun _ => 1) (r1 := fun _ _ => 472739)
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by norm_num) (by norm_num)
    (by decide +kernel) hf he hr hrM

end ErdosResearch.SubsetSumPair
