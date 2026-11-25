module

public import ErdosResearch.SubsetSumPair
public import ErdosResearch.OddWeirdPrefixIG

@[expose] public section

/-!
# A whole pair `(p, q)` of the staircase, shape `e_inf ≥ 1` (generalises `pairOK`)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 87).

`SubsetSumPair.pairOK` needs the row `e = 1` to stop being limit-deficient in `p` (shape `e_inf = 1`). The cost census of
session 87 found pairs with `e_inf ≥ 2` in about half of the sampled real prefixes (one or two per prefix). `pairOK2` adds a
start row `er`:

* columns `f < F` as in `pairOK` (limit rows in `q`);
* rows `e < er` for `f ≥ F` (`n q^e` limit-deficient in `p`): points `F ≤ f < f₀(e)` (`stepPointOK`) and the limit row
  `f ≥ f₀(e)` (`stepRowOK` with the roles of `p` and `q` swapped);
* two pseudoperfect corners `(fr, er)` and `(F, ec)`;
* the finite box `[F, fr) × [er, ec)`.

With `er = 1` it is `pairOK`. `not_weird_of_pairOK2`: `¬ (n p^f q^e r).Weird` for ALL `f, e ≥ 1` and every prime `r`,
`r ∤ n p^f q^e`. Stars `r^h` (`h ≥ 2`) are not covered. Elementary; new only as a formalisation.
-/

set_option Elab.async false

namespace ErdosResearch.SubsetSumPair2

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPoint ErdosResearch.SubsetSumStairPoint
  ErdosResearch.SubsetSumRow ErdosResearch.SubsetSumPair

/-- The Boolean of a pair with start row `er`. `r1 f e` is the `r₁` of the deficient point `(f, e)`; `r1 f 0`/`e0 f`
belong to the limit row of column `f < F`, and `r1 0 e`/`f0 e` to the limit row (in `p`) of row `e < er`. -/
def pairOK2 (n S c g p q F fr er ec : ℕ) (e0 f0 : ℕ → ℕ) (r1 : ℕ → ℕ → ℕ) : Bool :=
  stepAbOK n S c g [(p, fr), (q, er)] && stepAbOK n S c g [(p, F), (q, ec)] &&
    (List.range' 1 (F - 1)).all (fun f =>
      stepRowOK n S c g q 2 (r1 f 0) (e0 f) [(p, f)] &&
        (List.range' 1 (e0 f - 1)).all (fun e => stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)])) &&
    (List.range' 1 (er - 1)).all (fun e =>
      stepRowOK n S c g p 2 (r1 0 e) (f0 e) [(q, e)] &&
        (List.range' F (f0 e - F)).all (fun f => stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)])) &&
    (List.range' F (fr - F)).all (fun f => (List.range' er (ec - er)).all (fun e =>
      stepAbOK n S c g [(p, f), (q, e)] || stepPointOK n S c g 2 (r1 f e) [(p, f), (q, e)]))

/-- **A whole pair, any start row.** -/
theorem not_weird_of_pairOK2 {n S c g p q F fr er ec f e r : ℕ} {e0 f0 : ℕ → ℕ} {r1 : ℕ → ℕ → ℕ} (hn : 0 < n)
    (hg : 1 ≤ g) (h : IntervalGap n S c g) (hp : p.Prime) (hq : q.Prime)
    (hok : pairOK2 n S c g p q F fr er ec e0 f0 r1 = true) (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ n * p ^ f * q ^ e) : ¬ (n * p ^ f * q ^ e * r).Weird := by
  simp only [pairOK2, Bool.and_eq_true, List.all_eq_true, List.mem_range'_1, Bool.or_eq_true] at hok
  obtain ⟨⟨⟨⟨hc1, hc2⟩, hcol⟩, hrows⟩, hbox⟩ := hok
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
  · by_cases her : e < er
    · obtain ⟨hrow, hpts⟩ := hrows e ⟨he, by omega⟩
      by_cases hf0 : f < f0 e
      · exact hpt _ (hpts f ⟨by omega, by omega⟩)
      · have hq1 : ∀ s ∈ [(q, e)], s.1.Prime := by
          simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq]; exact hq
        have hcomm : n * p ^ f * q ^ e = n * q ^ e * p ^ f := by ring
        have hrM' : ¬ r ∣ (stepsEnd n S [(q, e)]).1 * p ^ f := by rwa [stepsEnd_one, ← hcomm]
        have := not_weird_of_stepRowOK hn hg h hq1 hp hrow (by omega) hr hrM' hr.two_le
        rwa [stepsEnd_one, ← hcomm] at this
    · by_cases hfr : fr ≤ f
      · exact hcorner fr er hc1 hfr (by omega)
      · by_cases hec : ec ≤ e
        · exact hcorner F ec hc2 (by omega) hec
        · rcases hbox f ⟨by omega, by omega⟩ e ⟨by omega, by omega⟩ with ha | hpo
          · exact hab ha
          · exact hpt _ hpo

/-- **Instance (shape `e_inf = 2`).** The pair `(109, 797)` below the real prefix `3^16·5^11·19^8` of the search: the only
pair of that prefix that `pairOK` could not take (session 87). `F = 2`, start row `er = 2` (row `e = 1` is a limit row in
`p` from `f₀ = 6`, points `f = 2..5`), corners `(2, 2)` and `(2, 2)`. So no `n·109^f·797^e·r` is weird (`f, e ≥ 1`,
`r` prime). Parameters from `/tmp` prototype `find2` (session 87), checked here by the kernel. -/
theorem not_weird_real_prefix_109_797 {f e r : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 16 * 5 ^ 11 * 19 ^ 8 * 109 ^ f * 797 ^ e) :
    ¬ (3 ^ 16 * 5 ^ 11 * 19 ^ 8 * 109 ^ f * 797 ^ e * r).Weird :=
  not_weird_of_pairOK2 (S := 34953892078295791325867031) (c := 57) (g := 2) (F := 2) (fr := 2) (er := 2) (ec := 2)
    (e0 := fun _ => 3) (f0 := fun _ => 6)
    (r1 := fun f e => if f = 0 ∧ e = 1 then 1355113 else if f = 1 ∧ e = 0 then 11999 else if f = 1 ∧ e = 1 then 11776 else if f = 1 ∧ e = 2 then 11998 else if f = 2 ∧ e = 1 then 662194 else if f = 3 ∧ e = 1 then 1342227 else if f = 4 ∧ e = 1 then 1354993 else if f = 5 ∧ e = 1 then 1355112 else 0)
    (by norm_num) (by norm_num) ErdosResearch.OddWeirdPrefixIG.intervalGap_real (by norm_num) (by norm_num)
    (by decide +kernel) hf he hr hrM

end ErdosResearch.SubsetSumPair2
