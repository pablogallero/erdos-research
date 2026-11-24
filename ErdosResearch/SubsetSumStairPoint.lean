module

public import ErdosResearch.SubsetSumPoint

@[expose] public section

/-!
# A staircase point after prime-power steps (towards `stairOK`)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 80).

The staircase decider (`scripts/plimit_probe.py`, `BOUNDED=1 FASTSTRIP=1`) works below a 3-prime prefix `n` with one
`IntervalGap n S c g` certificate. A point `(f, e)` of a pair `(p, q)` is the number `M = n p^f q^e`. Its certificate
is two prime-power steps (`intervalGap_of_stepsOK`), and for a deficient `M` the last prime `r` is decided in closed
form by `pointOK` (session 79). `stepPointOK` is that conjunction for an arbitrary list of steps, and
`not_weird_of_stepPointOK` gives `¬ (M r).Weird` for EVERY prime `r ≥ r₀`, `r ∤ M`, from one Boolean.

Above the staircase nothing more is needed: one pseudoperfect minimal corner (`stepAbOK`) covers every multiple
(`not_weird_of_upset`). Still missing for a whole pair: the quantification over all `(f, e)` (limit rows and columns via
`not_abundant_of_limit`) and the star layer. Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumStairPoint

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPoint

/-- Step conditions along `l`, then the closed-form last-prime test at the end point. -/
def stepPointOK (n S c g r₀ r₁ : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  stepsOK c g n S l && pointOK (stepsEnd n S l).1 (stepsEnd n S l).2 c g r₀ r₁

theorem stepsEnd_pos : ∀ (l : List (ℕ × ℕ)) (n S : ℕ), 0 < n → (∀ s ∈ l, s.1.Prime) →
    0 < (stepsEnd n S l).1
  | [], _, _, hn, _ => hn
  | (q, f) :: l, n, _, hn, hpr =>
      stepsEnd_pos l (n * q ^ f) _ (Nat.mul_pos hn (pow_pos (hpr (q, f) (List.mem_cons_self ..)).pos f))
        fun s hs => hpr s (List.mem_cons_of_mem _ hs)

/-- **One staircase point, every last prime.** -/
theorem not_weird_of_stepPointOK {n S c g r₀ r₁ r : ℕ} {l : List (ℕ × ℕ)} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hpr : ∀ s ∈ l, s.1.Prime) (hok : stepPointOK n S c g r₀ r₁ l = true)
    (hr : r.Prime) (hrM : ¬ r ∣ (stepsEnd n S l).1) (hr₀ : r₀ ≤ r) :
    ¬ ((stepsEnd n S l).1 * r).Weird := by
  simp only [stepPointOK, Bool.and_eq_true] at hok
  exact not_weird_mul_prime_of_pointOK (stepsEnd_pos l n S hn hpr) hg
    (intervalGap_of_stepsOK hg l n S hn hpr hok.1 h) hok.2 hr hrM hr₀

/-- **Abundant point.** An `IntervalGap` certificate whose interval contains the number itself makes it pseudoperfect. -/
theorem pseudoperfect_of_intervalGap {M S c g : ℕ} (hM : 0 < M) (h : IntervalGap M S c g) (hc : c ≤ M)
    (hab : M + c ≤ S) : M.Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ := h.2.1 M hc hab
  exact ⟨hM, t, ht, hsum⟩

/-- Boolean for an abundant staircase point: step conditions along `l`, then `c ≤ M` and `M + c ≤ ∑ D M`. -/
def stepAbOK (n S c g : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  stepsOK c g n S l && decide (c ≤ (stepsEnd n S l).1) &&
    decide ((stepsEnd n S l).1 + c ≤ (stepsEnd n S l).2)

/-- **Abundant staircase point:** `M = stepsEnd` is pseudoperfect, so none of its multiples is weird. -/
theorem pseudoperfect_of_stepAbOK {n S c g : ℕ} {l : List (ℕ × ℕ)} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hpr : ∀ s ∈ l, s.1.Prime) (hok : stepAbOK n S c g l = true) :
    (stepsEnd n S l).1.Pseudoperfect := by
  simp only [stepAbOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  exact pseudoperfect_of_intervalGap (stepsEnd_pos l n S hn hpr)
    (intervalGap_of_stepsOK hg l n S hn hpr hok.1.1 h) hok.1.2 hok.2

/-- **Instance (pair point).** Below the late prefix `n = 3^3·23·13^10·17^2·11` (certificate `(c, g) = (2295, 5)`),
the point `(p, f; q, e) = (37, 1; 307, 1)` is deficient, `M r` is abundant only for `r ≤ 6686`, and no `M r` with
`r` prime, `r ∤ M` is weird. Found by a throwaway scan (`/tmp`), checked here by the kernel. -/
theorem not_weird_late_prefix_pair_point {r : ℕ} (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ 1) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ 1 * r).Weird :=
  not_weird_of_stepPointOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 6686)
    (l := [(37, 1), (307, 1)]) (by norm_num) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; norm_num)
    (by decide +kernel) hr hrM hr.two_le

/-- **Instance (abundant pair point).** `3^3·23·13^10·17^2·11·37·41` is pseudoperfect (two steps from the late-prefix
certificate, then the interval contains the number), so none of its multiples is weird. -/
theorem pseudoperfect_late_prefix_pair_point :
    (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 41 ^ 1).Pseudoperfect :=
  pseudoperfect_of_stepAbOK (S := 256030928920159929) (c := 2295) (g := 5) (l := [(37, 1), (41, 1)])
    (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; norm_num)
    (by decide +kernel)

/-- **The up-set is free.** If the minimal abundant point `n p^f₀ q^e₀` is pseudoperfect, then every
`n p^f q^e m` with `f₀ ≤ f`, `e₀ ≤ e`, `m ≥ 1` is pseudoperfect, hence not weird (no step condition is needed
above the staircase). -/
theorem not_weird_of_upset {n p q f₀ e₀ f e m : ℕ} (hp : 0 < p) (hq : 0 < q) (h : (n * p ^ f₀ * q ^ e₀).Pseudoperfect)
    (hf : f₀ ≤ f) (he : e₀ ≤ e) (hm : 0 < m) : ¬ (n * p ^ f * q ^ e * m).Weird := by
  have hn : 0 < n := Nat.pos_of_ne_zero fun hn => by simp [hn] at h; exact absurd h.1 (lt_irrefl 0)
  have hpos : 0 < n * p ^ f * q ^ e * m := by positivity
  have hd : n * p ^ f₀ * q ^ e₀ ∣ n * p ^ f * q ^ e * m :=
    Dvd.dvd.mul_right (mul_dvd_mul (mul_dvd_mul_left n (pow_dvd_pow p hf)) (pow_dvd_pow q he)) m
  exact fun hw => hw.2 (h.of_dvd hd hpos)

/-- **Instance (whole up-set).** For `n = 3^3·23·13^10·17^2·11`, no `n·37^f·41^e·m` with `f, e ≥ 1`, `m ≥ 1` is weird. -/
theorem not_weird_late_prefix_37_41 {f e m : ℕ} (hf : 1 ≤ f) (he : 1 ≤ e) (hm : 0 < m) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * 41 ^ e * m).Weird :=
  not_weird_of_upset (by norm_num) (by norm_num) pseudoperfect_late_prefix_pair_point hf he hm

end ErdosResearch.SubsetSumStairPoint
