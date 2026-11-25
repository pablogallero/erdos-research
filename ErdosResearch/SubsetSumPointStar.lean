module

public import ErdosResearch.SubsetSumStairPoint
public import ErdosResearch.SubsetSumUniform

@[expose] public section

/-!
# One staircase point, every last prime power at once (stars `r^h`)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 84).

Session 79's `pointOK M S c g r₀ r₁` decides `M r` for every prime `r ≥ r₀` at a deficient point `M` with an
`IntervalGap M S c g` certificate. This file extends it to every power `M r^k` (`k ≥ 1`). With `T_h = ∑ D(M r^h)` and
`N_h = M r^h`, `T_{h+1} = σ(M) + r T_h` and `N_{h+1} = r N_h`, so:
* `r ≤ r₁`: `pointOK` certifies `M r` (`N_1 + c ≤ T_1`), and the certificate propagates to every `h`
  (`cert_mono`), because the step conditions at `r` do not depend on `h`;
* `r ≥ r₁ + 2`: the invariant `(r − 1) T_h + σ(M) ≤ (r − 1) N_h` holds at `h = 1` and is preserved, so `M r^h` is
  never abundant (`not_abundant_of_far`);
* `r = r₁ + 1` (the only possible "star-only" prime, cf. `star_prime_unique`): `pointStarOK` either sees that it is
  even and `> 2`, or checks the step conditions at `r` and runs `firstOK`, which finds the first abundant exponent and
  checks the certificate there (then `cert_mono` again).

`not_weird_mul_prime_pow_of_pointStarOK`: `¬ (M r^k).Weird` for EVERY prime `r ≥ r₀`, `r ∤ M`, and EVERY `k ≥ 1`;
`not_weird_of_stepPointStarOK` is the same after a list of prime-power steps (the star analogue of `stepPointOK`).
Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumPointStar

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPoint ErdosResearch.SubsetSumStairPoint

/-- From `(T, N) = (∑ D(M r^h), M r^h)`: find the first abundant exponent (at most `k` steps) and check the
certificate there (`c ≤ N`, `N + c ≤ T`). -/
def firstOK (S M c r : ℕ) : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | k + 1, T, N =>
    if N < T then decide (c ≤ N) && decide (N + c ≤ T) else firstOK S M c r k (S + (M + r * T)) (r * N)

/-- `pointOK` plus the star-only candidate `r₁ + 1`. -/
def pointStarOK (M S c g r₀ r₁ fuel : ℕ) : Bool :=
  pointOK M S c g r₀ r₁ &&
    ((decide ((r₁ + 1) % 2 = 0) && decide (2 < r₁ + 1)) ||
      (decide ((r₁ + 1) * g + 2 * c ≤ S + 1) &&
        firstOK S M c (r₁ + 1) fuel (S + (M + (r₁ + 1) * S)) (M * (r₁ + 1))))

theorem ppSum_succ (M r S h : ℕ) : ppSum M r S (h + 1) = S + (M + r * ppSum M r S h) := rfl

/-- A certified exponent stays certified for every larger exponent. -/
theorem cert_mono {M S c r h : ℕ} (hr : 1 ≤ r) (h1 : c ≤ M * r ^ h) (h2 : M * r ^ h + c ≤ ppSum M r S h) :
    ∀ j, c ≤ M * r ^ (h + j) ∧ M * r ^ (h + j) + c ≤ ppSum M r S (h + j) := by
  intro j
  induction j with
  | zero => exact ⟨h1, h2⟩
  | succ j ih =>
    obtain ⟨i1, i2⟩ := ih
    rw [← add_assoc, ppSum_succ, pow_succ, ← mul_assoc]
    have e1 : M * r ^ (h + j) ≤ M * r ^ (h + j) * r := Nat.le_mul_of_pos_right _ hr
    have e2 : r * (M * r ^ (h + j) + c) ≤ r * ppSum M r S (h + j) := Nat.mul_le_mul_left r i2
    have e3 : c ≤ r * c := Nat.le_mul_of_pos_left c hr
    refine ⟨le_trans i1 e1, ?_⟩
    have : M * r ^ (h + j) * r = r * (M * r ^ (h + j)) := by ring
    rw [this]
    nlinarith

theorem firstOK_sound {S M c r : ℕ} (hr : 1 ≤ r) :
    ∀ k h, firstOK S M c r k (ppSum M r S h) (M * r ^ h) = true →
      ∀ h', h ≤ h' → M * r ^ h' < ppSum M r S h' → c ≤ M * r ^ h' ∧ M * r ^ h' + c ≤ ppSum M r S h'
  | 0, _, hk => by simp [firstOK] at hk
  | k + 1, h, hk => by
    intro h' hh' hab
    unfold firstOK at hk
    by_cases hN : M * r ^ h < ppSum M r S h
    · simp only [hN, ↓reduceIte] at hk
      simp only [Bool.and_eq_true, decide_eq_true_eq] at hk
      obtain ⟨j, rfl⟩ : ∃ j, h' = h + j := ⟨h' - h, by omega⟩
      exact cert_mono hr hk.1 hk.2 j
    · simp only [hN, ↓reduceIte] at hk
      rcases Nat.eq_or_lt_of_le hh' with rfl | hlt
      · exact absurd hab hN
      · have hk' : firstOK S M c r k (ppSum M r S (h + 1)) (M * r ^ (h + 1)) = true := by
          rw [ppSum_succ, pow_succ, ← mul_assoc, show M * r ^ h * r = r * (M * r ^ h) by ring]; exact hk
        exact firstOK_sound hr k (h + 1) hk' h' (by omega) hab

/-- Far primes: `(r − 1) T_h + σ ≤ (r − 1) N_h` for every `h ≥ 1`, so `M r^h` is never abundant. -/
theorem not_abundant_of_far {M S a : ℕ} (hinv : (S + (M + (a + 1) * S)) * a + (S + M) ≤ M * (a + 1) * a)
    (ha : 1 ≤ a) : ∀ h, 1 ≤ h → ppSum M (a + 1) S h ≤ M * (a + 1) ^ h := by
  have key : ∀ h, 1 ≤ h → ppSum M (a + 1) S h * a + (S + M) ≤ M * (a + 1) ^ h * a := by
    intro h hh
    induction h with
    | zero => omega
    | succ h ih =>
      rcases Nat.eq_zero_or_pos h with rfl | hpos
      · simpa [ppSum] using hinv
      · have H := ih hpos
        rw [ppSum_succ, pow_succ]
        calc (S + (M + (a + 1) * ppSum M (a + 1) S h)) * a + (S + M)
            = (a + 1) * (ppSum M (a + 1) S h * a + (S + M)) := by ring
          _ ≤ (a + 1) * (M * (a + 1) ^ h * a) := Nat.mul_le_mul_left _ H
          _ = M * ((a + 1) ^ h * (a + 1)) * a := by ring
  intro h hh
  have := key h hh
  exact Nat.le_of_mul_le_mul_right (by omega : ppSum M (a + 1) S h * a ≤ M * (a + 1) ^ h * a) ha

/-- **Every last prime power at one deficient point.** -/
theorem not_weird_mul_prime_pow_of_pointStarOK {M S c g r₀ r₁ fuel r k : ℕ} (hM : 0 < M) (hg : 1 ≤ g)
    (h : IntervalGap M S c g) (hok : pointStarOK M S c g r₀ r₁ fuel = true) (hr : r.Prime) (hrM : ¬ r ∣ M)
    (hr₀ : r₀ ≤ r) (hk : 1 ≤ k) : ¬ (M * r ^ k).Weird := by
  simp only [pointStarOK, pointOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨⟨hSM, hab⟩, h1⟩, h2⟩, h3⟩, h4⟩, hstar⟩ := hok
  have hsum := ppSum_eq hM hr hrM h.1 k
  have hr1 : 1 ≤ r := hr.one_lt.le
  rintro ⟨habund, hnot⟩
  unfold Nat.Abundant at habund
  rw [hsum] at habund
  -- certified at `k` ⇒ pseudoperfect
  have finish : r * g + 2 * c ≤ S + 1 → c ≤ M * r ^ k → M * r ^ k + c ≤ ppSum M r S k → False := by
    intro s1 c1 c2
    have e3 : (r₀ + 1) * S ≤ (r + 1) * S := Nat.mul_le_mul_right S (by omega)
    exact hnot (ErdosResearch.SubsetSumUniform.pseudoperfect_mul_prime_pow_of_intervalGap hM hg h hr hrM s1
      (by omega) k c1 c2)
  obtain ⟨D, rfl⟩ : ∃ D, M = S + D := ⟨M - S, by omega⟩
  have hD : S + D - S = D := by omega
  rw [hD] at hab h2
  rcases Nat.lt_or_ge r (r₁ + 1) with hlt | hge
  · -- `r ≤ r₁`: certified at `h = 1`, then for all `k`
    have e1 : r * g ≤ r₁ * g := Nat.mul_le_mul_right g (by omega)
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
  · -- `r = r₁ + 1`: the star-only candidate
    subst heq
    rcases hstar with ⟨hev, h2lt⟩ | ⟨s1, hf⟩
    · exact absurd (hr.eq_one_or_self_of_dvd 2 (Nat.dvd_of_mod_eq_zero hev)) (by omega)
    · have hf' : firstOK S (S + D) c (r₁ + 1) fuel (ppSum (S + D) (r₁ + 1) S 1) ((S + D) * (r₁ + 1) ^ 1) = true := by
        simpa [ppSum] using hf
      obtain ⟨d1, d2⟩ := firstOK_sound hr1 fuel 1 hf' k hk habund
      exact finish s1 d1 d2
  · -- `r ≥ r₁ + 2`: never abundant
    obtain ⟨a, rfl⟩ : ∃ a, r = a + 1 := ⟨r - 1, by omega⟩
    have hAD : 2 * S + D ≤ a * D := by
      have : (r₁ + 1) * D ≤ a * D := Nat.mul_le_mul_right D (by omega)
      omega
    have hinv : (S + ((S + D) + (a + 1) * S)) * a + (S + (S + D)) ≤ (S + D) * (a + 1) * a := by
      have := Nat.mul_le_mul_left a hAD
      nlinarith
    have := not_abundant_of_far hinv (by omega) k hk
    omega

/-- **Instance on a real certificate.** `M = 3^3·11·13^10·17^2·23` (`intervalGap_late_prefix`): no `M r^k` is weird,
for every prime `r` and every `k ≥ 1`. Here the star-only candidate is `r₁ + 1 = 33` (odd, so `firstOK` checks it):
`M·33` is not abundant, `M·33²` is the first abundant power and is certified, so fuel `4` suffices. -/
theorem not_weird_late_prefix_mul_prime_pow {r k : ℕ} (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) (hk : 1 ≤ k) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * r ^ k).Weird :=
  not_weird_mul_prime_pow_of_pointStarOK (r₀ := 2) (r₁ := 32) (fuel := 4) (by norm_num) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by decide +kernel) hr hrM hr.two_le hk

/-- Star analogue of `stepPointOK`: prime-power steps from the prefix certificate, then `pointStarOK`. -/
def stepPointStarOK (n S c g r₀ r₁ fuel : ℕ) (l : List (ℕ × ℕ)) : Bool :=
  stepsOK c g n S l && pointStarOK (stepsEnd n S l).1 (stepsEnd n S l).2 c g r₀ r₁ fuel

/-- **One staircase point, every last prime power.** -/
theorem not_weird_of_stepPointStarOK {n S c g r₀ r₁ fuel r k : ℕ} {l : List (ℕ × ℕ)} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hpr : ∀ s ∈ l, s.1.Prime) (hok : stepPointStarOK n S c g r₀ r₁ fuel l = true)
    (hr : r.Prime) (hrM : ¬ r ∣ (stepsEnd n S l).1) (hr₀ : r₀ ≤ r) (hk : 1 ≤ k) :
    ¬ ((stepsEnd n S l).1 * r ^ k).Weird := by
  simp only [stepPointStarOK, Bool.and_eq_true] at hok
  exact not_weird_mul_prime_pow_of_pointStarOK (stepsEnd_pos l n S hn hpr) hg
    (intervalGap_of_stepsOK hg l n S hn hpr hok.1 h) hok.2 hr hrM hr₀ hk

/-- Instance: `M = n·37·307` below the late prefix (`r* = 6687`, first abundant at `h = 2`, certified): no `M r^k` is
weird, for every prime `r` and every `k ≥ 1`. -/
theorem not_weird_late_prefix_37_307_mul_prime_pow {r k : ℕ} (hr : r.Prime)
    (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ 1) (hk : 1 ≤ k) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ 1 * 307 ^ 1 * r ^ k).Weird :=
  not_weird_of_stepPointStarOK (S := 256030928920159929) (c := 2295) (g := 5) (r₀ := 2) (r₁ := 6686) (fuel := 4)
    (l := [(37, 1), (307, 1)]) (by norm_num) (by norm_num) ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix
    (by simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq]; norm_num)
    (by decide +kernel) hr hrM hr.two_le hk

end ErdosResearch.SubsetSumPointStar
