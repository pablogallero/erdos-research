module

public import Mathlib

@[expose] public section

/-!
# Stars `r^h` (`h ≥ 2`) below a deficient point: one candidate `r`, one exponent

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 76).

For `M` odd and `r` prime with `r ∤ M`, `σ(M r^h) = σ(M) σ(r^h)` and `σ(r^h) = 1 + r + ⋯ + r^h`, so the excess of
`M r^h` is `E h = σ(M) σ(r^h) − 2 M r^h`. This file has the pure algebra, with `s` standing for `σ(M)`:

* `starExcess_succ`: `E (h+1) = r E h + s`;
* `starExcess_ge_of_pos`: `E h ≥ 1`, `c ≤ s` ⇒ `E (h+1) ≥ c` (only the first abundant exponent can lack a certificate);
* `starExcess_ge_of_ge`: `c ≤ E h` (`0 ≤ c`) ⇒ `c ≤ E (h+k)` for every `k`;
* `star_window`: `E h > 0` for some `h` ⇒ `r (2M − s) < 2M`;
* `star_r_unique`: with `D = 2M − s > 0`, at most one `r` has `M r` not abundant (`E 1 ≤ 0`) and some `M r^h` abundant.

So per deficient point `M` the stars need one test at `r* = ⌈s / D⌉` (`scripts/plimit_star_probe.py`).
Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumStar

open Finset

/-- `1 + r + ⋯ + r^h` in `ℤ` (`= σ(r^h)` for `r` prime). -/
def geom (r h : ℕ) : ℤ := ∑ i ∈ range (h + 1), (r : ℤ) ^ i

/-- Excess `s · σ(r^h) − 2 M r^h` of `M r^h` when `s = σ(M)`. -/
def starExcess (s M r h : ℕ) : ℤ := (s : ℤ) * geom r h - 2 * (M : ℤ) * (r : ℤ) ^ h

theorem geom_succ (r h : ℕ) : geom r (h + 1) = r * geom r h + 1 := by
  unfold geom
  rw [Finset.sum_range_succ', Finset.mul_sum]
  simp [pow_succ, mul_comm]

theorem geom_mul_sub (r h : ℕ) : geom r h * ((r : ℤ) - 1) = (r : ℤ) ^ (h + 1) - 1 := by
  unfold geom; exact geom_sum_mul _ _

theorem starExcess_succ (s M r h : ℕ) :
    starExcess s M r (h + 1) = r * starExcess s M r h + s := by
  unfold starExcess; rw [geom_succ]; ring

theorem starExcess_one (s M r : ℕ) : starExcess s M r 1 = (s : ℤ) * (r + 1) - 2 * M * r := by
  unfold starExcess geom
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, pow_zero, pow_one]; ring

/-- Once `M r^h` is abundant (`E h ≥ 1`), the next excess is `≥ c` as soon as `c ≤ σ(M)`. -/
theorem starExcess_ge_of_pos {s M r h : ℕ} {c : ℤ} (hr : 1 ≤ r) (hc : c ≤ s) (h1 : 1 ≤ starExcess s M r h) :
    c ≤ starExcess s M r (h + 1) := by
  rw [starExcess_succ]
  have : (1 : ℤ) ≤ r := by exact_mod_cast hr
  nlinarith

/-- A certified excess stays certified for every larger exponent. -/
theorem starExcess_ge_of_ge {s M r h : ℕ} {c : ℤ} (hr : 1 ≤ r) (hc0 : 0 ≤ c) (h1 : c ≤ starExcess s M r h) :
    ∀ k, c ≤ starExcess s M r (h + k) := by
  intro k
  induction k with
  | zero => simpa using h1
  | succ k ih =>
    rw [← add_assoc, starExcess_succ]
    have : (1 : ℤ) ≤ r := by exact_mod_cast hr
    have hs : (0 : ℤ) ≤ s := by positivity
    nlinarith

/-- **Window.** If some `M r^h` is abundant then `r (2M − s) < 2M`. -/
theorem star_window {s M r h : ℕ} (hr : 2 ≤ r) (hpos : 0 < starExcess s M r h) :
    (r : ℤ) * (2 * M - s) < 2 * M := by
  unfold starExcess at hpos
  have hg := geom_mul_sub r h
  have hr1 : (1 : ℤ) ≤ (r : ℤ) - 1 := by
    have : (2 : ℤ) ≤ r := by exact_mod_cast hr
    linarith
  have hs : (0 : ℤ) ≤ s := by positivity
  have hrh : (0 : ℤ) < (r : ℤ) ^ h := by positivity
  have key : ((s : ℤ) * r - 2 * M * (r - 1)) * (r : ℤ) ^ h =
      ((r : ℤ) - 1) * ((s : ℤ) * geom r h - 2 * M * (r : ℤ) ^ h) + s := by
    have : (r : ℤ) ^ (h + 1) = geom r h * ((r : ℤ) - 1) + 1 := by linarith
    calc ((s : ℤ) * r - 2 * M * (r - 1)) * (r : ℤ) ^ h
        = (s : ℤ) * (r : ℤ) ^ (h + 1) - 2 * M * (r - 1) * (r : ℤ) ^ h := by ring
      _ = _ := by rw [this]; ring
  have hpos' : 0 < ((s : ℤ) * r - 2 * M * (r - 1)) * (r : ℤ) ^ h := by
    rw [key]; nlinarith
  have := pos_of_mul_pos_left hpos' hrh.le
  linarith

/-- **One candidate.** With `D = 2M − s > 0`, two primes `r₁, r₂` that both have `M r` not abundant but some `M r^h`
abundant are equal (both satisfy `s ≤ r D < s + D`). -/
theorem star_r_unique {s M r₁ r₂ h₁ h₂ : ℕ} (hD : (s : ℤ) < 2 * M) (hr₁ : 2 ≤ r₁) (hr₂ : 2 ≤ r₂)
    (hE₁ : starExcess s M r₁ 1 ≤ 0) (hE₂ : starExcess s M r₂ 1 ≤ 0)
    (hp₁ : 0 < starExcess s M r₁ h₁) (hp₂ : 0 < starExcess s M r₂ h₂) : r₁ = r₂ := by
  have w₁ := star_window hr₁ hp₁
  have w₂ := star_window hr₂ hp₂
  rw [starExcess_one] at hE₁ hE₂
  have hDpos : (0 : ℤ) < 2 * M - s := by linarith
  have a : ((r₁ : ℤ) - r₂) * (2 * M - s) < 1 * (2 * M - s) := by nlinarith
  have b : ((r₂ : ℤ) - r₁) * (2 * M - s) < 1 * (2 * M - s) := by nlinarith
  have a' := lt_of_mul_lt_mul_right a hDpos.le
  have b' := lt_of_mul_lt_mul_right b hDpos.le
  omega

end ErdosResearch.SubsetSumStar
