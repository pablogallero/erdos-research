module

public import ErdosResearch.SubsetSumFifthLoop

@[expose] public section

/-!
# One staircase point, every last prime at once (the `r¹` part of `stairOK`)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 79).

In the staircase decider (`scripts/plimit_probe.py`, `FASTSTRIP=1`), a deficient point `M = n p^f q^e` with an
`IntervalGap M S c g` certificate decides the last prime `r` (exponent 1) in closed form: with `D = M − S > 0`,
`M r` is abundant iff `r D < σ(M) = S + M`, and it is certified iff additionally `r D + c ≤ σ(M)` plus the two step
conditions. All conditions are monotone in `r`, so they only need checking at the two ends:

* `r₀` (the smallest `r` allowed): `M + 2c ≤ (r₀ + 1) S + 1` and `c ≤ M r₀`;
* `r₁` (any upper bound of the abundant range, `σ(M) ≤ (r₁ + 1) D`): `r₁ g + 2c ≤ S + 1` and `r₁ D + c ≤ σ(M)`.

`pointOK` is that Boolean, and `not_weird_mul_prime_of_pointOK` gives `¬ (M r).Weird` for EVERY prime `r ≥ r₀`,
`r ∤ M`, with no scan over `r` (if the window `(σ − c)/D < r < σ/D` contains a prime, `pointOK` is false and the
decider falls back to `lastOKR`). Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumPoint

open ErdosResearch.SubsetSumSteps

/-- Closed-form test for one deficient point `M` (`S = ∑ D(M) < M`), last primes `r ≥ r₀`; `r₁` bounds the abundant
range. -/
def pointOK (M S c g r₀ r₁ : ℕ) : Bool :=
  decide (S < M) && decide (S + M ≤ (r₁ + 1) * (M - S)) && decide (r₁ * g + 2 * c ≤ S + 1) &&
    decide (r₁ * (M - S) + c ≤ S + M) && decide (M + 2 * c ≤ (r₀ + 1) * S + 1) && decide (c ≤ M * r₀)

theorem not_weird_mul_prime_of_pointOK {M S c g r₀ r₁ r : ℕ} (hM : 0 < M) (hg : 1 ≤ g)
    (h : IntervalGap M S c g) (hok : pointOK M S c g r₀ r₁ = true) (hr : r.Prime) (hrM : ¬ r ∣ M)
    (hr₀ : r₀ ≤ r) : ¬ (M * r).Weird := by
  simp only [pointOK, Bool.and_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨⟨hSM, hab⟩, h1⟩, h2⟩, h3⟩, h4⟩ := hok
  refine not_weird_mul_prime_of_intervalGap hM hg h hr hrM fun habr => ?_
  obtain ⟨D, rfl⟩ : ∃ D, M = S + D := ⟨M - S, by omega⟩
  have hD : S + D - S = D := by omega
  rw [hD] at hab h2
  -- abundance of `M r` forces `r ≤ r₁`
  have hrr : r ≤ r₁ := by
    by_contra hlt
    have : (r₁ + 1) * D ≤ r * D := Nat.mul_le_mul_right D (by omega)
    nlinarith
  have e1 : r * g ≤ r₁ * g := Nat.mul_le_mul_right g hrr
  have e2 : r * D ≤ r₁ * D := Nat.mul_le_mul_right D hrr
  have e3 : (r₀ + 1) * S ≤ (r + 1) * S := Nat.mul_le_mul_right S (by omega)
  have e4 : (S + D) * r₀ ≤ (S + D) * r := Nat.mul_le_mul_left _ hr₀
  refine ⟨by omega, by omega, by omega, ?_⟩
  have : (S + D) * r = r * S + r * D := by ring
  omega

/-- Sanity check on a small deficient point: `M = 3^2·5·7 = 315` (`∑ D(315) = 309`, `D = 6`, abundant iff `r ≤ 103`).
`pointOK` with a made-up certificate shape `(c, g) = (1, 1)`: it only tests the Boolean, not the certificate. -/
example : pointOK 315 309 1 1 3 103 = true := by decide

/-- **Instance on a real certificate.** `M = 3^3·11·13^10·17^2·23` (`IntervalGap` with `(c, g) = (2295, 5)` from
`intervalGap_late_prefix`) is deficient (`M − S ≈ 1.6·10^16`), `M r` is abundant only for `r ≤ 32`, and every prime
`r ∤ M` gives `¬ (M r).Weird`, from one Boolean and no scan over `r`. -/
theorem not_weird_late_prefix_mul_prime {r : ℕ} (hr : r.Prime) (hrM : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * r).Weird :=
  not_weird_mul_prime_of_pointOK (r₀ := 2) (r₁ := 32) (by norm_num) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix (by decide +kernel) hr hrM hr.two_le

end ErdosResearch.SubsetSumPoint
