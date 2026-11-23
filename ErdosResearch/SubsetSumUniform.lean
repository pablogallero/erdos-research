module

public import ErdosResearch.SubsetSumSteps

@[expose] public section

/-!
# One certificate for a whole sub-tree: the last two primes of the search

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 63).

Session 63 measured (Python, `scripts/subroot_leaf_probe.py`, `UNIFORM=1`) that for a deficient 4-prime prefix
`n` of the ω = 6 search, ONE `IntervalGap n S c g` certificate (bitset base + steps + raises) plus the
prime-power step by the fifth prime `q` (conditions linear in `q`, valid for every exponent) already decides
every leaf of the sub-tree below `n` (abundant leaves: `n q^e` is pseudoperfect; deficient leaves: the
last-prime test), on 44 prefixes (2374 leaves for `3^20·5^18·19^4·97^3`). So the kernel only has to
certify `n` once, and the fifth prime enters only through the inequalities below.

* `intervalGap_mul_prime_pow`: `IntervalGap` survives the step `n ↦ n q^e`, for every `e`.
* `pseudoperfect_mul_prime_pow_of_intervalGap`: abundant leaf.
* `pseudoperfect_mul_prime_of_range`: every abundant leaf `n q` (exponent 1) with `q₀ ≤ q ≤ q₁` at once,
  from four inequalities at the ends (for `3^20·5^18·19^4·97^3`, `(c, g) = (57, 2)`: all 1112 abundant leaves,
  `q` from 101 to 9173, Python check).
* `not_weird_mul_prime_pow_mul_prime_of_intervalGap`: deficient leaf, sixth prime `r` with exponent 1.
* `pseudoperfect_star_of_intervalGap`: deficient leaf, sixth prime `r` with any exponent (the "star" part).

Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumUniform

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumPrimePow ErdosResearch.SubsetSumSteps

/-- The prime-power step in `IntervalGap` form: one certificate for `n` gives one for every `n q^e`. -/
theorem intervalGap_mul_prime_pow {n S c g q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (h1 : q * g + 2 * c ≤ S + 1) (h2 : n + 2 * c ≤ (q + 1) * S + 1) (e : ℕ) :
    IntervalGap (n * q ^ e) (ppSum n q S e) c g := by
  obtain ⟨hS, hI, hG⟩ := h
  have hsum := ppSum_eq hn hq hqn hS e
  obtain ⟨hI', hG'⟩ := interval_properDivisors_mul_prime_pow hn hq hqn hg
    (fun x h₁ h₂ => hI x h₁ (by rw [hS] at h₂; exact h₂))
    (fun x hx => by rw [hS] at hx ⊢; exact hG x hx)
    (by rw [hS]; exact h1) (by rw [hS]; exact h2) e
  refine ⟨hsum, fun x h₁ h₂ => hI' x h₁ (by rw [hsum]; exact h₂), fun x hx => ?_⟩
  rw [← hsum] at hx ⊢
  exact hG' x hx

/-- Abundant leaf: under the step conditions, `n q^e` is pseudoperfect as soon as it lies in
`[c, ∑ D(n q^e) − c]`. -/
theorem pseudoperfect_mul_prime_pow_of_intervalGap {n S c g q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (h1 : q * g + 2 * c ≤ S + 1) (h2 : n + 2 * c ≤ (q + 1) * S + 1) (e : ℕ)
    (hc : c ≤ n * q ^ e) (hab : n * q ^ e + c ≤ ppSum n q S e) :
    (n * q ^ e).Pseudoperfect := by
  obtain ⟨hS, hI, hG⟩ := h
  exact pseudoperfect_mul_prime_pow_of_interval hn hq hqn hg
    (fun x h₁ h₂ => hI x h₁ (by rw [hS] at h₂; exact h₂))
    (fun x hx => by rw [hS] at hx ⊢; exact hG x hx)
    (by rw [hS]; exact h1) (by rw [hS]; exact h2) e hc (by rw [ppSum_eq hn hq hqn hS e]; exact hab)

/-- Deficient leaf: from the certificate of `n`, the step by `q^e`, then the last-prime test for `r`. -/
theorem not_weird_mul_prime_pow_mul_prime_of_intervalGap {n S c g q r : ℕ} (hn : 0 < n)
    (hg : 1 ≤ g) (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (h1 : q * g + 2 * c ≤ S + 1) (h2 : n + 2 * c ≤ (q + 1) * S + 1) (e : ℕ)
    (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e)
    (hcov : n * q ^ e * r < ppSum n q S e + (n * q ^ e + r * ppSum n q S e) →
      r * g + 2 * c ≤ ppSum n q S e + 1 ∧ n * q ^ e + 2 * c ≤ (r + 1) * ppSum n q S e + 1 ∧
        c ≤ n * q ^ e * r ∧ n * q ^ e * r + c ≤ ppSum n q S e + (n * q ^ e + r * ppSum n q S e)) :
    ¬ (n * q ^ e * r).Weird :=
  not_weird_mul_prime_of_intervalGap (Nat.mul_pos hn (pow_pos hq.pos e)) hg
    (intervalGap_mul_prime_pow hn hg h hq hqn h1 h2 e) hr hrn hcov

/-- **Range version of the abundant leaf** (exponent 1): all side conditions are linear in `q`, so they
only need to be checked at the two ends `q₀ ≤ q ≤ q₁`; then `n q` is pseudoperfect for EVERY prime `q`
in the range not dividing `n`, with no per-prime computation. -/
theorem pseudoperfect_mul_prime_of_range {n S c g q₀ q₁ q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n) (hq₀ : q₀ ≤ q) (hq₁ : q ≤ q₁)
    (h1 : q₁ * g + 2 * c ≤ S + 1) (h2 : n + 2 * c ≤ (q₀ + 1) * S + 1) (h3 : c ≤ n * q₀)
    (h4 : n * q₁ + c ≤ S + (n + q₁ * S)) :
    (n * q).Pseudoperfect := by
  have e1 : q * g ≤ q₁ * g := Nat.mul_le_mul_right g hq₁
  have e2 : (q₀ + 1) * S ≤ (q + 1) * S := Nat.mul_le_mul_right S (by omega)
  have e3 : n * q₀ ≤ n * q := Nat.mul_le_mul_left n hq₀
  have hcS : c ≤ S := by
    have : g ≤ q₁ * g := Nat.le_mul_of_pos_left g (by have := hq.pos; omega)
    omega
  have h4' : n * q + c ≤ S + (n + q * S) := by
    rcases le_total S n with hSn | hnS
    · -- `(n − S) q ≤ (n − S) q₁`
      obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hSn
      have : (S + d) * q + c ≤ S + (S + d + q * S) := by
        have hh : (S + d) * q₁ + c ≤ S + (S + d + q₁ * S) := h4
        have : d * q ≤ d * q₁ := Nat.mul_le_mul_left d hq₁
        nlinarith
      exact this
    · have : n * q ≤ S * q := Nat.mul_le_mul_right q hnS
      nlinarith
  have := pseudoperfect_mul_prime_pow_of_intervalGap hn hg h hq hqn (by omega) (by omega) 1
    (by rw [pow_one]; omega) (by rw [pow_one]; simpa [ppSum] using h4')
  simpa using this

/-- Star leaf: the sixth prime `r` with any exponent `f` (two steps, then the interval test). -/
theorem pseudoperfect_star_of_intervalGap {n S c g q r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (h1 : q * g + 2 * c ≤ S + 1) (h2 : n + 2 * c ≤ (q + 1) * S + 1) (e : ℕ)
    (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e)
    (h3 : r * g + 2 * c ≤ ppSum n q S e + 1) (h4 : n * q ^ e + 2 * c ≤ (r + 1) * ppSum n q S e + 1)
    (f : ℕ) (hc : c ≤ n * q ^ e * r ^ f)
    (hab : n * q ^ e * r ^ f + c ≤ ppSum (n * q ^ e) r (ppSum n q S e) f) :
    (n * q ^ e * r ^ f).Pseudoperfect :=
  pseudoperfect_mul_prime_pow_of_intervalGap (Nat.mul_pos hn (pow_pos hq.pos e)) hg
    (intervalGap_mul_prime_pow hn hg h hq hqn h1 h2 e) hr hrn h3 h4 f hc hab

end ErdosResearch.SubsetSumUniform
