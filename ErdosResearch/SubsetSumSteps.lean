module

public import ErdosResearch.SubsetSumRaise

@[expose] public section

/-!
# A list of prime-power steps, checked by one Boolean

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 56).

Once some `n` has a certified interval `[c, ∑ D n − c]` with gaps `≤ g` (a bitset base, or a chain of
raises from `SubsetSumRaise.lean`), new primes can be added one at a time with the prime-power step
(`interval_properDivisors_mul_prime_pow`), which keeps `c` and `g`. Here a whole list of steps
`(q, f)` is checked by one Boolean `stepsOK`, using only the recursive sum `ppSum` (no divisors of the
large numbers): `interval_of_stepsOK`. Then `not_weird_mul_prime_of_interval` handles the last prime.

Instance: `not_weird_mul_prime_example`: no `3^4 · 11^10 · 13 · 17^10 · 23^10 · q` (`q` prime) is weird, from
the bitsets of `D 11583` and `D 1053`, nine raises of the exponent of 11, then the steps `17^10`, `23^10`. Elementary; not a new result.
-/

namespace ErdosResearch.SubsetSumSteps

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumPrimeStep
  ErdosResearch.SubsetSumPrimePow ErdosResearch.SubsetSumCert ErdosResearch.SubsetSumRaise

/-- `∑ D(n q^f)` from `S = ∑ D n` (`sum_properDivisors_mul_prime_pow_succ`). -/
def ppSum (n q S : ℕ) : ℕ → ℕ
  | 0 => S
  | f + 1 => S + (n + q * ppSum n q S f)

theorem ppSum_eq {n q S : ℕ} (hn : 0 < n) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hS : ∑ y ∈ n.properDivisors, y = S) :
    ∀ f, ∑ y ∈ (n * q ^ f).properDivisors, y = ppSum n q S f
  | 0 => by rw [pow_zero, mul_one, ppSum]; exact hS
  | f + 1 => by
      rw [sum_properDivisors_mul_prime_pow_succ f hn hq hqn, ppSum, ppSum_eq hn hq hqn hS f, hS]

/-- The number and the sum of proper divisors after a list of steps. -/
def stepsEnd : ℕ → ℕ → List (ℕ × ℕ) → ℕ × ℕ
  | n, S, [] => (n, S)
  | n, S, (q, f) :: l => stepsEnd (n * q ^ f) (ppSum n q S f) l

/-- The conditions of the prime-power step at every step of the list. -/
def stepsOK (c g : ℕ) : ℕ → ℕ → List (ℕ × ℕ) → Bool
  | _, _, [] => true
  | n, S, (q, f) :: l =>
      decide (n % q ≠ 0) && decide (q * g + 2 * c ≤ S + 1) &&
        decide (n + 2 * c ≤ (q + 1) * S + 1) && stepsOK c g (n * q ^ f) (ppSum n q S f) l

/-- Interval and gaps on `D n` (with `∑ D n = S`). -/
def IntervalGap (n S c g : ℕ) : Prop :=
  ∑ y ∈ n.properDivisors, y = S ∧
    (∀ x, c ≤ x → x + c ≤ S → x ∈ subsetSums n.properDivisors) ∧
    (∀ x < S, ∃ z ∈ subsetSums n.properDivisors, x < z ∧ z ≤ x + g ∧ z ≤ S)

theorem intervalGap_of_stepsOK {c g : ℕ} (hg : 1 ≤ g) :
    ∀ (l : List (ℕ × ℕ)) (n S : ℕ), 0 < n → (∀ s ∈ l, s.1.Prime) → stepsOK c g n S l = true →
      IntervalGap n S c g → IntervalGap (stepsEnd n S l).1 (stepsEnd n S l).2 c g
  | [], n, S, _, _, _, h => h
  | (q, f) :: l, n, S, hn, hpr, hok, ⟨hS, hI, hG⟩ => by
      have hq : q.Prime := hpr (q, f) (List.mem_cons_self ..)
      simp only [stepsOK, Bool.and_eq_true, decide_eq_true_eq] at hok
      obtain ⟨⟨⟨hqn, h1⟩, h2⟩, hrest⟩ := hok
      have hqn' : ¬ q ∣ n := fun h => hqn (Nat.mod_eq_zero_of_dvd h)
      have hsum := ppSum_eq hn hq hqn' hS f
      obtain ⟨hI', hG'⟩ := interval_properDivisors_mul_prime_pow hn hq hqn' hg
        (fun x h₁ h₂ => hI x h₁ (by rw [hS] at h₂; exact h₂))
        (fun x hx => by rw [hS] at hx ⊢; exact hG x hx)
        (by rw [hS]; exact h1) (by rw [hS]; exact h2) f
      refine intervalGap_of_stepsOK hg l (n * q ^ f) (ppSum n q S f)
        (Nat.mul_pos hn (pow_pos hq.pos f)) (fun s hs => hpr s (List.mem_cons_of_mem _ hs)) hrest
        ⟨hsum, fun x h₁ h₂ => hI' x h₁ (by rw [hsum]; exact h₂), fun x hx => ?_⟩
      rw [← hsum] at hx ⊢
      exact hG' x hx

/-- **Last prime.** Interval and gaps on `D n`, `q ∤ n` prime: if, whenever `n q` is abundant, the
prime-step conditions and the margin `n q + c ≤ ∑ D(n q)` hold, then `n q` is not weird. -/
theorem not_weird_mul_prime_of_intervalGap {n S c g q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (hcov : n * q < S + (n + q * S) →
      q * g + 2 * c ≤ S + 1 ∧ n + 2 * c ≤ (q + 1) * S + 1 ∧ c ≤ n * q ∧
        n * q + c ≤ S + (n + q * S)) :
    ¬ (n * q).Weird := by
  obtain ⟨hS, hI, hG⟩ := h
  rintro ⟨habund, hnot⟩
  have hsum1 := sum_properDivisors_mul_prime_pow_succ 0 hn hq hqn
  simp only [zero_add, pow_one, pow_zero, mul_one] at hsum1
  rw [hS] at hsum1
  have hab : n * q < S + (n + q * S) := by
    have := habund
    unfold Nat.Abundant at this
    rw [hsum1] at this
    exact this
  obtain ⟨h1, h2, h3, h4⟩ := hcov hab
  apply hnot
  have h := pseudoperfect_mul_prime_pow_of_interval hn hq hqn hg
    (fun x h₁ h₂ => hI x h₁ (by rw [hS] at h₂; exact h₂))
    (fun x hx => by rw [hS] at hx ⊢; exact hG x hx)
    (by rw [hS]; exact h1) (by rw [hS]; exact h2) 1 (by rw [pow_one]; exact h3)
    (by rw [pow_one, hsum1]; exact h4)
  simpa using h

/-- The raise certificate in `IntervalGap` form. -/
theorem intervalGap_of_raise_cert {m p e₀ c g gB k : ℕ} (lA lB : List ℕ)
    (hlA : lA.toFinset = (m * p ^ e₀).properDivisors) (hndA : lA.Nodup)
    (hI : intervalOK (ssBits lA) c lA.sum = true) (hG : gapOK (ssBits lA) g lA.sum = true)
    (hlB : lB.toFinset = m.properDivisors) (hndB : lB.Nodup)
    (hGB : gapOK (ssBits lB) gB lB.sum = true)
    (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (hg : 1 ≤ g)
    (hok : raiseOK m p e₀ c gB lB.sum lA.sum k = true) :
    IntervalGap (m * p ^ (e₀ + k)) (raiseSum m p e₀ lB.sum lA.sum k) c g := by
  obtain ⟨hrs, hI', hG'⟩ := interval_raise_of_cert lA lB hlA hndA hI hG hlB hndB hGB hm hp hpm hg hok
  refine ⟨hrs, fun x h₁ h₂ => hI' x h₁ (by rw [hrs]; exact h₂), fun x hx => ?_⟩
  rw [← hrs] at hx ⊢
  exact hG' x hx

/-- Proper divisors of `11583 = 3^4 · 11 · 13` and of `1053 = 3^4 · 13`. -/
def l11583 : List ℕ :=
  [1, 3, 9, 11, 13, 27, 33, 39, 81, 99, 117, 143, 297, 351, 429, 891, 1053, 1287, 3861]
def l1053 : List ℕ := [1, 3, 9, 13, 27, 39, 81, 117, 351]

theorem cert_11583_steps :
    l11583.toFinset = (1053 * 11 ^ 1).properDivisors ∧ l11583.Nodup ∧
      intervalOK (ssBits l11583) 69 l11583.sum = true ∧ gapOK (ssBits l11583) 5 l11583.sum = true ∧
      l1053.toFinset = (1053 : ℕ).properDivisors ∧ l1053.Nodup ∧
      gapOK (ssBits l1053) 61 l1053.sum = true ∧
      raiseOK 1053 11 1 69 61 l1053.sum l11583.sum 9 = true ∧
      stepsOK 69 5 (1053 * 11 ^ (1 + 9)) (raiseSum 1053 11 1 l1053.sum l11583.sum 9)
        [(17, 10), (23, 10)] = true ∧
      stepsEnd (1053 * 11 ^ (1 + 9)) (raiseSum 1053 11 1 l1053.sum l11583.sum 9)
        [(17, 10), (23, 10)] =
        (3 ^ 4 * 11 ^ 10 * 13 * 17 ^ 10 * 23 ^ 10, 2202693082240354409877835896112285871741) := by
  decide +kernel

/-- **A last-prime family with three high exponents.** No `3^4 · 11^10 · 13 · 17^10 · 23^10 · q`
(`q` prime, not dividing the prefix) is weird. The prefix is deficient; `n q` is abundant only for
`q ≤ 57`, and every such prime is covered by the interval (`c = 69`, `g = 5`) carried from the base
`11583` through nine raises of the exponent of `11` and the prime-power steps `17^10`, `23^10`. -/
theorem not_weird_mul_prime_example {q : ℕ} (hq : q.Prime)
    (hqn : ¬ q ∣ 3 ^ 4 * 11 ^ 10 * 13 * 17 ^ 10 * 23 ^ 10) :
    ¬ (3 ^ 4 * 11 ^ 10 * 13 * 17 ^ 10 * 23 ^ 10 * q).Weird := by
  obtain ⟨hlA, hndA, hI, hG, hlB, hndB, hGB, hok, hst, hend⟩ := cert_11583_steps
  have h0 := intervalGap_of_raise_cert l11583 l1053 hlA hndA hI hG hlB hndB hGB (by norm_num)
    (by norm_num) (by norm_num) (by norm_num) hok
  have h1 := intervalGap_of_stepsOK (by norm_num) [(17, 10), (23, 10)] _ _
    (by norm_num) (by simp; norm_num) hst h0
  rw [hend] at h1
  have hq2 := hq.two_le
  refine not_weird_mul_prime_of_intervalGap (by norm_num) (by norm_num) h1 hq hqn ?_
  norm_num
  intro hab
  refine ⟨by omega, by omega, by omega, by omega⟩

end ErdosResearch.SubsetSumSteps
