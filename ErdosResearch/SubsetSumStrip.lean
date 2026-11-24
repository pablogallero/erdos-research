module

public import ErdosResearch.SubsetSumExpLoop

@[expose] public section

/-!
# Two small pieces for the limit-deficient layer of the sub-tree checker

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 74).

Session 74 measured `subOK` (`SubsetSumBlock`) in Python on real 3-prime prefixes of the search: almost every prime
`p` after the prefix is *limit-deficient* (`σ(n) p ≤ 2 n (p − 1)`), so `n p^f` is deficient for every `f` and `fLoop`
can never stop. The planned replacement is a staircase over the exponents whose infinite rows and columns are closed by a
limit inequality. This file has its basic lemma, and a composite test that also catches squarefree composites dividing
`P1000` (which `skipB` lets through, e.g. `35`, `533`):

* `not_abundant_of_limit`: `σ(m) p ≤ 2 m (p − 1)` (with `σ(m) = S + m`, `p ∤ m`) ⇒ `m p^f` is not abundant, for every `f`.
* `skipS q L`: some `s ∈ L` with `2 ≤ s < q` divides `q`; `prime_imp_not_skipS`: primes are never skipped.

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumStrip

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumFifthLoop

/-- **Row / column strip.** If `σ(m) p ≤ 2 m (p − 1)` (with `σ(m) = S + m`), then `m p^f` is not abundant for any `f`. -/
theorem not_abundant_of_limit {m S p : ℕ} (hm : 0 < m) (hS : ∑ y ∈ m.properDivisors, y = S) (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hσ : (S + m) * p ≤ 2 * m * (p - 1)) (f : ℕ) : ¬ (m * p ^ f).Abundant := by
  intro hab
  have hsum := ppSum_eq hm hp hpm hS f
  have hab' : m * p ^ f < ppSum m p S f := by rw [← hsum]; exact hab
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 2 := ⟨p - 2, by have := hp.two_le; omega⟩
  have hx := ppSum_exact' m (p' + 2) S f
  rw [pow_succ] at hx
  have hσ' : (S + m) * (p' + 2) ≤ 2 * m * (p' + 1) := by
    have : p' + 2 - 1 = p' + 1 := by omega
    rwa [this] at hσ
  set T := ppSum m (p' + 2) S f
  set x := (p' + 2) ^ f
  have h1 : (T + m * x) * (p' + 1) + (S + m) = (S + m) * (p' + 2) * x := by
    have := hx; ring_nf at this ⊢; linarith
  have h2 : (S + m) * (p' + 2) * x ≤ 2 * m * (p' + 1) * x := Nat.mul_le_mul_right x hσ'
  have h3 : (T + m * x) * (p' + 1) < (2 * m * x) * (p' + 1) := by nlinarith
  have h4 := Nat.lt_of_mul_lt_mul_right h3
  linarith

/-- Composite test by small divisors: some `s ∈ L` with `2 ≤ s < q` divides `q`. -/
def skipS (q : ℕ) (L : List ℕ) : Bool :=
  L.any fun s => decide (2 ≤ s) && decide (s < q) && q % s == 0

theorem prime_imp_not_skipS {q : ℕ} (hq : q.Prime) (L : List ℕ) : skipS q L = false := by
  simp only [skipS, List.any_eq_false, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, not_and]
  intro s _ h2 hmod
  rcases hq.eq_one_or_self_of_dvd s (Nat.dvd_of_mod_eq_zero hmod) with h | h <;> omega

/-- Sanity: `35` and `533 = 13 · 41` are skipped with the odd primes below `50` (`skipB q P1000` keeps both). -/
example : skipS 35 [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] = true := by decide
example : skipS 533 [3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47] = true := by decide

end ErdosResearch.SubsetSumStrip
