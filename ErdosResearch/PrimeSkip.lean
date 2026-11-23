module

public import Mathlib

@[expose] public section

/-!
# Skipping candidates without proving primality

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 67).

A reflective checker for the ω = 6 search cannot afford to prove that each prime `q` it steps over is prime.
It does not need to. It runs over every odd `q` and skips one only when a cheap test proves `q`
composite. It decides every other `q`, which covers the primes plus a few composites that are harmless and only
cost time. The test is one GMP gcd with a primorial `P`: `Nat.gcd q P ≠ 1` and `¬ q ∣ P`.

* `not_prime_of_skip`: the skip test is sound for any `P` (no hypothesis on `P` at all).
* `skipB` / `prime_imp_not_skipB`: the Boolean version, for use inside `decide +kernel` checkers.
-/

namespace ErdosResearch.PrimeSkip

/-- If `gcd q P ≠ 1` and `q ∤ P`, then `q` is not prime (for every `P`). -/
theorem not_prime_of_skip {q P : ℕ} (hg : Nat.gcd q P ≠ 1) (hd : ¬ q ∣ P) : ¬ q.Prime := by
  intro hq
  rcases (Nat.coprime_or_dvd_of_prime hq P) with h | h
  · exact hg h
  · exact hd h

/-- Boolean skip test: `true` only for proven composites. -/
def skipB (q P : ℕ) : Bool := Nat.gcd q P != 1 && P % q != 0

theorem prime_imp_not_skipB {q P : ℕ} (hq : q.Prime) : skipB q P = false := by
  unfold skipB
  by_contra h
  simp only [Bool.not_eq_false, Bool.and_eq_true, bne_iff_ne, ne_eq] at h
  exact not_prime_of_skip h.1 (fun hd => h.2 (Nat.mod_eq_zero_of_dvd hd)) hq

/-- Sanity check: with the primorial of the odd primes ≤ 7, the test skips `9` and `25` but keeps `11`. -/
example : skipB 9 105 = true ∧ skipB 25 105 = true ∧ skipB 11 105 = false := by decide

end ErdosResearch.PrimeSkip
