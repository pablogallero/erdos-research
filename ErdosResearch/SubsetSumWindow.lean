module

public import ErdosResearch.SubsetSumStrip

@[expose] public section

/-!
# Window lemma: every prime in a range belongs to a given list

A cheap Boolean check (`windowOK`) over a range `[lo, hi)` says that each odd number in the range is either
a proven composite (`skipS`, a divisor test with a short list of small numbers) or appears in a list `L`.
Then every prime `q > 2` in the range is in `L`. Combined theorems use this to dispatch to per-case theorems
without testing primality in the kernel.

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 84). Elementary; not a new
result on #470.
-/

namespace ErdosResearch.SubsetSumWindow

open ErdosResearch.SubsetSumStrip

/-- Every odd `x ∈ [lo, hi)` is a proven composite (`skipS x P`) or belongs to `L`. -/
def windowOK (lo hi : ℕ) (P L : List ℕ) : Bool :=
  (List.range' lo (hi - lo)).all (fun x => x % 2 == 0 || skipS x P || L.contains x)

theorem mem_of_windowOK {q lo hi : ℕ} {P L : List ℕ} (hq : q.Prime) (h2 : 2 < q) (hlo : lo ≤ q)
    (hhi : q < hi) (hc : windowOK lo hi P L = true) : q ∈ L := by
  unfold windowOK at hc
  rw [List.all_eq_true] at hc
  have hx := hc q (List.mem_range'_1.mpr ⟨hlo, by omega⟩)
  have hodd : q % 2 = 1 := Nat.odd_iff.mp (hq.odd_of_ne_two (by omega))
  rw [prime_imp_not_skipS hq] at hx
  simpa [hodd] using hx

/-- A prime `r` that divides neither `n` nor the prime `p ≠ r` does not divide `n * p ^ f`. -/
theorem not_dvd_mul_pow {r n p : ℕ} (f : ℕ) (hr : r.Prime) (hrn : ¬ r ∣ n) (hp : p.Prime) (hrp : r ≠ p) :
    ¬ r ∣ n * p ^ f := by
  intro h
  rcases (Nat.Prime.dvd_mul hr).1 h with h | h
  · exact hrn h
  · exact hrp ((Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow h))

theorem not_dvd_mul {r n p : ℕ} (hr : r.Prime) (hrn : ¬ r ∣ n) (hp : p.Prime) (hrp : r ≠ p) :
    ¬ r ∣ n * p := by
  simpa using not_dvd_mul_pow 1 hr hrn hp hrp

/-- Sanity: in `[24, 40)` the odd non-composites (with divisors `3, 5`) are exactly `29, 31, 37`. -/
example : windowOK 24 40 [3, 5] [29, 31, 37] = true := by decide
example : windowOK 24 40 [3, 5] [29, 31] = false := by decide

end ErdosResearch.SubsetSumWindow
