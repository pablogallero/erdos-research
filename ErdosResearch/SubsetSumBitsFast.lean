module

public import ErdosResearch.SubsetSumLate

@[expose] public section

/-!
# Interval and gap checks on a bitset by whole-number operations

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 58).

`intervalOK` / `gapOK` (`SubsetSumCert.lean`) test one bit at a time, so the kernel does about `s²` bit operations
for a bitset of `s` bits: a base near `10^6` runs out of memory. Here both checks use a few masks and shifts
(`&&&`, `|||`, `>>>`, `2^w − 1`), which the kernel evaluates with GMP.

* `intervalOKB`, `gapOKB` and their soundness; `intervalGap_of_bitsB` (as `intervalGap_of_bits`).

Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumBitsFast

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumCert ErdosResearch.SubsetSumSteps

/-- Every bit of `b` in `[c, s − c]` is set (vacuous if `s < 2c`). -/
def intervalOKB (b c s : ℕ) : Bool :=
  decide (s < 2 * c) || ((b >>> c) &&& (2 ^ (s + 1 - 2 * c) - 1) == 2 ^ (s + 1 - 2 * c) - 1)

theorem testBit_of_intervalOKB {b c s : ℕ} (h : intervalOKB b c s = true) :
    ∀ x, c ≤ x → x + c ≤ s → b.testBit x = true := by
  intro x h1 h2
  simp only [intervalOKB, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  rcases h with h | h
  · omega
  have := congrArg (fun t => t.testBit (x - c)) h
  simp only [Nat.testBit_and, Nat.testBit_shiftRight, Nat.testBit_two_pow_sub_one] at this
  have hlt : x - c < s + 1 - 2 * c := by omega
  simp only [hlt, decide_true, Bool.and_true] at this
  rwa [show c + (x - c) = x by omega] at this

/-- `b` shifted right by `1, …, k`, ORed together (bit `x` set iff some bit `x + i`, `1 ≤ i ≤ k`, is set). -/
def orShifts (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => orShifts b k ||| (b >>> (k + 1))

lemma exists_of_testBit_orShifts (b x : ℕ) :
    ∀ k, (orShifts b k).testBit x = true → ∃ i, 1 ≤ i ∧ i ≤ k ∧ b.testBit (x + i) = true
  | 0, h => by simp [orShifts] at h
  | k + 1, h => by
    simp only [orShifts, Nat.testBit_or, Bool.or_eq_true, Nat.testBit_shiftRight] at h
    rcases h with h | h
    · obtain ⟨i, h1, h2, h3⟩ := exists_of_testBit_orShifts b x k h
      exact ⟨i, h1, by omega, h3⟩
    · exact ⟨k + 1, by omega, le_refl _, by rwa [Nat.add_comm]⟩

/-- After every `x < s` some `z ∈ (x, x + g]`, `z ≤ s`, has its bit set in `b`. -/
def gapOKB (b g s : ℕ) : Bool :=
  orShifts (b &&& (2 ^ (s + 1) - 1)) g &&& (2 ^ s - 1) == 2 ^ s - 1

theorem exists_testBit_of_gapOKB {b g s : ℕ} (h : gapOKB b g s = true) :
    ∀ x < s, ∃ z, b.testBit z = true ∧ x < z ∧ z ≤ x + g ∧ z ≤ s := by
  intro x hx
  simp only [gapOKB, beq_iff_eq] at h
  have := congrArg (fun t => t.testBit x) h
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, hx, decide_true, Bool.and_true] at this
  obtain ⟨i, h1, h2, h3⟩ := exists_of_testBit_orShifts _ x g this
  simp only [Nat.testBit_and, Nat.testBit_two_pow_sub_one, Bool.and_eq_true, decide_eq_true_eq] at h3
  exact ⟨x + i, h3.1, by omega, by omega, by omega⟩

/-- A bitset certificate (fast checks) gives `IntervalGap`. -/
theorem intervalGap_of_bitsB {n c g : ℕ} (l : List ℕ) (hl : l.toFinset = n.properDivisors)
    (hnd : l.Nodup) (hI : intervalOKB (ssBits l) c l.sum = true)
    (hG : gapOKB (ssBits l) g l.sum = true) : IntervalGap n l.sum c g := by
  have hs : ∑ y ∈ n.properDivisors, y = l.sum := by
    rw [← hl, List.sum_toFinset _ hnd, List.map_id']
  have hmem : ∀ x, (ssBits l).testBit x = true → x ∈ subsetSums n.properDivisors := by
    intro x hx; rw [← hl]; exact mem_subsetSums_of_testBit l hnd x hx
  refine ⟨hs, fun x h1 h2 => hmem x (testBit_of_intervalOKB hI x h1 h2), fun x hx => ?_⟩
  obtain ⟨z, hz, h1, h2, h3⟩ := exists_testBit_of_gapOKB hG x hx
  exact ⟨z, hmem z hz, h1, h2, h3⟩

end ErdosResearch.SubsetSumBitsFast
