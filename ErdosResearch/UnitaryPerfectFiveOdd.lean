module

public import ErdosResearch.UnitaryPerfectFourOdd

@[expose] public section

/-!
# Erdős Problem 1052: no unitary perfect number has exactly five odd prime factors

This proof does not generate a case tree. It uses a *reflective* checker instead:
* `upnCheck` is a Boolean search over sorted, pairwise coprime lists `y₁ < ⋯ < y_r`. It
  decides that `Q · ∏ (1 + yᵢ) = 2 P · ∏ yᵢ` has no solution;
* `upnCheck_sound` proves, once and for all, that a `true` answer is correct;
* the kernel evaluates `upnCheck … = true` (`decide +kernel`), using its GMP-accelerated
  arithmetic on `Nat`.

`upnCheck`, `upnCheck_sound` and their helper lemmas are defined in `UnitaryPerfectFourOdd.lean`
(since session 61, where they also prove the four-odd-prime case); this file only runs them.

The search. Let `y` be the smallest remaining variable, with `y ≥ L`.
* If `2P ≤ Q`, there is no solution, since `∏ (1 + y) > ∏ y`.
* With one variable left, the equation is linear: `y = Q / (2P - Q)`.
* Otherwise, if `Q · ∏_{j<r} (L + 1 + j) < 2P · ∏_{j<r} (L + j)`, there is no solution, because
  `(1 + y)/y` decreases and sorted variables satisfy `yⱼ ≥ L + j` (`prod_succ_mul_le`).
* Otherwise, split into `y = L`, pruned if `L` shares a factor with an earlier variable, and
  `y ≥ L + 1`.

`not_isUnitaryPerfect_of_card_primeFactors_eq_six`: no UPN has exactly six prime factors (five
odd). Known mathematically (Wall 1988 has "≥ 9 odd prime factors" for a sixth UPN; see
`notes/erdos-1052.md`). New only as a formalisation.
-/

namespace ErdosResearch.Erdos1052

/-- Kernel computation (about 30 s): no sorted, pairwise coprime `2 ≤ y₁ < ⋯ < y₆` satisfies
`∏ (1 + yᵢ) = 2 ∏ yᵢ`. The search visits about 29400 nodes, with depth `< 2100 ≤ fuel`. -/
theorem upnCheck_six : upnCheck 5000 1 1 2 [] 6 = true := by decide +kernel

/-- There is no unitary perfect number with exactly six prime factors (five of them odd). -/
theorem not_isUnitaryPerfect_of_card_primeFactors_eq_six {n : ℕ} (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 6) : False := by
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  obtain ⟨l, hsort, hlen, hgt, hcop, hprod, hsig⟩ := exists_sorted_factors hpos.ne'
  rw [hcard] at hlen
  refine upnCheck_sound 5000 1 1 2 [] 6 upnCheck_six (by norm_num) l hlen hsort
    (fun y hy => hgt y hy) (by simp) hcop ?_
  rw [one_mul, mul_one, hsig, hs, hprod]

/-- Classification of unitary perfect numbers with at most six prime factors (i.e. at most five
odd prime factors): they are exactly `6`, `60`, `90` and `87360`. -/
theorem isUnitaryPerfect_of_card_primeFactors_le_six_iff {n : ℕ}
    (hcard : n.primeFactors.card ≤ 6) :
    IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 := by
  rcases (show n.primeFactors.card ≤ 5 ∨ n.primeFactors.card = 6 by omega) with h5 | h6
  · exact isUnitaryPerfect_of_card_primeFactors_le_five_iff h5
  · constructor
    · intro h; exact (not_isUnitaryPerfect_of_card_primeFactors_eq_six h h6).elim
    · rintro (rfl | rfl | rfl | rfl)
      exacts [isUnitaryPerfect_6, isUnitaryPerfect_60, isUnitaryPerfect_90,
        isUnitaryPerfect_87360]

end ErdosResearch.Erdos1052
