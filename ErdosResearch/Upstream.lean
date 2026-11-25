module

public import Mathlib

@[expose] public section

/-!
# Draft for upstreaming to Mathlib (NOT submitted; needs Pablo's approval)

Small, general lemmas that this repository needed and that Mathlib (checked against `master` on
2026-11-25) does not have. They are written in Mathlib style, so that a PR only has to move them:

* to `Mathlib/NumberTheory/FactorisationProperties.lean` (namespace `Nat`):
  `Pseudoperfect.of_dvd`, `Pseudoperfect.mul_left`, `Pseudoperfect.not_deficient`,
  `Weird.not_pseudoperfect_of_dvd`, `Deficient.not_weird`, `Perfect.not_weird`;
* to `Mathlib/Combinatorics/Additive/SubsetSum.lean` (namespace `Finset`):
  `mem_subsetSum_of_chain` (the chain criterion of Stewart 1954 / Brown 1961: if every element is
  at most one more than the sum of the smaller ones, every `m ≤ ∑ A` is a subset sum), plus the
  consequence `Nat.pseudoperfect_of_chain` for pseudoperfect numbers.

Here they live in `ErdosResearch.Upstream` so they do not clash with the `_root_` lemma
`Nat.Pseudoperfect.of_dvd` of `OddWeirdThree.lean`. See `notes/mathlib-upstream.md`.
-/

namespace ErdosResearch.Upstream

open Finset

/-! ### Pseudoperfect and weird numbers -/

/-- A nonzero multiple of a pseudoperfect number is pseudoperfect (scale the subset). -/
theorem Pseudoperfect.of_dvd {m n : ℕ} (h : m.Pseudoperfect) (hd : m ∣ n) (hn : n ≠ 0) :
    n.Pseudoperfect := by
  obtain ⟨-, s, hs, hsum⟩ := h
  obtain ⟨k, rfl⟩ := hd
  have hk : 0 < k := Nat.pos_of_ne_zero (by rintro rfl; simp at hn)
  refine ⟨Nat.pos_of_ne_zero hn, s.image (· * k), ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi, rfl⟩ := mem_image.mp hx
    obtain ⟨hdvd, hlt⟩ := Nat.mem_properDivisors.mp (hs hi)
    exact Nat.mem_properDivisors.mpr ⟨Nat.mul_dvd_mul_right hdvd k,
      Nat.mul_lt_mul_of_pos_right hlt hk⟩
  · rw [sum_image (fun x _ y _ hxy => Nat.eq_of_mul_eq_mul_right hk hxy), ← sum_mul, hsum]

theorem Pseudoperfect.mul_left {m n : ℕ} (h : n.Pseudoperfect) (hm : m ≠ 0) :
    (m * n).Pseudoperfect :=
  Pseudoperfect.of_dvd h (dvd_mul_left n m) (mul_ne_zero hm h.1.ne')

/-- A pseudoperfect number is not deficient. -/
theorem Pseudoperfect.not_deficient {n : ℕ} (h : n.Pseudoperfect) : ¬ n.Deficient := by
  obtain ⟨-, s, hs, hsum⟩ := h
  intro hd
  have := sum_le_sum_of_subset (f := id) hs
  simp only [id] at this
  exact absurd hd (by unfold Nat.Deficient; omega)

/-- No divisor of a weird number is pseudoperfect: weird numbers are multiples of no
pseudoperfect number. -/
theorem Weird.not_pseudoperfect_of_dvd {m n : ℕ} (h : n.Weird) (hd : m ∣ n) :
    ¬ m.Pseudoperfect := fun hm => h.2 (Pseudoperfect.of_dvd hm hd h.1.pos.ne')

theorem Deficient.not_weird {n : ℕ} (h : n.Deficient) : ¬ n.Weird := fun hw => by
  have := hw.1
  unfold Nat.Deficient at h
  unfold Nat.Abundant at this
  omega

theorem Perfect.not_weird {n : ℕ} (h : n.Perfect) : ¬ n.Weird := fun hw =>
  hw.2 (Nat.Perfect.pseudoperfect h)

/-! ### The chain criterion for subset sums -/

/-- **Chain criterion** (Stewart 1954, Brown 1961). If every element of a finset `A` of naturals is
at most one more than the sum of the elements of `A` smaller than it, then every `m ≤ ∑ A` is the sum
of a subset of `A`. -/
theorem mem_subsetSum_of_chain (A : Finset ℕ)
    (hA : ∀ a ∈ A, a ≤ ∑ b ∈ A with b < a, b + 1) {m : ℕ} (hm : m ≤ ∑ a ∈ A, a) :
    m ∈ A.subsetSum := by
  induction A using Finset.induction_on_max generalizing m with
  | empty => simp_all
  | insert a s hlt ih =>
    have ha : a ∉ s := fun h => lt_irrefl a (hlt a h)
    have hfa : (∑ b ∈ insert a s with b < a, b) = ∑ b ∈ s, b := by
      rw [filter_insert, ite_eq_right (lt_irrefl a), filter_true_of_mem hlt]
    have hs : ∀ x ∈ s, x ≤ ∑ b ∈ s with b < x, b + 1 := by
      intro x hx
      have := hA x (mem_insert_of_mem hx)
      rwa [filter_insert, ite_eq_right (not_lt.mpr (hlt x hx).le)] at this
    have hai : a ≤ ∑ b ∈ s, b + 1 := hfa ▸ hA a (mem_insert_self a s)
    rw [sum_insert ha] at hm
    by_cases h : m ≤ ∑ b ∈ s, b
    · exact subsetSum_mono (subset_insert a s) (ih hs h)
    · obtain ⟨B, hB, hBsum⟩ := mem_subsetSum_iff.mp (ih hs (m := m - a) (by omega))
      refine mem_subsetSum_iff.mpr ⟨insert a B, insert_subset_insert a hB, ?_⟩
      rw [sum_insert (fun h' => ha (hB h')), hBsum]
      omega

/-- Consequence: a number that is not deficient and whose proper divisors satisfy the chain
condition is pseudoperfect. -/
theorem pseudoperfect_of_chain {n : ℕ} (hn : n ≠ 0)
    (hc : ∀ d ∈ n.properDivisors, d ≤ ∑ e ∈ n.properDivisors with e < d, e + 1)
    (hd : ¬ n.Deficient) : n.Pseudoperfect := by
  unfold Nat.Deficient at hd
  exact ⟨Nat.pos_of_ne_zero hn, mem_subsetSum_iff.mp
    (mem_subsetSum_of_chain _ hc (by omega))⟩

/-! ### Sanity checks -/

example : ¬ (70 : ℕ).Pseudoperfect := Nat.weird_seventy.2

/-- 12 is pseudoperfect by the chain criterion (proper divisors 1, 2, 3, 4, 6). -/
example : (12 : ℕ).Pseudoperfect :=
  pseudoperfect_of_chain (by norm_num) (by decide) (by decide)

end ErdosResearch.Upstream
