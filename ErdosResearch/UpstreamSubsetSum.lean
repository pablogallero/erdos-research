module

public import Mathlib

@[expose] public section

/-!
# General `Finset.subsetSum` API (candidate for a second Mathlib patch)

Reference: <https://www.erdosproblems.com/470>; plan in `notes/mathlib-upstream.md` (session 94).

`Mathlib/Combinatorics/Additive/SubsetSum.lean` (master 348837d3) only has `subsetSum_mono`,
`subsetSum_erase_zero` and the inclusion `a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum`. The
equalities below are the general form of `ErdosResearch/SubsetSumGlue.lean` (`subsetSums_union`,
`subsetSums_image_mul`), stated for `Finset.subsetSum` in any commutative monoid:

* `Finset.subsetSum_empty`, `Finset.subsetSum_singleton`, `Finset.sum_mem_subsetSum`;
* `Finset.subsetSum_insert`: `(insert a A).subsetSum = A.subsetSum ∪ (a +ᵥ A.subsetSum)`, `a ∉ A`;
* `Finset.subsetSum_union`: `(A ∪ B).subsetSum = A.subsetSum + B.subsetSum` for disjoint `A`, `B`;
* `Finset.subsetSum_image`: `(A.image f).subsetSum = A.subsetSum.image f` for an additive monoid hom
  injective on `A`.

Elementary; not a research result. Names live in `ErdosResearch.Upstream` so they cannot clash with
a future Mathlib version.
-/

namespace ErdosResearch.Upstream

open Finset
open scoped Pointwise

variable {M N : Type*} [DecidableEq M] [AddCommMonoid M] [DecidableEq N] [AddCommMonoid N]
  {A B : Finset M} {a : M}

@[simp] lemma subsetSum_empty : (∅ : Finset M).subsetSum = {0} := by
  ext x; simp [mem_subsetSum_iff, eq_comm]

@[simp] lemma subsetSum_singleton : ({a} : Finset M).subsetSum = {0, a} := by
  ext x
  simp only [mem_subsetSum_iff, subset_singleton_iff, mem_insert, mem_singleton]
  constructor
  · rintro ⟨B, rfl | rfl, rfl⟩ <;> simp
  · rintro (rfl | rfl)
    · exact ⟨∅, Or.inl rfl, by simp⟩
    · exact ⟨_, Or.inr rfl, by simp⟩

lemma sum_mem_subsetSum : ∑ x ∈ A, x ∈ A.subsetSum := mem_subsetSum_iff.mpr ⟨A, subset_refl _, rfl⟩

/-- The subset sums of a disjoint union are the sumset of the subset sums. -/
lemma subsetSum_union (h : Disjoint A B) : (A ∪ B).subsetSum = A.subsetSum + B.subsetSum := by
  ext x
  simp only [mem_add, mem_subsetSum_iff]
  constructor
  · rintro ⟨C, hC, rfl⟩
    refine ⟨_, ⟨C ∩ A, inter_subset_right, rfl⟩, _, ⟨C ∩ B, inter_subset_right, rfl⟩, ?_⟩
    rw [← sum_union (disjoint_of_subset_left inter_subset_right
      (disjoint_of_subset_right inter_subset_right h)), ← inter_union_distrib_left,
      inter_eq_left.mpr hC]
  · rintro ⟨_, ⟨C, hC, rfl⟩, _, ⟨D, hD, rfl⟩, rfl⟩
    exact ⟨C ∪ D, union_subset_union hC hD,
      sum_union (disjoint_of_subset_left hC (disjoint_of_subset_right hD h))⟩

/-- Inserting a new element: the old subset sums, plus the old subset sums shifted by `a`. -/
lemma subsetSum_insert (ha : a ∉ A) :
    (insert a A).subsetSum = A.subsetSum ∪ (a +ᵥ A.subsetSum) := by
  rw [insert_eq, union_comm, subsetSum_union (disjoint_singleton_right.mpr ha),
    subsetSum_singleton]
  ext x
  simp only [mem_add, mem_insert, mem_singleton, mem_union, mem_vadd_finset, vadd_eq_add]
  constructor
  · rintro ⟨y, hy, z, rfl | rfl, rfl⟩
    · exact Or.inl (by simpa using hy)
    · exact Or.inr ⟨y, hy, add_comm _ _⟩
  · rintro (hx | ⟨y, hy, rfl⟩)
    · exact ⟨x, hx, 0, Or.inl rfl, add_zero x⟩
    · exact ⟨y, hy, a, Or.inr rfl, add_comm _ _⟩

/-- Subset sums commute with an additive monoid hom that is injective on the set. -/
lemma subsetSum_image (f : M →+ N) (hf : Set.InjOn f A) :
    (A.image f).subsetSum = A.subsetSum.image f := by
  ext y
  simp only [mem_image, mem_subsetSum_iff]
  constructor
  · rintro ⟨C, hC, rfl⟩
    obtain ⟨D, hDA, rfl⟩ := subset_image_iff.mp hC
    refine ⟨_, ⟨D, hDA, rfl⟩, ?_⟩
    rw [map_sum, sum_image fun x hx y hy hxy ↦ hf (hDA hx) (hDA hy) hxy]
  · rintro ⟨_, ⟨D, hDA, rfl⟩, rfl⟩
    refine ⟨D.image f, image_subset_image hDA, ?_⟩
    rw [map_sum, sum_image fun x hx y hy hxy ↦ hf (hDA hx) (hDA hy) hxy]

/-- Sanity check of `subsetSum_insert`: the subset sums of `{1, 2}` are `0, 1, 2, 3`. -/
example : ({1, 2} : Finset ℕ).subsetSum = {0, 1, 2, 3} := by
  rw [subsetSum_insert (by decide), subsetSum_singleton]
  ext m
  simp only [mem_union, mem_insert, mem_singleton, mem_vadd_finset, vadd_eq_add]
  simp only [or_and_right, exists_or, exists_eq_left, or_assoc]
  omega

/-- Sanity check of `subsetSum_image`: scaling `{1, 2}` by `3` scales its subset sums. -/
example : (({1, 2} : Finset ℕ).image (AddMonoidHom.mulLeft 3)).subsetSum =
    ({0, 1, 2, 3} : Finset ℕ).image (AddMonoidHom.mulLeft 3) := by
  rw [subsetSum_image _ (mul_right_injective₀ (by norm_num : (3 : ℕ) ≠ 0)).injOn,
    subsetSum_insert (by decide), subsetSum_singleton]
  congr 1
  ext m
  simp only [mem_union, mem_insert, mem_singleton, mem_vadd_finset, vadd_eq_add]
  simp only [or_and_right, exists_or, exists_eq_left, or_assoc]
  omega

end ErdosResearch.Upstream
