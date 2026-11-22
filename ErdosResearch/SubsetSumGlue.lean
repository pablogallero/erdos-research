module

public import Mathlib

@[expose] public section

/-!
# Gluing intervals of subset sums

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 53).

The family search (`scripts/odd_weird_family.{py,c}`) needs, for every deficient prefix `M`, an exact
description of the set `SS(div M)` of subset sums of the divisors of `M`. Today it sorts all divisors
and runs the chain condition (`SubsetSumChain.lean`). The planned *multiplicative interval lemma*
avoids the sort by building `SS` prime by prime, since `div(A p) = div A ∪ p · div A` for `p ∤ A`.
This file proves the additive core of that plan:

* `glue`: if `A ⊇ [c, T − c]` and `B` runs from `0` to `U` with consecutive gaps at most
  `T − 2c + 1`, then `A + B ⊇ [c, T + U − c]`.
* `subsetSums_union`: for disjoint finsets, `SS s₁ + SS s₂ ⊆ SS (s₁ ∪ s₂)`.
* `subsetSums_image_mul`: `SS (k · s) ⊇ k · SS s`.
* `glue_subsetSums`: the two combined, i.e. the interval step of the plan.
* `divisors_mul_prime`: `div(n p) = div n ∪ p · div n`, a disjoint union, for a prime `p ∤ n`.

All of this is elementary and classical; it is a building block, not a new result. The paper obstacle
recorded in the notes (the middle gap `(σ(A) − A, A)` of a deficient `A`) is not addressed here.
-/

namespace ErdosResearch.SubsetSumGlue

open Finset

/-- The subset sums of a finset of naturals. -/
def subsetSums (s : Finset ℕ) : Set ℕ := {m | ∃ t ⊆ s, ∑ x ∈ t, x = m}

lemma zero_mem_subsetSums (s : Finset ℕ) : 0 ∈ subsetSums s := ⟨∅, empty_subset _, by simp⟩

lemma sum_mem_subsetSums (s : Finset ℕ) : ∑ x ∈ s, x ∈ subsetSums s := ⟨s, subset_refl _, rfl⟩

/-- Gluing an interval with a set of bounded gaps. `A` contains every `x` with `c ≤ x` and
`x + c ≤ T`; `B` contains `0`, and after every `x < U` it has an element `b ≤ U` with
`b + 2c ≤ x + T + 1` (a gap of at most `T − 2c + 1`). Then every `m` with `c ≤ m` and
`m + c ≤ T + U` is `a + b` with `a ∈ A`, `b ∈ B`. -/
theorem glue {A B : Set ℕ} {c T U : ℕ}
    (hA : ∀ x, c ≤ x → x + c ≤ T → x ∈ A)
    (hB0 : 0 ∈ B)
    (hB : ∀ x < U, ∃ b ∈ B, x < b ∧ b ≤ U ∧ b + 2 * c ≤ x + T + 1)
    {m : ℕ} (hm1 : c ≤ m) (hm2 : m + c ≤ T + U) :
    ∃ a ∈ A, ∃ b ∈ B, a + b = m := by
  classical
  -- the largest `b ∈ B` with `b ≤ U` and `b + c ≤ m`
  set F := (range (U + 1)).filter (fun b => b ∈ B ∧ b + c ≤ m) with hF
  have h0 : 0 ∈ F := by simp [hF, hB0, hm1]
  set b := F.max' ⟨0, h0⟩ with hb
  have hbF : b ∈ F := max'_mem _ _
  simp only [hF, mem_filter, mem_range] at hbF
  obtain ⟨hbU, hbB, hbm⟩ := hbF
  refine ⟨m - b, ?_, b, hbB, by omega⟩
  apply hA _ (by omega)
  rcases Nat.lt_or_ge b U with hlt | hge
  · obtain ⟨b', hb'B, hbb', hb'U, hb'gap⟩ := hB b hlt
    have : ¬ b' + c ≤ m := by
      intro h
      have hmem : b' ∈ F := by simp [hF, hb'B, h]; omega
      have := le_max' F b' hmem
      omega
    omega
  · omega

/-- Subset sums of a disjoint union contain the sumset. -/
lemma subsetSums_union {s₁ s₂ : Finset ℕ} (hd : Disjoint s₁ s₂) {a b : ℕ}
    (ha : a ∈ subsetSums s₁) (hb : b ∈ subsetSums s₂) : a + b ∈ subsetSums (s₁ ∪ s₂) := by
  obtain ⟨t₁, ht₁, rfl⟩ := ha
  obtain ⟨t₂, ht₂, rfl⟩ := hb
  exact ⟨t₁ ∪ t₂, union_subset_union ht₁ ht₂,
    sum_union (disjoint_of_subset_left ht₁ (disjoint_of_subset_right ht₂ hd))⟩

/-- Scaling: `k · SS s ⊆ SS (k · s)`. -/
lemma subsetSums_image_mul {s : Finset ℕ} (k : ℕ) {a : ℕ} (ha : a ∈ subsetSums s) :
    k * a ∈ subsetSums (s.image (k * ·)) := by
  obtain ⟨t, ht, rfl⟩ := ha
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · exact ⟨∅, empty_subset _, by simp⟩
  refine ⟨t.image (k * ·), image_subset_image ht, ?_⟩
  rw [sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hk h), mul_sum]

/-- The interval step: if the subset sums of `s₁` cover `[c, T − c]` and those of `s₂` (total `U`)
have gaps at most `T − 2c + 1`, then the subset sums of `s₁ ∪ s₂` cover `[c, T + U − c]`. -/
theorem glue_subsetSums {s₁ s₂ : Finset ℕ} (hd : Disjoint s₁ s₂) {c T : ℕ}
    (h₁ : ∀ x, c ≤ x → x + c ≤ T → x ∈ subsetSums s₁)
    (h₂ : ∀ x < ∑ y ∈ s₂, y, ∃ b ∈ subsetSums s₂,
      x < b ∧ b ≤ ∑ y ∈ s₂, y ∧ b + 2 * c ≤ x + T + 1)
    {m : ℕ} (hm1 : c ≤ m) (hm2 : m + c ≤ T + ∑ y ∈ s₂, y) :
    m ∈ subsetSums (s₁ ∪ s₂) := by
  obtain ⟨a, ha, b, hb, rfl⟩ :=
    glue h₁ (zero_mem_subsetSums s₂) h₂ hm1 hm2
  exact subsetSums_union hd ha hb

/-- Special case: when `s₂` is *complete* (every value up to its total is a subset sum, e.g. by the
chain condition of `SubsetSumChain.lean`), gap `1` suffices, so only `2c ≤ T` is needed. -/
theorem glue_subsetSums_complete {s₁ s₂ : Finset ℕ} (hd : Disjoint s₁ s₂) {c T : ℕ} (hcT : 2 * c ≤ T)
    (h₁ : ∀ x, c ≤ x → x + c ≤ T → x ∈ subsetSums s₁)
    (h₂ : ∀ x ≤ ∑ y ∈ s₂, y, x ∈ subsetSums s₂)
    {m : ℕ} (hm1 : c ≤ m) (hm2 : m + c ≤ T + ∑ y ∈ s₂, y) :
    m ∈ subsetSums (s₁ ∪ s₂) :=
  glue_subsetSums hd h₁ (fun x hx => ⟨x + 1, h₂ _ hx, by omega, hx, by omega⟩) hm1 hm2

/-- The divisors of `n p`, for a prime `p ∤ n`, are the divisors of `n` together with `p` times
them, and the two parts are disjoint. This is the step `div(A p) = div A ∪ p · div A` along which the
interval is meant to be propagated (with `glue_subsetSums` and `subsetSums_image_mul`). -/
theorem divisors_mul_prime {n p : ℕ} (hp : p.Prime) (hpn : ¬ p ∣ n) :
    (n * p).divisors = n.divisors ∪ n.divisors.image (p * ·) ∧
      Disjoint n.divisors (n.divisors.image (p * ·)) := by
  constructor
  · ext d
    simp only [mem_union, mem_image, Nat.mem_divisors]
    constructor
    · rintro ⟨hd, hnp⟩
      have hn : n ≠ 0 := fun h => by simp [h] at hnp
      by_cases hpd : p ∣ d
      · obtain ⟨e, rfl⟩ := hpd
        refine Or.inr ⟨e, ⟨?_, hn⟩, rfl⟩
        rw [mul_comm n p] at hd
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos hd
      · refine Or.inl ⟨?_, hn⟩
        have hcop : Nat.Coprime d p := (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd))
        exact hcop.dvd_of_dvd_mul_right hd
    · rintro (⟨hd, hn⟩ | ⟨e, ⟨he, hn⟩, rfl⟩)
      · exact ⟨Dvd.dvd.mul_right hd p, mul_ne_zero hn hp.ne_zero⟩
      · refine ⟨?_, mul_ne_zero hn hp.ne_zero⟩
        rw [mul_comm n p]
        exact Nat.mul_dvd_mul_left p he
  · rw [disjoint_left]
    rintro d hd hd'
    obtain ⟨e, he, rfl⟩ := mem_image.1 hd'
    exact hpn ((dvd_mul_right p e).trans (Nat.dvd_of_mem_divisors hd))

/-- Sanity check: the divisors of `15 · 7 = 105` split as those of `15` and `7` times them. -/
example : (15 * 7).divisors = (15 : ℕ).divisors ∪ (15 : ℕ).divisors.image (7 * ·) :=
  (divisors_mul_prime (by norm_num) (by norm_num)).1

end ErdosResearch.SubsetSumGlue
