module

public import Mathlib

@[expose] public section

/-!
# Subset sums under the chain condition

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 52).

`scripts/odd_weird_family.py` / `odd_weird_family.c` certify that a whole interval `[c, S]` consists
of subset sums of the divisors of a prefix `M` by the *chain condition*: if the elements, taken in
decreasing order, satisfy `d ≤ 1 + (sum of the smaller ones)`, then every integer between `0` and the
total is a subset sum. This file proves that classical fact (it is the criterion behind practical
numbers; Stewart 1954, Zbl 0056.27004), as one more building block for a Lean version of the
family search. Nothing here is new mathematics.

* `subsetSum_of_chainOK_list`: for a list with the chain condition, every `m ≤ l.sum` is the sum of
  a sublist.
* `subsetSum_of_chainOK_finset`: the same for a finset, read in decreasing order.
* `pseudoperfect_of_chainOK`: the consequence for pseudoperfect numbers.
* `Complete.cons`, `complete_append`: a base certified another way (a bitset in the search) extended by
  the chain condition.
-/

namespace ErdosResearch.SubsetSumChain

/-- The chain condition, for a list read from its largest element: each element is at most one more
than the sum of the elements after it. -/
def ChainOK : List ℕ → Prop
  | [] => True
  | d :: r => d ≤ r.sum + 1 ∧ ChainOK r

/-- Decidability of `ChainOK`, by recursion on the list. -/
def decChainOK : (l : List ℕ) → Decidable (ChainOK l)
  | [] => isTrue trivial
  | d :: r => @instDecidableAnd (d ≤ r.sum + 1) (ChainOK r) _ (decChainOK r)

instance : DecidablePred ChainOK := decChainOK

@[simp] lemma chainOK_nil : ChainOK [] := trivial

@[simp] lemma chainOK_cons (d : ℕ) (r : List ℕ) :
    ChainOK (d :: r) ↔ d ≤ r.sum + 1 ∧ ChainOK r := Iff.rfl

/-- Under the chain condition every `m ≤ l.sum` is the sum of a sublist of `l`. -/
theorem subsetSum_of_chainOK_list :
    ∀ (l : List ℕ), ChainOK l → ∀ m ≤ l.sum, ∃ s : List ℕ, s.Sublist l ∧ s.sum = m
  | [], _, m, hm => ⟨[], List.Sublist.slnil, by simp at hm; simp [hm]⟩
  | d :: r, ⟨hd, hr⟩, m, hm => by
    simp only [List.sum_cons] at hm
    by_cases h : m ≤ r.sum
    · obtain ⟨s, hs, hsum⟩ := subsetSum_of_chainOK_list r hr m h
      exact ⟨s, hs.cons d, hsum⟩
    · obtain ⟨s, hs, hsum⟩ := subsetSum_of_chainOK_list r hr (m - d) (by omega)
      exact ⟨d :: s, hs.cons_cons d, by simp [hsum]; omega⟩

/-- `l` is *complete* when every `m ≤ l.sum` is the sum of a sublist of `l`. -/
def Complete (l : List ℕ) : Prop := ∀ m ≤ l.sum, ∃ s : List ℕ, s.Sublist l ∧ s.sum = m

/-- One chain step: a complete list stays complete when an element `d ≤ r.sum + 1` is put in front.
This lets a base checked another way (in the search: a bitset of the small divisors) be extended by
the chain condition. -/
theorem Complete.cons {r : List ℕ} (hr : Complete r) {d : ℕ} (hd : d ≤ r.sum + 1) :
    Complete (d :: r) := by
  intro m hm
  simp only [List.sum_cons] at hm
  by_cases h : m ≤ r.sum
  · obtain ⟨s, hs, hsum⟩ := hr m h
    exact ⟨s, hs.cons d, hsum⟩
  · obtain ⟨s, hs, hsum⟩ := hr (m - d) (by omega)
    exact ⟨d :: s, hs.cons_cons d, by simp [hsum]; omega⟩

/-- Base plus chain: if `r` is complete and `big` satisfies the chain condition relative to `r`
(each element at most one more than the sum of everything after it, `r` included), then
`big ++ r` is complete. -/
theorem complete_append :
    ∀ (big : List ℕ) {r : List ℕ}, Complete r → ChainOK (big ++ r) → Complete (big ++ r)
  | [], _, hr, _ => hr
  | _ :: big, _, hr, ⟨hd, hc⟩ => (complete_append big hr hc).cons hd

/-- Finset version: if the elements of `A`, sorted in decreasing order, satisfy the chain condition,
then every `m ≤ ∑ A` is the sum of a subset of `A`. -/
theorem subsetSum_of_chainOK_finset (A : Finset ℕ)
    (hA : ChainOK (A.sort (· ≥ ·))) (m : ℕ) (hm : m ≤ ∑ a ∈ A, a) :
    ∃ B ⊆ A, ∑ b ∈ B, b = m := by
  set l := A.sort (· ≥ ·) with hl
  have hnd : l.Nodup := Finset.sort_nodup A _
  have hsum : l.sum = ∑ a ∈ A, a := by
    conv_rhs => rw [← Finset.sort_toFinset A (· ≥ ·)]
    rw [List.sum_toFinset _ hnd, List.map_id']
  obtain ⟨s, hs, hs_sum⟩ := subsetSum_of_chainOK_list l hA m (hsum ▸ hm)
  refine ⟨s.toFinset, ?_, ?_⟩
  · intro x hx
    rw [List.mem_toFinset] at hx
    have := hs.subset hx
    rwa [hl, Finset.mem_sort] at this
  · rw [List.sum_toFinset _ (hs.nodup hnd), List.map_id']
    exact hs_sum

/-- Consequence for pseudoperfect numbers: if the proper divisors of `n > 0`, in decreasing order,
satisfy the chain condition and `n` is not deficient (`n ≤ ∑ properDivisors`), then `n` is
pseudoperfect. (No odd number qualifies, since `3 > 1 + 1`: for odd `n` the search uses the chain
condition only above a threshold, through `complete_append`.) -/
theorem pseudoperfect_of_chainOK {n : ℕ} (hn : 0 < n)
    (hc : ChainOK (n.properDivisors.sort (· ≥ ·))) (hab : n ≤ ∑ i ∈ n.properDivisors, i) :
    n.Pseudoperfect :=
  ⟨hn, subsetSum_of_chainOK_finset _ hc n hab⟩

/-- Sanity check: the proper divisors of 12, in decreasing order, pass the chain condition (so every
integer up to 16 is a subset sum); those of 945 (the smallest odd abundant number) do not (already
`3 > 1 + 1`), which is why the search only uses the condition above a bitset-computed threshold. -/
example : ChainOK [6, 4, 3, 2, 1] := by decide

example : ¬ ChainOK [315, 189, 135, 105, 63, 45, 35, 27, 21, 15, 9, 7, 5, 3, 1] := by decide

end ErdosResearch.SubsetSumChain
