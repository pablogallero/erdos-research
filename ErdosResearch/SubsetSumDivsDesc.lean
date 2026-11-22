module

public import ErdosResearch.SubsetSumGreedy

@[expose] public section

/-!
# Decreasing divisors by merging (for `gapCert` on large cofactors)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 58).

`gapCert` (`SubsetSumGreedy.lean`) sorts the divisors with an insertion sort: quadratic, and in the kernel
(`decide +kernel`) a cofactor with ~700 divisors already runs out of memory (8 GB). Here the divisors of
`p^e · m` are built as the merge of the `e + 1` decreasing lists `p^i · D(m)`, so the cost is about
`(#divisors) · (e + 1)` per prime. The merge has a fuel argument; with too little fuel it just appends, so
the result is always a permutation of `divsOf fs` (`divsDesc_perm`) and the order is never trusted
(`gapCertM` still checks `descOK`).

* `mergeF`, `mergeAll`, `divsDesc` and `divsDesc_perm`;
* `gapCertM` and **`gap_properDivisors_of_gapCertM`** (same statement as `gap_properDivisors_of_gapCert`);
* `baseOK`, `baseList` and `baseList_properDivisors`: the proper divisors of a bitset base from its factorisation
  (kernel `properDivisors b` scans up to `b`, which is slow for `b` near `10^6`).

Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumDivsDesc

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumGreedy

/-- Merge of two decreasing lists, with fuel (out of fuel: append). -/
def mergeF : ℕ → List ℕ → List ℕ → List ℕ
  | 0, l₁, l₂ => l₁ ++ l₂
  | _ + 1, [], l₂ => l₂
  | _ + 1, a :: l₁, [] => a :: l₁
  | n + 1, a :: l₁, b :: l₂ =>
      if b ≤ a then a :: mergeF n l₁ (b :: l₂) else b :: mergeF n (a :: l₁) l₂

lemma perm_mergeF : ∀ (n : ℕ) (l₁ l₂ : List ℕ), (mergeF n l₁ l₂).Perm (l₁ ++ l₂)
  | 0, _, _ => List.Perm.refl _
  | _ + 1, [], _ => List.Perm.refl _
  | _ + 1, _ :: _, [] => by simp [mergeF]
  | n + 1, a :: l₁, b :: l₂ => by
    unfold mergeF
    split
    · exact (perm_mergeF n l₁ (b :: l₂)).cons a
    · refine ((perm_mergeF n (a :: l₁) l₂).cons b).trans ?_
      exact (List.perm_middle).symm

/-- Merge of a list of decreasing lists. -/
def mergeAll : List (List ℕ) → List ℕ
  | [] => []
  | l :: ls => let r := mergeAll ls; mergeF (l.length + r.length) l r

lemma perm_mergeAll : ∀ ls : List (List ℕ), (mergeAll ls).Perm ls.flatten
  | [] => List.Perm.refl _
  | l :: ls => by
    simp only [mergeAll, List.flatten_cons]
    exact (perm_mergeF _ _ _).trans ((perm_mergeAll ls).append_left l)

/-- The divisors of `prodOf fs`, decreasing when the primes are distinct (by merging). -/
def divsDesc : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | pe :: fs => let D := divsDesc fs
      mergeAll (((List.range (pe.2 + 1)).reverse).map fun i => D.map fun d => pe.1 ^ i * d)

lemma divsDesc_perm : ∀ fs : List (ℕ × ℕ), (divsDesc fs).Perm (divsOf fs)
  | [] => List.Perm.refl _
  | pe :: fs => by
    simp only [divsDesc, divsOf]
    refine (perm_mergeAll _).trans ?_
    have h1 : (((List.range (pe.2 + 1)).reverse.map fun i => (divsDesc fs).map fun d => pe.1 ^ i * d).flatten).Perm
        (((List.range (pe.2 + 1)).map fun i => (divsDesc fs).map fun d => pe.1 ^ i * d).flatten) := by
      rw [List.map_reverse]
      exact List.Perm.flatten (List.reverse_perm _)
    refine h1.trans ?_
    rw [← List.flatMap_def]
    exact List.Perm.flatMap_left _ fun i _ => (divsDesc_perm fs).map _

/-- `gapCert` with the merged divisor list. -/
def gapCertM (fs : List (ℕ × ℕ)) (G S : ℕ) : Bool :=
  match divsDesc fs with
  | [] => false
  | d :: l => descOK (d :: l) && d == prodOf fs && l.sum == S && decide (greedyGap l ≤ G)

/-- **`gapCert` with merged divisors**: the same conclusion as `gap_properDivisors_of_gapCert`. -/
theorem gap_properDivisors_of_gapCertM {fs : List (ℕ × ℕ)} {G S : ℕ} (hp : ∀ pe ∈ fs, pe.1.Prime)
    (h : gapCertM fs G S = true) :
    ∑ y ∈ (prodOf fs).properDivisors, y = S ∧ ∀ x < ∑ y ∈ (prodOf fs).properDivisors, y, ∃ z ∈ subsetSums (prodOf fs).properDivisors,
      x < z ∧ z ≤ x + G ∧ z ≤ ∑ y ∈ (prodOf fs).properDivisors, y := by
  have hperm := divsDesc_perm fs
  have hset := divsOf_toFinset fs hp
  unfold gapCertM at h
  generalize hL : divsDesc fs = L at h hperm
  cases L with
  | nil => simp at h
  | cons d l =>
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
    obtain ⟨⟨⟨hdesc, hd⟩, hS⟩, hG⟩ := h
    have hnd := nodup_of_descOK _ hdesc
    have hdl : d ∉ l := (List.nodup_cons.1 hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.1 hnd).2
    have hfin : (d :: l).toFinset = (prodOf fs).divisors := by
      rw [← hset]; ext y; simp only [List.mem_toFinset]; exact hperm.mem_iff
    have hm0 : prodOf fs ≠ 0 := by
      intro h0
      have : d ∈ (prodOf fs).divisors := by rw [← hfin]; simp
      simp [h0] at this
    have hl : l.toFinset = (prodOf fs).properDivisors := by
      ext y
      rw [← Nat.insert_self_properDivisors hm0, hd] at hfin
      rw [hd] at hdl
      have hy := Finset.ext_iff.1 hfin y
      simp only [List.mem_toFinset, List.mem_cons, Finset.mem_insert] at hy ⊢
      constructor
      · intro hyl
        have hyd : y ≠ prodOf fs := fun e => hdl (e ▸ hyl)
        rcases hy.1 (Or.inr hyl) with e | e
        · exact absurd e hyd
        · exact e
      · intro hyD
        have hyd : y ≠ prodOf fs := by
          rintro rfl; exact lt_irrefl _ (Nat.mem_properDivisors.1 hyD).2
        rcases hy.2 (Or.inr hyD) with e | e
        · exact absurd e hyd
        · exact e
    have hsum : ∑ y ∈ (prodOf fs).properDivisors, y = l.sum := by
      rw [← hl, List.sum_toFinset _ hnd', List.map_id']
    refine ⟨hsum.trans hS, fun x hx => ?_⟩
    rw [hsum] at hx ⊢
    obtain ⟨z, hz, hxz, hzx, hzs⟩ := gap_greedy l hnd' x hx
    rw [hl] at hz
    exact ⟨z, hz, hxz, by omega, hzs⟩

/-- The base check: the merged divisor list is strictly decreasing and starts with `prodOf fs`. -/
def baseOK (fs : List (ℕ × ℕ)) : Bool :=
  match divsDesc fs with
  | [] => false
  | d :: l => descOK (d :: l) && d == prodOf fs

/-- The proper divisors of `prodOf fs`, listed from the factorisation (no scan up to `prodOf fs`). -/
def baseList (fs : List (ℕ × ℕ)) : List ℕ := (divsDesc fs).tail

/-- **Proper divisors from the factorisation**, for bitset bases: `baseOK` gives the finset and `Nodup`. -/
theorem baseList_properDivisors {fs : List (ℕ × ℕ)} (hp : ∀ pe ∈ fs, pe.1.Prime)
    (h : baseOK fs = true) :
    (baseList fs).toFinset = (prodOf fs).properDivisors ∧ (baseList fs).Nodup := by
  have hperm := divsDesc_perm fs
  have hset := divsOf_toFinset fs hp
  unfold baseOK at h
  unfold baseList
  generalize hL : divsDesc fs = L at h hperm
  cases L with
  | nil => simp at h
  | cons d l =>
    simp only [Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨hdesc, hd⟩ := h
    have hnd := nodup_of_descOK _ hdesc
    have hdl : d ∉ l := (List.nodup_cons.1 hnd).1
    have hnd' : l.Nodup := (List.nodup_cons.1 hnd).2
    have hfin : (d :: l).toFinset = (prodOf fs).divisors := by
      rw [← hset]; ext y; simp only [List.mem_toFinset]; exact hperm.mem_iff
    have hm0 : prodOf fs ≠ 0 := by
      intro h0
      have : d ∈ (prodOf fs).divisors := by rw [← hfin]; simp
      simp [h0] at this
    refine ⟨?_, hnd'⟩
    ext y
    rw [← Nat.insert_self_properDivisors hm0, hd] at hfin
    rw [hd] at hdl
    have hy := Finset.ext_iff.1 hfin y
    simp only [List.tail_cons, List.mem_toFinset, List.mem_cons, Finset.mem_insert] at hy ⊢
    constructor
    · intro hyl
      have hyd : y ≠ prodOf fs := fun e => hdl (e ▸ hyl)
      rcases hy.1 (Or.inr hyl) with e | e
      · exact absurd e hyd
      · exact e
    · intro hyD
      have hyd : y ≠ prodOf fs := by
        rintro rfl; exact lt_irrefl _ (Nat.mem_properDivisors.1 hyD).2
      rcases hy.2 (Or.inr hyD) with e | e
      · exact absurd e hyd
      · exact e

end ErdosResearch.SubsetSumDivsDesc
