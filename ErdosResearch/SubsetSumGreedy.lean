module

public import ErdosResearch.SubsetSumGlue

@[expose] public section

/-!
# A greedy gap bound for subset sums of proper divisors (no bitset)

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 57).

The raise step (`SubsetSumRaise.lean`) needs a bound `gB` on the gaps of the subset sums of `D m`
(proper divisors of the cofactor `m`). So far `gB` came from a bitset, so `m` had to be small. Here
`gB` comes from the classical greedy bound: if the elements are added in increasing order
`d₁ < d₂ < …` with prefix sums `Pᵢ`, the subset sums in `[0, ∑]` have gaps at most
`max(1, maxᵢ (dᵢ − Pᵢ₋₁))` (`gap_greedy`). The list of divisors is built from the factorisation
(`divsOf`, `Nat.divisors_mul`, `Nat.divisors_prime_pow`), so `m` itself is never factored or
scanned by the kernel; `gapCert` packs everything into one Boolean (`gap_properDivisors_of_gapCert`).

Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumGreedy

open Finset ErdosResearch.SubsetSumGlue

/-- Greedy gap bound. The head of the list is the element added *last* (so the list should be
in decreasing order for a good bound): `greedyGap (d :: l) = max (greedyGap l) (d - l.sum)`. -/
def greedyGap : List ℕ → ℕ
  | [] => 1
  | d :: l => max (greedyGap l) (d - l.sum)

lemma one_le_greedyGap : ∀ l : List ℕ, 1 ≤ greedyGap l
  | [] => le_refl _
  | _ :: l => le_trans (one_le_greedyGap l) (le_max_left _ _)

lemma subsetSums_mono {s t : Finset ℕ} (h : s ⊆ t) {a : ℕ} (ha : a ∈ subsetSums s) :
    a ∈ subsetSums t := by
  obtain ⟨u, hu, rfl⟩ := ha
  exact ⟨u, hu.trans h, rfl⟩

/-- **Greedy gap bound.** For a list without repetitions, after every `x` below the total there is
a subset sum `z` with `x < z ≤ x + greedyGap l` and `z ≤` total. -/
theorem gap_greedy : ∀ (l : List ℕ), l.Nodup → ∀ x < l.sum,
    ∃ z ∈ subsetSums l.toFinset, x < z ∧ z ≤ x + greedyGap l ∧ z ≤ l.sum
  | [], _, _, hx => by simp at hx
  | d :: l, hnd, x, hx => by
    rw [List.nodup_cons] at hnd
    obtain ⟨hdl, hnd⟩ := hnd
    have ih := gap_greedy l hnd
    have hG₁ : greedyGap l ≤ greedyGap (d :: l) := le_max_left _ _
    have hG₂ : d - l.sum ≤ greedyGap (d :: l) := le_max_right _ _
    have hsub : l.toFinset ⊆ (d :: l).toFinset := by
      intro y hy; simp only [List.mem_toFinset, List.mem_cons] at hy ⊢; exact Or.inr hy
    rw [List.sum_cons] at hx ⊢
    by_cases h1 : x < l.sum
    · obtain ⟨z, hz, hxz, hzx, hzs⟩ := ih x h1
      exact ⟨z, subsetSums_mono hsub hz, hxz, by omega, by omega⟩
    · by_cases h2 : x < d
      · refine ⟨d, ⟨{d}, ?_, by simp⟩, h2, by omega, by omega⟩
        intro y hy; simp only [Finset.mem_singleton] at hy; simp [hy]
      · have h3 : x - d < l.sum := by omega
        obtain ⟨z, hz, hxz, hzx, hzs⟩ := ih (x - d) h3
        have hdisj : Disjoint ({d} : Finset ℕ) l.toFinset := by
          rw [Finset.disjoint_singleton_left, List.mem_toFinset]; exact hdl
        have hmem : d + z ∈ subsetSums ({d} ∪ l.toFinset) :=
          subsetSums_union hdisj ⟨{d}, subset_refl _, by simp⟩ hz
        have heq : ({d} ∪ l.toFinset : Finset ℕ) = (d :: l).toFinset := by
          ext y; simp
        rw [heq] at hmem
        exact ⟨d + z, hmem, by omega, by omega, by omega⟩

/-! ### Divisors from a factorisation -/

/-- `∏ p^e` over a list of pairs `(p, e)`. -/
def prodOf : List (ℕ × ℕ) → ℕ
  | [] => 1
  | pe :: fs => pe.1 ^ pe.2 * prodOf fs

/-- All divisors of `prodOf fs`, built from the factorisation (with repetitions if the primes
repeat; `gapCert` checks that there are none). -/
def divsOf : List (ℕ × ℕ) → List ℕ
  | [] => [1]
  | pe :: fs => (List.range (pe.2 + 1)).flatMap (fun i => (divsOf fs).map (fun d => pe.1 ^ i * d))

theorem divsOf_toFinset : ∀ (fs : List (ℕ × ℕ)), (∀ pe ∈ fs, pe.1.Prime) →
    (divsOf fs).toFinset = (prodOf fs).divisors
  | [], _ => by simp [divsOf, prodOf]
  | pe :: fs, hp => by
    have ih := divsOf_toFinset fs (fun q hq => hp q (List.mem_cons_of_mem _ hq))
    have hp0 : pe.1.Prime := hp pe List.mem_cons_self
    rw [prodOf, Nat.divisors_mul, Nat.divisors_prime_pow hp0, ← ih]
    ext y
    simp only [divsOf, List.mem_toFinset, List.mem_flatMap, List.mem_range, List.mem_map,
      Finset.mem_mul, Finset.mem_map, Finset.mem_range, Function.Embedding.coeFn_mk]
    constructor
    · rintro ⟨i, hi, d, hd, rfl⟩
      exact ⟨pe.1 ^ i, ⟨i, hi, rfl⟩, d, hd, rfl⟩
    · rintro ⟨_, ⟨i, hi, rfl⟩, d, hd, rfl⟩
      exact ⟨i, hi, d, hd, rfl⟩

/-- Strictly decreasing (linear-time check). -/
def descOK : List ℕ → Bool
  | a :: b :: l => decide (b < a) && descOK (b :: l)
  | _ => true

lemma lt_of_descOK : ∀ (a : ℕ) (l : List ℕ), descOK (a :: l) = true → ∀ y ∈ l, y < a
  | _, [], _, _, hy => by simp at hy
  | a, b :: l, h, y, hy => by
    simp only [descOK, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases List.mem_cons.1 hy with rfl | hy
    · exact h.1
    · exact lt_trans (lt_of_descOK b l h.2 y hy) h.1

lemma nodup_of_descOK : ∀ (l : List ℕ), descOK l = true → l.Nodup
  | [], _ => List.nodup_nil
  | a :: l, h => by
    rw [List.nodup_cons]
    refine ⟨fun ha => lt_irrefl a (lt_of_descOK a l h a ha), nodup_of_descOK l ?_⟩
    cases l with
    | nil => rfl
    | cons b l => simp only [descOK, Bool.and_eq_true] at h; exact h.2

/-- Insertion into a decreasing list (local: Mathlib's `List.insertionSort` is not exposed to
`decide` from a `module`). -/
def insDesc (a : ℕ) : List ℕ → List ℕ
  | [] => [a]
  | b :: l => if b ≤ a then a :: b :: l else b :: insDesc a l

/-- Insertion sort, decreasing. -/
def sortDesc : List ℕ → List ℕ
  | [] => []
  | a :: l => insDesc a (sortDesc l)

lemma perm_insDesc (a : ℕ) : ∀ l : List ℕ, (insDesc a l).Perm (a :: l)
  | [] => List.Perm.refl _
  | b :: l => by
    unfold insDesc
    split
    · exact List.Perm.refl _
    · exact ((perm_insDesc a l).cons b).trans (List.Perm.swap a b l)

lemma perm_sortDesc : ∀ l : List ℕ, (sortDesc l).Perm l
  | [] => List.Perm.refl _
  | a :: l => (perm_insDesc a _).trans ((perm_sortDesc l).cons a)

/-- One Boolean: the divisors of `prodOf fs`, sorted decreasingly, have no repetitions, the largest
is `prodOf fs`, the others (the proper divisors) sum to `S`, and their greedy bound is at most `G`. -/
def gapCert (fs : List (ℕ × ℕ)) (G S : ℕ) : Bool :=
  match sortDesc (divsOf fs) with
  | [] => false
  | d :: l => descOK (d :: l) && d == prodOf fs && l.sum == S && decide (greedyGap l ≤ G)

/-- **Gap bound for `D m` from the factorisation of `m`**, in the form used by the raise step. -/
theorem gap_properDivisors_of_gapCert {fs : List (ℕ × ℕ)} {G S : ℕ} (hp : ∀ pe ∈ fs, pe.1.Prime)
    (h : gapCert fs G S = true) :
    ∑ y ∈ (prodOf fs).properDivisors, y = S ∧ ∀ x < ∑ y ∈ (prodOf fs).properDivisors, y, ∃ z ∈ subsetSums (prodOf fs).properDivisors,
      x < z ∧ z ≤ x + G ∧ z ≤ ∑ y ∈ (prodOf fs).properDivisors, y := by
  have hperm := perm_sortDesc (divsOf fs)
  have hset := divsOf_toFinset fs hp
  unfold gapCert at h
  generalize hL : sortDesc (divsOf fs) = L at h hperm
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

/-- Sanity instance: the gaps of the subset sums of `D(3 · 5^6 · 13^3)` are at most `4` (exactly the
true maximum gap), with no bitset and no kernel `properDivisors` (`m = 102984375`, 56 divisors). -/
theorem gap_example :
    ∀ x < ∑ y ∈ (prodOf [(3, 1), (5, 6), (13, 3)]).properDivisors, y,
      ∃ z ∈ subsetSums (prodOf [(3, 1), (5, 6), (13, 3)]).properDivisors,
        x < z ∧ z ≤ x + 4 ∧ z ≤ ∑ y ∈ (prodOf [(3, 1), (5, 6), (13, 3)]).properDivisors, y :=
  (gap_properDivisors_of_gapCert (S := 82950745) (by simp; norm_num) (by decide +kernel)).2

end ErdosResearch.SubsetSumGreedy
