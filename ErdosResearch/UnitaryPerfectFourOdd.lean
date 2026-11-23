module

public import ErdosResearch.UnitaryPerfect

@[expose] public section

/-!
# Erdős Problem 1052: unitary perfect numbers with four odd prime factors

* `exists_sorted_factors`: the prime-power factors `p ^ v_p(n)` of `n ≠ 0`, as a strictly
  increasing, pairwise coprime list with product `n` and `∏ (1 + y) = σ*(n)`.
* `arith_sorted_5`: if `1 < y₁ < ⋯ < y₅` are pairwise coprime and
  `∏ (1 + yᵢ) = 2 ∏ yᵢ`, then `∏ yᵢ = 87360`. Parity and "power of two" are not used; only the
  order and coprimality are.
* `eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five`: the only unitary perfect number
  with exactly four odd prime factors is `87360 = 2^6 · 3 · 5 · 7 · 13`.
* `isUnitaryPerfect_of_card_primeFactors_le_five_iff`: with at most four odd prime factors, the
  unitary perfect numbers are exactly `6, 60, 90, 87360`.

All of this is known mathematically (see `notes/erdos-1052.md`); it is new only as a
formalisation.

## How `arith_sorted_5` is proved (reflective checker)

`upnCheck` (the Boolean search of `UnitaryPerfectFiveOdd.lean`, moved here) decides that a family
of sorted, pairwise coprime lists has no solution, and `upnCheck_sound` proves that `true` is
correct. Since `(3, 5, 7, 13, 64)` *is* a solution, the search cannot run on the whole tree, so
`arith_sorted_5` splits by hand along that one branch (`y₁ ∈ {2, 3, ≥ 4}`, then `y₂`, `y₃`, `y₄`)
and gives every other branch to one `upnCheck … = true` (`decide +kernel`). On the branch
`(3, 5, 7, 13)` the equation is linear in `y₅`, and `omega` gives `y₅ = 64`.
Until session 61 this lemma was a generated case tree (`scripts/upn_case_tree.py`, ~900 lines,
≈ 235 s to compile); the reflective proof compiles in well under a minute.
-/

namespace ErdosResearch.Erdos1052

open Finset

/-- The prime-power factors `p ^ v_p(n)` of `n ≠ 0`, sorted: a strictly increasing list of
pairwise coprime numbers `> 1`, of length `ω(n)`, with product `n` and `∏ (1 + y) = σ*(n)`. -/
lemma exists_sorted_factors {n : ℕ} (hn : n ≠ 0) :
    ∃ l : List ℕ, l.Pairwise (· < ·) ∧ l.length = n.primeFactors.card ∧ (∀ y ∈ l, 1 < y) ∧
      l.Pairwise Nat.Coprime ∧ l.prod = n ∧ (l.map (1 + ·)).prod = usigma n := by
  set f : ℕ → ℕ := fun p => p ^ n.factorization p with hf
  have hinj : Set.InjOn f n.primeFactors := by
    intro p hp q hq hpq
    have hp' := Nat.prime_of_mem_primeFactors hp
    have hq' := Nat.prime_of_mem_primeFactors hq
    have hvp : 0 < n.factorization p :=
      hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)
    have hdvd : p ∣ q ^ n.factorization q := by
      have : p ∣ f p := dvd_pow_self p hvp.ne'
      rwa [hpq] at this
    exact (Nat.prime_dvd_prime_iff_eq hp' hq').1 (hp'.dvd_of_dvd_pow hdvd)
  set s := n.primeFactors.image f with hs
  refine ⟨s.sort (· ≤ ·), (Finset.sortedLT_sort s).pairwise, ?_, ?_, ?_, ?_, ?_⟩
  · rw [length_sort, card_image_of_injOn hinj]
  · intro y hy
    obtain ⟨p, hp, rfl⟩ := mem_image.1 ((mem_sort _).1 hy)
    have hp' := Nat.prime_of_mem_primeFactors hp
    exact Nat.one_lt_pow (hp'.factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp)).ne'
      hp'.one_lt
  · refine (Finset.sortedLT_sort s).pairwise.imp_of_mem ?_
    intro x y hx hy hxy
    obtain ⟨p, hp, rfl⟩ := mem_image.1 ((mem_sort _).1 hx)
    obtain ⟨q, hq, rfl⟩ := mem_image.1 ((mem_sort _).1 hy)
    have hpq : p ≠ q := by rintro rfl; exact hxy.ne rfl
    exact Nat.coprime_pow_primes _ _ (Nat.prime_of_mem_primeFactors hp)
      (Nat.prime_of_mem_primeFactors hq) hpq
  · have : (s.sort (· ≤ ·)).prod = ∏ y ∈ s, y := by
      rw [Finset.prod_eq_multiset_prod, Multiset.map_id', ← Finset.sort_eq s (· ≤ ·),
        Multiset.prod_coe]
    rw [this, prod_image hinj]
    conv_rhs => rw [← Nat.prod_factorization_pow_eq_self hn]
    rfl
  · have : ((s.sort (· ≤ ·)).map (1 + ·)).prod = ∏ y ∈ s, (1 + y) := by
      rw [Finset.prod_eq_multiset_prod, ← Finset.sort_eq s (· ≤ ·), Multiset.map_coe,
        Multiset.prod_coe]
    rw [this, prod_image hinj, Nat.multiplicative_factorization usigma
      (fun _ _ h => usigma_mul h) usigma_one hn]
    refine prod_congr rfl fun p hp => ?_
    rw [Nat.support_factorization] at hp
    show 1 + p ^ n.factorization p = usigma (p ^ n.factorization p)
    rw [usigma_prime_pow (Nat.prime_of_mem_primeFactors hp)
      ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn
        (Nat.dvd_of_mem_primeFactors hp))]

/-! ## The reflective checker `upnCheck`

`upnCheck` and `upnCheck_sound` (described in `UnitaryPerfectFiveOdd.lean`, where they were first
used for five odd primes) live here so that `arith_sorted_5` can use them. -/

/-- `ascProd L r = L · (L+1) ⋯ (L+r-1)`. -/
def ascProd (L : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => L * ascProd (L + 1) r

/-- `true` iff `y` is coprime to every element of `pre`. -/
def coprimeAll (y : ℕ) : List ℕ → Bool
  | [] => true
  | p :: ps => Nat.gcd y p == 1 && coprimeAll y ps

lemma coprimeAll_spec {y : ℕ} {pre : List ℕ} (h : coprimeAll y pre = true) :
    ∀ p ∈ pre, Nat.Coprime y p := by
  induction pre with
  | nil => simp
  | cons q qs ih =>
    simp only [coprimeAll, Bool.and_eq_true, beq_iff_eq] at h
    intro p hp
    rcases List.mem_cons.1 hp with rfl | hp
    · exact h.1
    · exact ih h.2 p hp

lemma coprimeAll_of {y : ℕ} {pre : List ℕ} (h : ∀ p ∈ pre, Nat.Coprime y p) :
    coprimeAll y pre = true := by
  induction pre with
  | nil => rfl
  | cons q qs ih =>
    simp only [coprimeAll, Bool.and_eq_true, beq_iff_eq]
    exact ⟨h q (by simp), ih fun p hp => h p (by simp [hp])⟩

/-- The search. `true` means: there is no list `ys` of length `r`, strictly increasing,
with entries `≥ L`, pairwise coprime and coprime to `pre`, such that
`Q · ∏ (1 + y) = 2 P · ∏ y`. `fuel` only makes the recursion structural. -/
def upnCheck : ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ → Bool
  | _, P, Q, _, _, 0 => Q != 2 * P
  | 0, _, _, _, _, _ + 1 => false
  | fuel + 1, P, Q, L, pre, r + 1 =>
    if 2 * P ≤ Q then 0 < Q
    else if r = 0 then
      (Q % (2 * P - Q) != 0) || (Q / (2 * P - Q) < L) || !coprimeAll (Q / (2 * P - Q)) pre
    else if Q * ascProd (L + 1) (r + 1) < 2 * P * ascProd L (r + 1) then true
    else (!coprimeAll L pre || upnCheck fuel (P * L) (Q * (1 + L)) (L + 1) (L :: pre) r) &&
      upnCheck fuel P Q (L + 1) pre (r + 1)

/-- Sorted lists with entries `≥ L`: `∏ (1 + y) · L⋯(L+r-1) ≤ ∏ y · (L+1)⋯(L+r)`. -/
lemma prod_succ_mul_le : ∀ (ys : List ℕ) (L : ℕ), ys.Pairwise (· < ·) → (∀ y ∈ ys, L ≤ y) →
    (ys.map (1 + ·)).prod * ascProd L ys.length ≤ ys.prod * ascProd (L + 1) ys.length
  | [], _, _, _ => by simp [ascProd]
  | y :: ys, L, hs, hL => by
    rw [List.pairwise_cons] at hs
    have hy : L ≤ y := hL y (by simp)
    have ih := prod_succ_mul_le ys (L + 1) hs.2 fun z hz => by have := hs.1 z hz; omega
    simp only [List.map_cons, List.prod_cons, List.length_cons, ascProd]
    have h1 : (1 + y) * L ≤ y * (L + 1) := by nlinarith
    calc (1 + y) * (ys.map (1 + ·)).prod * (L * ascProd (L + 1) ys.length)
        = ((1 + y) * L) * ((ys.map (1 + ·)).prod * ascProd (L + 1) ys.length) := by ring
      _ ≤ (y * (L + 1)) * (ys.prod * ascProd (L + 1 + 1) ys.length) := Nat.mul_le_mul h1 ih
      _ = y * ys.prod * ((L + 1) * ascProd (L + 1 + 1) ys.length) := by ring

lemma prod_lt_prod_succ : ∀ (ys : List ℕ), ys ≠ [] → (∀ y ∈ ys, 1 ≤ y) →
    ys.prod < (ys.map (1 + ·)).prod
  | [], h, _ => (h rfl).elim
  | [y], _, _ => by simp
  | y :: z :: ys, _, h => by
    have ih := prod_lt_prod_succ (z :: ys) (by simp) fun w hw => h w (by simp [hw])
    have hy : 1 ≤ y := h y (by simp)
    simp only [List.map_cons, List.prod_cons] at ih ⊢
    exact Nat.mul_lt_mul_of_le_of_lt (by omega) ih (by omega)

lemma prod_pos_of_one_le : ∀ (ys : List ℕ), (∀ y ∈ ys, 1 ≤ y) → 0 < ys.prod
  | [], _ => by simp
  | y :: ys, h => by
    simp only [List.prod_cons]
    exact Nat.mul_pos (h y (by simp)) (prod_pos_of_one_le ys fun w hw => h w (by simp [hw]))

/-- Soundness of `upnCheck`. -/
theorem upnCheck_sound : ∀ (fuel P Q L : ℕ) (pre : List ℕ) (r : ℕ),
    upnCheck fuel P Q L pre r = true → 1 ≤ L →
    ∀ ys : List ℕ, ys.length = r → ys.Pairwise (· < ·) → (∀ y ∈ ys, L ≤ y) →
      (∀ y ∈ ys, ∀ p ∈ pre, Nat.Coprime y p) → ys.Pairwise Nat.Coprime →
      Q * (ys.map (1 + ·)).prod ≠ 2 * P * ys.prod
  | _, P, Q, _, _, 0, h, _, ys, hlen, _, _, _, _ => by
    rw [List.length_eq_zero_iff] at hlen
    subst hlen
    simp only [upnCheck, bne_iff_ne, ne_eq] at h
    simpa using h
  | 0, _, _, _, _, _ + 1, h, _, _, _, _, _, _, _ => by simp [upnCheck] at h
  | fuel + 1, P, Q, L, pre, r + 1, h, hL1, ys, hlen, hs, hL, hpre, hcop => by
    have hone : ∀ y ∈ ys, 1 ≤ y := fun y hy => le_trans hL1 (hL y hy)
    have hne : ys ≠ [] := by rintro rfl; simp at hlen
    have hpos := prod_pos_of_one_le ys hone
    have hlt := prod_lt_prod_succ ys hne hone
    intro heq
    simp only [upnCheck] at h
    by_cases h2P : 2 * P ≤ Q
    · rw [if_pos h2P, decide_eq_true_iff] at h
      have : 2 * P * ys.prod < Q * (ys.map (1 + ·)).prod :=
        lt_of_le_of_lt (Nat.mul_le_mul_right _ h2P) (Nat.mul_lt_mul_of_pos_left hlt h)
      omega
    rw [if_neg h2P] at h
    by_cases hr : r = 0
    · subst hr
      rw [if_pos rfl] at h
      obtain ⟨y, rfl⟩ : ∃ y, ys = [y] := by
        rcases ys with _ | ⟨y, _ | ⟨z, ys⟩⟩
        · simp at hlen
        · exact ⟨y, rfl⟩
        · simp at hlen
      simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at heq
      have hq : Q = (2 * P - Q) * y := by
        rw [Nat.sub_mul]; rw [mul_add, mul_one] at heq; omega
      have hd : 0 < 2 * P - Q := by omega
      have hdiv : Q / (2 * P - Q) = y :=
        Nat.div_eq_of_eq_mul_left hd (by rw [mul_comm]; exact hq)
      have hmod : Q % (2 * P - Q) = 0 := Nat.mod_eq_zero_of_dvd ⟨y, hq⟩
      rw [hdiv, hmod] at h
      have hyL : ¬ y < L := not_lt.2 (hL y (by simp))
      have hca : coprimeAll y pre = true := coprimeAll_of (hpre y (by simp))
      simp [hyL, hca] at h
    rw [if_neg hr] at h
    by_cases hb : Q * ascProd (L + 1) (r + 1) < 2 * P * ascProd L (r + 1)
    · have hm := prod_succ_mul_le ys L hs hL
      rw [hlen] at hm
      have hm' := Nat.mul_le_mul_left Q hm
      have hA : 0 < ascProd L (r + 1) := by
        have : ∀ L r, 1 ≤ L → 0 < ascProd L r := by
          intro L r; induction r generalizing L with
          | zero => simp [ascProd]
          | succ r ih => intro hL; simp only [ascProd]; exact Nat.mul_pos (by omega) (ih _ (by omega))
        exact this L _ hL1
      have key : 2 * P * ys.prod * ascProd L (r + 1) ≤ Q * ascProd (L + 1) (r + 1) * ys.prod := by
        calc 2 * P * ys.prod * ascProd L (r + 1) = Q * ((ys.map (1 + ·)).prod * ascProd L (r + 1)) := by
              rw [← heq]; ring
          _ ≤ Q * (ys.prod * ascProd (L + 1) (r + 1)) := hm'
          _ = Q * ascProd (L + 1) (r + 1) * ys.prod := by ring
      have := Nat.mul_lt_mul_of_pos_right hb hpos
      nlinarith
    rw [if_neg hb, Bool.and_eq_true, Bool.or_eq_true] at h
    obtain ⟨hy, hrest⟩ := h
    obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := List.exists_cons_of_ne_nil hne
    rw [List.pairwise_cons] at hs
    by_cases hyL : y = L
    · subst hyL
      rcases hy with hy | hy
      · have : coprimeAll y pre = true := coprimeAll_of (hpre y (by simp))
        simp [this] at hy
      · rw [List.pairwise_cons] at hcop
        refine upnCheck_sound fuel (P * y) (Q * (1 + y)) (y + 1) (y :: pre) r hy (by omega) ys'
          (by simpa using hlen) hs.2 (fun z hz => hs.1 z hz) ?_ hcop.2 ?_
        · intro z hz p hp
          rcases List.mem_cons.1 hp with rfl | hp
          · exact (hcop.1 z hz).symm
          · exact hpre z (by simp [hz]) p hp
        · simp only [List.map_cons, List.prod_cons] at heq
          linarith [heq]
    · refine upnCheck_sound fuel P Q (L + 1) pre (r + 1) hrest (by omega) (y :: ys') hlen
        (List.pairwise_cons.2 hs) ?_ hpre hcop heq
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · have := hL z (by simp); omega
      · have := hs.1 z hz; have := hL y (by simp); omega
/-- Close the side conditions of `upnCheck_sound` on an explicit list. -/
macro "upn_side" : tactic => `(tactic| (
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp,
    forall_eq, List.Pairwise.nil, and_true, List.forall_mem_nil, implies_true, IsEmpty.forall_iff,
    List.mem_nil_iff, false_imp_iff, true_and]
  try and_intros
  all_goals first | omega | assumption | exact Nat.Coprime.symm (by assumption) | trivial))

/-- Close the equation side condition of `upnCheck_sound` from `h`. -/
macro "upn_eq" : tactic => `(tactic| (
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at *
  linarith))

lemma arith_sorted_5 {y1 y2 y3 y4 y5 : ℕ} (h1 : 1 < y1)
    (hlt1 : y1 < y2) (hlt2 : y2 < y3) (hlt3 : y3 < y4) (hlt4 : y4 < y5) (c1_2 : Nat.Coprime y1 y2)
    (c1_3 : Nat.Coprime y1 y3) (c1_4 : Nat.Coprime y1 y4) (c1_5 : Nat.Coprime y1 y5)
    (c2_3 : Nat.Coprime y2 y3) (c2_4 : Nat.Coprime y2 y4) (c2_5 : Nat.Coprime y2 y5)
    (c3_4 : Nat.Coprime y3 y4) (c3_5 : Nat.Coprime y3 y5) (c4_5 : Nat.Coprime y4 y5)
    (h : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5) :
    y1 * y2 * y3 * y4 * y5 = 87360 := by
  rcases (show y1 = 2 ∨ y1 = 3 ∨ 4 ≤ y1 by omega) with rfl | rfl | h4
  · exact (upnCheck_sound 5000 2 3 3 [2] 4 (by decide +kernel) (by norm_num) [y2, y3, y4, y5] rfl
      (by upn_side) (by upn_side) (by upn_side) (by upn_side) (by upn_eq)).elim
  · rcases (show y2 = 4 ∨ y2 = 5 ∨ 6 ≤ y2 by omega) with rfl | rfl | h6
    · exact (upnCheck_sound 5000 12 20 5 [4, 3] 3 (by decide +kernel) (by norm_num) [y3, y4, y5] rfl
        (by upn_side) (by upn_side) (by upn_side) (by upn_side) (by upn_eq)).elim
    · rcases (show y3 = 6 ∨ y3 = 7 ∨ 8 ≤ y3 by omega) with rfl | rfl | h8
      · norm_num at c1_3
      · rcases (show y4 = 8 ∨ y4 = 9 ∨ y4 = 10 ∨ y4 = 11 ∨ y4 = 12 ∨ y4 = 13 ∨ 14 ≤ y4 by omega)
          with rfl | rfl | rfl | rfl | rfl | rfl | h14
        · exact (upnCheck_sound 5000 (105 * 8) (192 * 9) 9 [8, 7, 5, 3] 1 (by decide +kernel)
            (by norm_num) [y5] rfl (by upn_side) (by upn_side) (by upn_side) (by upn_side)
            (by upn_eq)).elim
        · norm_num at c1_4
        · norm_num at c2_4
        · exact (upnCheck_sound 5000 (105 * 11) (192 * 12) 12 [11, 7, 5, 3] 1 (by decide +kernel)
            (by norm_num) [y5] rfl (by upn_side) (by upn_side) (by upn_side) (by upn_side)
            (by upn_eq)).elim
        · norm_num at c1_4
        · omega
        · exact (upnCheck_sound 5000 105 192 14 [7, 5, 3] 2 (by decide +kernel) (by norm_num)
            [y4, y5] rfl (by upn_side) (by upn_side) (by upn_side) (by upn_side)
            (by upn_eq)).elim
      · exact (upnCheck_sound 5000 15 24 8 [5, 3] 3 (by decide +kernel) (by norm_num)
          [y3, y4, y5] rfl (by upn_side) (by upn_side) (by upn_side) (by upn_side)
          (by upn_eq)).elim
    · exact (upnCheck_sound 5000 3 4 6 [3] 4 (by decide +kernel) (by norm_num) [y2, y3, y4, y5] rfl
        (by upn_side) (by upn_side) (by upn_side) (by upn_side) (by upn_eq)).elim
  · exact (upnCheck_sound 5000 1 1 4 [] 5 (by decide +kernel) (by norm_num) [y1, y2, y3, y4, y5]
      rfl (by upn_side) (by upn_side) (by upn_side) (by upn_side) (by upn_eq)).elim

/-- The only unitary perfect number with exactly four odd prime factors is `87360`. -/
theorem eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five {n : ℕ}
    (h : IsUnitaryPerfect n) (hcard : n.primeFactors.card = 5) : n = 87360 := by
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  obtain ⟨l, hsort, hlen, hgt, hcop, hprod, hsig⟩ := exists_sorted_factors hpos.ne'
  rw [hcard] at hlen
  rcases l with _ | ⟨y1, _ | ⟨y2, _ | ⟨y3, _ | ⟨y4, _ | ⟨y5, _ | ⟨y6, l⟩⟩⟩⟩⟩⟩ <;>
    simp only [List.length_cons, List.length_nil] at hlen <;> try omega
  simp only [List.pairwise_cons, List.mem_cons, List.not_mem_nil, or_false,
    forall_eq_or_imp, forall_eq, List.Pairwise.nil, and_true] at hsort hcop
  simp only [List.mem_cons, List.not_mem_nil, or_false, forall_eq_or_imp, forall_eq] at hgt
  simp only [List.prod_cons, List.prod_nil, List.map_cons, List.map_nil, mul_one] at hprod hsig
  obtain ⟨⟨hlt1, -, -, -⟩, ⟨hlt2, -, -⟩, ⟨hlt3, -⟩, hlt4⟩ := hsort
  obtain ⟨⟨c12, c13, c14, c15⟩, ⟨c23, c24, c25⟩, ⟨c34, c35⟩, c45⟩ := hcop
  have heq : (1 + y1) * (1 + y2) * (1 + y3) * (1 + y4) * (1 + y5) =
      2 * y1 * y2 * y3 * y4 * y5 := by
    have := hsig.trans (hs.trans (congrArg (2 * ·) hprod.symm))
    convert this using 1 <;> ring
  rw [← hprod]
  have := arith_sorted_5 hgt.1 hlt1 hlt2 hlt3 hlt4.1 c12 c13 c14 c15 c23 c24 c25 c34 c35
    c45.1 heq
  rw [← this]; ring

/-- Classification of unitary perfect numbers with at most five prime factors (i.e. at most four
odd prime factors): they are exactly `6`, `60`, `90` and `87360`. -/
theorem isUnitaryPerfect_of_card_primeFactors_le_five_iff {n : ℕ}
    (hcard : n.primeFactors.card ≤ 5) :
    IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 := by
  constructor
  · intro h
    rcases (show n.primeFactors.card ≤ 4 ∨ n.primeFactors.card = 5 by omega) with h4 | h5
    · rcases (isUnitaryPerfect_of_card_primeFactors_le_four_iff h4).1 h with h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr (eq_87360_of_isUnitaryPerfect_of_card_primeFactors_eq_five h h5)))
  · rintro (rfl | rfl | rfl | rfl)
    exacts [isUnitaryPerfect_6, isUnitaryPerfect_60, isUnitaryPerfect_90, isUnitaryPerfect_87360]

end ErdosResearch.Erdos1052
