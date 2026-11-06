import ErdosResearch.UnitaryPerfectFourOdd

/-!
# Erdős Problem 1052: no unitary perfect number has exactly five odd prime factors

This proof does not generate a case tree. It uses a *reflective* checker instead:
* `upnCheck` is a Boolean search over sorted, pairwise coprime lists `y₁ < ⋯ < y_r`. It
  decides that `Q · ∏ (1 + yᵢ) = 2 P · ∏ yᵢ` has no solution;
* `upnCheck_sound` proves, once and for all, that a `true` answer is correct;
* the kernel evaluates `upnCheck … = true` (`decide +kernel`), using its GMP-accelerated
  arithmetic on `Nat`.

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
lemma prod_succ_mul_le : ∀ (ys : List ℕ) (L : ℕ), ys.Sorted (· < ·) → (∀ y ∈ ys, L ≤ y) →
    (ys.map (1 + ·)).prod * ascProd L ys.length ≤ ys.prod * ascProd (L + 1) ys.length
  | [], _, _, _ => by simp [ascProd]
  | y :: ys, L, hs, hL => by
    rw [List.sorted_cons] at hs
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
    ∀ ys : List ℕ, ys.length = r → ys.Sorted (· < ·) → (∀ y ∈ ys, L ≤ y) →
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
    rw [List.sorted_cons] at hs
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
        (List.sorted_cons.2 hs) ?_ hpre hcop heq
      intro z hz
      rcases List.mem_cons.1 hz with rfl | hz
      · have := hL z (by simp); omega
      · have := hs.1 z hz; have := hL y (by simp); omega

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
