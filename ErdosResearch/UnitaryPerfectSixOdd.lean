import ErdosResearch.UnitaryPerfectFiveOdd

/-!
# Erdős Problem 1052: no unitary perfect number has exactly six odd prime factors

The search in `UnitaryPerfectFiveOdd.lean` treats the power of two `2^a` as one more sorted
variable and needs ~21M nodes for seven factors. Here the power of two gets special treatment:

* `n = 2^a · q₁ ⋯ q_k`, with odd `q₁ < ⋯ < q_k`, pairwise coprime;
  `σ*(n) = 2n` reads `(1 + 2^a) ∏ (1 + qᵢ) = 2 · 2^a ∏ qᵢ`;
* **2-adic bound**: each `1 + qᵢ` is even, so `2^k ∣ 2^{a+1}` and `2^a ≥ 2^{k-1}`
  (`two_pow_le_of_eq`); this lower bound on the even factor drives the pruning;
* the odd variables are walked with stride-2 bounds (`ascProd2`, `prod2_succ_mul_le`);
* once `2^a` has been placed, the rest is the old `upnCheck` (exact target);
* with one odd variable `y` and `2^a` still to place, there is no walk: `2^a ∣ Q (1 + y)` and
  `min(y, 2^a) ≤ 3Q / (2P - Q)` bound `2^a`, so the checker loops over the powers of two
  (`powLoop`) and solves the linear equation for `y`.

For six odd prime factors the search visits ~5400 nodes plus ~7800 loop steps
(`scripts/upn_search_hybrid.py 6`).

`not_isUnitaryPerfect_of_card_primeFactors_eq_seven`: no UPN has exactly seven prime factors.
Known mathematically (Wall 1988: a sixth UPN has ≥ 9 odd prime factors; cited second-hand). New
only as a formalisation.
-/

namespace ErdosResearch.Erdos1052

/-! ## Stride-2 bound -/

/-- `ascProd2 L r = L · (L+2) ⋯ (L+2(r-1))`. -/
def ascProd2 (L : ℕ) : ℕ → ℕ
  | 0 => 1
  | r + 1 => L * ascProd2 (L + 2) r

lemma ascProd2_pos : ∀ (L r : ℕ), 1 ≤ L → 0 < ascProd2 L r
  | _, 0, _ => by simp [ascProd2]
  | L, r + 1, h => by
    simp only [ascProd2]; exact Nat.mul_pos (by omega) (ascProd2_pos _ r (by omega))

/-- Sorted odd entries `≥ L`: `∏ (1 + y) · L(L+2)⋯ ≤ ∏ y · (L+1)(L+3)⋯`. -/
lemma prod2_succ_mul_le : ∀ (ys : List ℕ) (L : ℕ), ys.Sorted (· < ·) → (∀ y ∈ ys, y % 2 = 1) →
    (∀ y ∈ ys, L ≤ y) →
    (ys.map (1 + ·)).prod * ascProd2 L ys.length ≤ ys.prod * ascProd2 (L + 1) ys.length
  | [], _, _, _, _ => by simp [ascProd2]
  | y :: ys, L, hs, ho, hL => by
    rw [List.sorted_cons] at hs
    have hy : L ≤ y := hL y (by simp)
    have hoy : y % 2 = 1 := ho y (by simp)
    have ih := prod2_succ_mul_le ys (L + 2) hs.2 (fun z hz => ho z (by simp [hz])) fun z hz => by
      have h1 := hs.1 z hz; have h2 := ho z (by simp [hz]); omega
    simp only [List.map_cons, List.prod_cons, List.length_cons, ascProd2]
    have h1 : (1 + y) * L ≤ y * (L + 1) := by nlinarith
    calc (1 + y) * (ys.map (1 + ·)).prod * (L * ascProd2 (L + 2) ys.length)
        = ((1 + y) * L) * ((ys.map (1 + ·)).prod * ascProd2 (L + 2) ys.length) := by ring
      _ ≤ (y * (L + 1)) * (ys.prod * ascProd2 (L + 2 + 1) ys.length) := Nat.mul_le_mul h1 ih
      _ = y * ys.prod * ((L + 1) * ascProd2 (L + 1 + 2) ys.length) := by
        rw [show L + 2 + 1 = L + 1 + 2 by omega]; ring

lemma prod_le_prod_succ : ∀ (ys : List ℕ), ys.prod ≤ (ys.map (1 + ·)).prod ∧
    0 < (ys.map (1 + ·)).prod
  | [] => by simp
  | y :: ys => by
    obtain ⟨h1, h2⟩ := prod_le_prod_succ ys
    simp only [List.map_cons, List.prod_cons]
    exact ⟨Nat.mul_le_mul (by omega) h1, Nat.mul_pos (by omega) h2⟩

/-- If `2P ≤ Q` and `0 < Q` there is no solution. -/
lemma ne_of_two_mul_le {P Q E : ℕ} (ys : List ℕ) (h : 2 * P ≤ Q) (hQ : 0 < Q) :
    Q * (1 + E) * (ys.map (1 + ·)).prod ≠ 2 * P * E * ys.prod := by
  obtain ⟨h1, h2⟩ := prod_le_prod_succ ys
  have h3 : E * ys.prod < (1 + E) * (ys.map (1 + ·)).prod := by
    calc E * ys.prod ≤ E * (ys.map (1 + ·)).prod := Nat.mul_le_mul_left _ h1
      _ < (1 + E) * (ys.map (1 + ·)).prod := Nat.mul_lt_mul_of_pos_right (by omega) h2
  intro heq
  have h4 : 2 * P * (E * ys.prod) ≤ Q * (E * ys.prod) := Nat.mul_le_mul_right _ h
  have h5 : Q * (E * ys.prod) < Q * ((1 + E) * (ys.map (1 + ·)).prod) :=
    Nat.mul_lt_mul_of_pos_left h3 hQ
  have : Q * ((1 + E) * (ys.map (1 + ·)).prod) = 2 * P * (E * ys.prod) := by
    rw [← mul_assoc, heq]; ring
  omega

/-! ## Recognising powers of two -/

/-- `isPow2From f e n`: is `n` one of `e, 2e, 4e, …` (at most `f` steps)? -/
def isPow2From : ℕ → ℕ → ℕ → Bool
  | 0, _, _ => false
  | f + 1, e, n => e == n || (decide (e < n) && isPow2From f (2 * e) n)

lemma isPow2From_pow : ∀ (f i a : ℕ), i ≤ a → a < i + f → isPow2From f (2 ^ i) (2 ^ a) = true
  | 0, i, a, h1, h2 => by omega
  | f + 1, i, a, h1, h2 => by
    simp only [isPow2From, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq]
    rcases h1.lt_or_eq with h | rfl
    · right
      refine ⟨Nat.pow_lt_pow_right (by norm_num) h, ?_⟩
      rw [← pow_succ']
      exact isPow2From_pow f (i + 1) a h (by omega)
    · left; rfl

/-! ## The last odd variable: a loop over the powers of two -/

/-- `true` iff `e` does not give a solution `y ≥ L`, coprime to `pre`, of
`Q (1 + e)(1 + y) = 2 P e y`. -/
def candOk (P Q L : ℕ) (pre : List ℕ) (e : ℕ) : Bool :=
  !(decide (Q * (1 + e) < 2 * P * e) && Q * (1 + e) % (2 * P * e - Q * (1 + e)) == 0 &&
    decide (L ≤ Q * (1 + e) / (2 * P * e - Q * (1 + e))) &&
    coprimeAll (Q * (1 + e) / (2 * P * e - Q * (1 + e))) pre)

lemma candOk_false {P Q L e y : ℕ} {pre : List ℕ} (hP : 0 < P) (he : 0 < e) (hy : 0 < y)
    (hL : L ≤ y) (hpre : ∀ p ∈ pre, Nat.Coprime y p)
    (heq : Q * (1 + e) * (1 + y) = 2 * P * e * y) : candOk P Q L pre e = false := by
  set X := Q * (1 + e) with hX
  have hX0 : 0 < X := by
    rcases Nat.eq_zero_or_pos X with h0 | h0
    · rw [h0, zero_mul] at heq
      have : 0 < 2 * P * e * y := Nat.mul_pos (Nat.mul_pos (by omega) he) hy
      omega
    · exact h0
  have hd : X = (2 * P * e - X) * y := by
    rw [Nat.sub_mul]; rw [mul_add, mul_one] at heq; omega
  have hdpos : 0 < 2 * P * e - X := by
    rcases Nat.eq_zero_or_pos (2 * P * e - X) with h0 | h0
    · rw [h0, zero_mul] at hd; omega
    · exact h0
  have hlt : X < 2 * P * e := by omega
  have hdiv : X / (2 * P * e - X) = y :=
    Nat.div_eq_of_eq_mul_left hdpos (by rw [mul_comm]; exact hd)
  have hmod : X % (2 * P * e - X) = 0 := Nat.mod_eq_zero_of_dvd ⟨y, hd⟩
  have hca : coprimeAll y pre = true := coprimeAll_of hpre
  simp only [candOk, ← hX, hdiv, hmod, hlt, hL, hca, decide_true, beq_self_eq_true,
    Bool.and_self, Bool.not_true]

/-- Loop over `e = 2^i, 2^{i+1}, …` while `e ≤ B`. -/
def powLoop (P Q L : ℕ) (pre : List ℕ) (B : ℕ) : ℕ → ℕ → Bool
  | 0, _ => false
  | f + 1, e => decide (B < e) || (candOk P Q L pre e && powLoop P Q L pre B f (2 * e))

lemma powLoop_spec {P Q L B : ℕ} {pre : List ℕ} : ∀ (f i a : ℕ),
    powLoop P Q L pre B f (2 ^ i) = true → i ≤ a → 2 ^ a ≤ B → candOk P Q L pre (2 ^ a) = true
  | 0, _, _, h, _, _ => by simp [powLoop] at h
  | f + 1, i, a, h, hia, haB => by
    simp only [powLoop, Bool.or_eq_true, decide_eq_true_eq, Bool.and_eq_true] at h
    rcases h with h | ⟨hc, hr⟩
    · have := Nat.pow_le_pow_right (show 0 < 2 by norm_num) hia; omega
    · rcases hia.lt_or_eq with hlt | rfl
      · rw [← pow_succ'] at hr
        exact powLoop_spec f (i + 1) a hr hlt haB
      · exact hc

/-- `min(m, x) = m` and `Q (1 + m)(1 + x) = 2 P m x` give `(2P - Q) m ≤ 3Q`. -/
lemma min_bound {P Q m x : ℕ} (hm : 1 ≤ m) (hmx : m ≤ x)
    (heq : Q * (1 + m) * (1 + x) = 2 * P * m * x) : (2 * P - Q) * m ≤ 3 * Q := by
  have hx : 0 < x := by omega
  have h1 : (1 + x) * m ≤ (1 + m) * x := by nlinarith
  have h2 : 2 * P * m * m * x ≤ Q * (1 + m) * (1 + m) * x := by
    calc 2 * P * m * m * x = Q * (1 + m) * ((1 + x) * m) := by
          rw [show 2 * P * m * m * x = 2 * P * m * x * m by ring, ← heq]; ring
      _ ≤ Q * (1 + m) * ((1 + m) * x) := Nat.mul_le_mul_left _ h1
      _ = Q * (1 + m) * (1 + m) * x := by ring
  have h3 : 2 * P * m * m ≤ Q * (1 + m) * (1 + m) := Nat.le_of_mul_le_mul_right h2 hx
  have h4 : 2 * P * m * m ≤ Q * m * m + 3 * Q * m := by nlinarith
  have h5 : (2 * P - Q) * m * m ≤ 3 * Q * m := by
    rw [Nat.sub_mul, Nat.sub_mul]; omega
  exact Nat.le_of_mul_le_mul_right h5 (by omega)

/-- The bound on the power of two in the last step. -/
lemma pow_le_bound {P Q a y : ℕ} (hPQ : Q < 2 * P) (hy : 1 ≤ y)
    (heq : Q * (1 + 2 ^ a) * (1 + y) = 2 * P * 2 ^ a * y) :
    2 ^ a ≤ Q * (1 + 3 * Q / (2 * P - Q)) := by
  set E := 2 ^ a with hE
  have hE1 : 1 ≤ E := Nat.one_le_two_pow
  have hd : 0 < 2 * P - Q := by omega
  have hQ : 0 < Q := by
    rcases Nat.eq_zero_or_pos Q with h0 | h0
    · rw [h0] at heq
      have : 0 < 2 * P * E * y := Nat.mul_pos (Nat.mul_pos (by omega) hE1) hy
      simp at heq; omega
    · exact h0
  -- `E ∣ Q (1 + y)`, since `E` is coprime to `1 + E`.
  have hdvd : E ∣ Q * (1 + y) := by
    have h1 : E ∣ Q * (1 + y) * (1 + E) :=
      ⟨2 * P * y, by rw [show Q * (1 + y) * (1 + E) = Q * (1 + E) * (1 + y) by ring, heq]; ring⟩
    have hc : Nat.Coprime E (1 + E) := by
      rw [Nat.coprime_comm, Nat.coprime_add_self_left]; exact Nat.coprime_one_left E
    exact hc.dvd_of_dvd_mul_right h1
  have hEle : E ≤ Q * (1 + y) := Nat.le_of_dvd (Nat.mul_pos hQ (by omega)) hdvd
  rcases le_total y E with hyE | hEy
  · have hb := min_bound (P := P) (Q := Q) hy hyE (by
      rw [show Q * (1 + y) * (1 + E) = Q * (1 + E) * (1 + y) by ring, heq]; ring)
    have : y ≤ 3 * Q / (2 * P - Q) := (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hb)
    calc E ≤ Q * (1 + y) := hEle
      _ ≤ Q * (1 + 3 * Q / (2 * P - Q)) := Nat.mul_le_mul_left _ (by omega)
  · have hb := min_bound hE1 hEy heq
    have : E ≤ 3 * Q / (2 * P - Q) := (Nat.le_div_iff_mul_le hd).2 (by rw [mul_comm]; exact hb)
    calc E ≤ 3 * Q / (2 * P - Q) := this
      _ ≤ 1 * (1 + 3 * Q / (2 * P - Q)) := by omega
      _ ≤ Q * (1 + 3 * Q / (2 * P - Q)) := Nat.mul_le_mul_right _ hQ

/-! ## The checker -/

/-- The search. `true` means: there are no sorted, odd, pairwise coprime `y₁ < ⋯ < y_r`
(all `≥ L`, coprime to `pre`) and no `a` with `2^a ≥ max L M` such that
`Q (1 + 2^a) ∏ (1 + yᵢ) = 2 P 2^a ∏ yᵢ`. `fuel` only makes the recursion structural. -/
def fchk : ℕ → ℕ → ℕ → ℕ → ℕ → List ℕ → ℕ → Bool
  | 0, _, _, _, _, _, _ => false
  | _ + 1, _, _, _, _, _, 0 => false
  | _ + 1, P, Q, _, L, pre, 1 =>
    if 2 * P ≤ Q then 0 < Q
    else powLoop P Q L pre (Q * (1 + 3 * Q / (2 * P - Q))) (Q * (1 + 3 * Q / (2 * P - Q)) + 1) 1
  | f + 1, P, Q, M, L, pre, r + 2 =>
    if 2 * P ≤ Q then 0 < Q
    else if Q * ascProd2 (2 * (L / 2) + 1 + 1) (r + 2) * (max L M + 1) <
        2 * P * ascProd2 (2 * (L / 2) + 1) (r + 2) * max L M then true
    else
      (if L % 2 = 1 then
        (!coprimeAll L pre || fchk f (P * L) (Q * (1 + L)) M (L + 1) (L :: pre) (r + 1))
      else
        (!(isPow2From L 1 L && decide (M ≤ L)) ||
          upnCheck f (P * L) (Q * (1 + L)) (L + 1) pre (r + 2))) &&
      fchk f P Q M (L + 1) pre (r + 2)

/-- Soundness of `fchk`. -/
theorem fchk_sound : ∀ (fuel P Q M L : ℕ) (pre : List ℕ) (r : ℕ),
    fchk fuel P Q M L pre r = true → 2 ≤ L →
    ∀ (ys : List ℕ) (a : ℕ), ys.length = r → ys.Sorted (· < ·) → (∀ y ∈ ys, L ≤ y) →
      (∀ y ∈ ys, y % 2 = 1) → (∀ y ∈ ys, ∀ p ∈ pre, Nat.Coprime y p) →
      ys.Pairwise Nat.Coprime → L ≤ 2 ^ a → M ≤ 2 ^ a →
      Q * (1 + 2 ^ a) * (ys.map (1 + ·)).prod ≠ 2 * P * 2 ^ a * ys.prod
  | 0, _, _, _, _, _, _, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [fchk] at h
  | _ + 1, _, _, _, _, _, 0, h, _, _, _, _, _, _, _, _, _, _, _ => by simp [fchk] at h
  | f + 1, P, Q, M, L, pre, 1, h, hL2, ys, a, hlen, _, hL, _, hpre, _, hLE, _ => by
    simp only [fchk] at h
    by_cases h2P : 2 * P ≤ Q
    · rw [if_pos h2P, decide_eq_true_iff] at h
      exact ne_of_two_mul_le ys h2P h
    rw [if_neg h2P] at h
    obtain ⟨y, rfl⟩ : ∃ y, ys = [y] := by
      rcases ys with _ | ⟨y, _ | ⟨z, ys⟩⟩
      · simp at hlen
      · exact ⟨y, rfl⟩
      · simp at hlen
    intro heq
    simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one] at heq
    have hy : L ≤ y := hL y (by simp)
    have hB := pow_le_bound (by omega) (by omega) heq
    have hc := powLoop_spec _ 0 a (by simpa using h) (Nat.zero_le a) hB
    rw [candOk_false (by omega) Nat.one_le_two_pow (by omega) hy (hpre y (by simp)) heq] at hc
    exact Bool.false_ne_true hc
  | f + 1, P, Q, M, L, pre, r + 2, h, hL2, ys, a, hlen, hs, hL, hodd, hpre, hcop, hLE, hME => by
    simp only [fchk] at h
    by_cases h2P : 2 * P ≤ Q
    · rw [if_pos h2P, decide_eq_true_iff] at h
      exact ne_of_two_mul_le ys h2P h
    rw [if_neg h2P] at h
    set E := 2 ^ a with hE
    have hE1 : 1 ≤ E := Nat.one_le_two_pow
    have ha : a ≠ 0 := by rintro rfl; simp [hE] at hLE; omega
    have hEev : E % 2 = 0 := Nat.even_iff.1 (by rw [hE]; exact (Nat.even_pow' ha).2 even_two)
    set Lo := 2 * (L / 2) + 1 with hLo
    set ME := max L M with hMEdef
    have hyLo : ∀ y ∈ ys, Lo ≤ y := fun y hy => by
      have := hL y hy; have := hodd y hy; omega
    have hone : ∀ y ∈ ys, 1 ≤ y := fun y hy => by have := hL y hy; omega
    have hpos := prod_pos_of_one_le ys hone
    by_cases hb : Q * ascProd2 (Lo + 1) (r + 2) * (ME + 1) < 2 * P * ascProd2 Lo (r + 2) * ME
    · intro heq
      have hm := prod2_succ_mul_le ys Lo hs hodd hyLo
      rw [hlen] at hm
      have hEME : (1 + E) * ME ≤ E * (ME + 1) := by
        have : ME ≤ E := max_le hLE hME
        nlinarith
      have hA : 0 < ascProd2 Lo (r + 2) := ascProd2_pos _ _ (by omega)
      have hEp : 0 < E * ys.prod := Nat.mul_pos hE1 hpos
      have key : 2 * P * ascProd2 Lo (r + 2) * ME * (E * ys.prod) ≤
          Q * ascProd2 (Lo + 1) (r + 2) * (ME + 1) * (E * ys.prod) := by
        calc 2 * P * ascProd2 Lo (r + 2) * ME * (E * ys.prod)
            = Q * (1 + E) * (ys.map (1 + ·)).prod * ascProd2 Lo (r + 2) * ME := by
              rw [heq]; ring
          _ = Q * (((1 + E) * ME) * ((ys.map (1 + ·)).prod * ascProd2 Lo (r + 2))) := by ring
          _ ≤ Q * ((E * (ME + 1)) * (ys.prod * ascProd2 (Lo + 1) (r + 2))) :=
              Nat.mul_le_mul_left _ (Nat.mul_le_mul hEME hm)
          _ = Q * ascProd2 (Lo + 1) (r + 2) * (ME + 1) * (E * ys.prod) := by ring
      have := Nat.mul_lt_mul_of_pos_right hb hEp
      omega
    rw [if_neg hb, Bool.and_eq_true] at h
    obtain ⟨hbr, hrest⟩ := h
    have hne : ys ≠ [] := by rintro rfl; simp at hlen
    obtain ⟨y, ys', rfl⟩ : ∃ y ys', ys = y :: ys' := List.exists_cons_of_ne_nil hne
    have hs' := List.sorted_cons.1 hs
    have hyL : L ≤ y := hL y (by simp)
    have hyo : y % 2 = 1 := hodd y (by simp)
    -- The generic step: everything is `≥ L + 1`.
    have step : (∀ z ∈ y :: ys', L + 1 ≤ z) → L + 1 ≤ E →
        Q * (1 + E) * ((y :: ys').map (1 + ·)).prod ≠ 2 * P * E * (y :: ys').prod :=
      fun h1 h2 => fchk_sound f P Q M (L + 1) pre (r + 2) hrest (by omega) (y :: ys') a hlen hs
        h1 hodd hpre hcop h2 hME
    by_cases hLodd : L % 2 = 1
    · rw [if_pos hLodd] at hbr
      have hEL : L + 1 ≤ E := by omega
      by_cases hyL' : y = L
      · subst hyL'
        rw [Bool.or_eq_true] at hbr
        rcases hbr with hbr | hbr
        · have : coprimeAll y pre = true := coprimeAll_of (hpre y (by simp))
          simp [this] at hbr
        · rw [List.pairwise_cons] at hcop
          intro heq
          refine fchk_sound f (P * y) (Q * (1 + y)) M (y + 1) (y :: pre) (r + 1) hbr (by omega)
            ys' a (by simpa using hlen) hs'.2 (fun z hz => hs'.1 z hz)
            (fun z hz => hodd z (by simp [hz])) ?_ hcop.2 hEL hME ?_
          · intro z hz p hp
            rcases List.mem_cons.1 hp with rfl | hp
            · exact (hcop.1 z hz).symm
            · exact hpre z (by simp [hz]) p hp
          · simp only [List.map_cons, List.prod_cons] at heq
            rw [← hE]; linarith [heq]
      · refine step (fun z hz => ?_) hEL
        rcases List.mem_cons.1 hz with rfl | hz
        · omega
        · have := hs'.1 z hz; omega
    · rw [if_neg hLodd] at hbr
      have hall : ∀ z ∈ y :: ys', L + 1 ≤ z := fun z hz => by
        have := hL z hz; have := hodd z hz; omega
      by_cases hEL : E = L
      · rw [Bool.or_eq_true] at hbr
        rcases hbr with hbr | hbr
        · have hp2 : isPow2From L 1 L = true := by
            rw [← hEL, hE, show (1 : ℕ) = 2 ^ 0 from rfl]
            exact isPow2From_pow _ 0 a (Nat.zero_le a) (by simpa using Nat.lt_two_pow_self)
          rw [← hEL] at hbr
          simp [hp2, hEL, show M ≤ L by omega] at hbr
        · intro heq
          refine upnCheck_sound f (P * L) (Q * (1 + L)) (L + 1) pre (r + 2) hbr (by omega)
            (y :: ys') hlen hs hall hpre hcop ?_
          rw [← hEL]; linarith [heq]
      · exact step hall (by omega)

/-! ## The 2-adic lower bound on the power of two -/

lemma two_pow_dvd_prod : ∀ (ys : List ℕ), (∀ y ∈ ys, y % 2 = 1) →
    2 ^ ys.length ∣ (ys.map (1 + ·)).prod
  | [], _ => by simp
  | y :: ys, h => by
    simp only [List.length_cons, List.map_cons, List.prod_cons, pow_succ']
    have h2 : 2 ∣ 1 + y := by have := h y (by simp); omega
    exact mul_dvd_mul h2 (two_pow_dvd_prod ys fun z hz => h z (by simp [hz]))

/-- `(1 + 2^a) ∏ (1 + yᵢ) = 2 · 2^a ∏ yᵢ` with `k` odd `yᵢ` forces `k ≤ a + 1`. -/
lemma two_pow_le_of_eq {a : ℕ} {ys : List ℕ} (hodd : ∀ y ∈ ys, y % 2 = 1)
    (hodd' : ys.prod % 2 = 1)
    (heq : (1 + 2 ^ a) * (ys.map (1 + ·)).prod = 2 * 2 ^ a * ys.prod) :
    ys.length ≤ a + 1 := by
  have h1 : 2 ^ ys.length ∣ 2 ^ (a + 1) * ys.prod := by
    have := two_pow_dvd_prod ys hodd
    rw [pow_succ', ← heq]
    exact Dvd.dvd.mul_left this _
  have hc : Nat.Coprime (2 ^ ys.length) ys.prod :=
    Nat.Coprime.pow_left _ (Nat.coprime_two_left.2 (Nat.odd_iff.2 hodd'))
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).1 (hc.dvd_of_dvd_mul_right h1)

/-! ## Six odd prime factors -/

/-- Kernel computation: no six sorted, odd, pairwise coprime `yᵢ ≥ 2` and `2^a ≥ 32` satisfy
`(1 + 2^a) ∏ (1 + yᵢ) = 2 · 2^a ∏ yᵢ`. -/
theorem fchk_six : fchk 5000 1 1 32 2 [2] 6 = true := by decide +kernel

/-- There is no unitary perfect number with exactly seven prime factors (six of them odd). -/
theorem not_isUnitaryPerfect_of_card_primeFactors_eq_seven {n : ℕ} (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 7) : False := by
  have hev := even_of_isUnitaryPerfect h
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  obtain ⟨a, m, ha, hc2, hnm, hcm⟩ :=
    exists_split_of_dvd Nat.prime_two hn0 (even_iff_two_dvd.1 hev)
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hnm; exact hn0 hnm.symm
  have hmodd : m % 2 = 1 := Nat.odd_iff.1 <|
    Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_left (dvd_pow_self 2 ha.ne') hc2)
  obtain ⟨l, hsort, hlen, hgt, hcop, hprod, hsig⟩ := exists_sorted_factors hm0
  have hlen6 : l.length = 6 := by omega
  have hodd : ∀ y ∈ l, y % 2 = 1 := fun y hy => by
    have hd : y ∣ m := hprod ▸ List.dvd_prod hy
    exact Nat.odd_iff.1 ((Nat.odd_iff.2 hmodd).of_dvd_nat hd)
  have heq : (1 + 2 ^ a) * (l.map (1 + ·)).prod = 2 * 2 ^ a * l.prod := by
    rw [hsig, hprod, ← usigma_prime_pow_mul Nat.prime_two ha hc2, hnm, hs, ← hnm]; ring
  have ha5 : 6 ≤ a + 1 := hlen6 ▸ two_pow_le_of_eq hodd (hprod ▸ hmodd) heq
  refine fchk_sound 5000 1 1 32 2 [2] 6 fchk_six le_rfl l a hlen6 hsort
    (fun y hy => hgt y hy) hodd ?_ hcop ?_ ?_ ?_
  · intro y hy p hp
    simp only [List.mem_singleton] at hp
    subst hp
    exact Nat.coprime_two_right.2 (Nat.odd_iff.2 (hodd y hy))
  · calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  · calc 32 = 2 ^ 5 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
  · rw [one_mul, mul_one]; exact heq

/-- Classification of unitary perfect numbers with at most seven prime factors (at most six odd
prime factors): they are exactly `6`, `60`, `90` and `87360`. -/
theorem isUnitaryPerfect_of_card_primeFactors_le_seven_iff {n : ℕ}
    (hcard : n.primeFactors.card ≤ 7) :
    IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 ∨ n = 87360 := by
  rcases (show n.primeFactors.card ≤ 6 ∨ n.primeFactors.card = 7 by omega) with h6 | h7
  · exact isUnitaryPerfect_of_card_primeFactors_le_six_iff h6
  · constructor
    · intro h; exact (not_isUnitaryPerfect_of_card_primeFactors_eq_seven h h7).elim
    · rintro (rfl | rfl | rfl | rfl)
      exacts [isUnitaryPerfect_6, isUnitaryPerfect_60, isUnitaryPerfect_90,
        isUnitaryPerfect_87360]

end ErdosResearch.Erdos1052
