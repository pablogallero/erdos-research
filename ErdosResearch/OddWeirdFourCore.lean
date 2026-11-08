import ErdosResearch.OddWeirdThree

/-!
# Erdős Problem 470: a sound checker for "multiple of a pseudoperfect base, or deficient"

`chk` walks the odd numbers `n = p₁^{x₁} ⋯ p_j^{x_j}` with `3 ≤ p₁ < ⋯ < p_j` odd primes, in the
order "smallest prime first, then its exponent". A node carries
* `rs : Facts`: factorizations of pseudoperfect bases, with the primes already chosen consumed
  (`step`); an empty factorization means a base divides the prefix (`hasNil`), so `n` is
  pseudoperfect;
* `A / B`: an upper bound for `σ(M)/M` of the prefix `M` chosen so far;
* `j`: the number of primes still to choose, all `≥ q`;
* `e`: `0` while looking for the next prime, `e ≥ 1` once the next prime is `q` with exponent `≥ e`.

At `e = 0` the node is closed if the stride-2 bound `A/B · ∏ (q+2i)/(q+2i-1) < 2` shows every
completion is deficient; otherwise `q` (if it may be prime) and `q + 2` are explored. At `e ≥ 1`
the node tries the *region* "`x ≥ e`" with the bound `q/(q-1)`, and if that fails, the exact
exponent `e` (ratio `σ(q^e)/q^e`) and then `x ≥ e + 1`.

`Sound rs A B j q e` is the statement the node certifies; `chk_sound` proves `chk … = true →
Sound …`, and the combinators `sound_loop`, `sound_exp` let a proof be split into separately
checked pieces (each `decide +kernel` gets its own kernel cache).
-/

namespace Erdos470Research

open ArithmeticFunction

/-! ## Definitions -/

/-- `ascP q j = q (q+2) ⋯ (q + 2(j-1))`. -/
def ascP : ℕ → ℕ → ℕ
  | _, 0 => 1
  | q, j + 1 => q * ascP (q + 2) j

/-- `geom q e = 1 + q + ⋯ + q^e`. -/
def geom (q : ℕ) : ℕ → ℕ
  | 0 => 1
  | e + 1 => geom q e + q ^ (e + 1)

/-- Trial division of `q` by `d, d+2, …`: `1` if `q < d*d` is reached, a divisor `≥ d` if one is
found, `0` if the fuel runs out. -/
def findDiv (q d : ℕ) : ℕ → ℕ
  | 0 => 0
  | f + 1 => if q < d * d then 1 else if q % d = 0 then d else findDiv q (d + 2) f

/-- `q` certainly is not prime. -/
def skipB (q : ℕ) : Bool := decide (2 ≤ findDiv q 3 q)

/-- Remaining factorizations `[(p, k), …]` of the bases. -/
abbrev Facts := List (List (ℕ × ℕ))

/-- Choose the prime `q` with exponent `e`: drop the factorizations that need a skipped smaller
prime or a higher power of `q`, and consume `q` from the others. -/
def step (q e : ℕ) : Facts → Facts
  | [] => []
  | [] :: rs => [] :: step q e rs
  | ((p, k) :: r) :: rs =>
    if p < q then step q e rs
    else if p = q then (if k ≤ e then r :: step q e rs else step q e rs)
    else ((p, k) :: r) :: step q e rs

def hasNil : Facts → Bool
  | [] => false
  | [] :: _ => true
  | _ :: rs => hasNil rs

/-- The checker (see the module docstring). -/
def chk : Facts → ℕ → ℕ → ℕ → ℕ → ℕ → ℕ → Bool
  | _, 0, _, _, _, _, _ => false
  | _, _ + 1, A, B, 0, _, 0 => decide (A < 2 * B)
  | rs, f + 1, A, B, j + 1, q, 0 =>
    decide (A * ascP q (j + 1) < 2 * B * ascP (q - 1) (j + 1)) ||
      ((skipB q || chk rs f A B (j + 1) q 1) && chk rs f A B (j + 1) (q + 2) 0)
  | rs, f + 1, A, B, j, q, e + 1 =>
    hasNil (step q (e + 1) rs) ||
    chk (step q (e + 1) rs) f (A * q) (B * (q - 1)) (j - 1) (q + 2) 0 ||
    (chk (step q (e + 1) rs) f (A * geom q (e + 1)) (B * q ^ (e + 1)) (j - 1) (q + 2) 0 &&
      chk rs f A B j q (e + 2))

/-- Strictly decreasing. -/
def decB : List ℕ → Bool
  | a :: b :: l => decide (b < a) && decB (b :: l)
  | _ => true

/-- `∏ p^k`. -/
def ppow (r : List (ℕ × ℕ)) : ℕ := (r.map fun pe => pe.1 ^ pe.2).prod

/-- A certificate `(b, [(p, k), …], X)`: `b = ∏ p^k` with increasing odd primes `p` (checked by
trial division), and `X` is a strictly decreasing list of proper divisors of `b` with sum
`σ(b) - 2b`; the other proper divisors then sum to `b`. -/
def certOK (c : ℕ × List (ℕ × ℕ) × List ℕ) : Bool :=
  decide (0 < c.1) && decB (c.2.1.map Prod.fst).reverse &&
    c.2.1.all (fun pe => decide (3 ≤ pe.1) && pe.1 % 2 == 1 && findDiv pe.1 3 pe.1 == 1) &&
    ppow c.2.1 == c.1 && decB c.2.2 &&
    c.2.2.all (fun d => c.1 % d == 0 && decide (d < c.1)) &&
    decide (2 * c.1 ≤ (c.2.1.map fun pe => geom pe.1 pe.2).prod) &&
    c.2.2.sum + 2 * c.1 == (c.2.1.map fun pe => geom pe.1 pe.2).prod

/-! ## Arithmetic lemmas -/

lemma geom_eq {p : ℕ} (hp : p.Prime) (e : ℕ) : geom p e = σ 1 (p ^ e) := by
  rw [sigma_one_apply_prime_pow hp]
  induction e with
  | zero => simp [geom]
  | succ e ih => rw [geom, ih, Finset.sum_range_succ _ (e + 1)]

lemma findDiv_one : ∀ (f q d : ℕ), findDiv q d f = 1 → 2 ≤ d →
    ∀ m, d ≤ m → m % 2 = d % 2 → m * m ≤ q → ¬ m ∣ q
  | 0, _, _, h, _ => by simp [findDiv] at h
  | f + 1, q, d, h, hd => by
    intro m hm hpar hmq
    simp only [findDiv] at h
    split_ifs at h with h1 h2
    · exact absurd (lt_of_lt_of_le h1 (Nat.mul_le_mul hm hm)) (by omega)
    · omega
    · rcases Nat.eq_or_lt_of_le hm with rfl | hlt
      · exact fun hdvd => h2 (Nat.mod_eq_zero_of_dvd hdvd)
      · exact findDiv_one f q (d + 2) h (by omega) m (by omega) (by omega) hmq

lemma findDiv_ge : ∀ (f q d : ℕ), 2 ≤ findDiv q d f → 2 ≤ d →
    findDiv q d f ∣ q ∧ findDiv q d f * findDiv q d f ≤ q
  | 0, _, _, h, _ => by simp [findDiv] at h
  | f + 1, q, d, h, hd => by
    simp only [findDiv] at h ⊢
    split_ifs at h ⊢ with h1 h2
    · omega
    · exact ⟨Nat.dvd_of_mod_eq_zero h2, by omega⟩
    · exact findDiv_ge f q (d + 2) h (by omega)

lemma not_prime_of_skipB {q : ℕ} (h : skipB q = true) : ¬ q.Prime := by
  simp only [skipB, decide_eq_true_eq] at h
  obtain ⟨hdvd, hsq⟩ := findDiv_ge q q 3 h (by norm_num)
  intro hq
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | h1
  · omega
  · rw [h1] at hsq
    have : q * q > q * 1 := Nat.mul_lt_mul_of_pos_left (by have := hq.one_lt; omega) hq.pos
    omega

lemma prime_of_findDiv {q : ℕ} (h3 : 3 ≤ q) (hodd : q % 2 = 1) (h : findDiv q 3 q = 1) :
    q.Prime := by
  by_contra hq
  have hm := Nat.minFac_sq_le_self (by omega) hq
  have hdvd := Nat.minFac_dvd q
  have hmp := Nat.minFac_prime (show q ≠ 1 by omega)
  have h2 : q.minFac ≠ 2 := by
    intro h2; rw [h2] at hdvd; omega
  have hodd' : q.minFac % 2 = 1 := by
    rcases hmp.eq_two_or_odd with h' | h'
    · exact absurd h' h2
    · exact h'
  have hge : 3 ≤ q.minFac := by have := hmp.two_le; omega
  exact findDiv_one q q 3 h (by norm_num) q.minFac hge (by omega) (by nlinarith) hdvd

/-! ## `σ` of a product of prime powers -/

lemma coprime_ppow {p e : ℕ} (hp : p.Prime) :
    ∀ (r : List (ℕ × ℕ)), (∀ pe ∈ r, pe.1.Prime ∧ pe.1 ≠ p) → Nat.Coprime (p ^ e) (ppow r)
  | [], _ => by simp [ppow]
  | (q, k) :: r, h => by
    simp only [ppow, List.map_cons, List.prod_cons]
    have hq := h (q, k) (by simp)
    refine Nat.Coprime.mul_right ?_ (coprime_ppow hp r fun pe hpe => h pe (by simp [hpe]))
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes hp hq.1).2 (Ne.symm hq.2))

/-- `σ(∏ p^k) = ∏ (1 + p + ⋯ + p^k)` for distinct primes. -/
lemma sigma_ppow : ∀ (r : List (ℕ × ℕ)), (r.map Prod.fst).Nodup → (∀ pe ∈ r, pe.1.Prime) →
    σ 1 (ppow r) = (r.map fun pe => geom pe.1 pe.2).prod
  | [], _, _ => by simp [ppow]
  | (p, k) :: r, hnd, hp => by
    simp only [List.map_cons, List.nodup_cons, List.mem_map] at hnd
    have hp0 : p.Prime := hp (p, k) (by simp)
    have hcop : Nat.Coprime (p ^ k) (ppow r) := coprime_ppow hp0 r fun pe hpe =>
      ⟨hp pe (by simp [hpe]), fun h => hnd.1 ⟨pe, hpe, h⟩⟩
    have ih := sigma_ppow r hnd.2 fun pe hpe => hp pe (by simp [hpe])
    have : ppow ((p, k) :: r) = p ^ k * ppow r := by simp [ppow]
    rw [this, isMultiplicative_sigma.map_mul_of_coprime hcop, ih]
    simp [geom_eq hp0]

lemma ppow_pos : ∀ (r : List (ℕ × ℕ)), (∀ pe ∈ r, 0 < pe.1) → 0 < ppow r
  | [], _ => by simp [ppow]
  | (p, k) :: r, h => by
    simp only [ppow, List.map_cons, List.prod_cons]
    exact Nat.mul_pos (Nat.pow_pos (h (p, k) (by simp)))
      (ppow_pos r fun pe hpe => h pe (by simp [hpe]))

/-! ## Certificates -/

lemma decB_sorted : ∀ (l : List ℕ), decB l = true → l.Sorted (· > ·)
  | [], _ => by simp
  | [_], _ => by simp
  | a :: b :: l, h => by
    simp only [decB, Bool.and_eq_true, decide_eq_true_eq] at h
    have ih := decB_sorted (b :: l) h.2
    rw [List.sorted_cons]
    have ih' := ih
    rw [List.sorted_cons] at ih'
    refine ⟨fun c hc => ?_, ih⟩
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact lt_trans (ih'.1 c hc) h.1

lemma pseudoperfect_of_certOK {c : ℕ × List (ℕ × ℕ) × List ℕ} (h : certOK c = true) :
    c.1.Pseudoperfect ∧ ppow c.2.1 = c.1 := by
  obtain ⟨b, fs, xs⟩ := c
  simp only [certOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true]
    at h
  obtain ⟨⟨⟨⟨⟨⟨⟨hb, hinc⟩, hpr⟩, hprod⟩, hdec⟩, hdiv⟩, hle⟩, hsum⟩ := h
  have hprime : ∀ pe ∈ fs, pe.1.Prime := fun pe hpe => by
    have := hpr pe hpe
    exact prime_of_findDiv this.1.1 this.1.2 this.2
  have hnd : (fs.map Prod.fst).Nodup := by
    have := (decB_sorted _ hinc).nodup
    rwa [List.nodup_reverse] at this
  have hσ : σ 1 b = (fs.map fun pe => geom pe.1 pe.2).prod := by
    rw [← hprod]; exact sigma_ppow fs hnd hprime
  refine ⟨⟨hb, b.properDivisors \ xs.toFinset, Finset.sdiff_subset, ?_⟩, hprod⟩
  have hsub : xs.toFinset ⊆ b.properDivisors := fun d hd => by
    have := hdiv d (List.mem_toFinset.mp hd)
    exact Nat.mem_properDivisors.mpr ⟨Nat.dvd_of_mod_eq_zero this.1, this.2⟩
  have h1 := Finset.sum_sdiff hsub (f := fun d => d)
  beta_reduce at h1
  have h2 : ∑ d ∈ xs.toFinset, d = xs.sum := by
    rw [List.sum_toFinset _ (decB_sorted xs hdec).nodup]; simp
  have h3 : ∑ d ∈ b.properDivisors, d + b = σ 1 b := by
    rw [sigma_one_apply, Nat.sum_divisors_eq_sum_properDivisors_add_self]
  omega

/-! ## Bases along the search -/

/-- Every remaining factorization `r` comes from a pseudoperfect base dividing `N · ∏ r`. -/
def Good (N : ℕ) (rs : Facts) : Prop := ∀ r ∈ rs, ∃ b, b.Pseudoperfect ∧ b ∣ N * ppow r

lemma good_step {N : ℕ} (q e : ℕ) : ∀ (rs : Facts), Good N rs → Good (N * q ^ e) (step q e rs)
  | [], _ => by simp [Good, step]
  | [] :: rs, h => by
    intro r hr
    simp only [step, List.mem_cons] at hr
    rcases hr with rfl | hr
    · obtain ⟨b, hb, hdvd⟩ := h [] (by simp)
      exact ⟨b, hb, by simpa [ppow] using dvd_mul_of_dvd_left (by simpa [ppow] using hdvd) _⟩
    · exact good_step q e rs (fun r hr => h r (by simp [hr])) r hr
  | ((p, k) :: r') :: rs, h => by
    have ih := good_step q e rs (fun r hr => h r (by simp [hr]))
    obtain ⟨b, hb, hdvd⟩ := h ((p, k) :: r') (by simp)
    have hpp : ppow ((p, k) :: r') = p ^ k * ppow r' := by simp [ppow]
    intro r hr
    simp only [step] at hr
    split_ifs at hr with h1 h2 h3
    · exact ih r hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · refine ⟨b, hb, hdvd.trans ?_⟩
        rw [hpp, h2]
        have : q ^ k ∣ q ^ e := Nat.pow_dvd_pow q h3
        calc N * (q ^ k * ppow r) = (N * q ^ k) * ppow r := by ring
          _ ∣ (N * q ^ e) * ppow r := Nat.mul_dvd_mul_right (Nat.mul_dvd_mul_left N this) _
      · exact ih r hr
    · exact ih r hr
    · rcases List.mem_cons.mp hr with rfl | hr
      · exact ⟨b, hb, hdvd.trans (by
          rw [mul_assoc, mul_comm (q ^ e), ← mul_assoc]; exact dvd_mul_right _ _)⟩
      · exact ih r hr

lemma good_hasNil {N : ℕ} : ∀ (rs : Facts), Good N rs → hasNil rs = true →
    ∃ b, b.Pseudoperfect ∧ b ∣ N
  | [], _, h => by simp [hasNil] at h
  | [] :: _, hg, _ => by simpa [ppow] using hg [] (by simp)
  | (_ :: _) :: rs, hg, h => good_hasNil rs (fun r hr => hg r (by simp [hr])) (by
      simpa [hasNil] using h)

/-- The bases of `OddWeirdFourData.lean`, as a starting point. -/
lemma good_certs (cs : List (ℕ × List (ℕ × ℕ) × List ℕ)) (h : cs.all certOK = true) :
    Good 1 (cs.map (·.2.1)) := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  obtain ⟨h1, h2⟩ := pseudoperfect_of_certOK (List.all_eq_true.mp h c hc)
  exact ⟨c.1, h1, by rw [one_mul, h2]⟩

/-! ## What a node certifies -/

/-- The prime powers `p ^ ex p` for `p ∈ ps`. -/
def fsOf (ps : List ℕ) (ex : ℕ → ℕ) : List (ℕ × ℕ) := ps.map fun p => (p, ex p)

/-- The statement certified by the node `(rs, A, B, j, q, e)`: for every prefix `M` with
`σ(M)/M ≤ A/B` that is a multiple of `N` (where `rs` is good for `N`), and every completion by
`j` odd primes `≥ q` (the first one `q` with exponent `≥ e`, if `e ≠ 0`) not dividing `M`, the
number `n` is deficient or pseudoperfect. -/
def Sound (rs : Facts) (A B j q e : ℕ) : Prop :=
  ∀ (N M : ℕ) (ps : List ℕ) (ex : ℕ → ℕ), Good N rs → N ∣ M → 0 < M →
    σ 1 M * B ≤ A * M → 3 ≤ q → q % 2 = 1 →
    ps.length = j → ps.Sorted (· < ·) →
    (∀ p ∈ ps, p.Prime ∧ q ≤ p ∧ p % 2 = 1 ∧ ¬ p ∣ M ∧ 1 ≤ ex p) →
    (e ≠ 0 → ps.head? = some q ∧ e ≤ ex q) →
    σ 1 (M * ppow (fsOf ps ex)) < 2 * (M * ppow (fsOf ps ex)) ∨
      (M * ppow (fsOf ps ex)).Pseudoperfect

lemma ppow_fsOf_cons (p : ℕ) (ps : List ℕ) (ex : ℕ → ℕ) :
    ppow (fsOf (p :: ps) ex) = p ^ ex p * ppow (fsOf ps ex) := by
  simp [ppow, fsOf]

lemma ppow_fsOf_pos (ps : List ℕ) (ex : ℕ → ℕ) (h : ∀ p ∈ ps, p.Prime) :
    0 < ppow (fsOf ps ex) :=
  ppow_pos _ fun pe hpe => by
    obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hpe
    exact (h p hp).pos

lemma coprime_M_ppow {M : ℕ} : ∀ (ps : List ℕ) (ex : ℕ → ℕ), (∀ p ∈ ps, p.Prime ∧ ¬ p ∣ M) →
    Nat.Coprime M (ppow (fsOf ps ex))
  | [], _, _ => by simp [ppow, fsOf]
  | p :: ps, ex, h => by
    rw [ppow_fsOf_cons]
    have hp := h p (by simp)
    refine Nat.Coprime.mul_right ?_ (coprime_M_ppow ps ex fun p hp => h p (by simp [hp]))
    exact Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hp.1).2 hp.2).symm

/-- `σ(R) ∏ (p - 1) ≤ R ∏ p` for `R = ∏ p^{ex p}` over sorted primes. -/
lemma sigma_ppow_fsOf_le : ∀ (ps : List ℕ) (ex : ℕ → ℕ), ps.Sorted (· < ·) →
    (∀ p ∈ ps, p.Prime) →
    σ 1 (ppow (fsOf ps ex)) * (ps.map (· - 1)).prod ≤ ppow (fsOf ps ex) * ps.prod
  | [], _, _, _ => by simp [ppow, fsOf]
  | p :: ps, ex, hs, hp => by
    rw [List.sorted_cons] at hs
    have hp0 := hp p (by simp)
    have hcop : Nat.Coprime (p ^ ex p) (ppow (fsOf ps ex)) := coprime_ppow hp0 _ fun pe hpe => by
      obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hpe
      exact ⟨hp r (by simp [hr]), (ne_of_lt (hs.1 r hr)).symm⟩
    have ih := sigma_ppow_fsOf_le ps ex hs.2 fun r hr => hp r (by simp [hr])
    have h1 := sub_one_mul_sigma_prime_pow_le hp0 (ex p)
    rw [ppow_fsOf_cons, isMultiplicative_sigma.map_mul_of_coprime hcop]
    simp only [List.map_cons, List.prod_cons]
    calc σ 1 (p ^ ex p) * σ 1 (ppow (fsOf ps ex)) * ((p - 1) * (ps.map (· - 1)).prod)
        = ((p - 1) * σ 1 (p ^ ex p)) * (σ 1 (ppow (fsOf ps ex)) * (ps.map (· - 1)).prod) := by
          ring
      _ ≤ (p ^ ex p * p) * (ppow (fsOf ps ex) * ps.prod) := Nat.mul_le_mul h1 ih
      _ = p ^ ex p * ppow (fsOf ps ex) * (p * ps.prod) := by ring

/-- Stride-2 bound: sorted odd `p ≥ L` give `∏ p · ascP (L-1) ≤ ∏ (p-1) · ascP L`. -/
lemma prod_mul_ascP_le : ∀ (ps : List ℕ) (L : ℕ), ps.Sorted (· < ·) → (∀ p ∈ ps, p % 2 = 1) →
    (∀ p ∈ ps, L ≤ p) → 1 ≤ L →
    ps.prod * ascP (L - 1) ps.length ≤ (ps.map (· - 1)).prod * ascP L ps.length
  | [], _, _, _, _, _ => by simp [ascP]
  | p :: ps, L, hs, ho, hL, h1 => by
    rw [List.sorted_cons] at hs
    have hpL := hL p (by simp)
    have ih := prod_mul_ascP_le ps (L + 2) hs.2 (fun r hr => ho r (by simp [hr]))
      (fun r hr => by
        have := hs.1 r hr; have := ho r (by simp [hr]); have := ho p (by simp); omega)
      (by omega)
    simp only [List.prod_cons, List.map_cons, List.length_cons, ascP]
    rw [show L + 2 - 1 = L - 1 + 2 by omega] at ih
    have hpL' : p * (L - 1) ≤ (p - 1) * L := by
      obtain ⟨a, rfl⟩ : ∃ a, L = a + 1 := ⟨L - 1, by omega⟩
      obtain ⟨b, rfl⟩ : ∃ b, p = b + 1 := ⟨p - 1, by omega⟩
      simp only [Nat.add_sub_cancel]; nlinarith
    calc p * ps.prod * ((L - 1) * ascP (L - 1 + 2) ps.length)
        = (p * (L - 1)) * (ps.prod * ascP (L - 1 + 2) ps.length) := by ring
      _ ≤ ((p - 1) * L) * ((ps.map (· - 1)).prod * ascP (L + 2) ps.length) :=
          Nat.mul_le_mul hpL' ih
      _ = (p - 1) * (ps.map (· - 1)).prod * (L * ascP (L + 2) ps.length) := by ring

lemma ascP_pos : ∀ (L j : ℕ), 1 ≤ L → 0 < ascP L j
  | _, 0, _ => by simp [ascP]
  | L, j + 1, h => Nat.mul_pos (by omega) (ascP_pos (L + 2) j (by omega))

lemma prod_sub_one_pos : ∀ (ps : List ℕ), (∀ p ∈ ps, 2 ≤ p) → 0 < (ps.map (· - 1)).prod
  | [], _ => by simp
  | p :: ps, h => by
    simp only [List.map_cons, List.prod_cons]
    exact Nat.mul_pos (by have := h p (by simp); omega)
      (prod_sub_one_pos ps fun r hr => h r (by simp [hr]))

/-! ## Combinators -/

lemma sound_zero {rs : Facts} {A B q : ℕ} (h : A < 2 * B) : Sound rs A B 0 q 0 := by
  intro N M ps ex _ _ hM hσ _ _ hlen _ _ _
  left
  obtain rfl : ps = [] := List.eq_nil_of_length_eq_zero hlen
  simp only [fsOf, List.map_nil, ppow, List.prod_nil, mul_one]
  by_contra hc
  push_neg at hc
  have h1 : 2 * M * B ≤ σ 1 M * B := Nat.mul_le_mul_right _ hc
  have h2 : A * M < 2 * B * M := Nat.mul_lt_mul_of_pos_right h hM
  have : 2 * M * B = 2 * B * M := by ring
  omega

lemma sound_prune {rs : Facts} {A B j q e : ℕ}
    (h : A * ascP q (j + 1) < 2 * B * ascP (q - 1) (j + 1)) : Sound rs A B (j + 1) q e := by
  intro N M ps ex _ _ hM hσ hq3 _ hlen hs hps _
  left
  have hpr : ∀ p ∈ ps, p.Prime := fun p hp => (hps p hp).1
  have hcop := coprime_M_ppow ps ex fun p hp => ⟨(hps p hp).1, (hps p hp).2.2.2.1⟩
  rw [isMultiplicative_sigma.map_mul_of_coprime hcop]
  set R := ppow (fsOf ps ex)
  set S := σ 1 M
  set T := σ 1 R
  set P := ps.prod
  set P1 := (ps.map (· - 1)).prod
  set a := ascP q (j + 1)
  set a1 := ascP (q - 1) (j + 1)
  have hTR : T * P1 ≤ R * P := sigma_ppow_fsOf_le ps ex hs hpr
  have hPa : P * a1 ≤ P1 * a := by
    have := prod_mul_ascP_le ps q hs (fun p hp => (hps p hp).2.2.1) (fun p hp => (hps p hp).2.1)
      (by omega)
    rwa [hlen] at this
  have hP1 : 0 < P1 := prod_sub_one_pos ps fun p hp => (hpr p hp).two_le
  have ha1 : 0 < a1 := ascP_pos _ _ (by omega)
  have hB : 0 < B := by
    rcases Nat.eq_zero_or_pos B with h0 | h0
    · rw [h0] at h; simp at h
    · exact h0
  have hpos : 0 < B * P1 * a1 := Nat.mul_pos (Nat.mul_pos hB hP1) ha1
  have key : S * T * (B * P1 * a1) < 2 * (M * R) * (B * P1 * a1) := by
    calc S * T * (B * P1 * a1) = (S * B) * (T * P1) * a1 := by ring
      _ ≤ (A * M) * (R * P) * a1 := Nat.mul_le_mul_right _ (Nat.mul_le_mul hσ hTR)
      _ = (A * M * R) * (P * a1) := by ring
      _ ≤ (A * M * R) * (P1 * a) := Nat.mul_le_mul_left _ hPa
      _ = (A * a) * (M * R * P1) := by ring
      _ < (2 * B * a1) * (M * R * P1) := by
          refine Nat.mul_lt_mul_of_pos_right h (Nat.mul_pos (Nat.mul_pos hM ?_) hP1)
          exact ppow_fsOf_pos ps ex hpr
      _ = 2 * (M * R) * (B * P1 * a1) := by ring
  exact Nat.lt_of_mul_lt_mul_right key

lemma sound_loop {rs : Facts} {A B j q : ℕ}
    (h : (skipB q = true ∨ Sound rs A B (j + 1) q 1) ∧ Sound rs A B (j + 1) (q + 2) 0) :
    Sound rs A B (j + 1) q 0 := by
  intro N M ps ex hg hN hM hσ hq3 hqo hlen hs hps _
  obtain ⟨p, ps', rfl⟩ : ∃ p ps', ps = p :: ps' := by
    cases ps with
    | nil => simp at hlen
    | cons p ps' => exact ⟨p, ps', rfl⟩
  have hp := hps p (by simp)
  rcases eq_or_ne p q with rfl | hne
  · rcases h.1 with hskip | hs1
    · exact absurd hp.1 (not_prime_of_skipB hskip)
    · exact hs1 N M _ ex hg hN hM hσ hq3 hqo hlen hs hps fun _ => ⟨rfl, hp.2.2.2.2⟩
  · have hs' := hs
    rw [List.sorted_cons] at hs'
    refine h.2 N M _ ex hg hN hM hσ (by omega) (by omega) hlen hs ?_ (by simp)
    intro r hr
    have hr' := hps r hr
    refine ⟨hr'.1, ?_, hr'.2.2⟩
    rcases List.mem_cons.mp hr with rfl | hr
    · omega
    · have := hs'.1 r hr; omega

lemma sound_exp {rs : Facts} {A B j q e : ℕ}
    (h : hasNil (step q (e + 1) rs) = true ∨
      Sound (step q (e + 1) rs) (A * q) (B * (q - 1)) (j - 1) (q + 2) 0 ∨
      (Sound (step q (e + 1) rs) (A * geom q (e + 1)) (B * q ^ (e + 1)) (j - 1) (q + 2) 0 ∧
        Sound rs A B j q (e + 2))) :
    Sound rs A B j q (e + 1) := by
  intro N M ps ex hg hN hM hσ hq3 hqo hlen hs hps he
  obtain ⟨hhead, hex⟩ := he (by omega)
  obtain ⟨ps', rfl⟩ : ∃ ps', ps = q :: ps' := by
    cases ps with
    | nil => simp at hhead
    | cons p ps' => simp at hhead; exact ⟨ps', by rw [hhead]⟩
  have hq := hps q (by simp)
  have hs' := hs
  rw [List.sorted_cons] at hs'
  set x := ex q
  have hn : M * ppow (fsOf (q :: ps') ex) = (M * q ^ x) * ppow (fsOf ps' ex) := by
    rw [ppow_fsOf_cons]; ring
  have hg' : Good (N * q ^ (e + 1)) (step q (e + 1) rs) := good_step q (e + 1) rs hg
  have hN' : N * q ^ (e + 1) ∣ M * q ^ x := Nat.mul_dvd_mul hN (Nat.pow_dvd_pow q hex)
  have hM' : 0 < M * q ^ x := Nat.mul_pos hM (Nat.pow_pos hq.1.pos)
  have hcop : Nat.Coprime M (q ^ x) :=
    Nat.Coprime.pow_right _ ((Nat.Prime.coprime_iff_not_dvd hq.1).2 hq.2.2.2.1).symm
  have hσM' : σ 1 (M * q ^ x) = σ 1 M * σ 1 (q ^ x) :=
    isMultiplicative_sigma.map_mul_of_coprime hcop
  have hlen' : ps'.length = j - 1 := by simp at hlen; omega
  have hps' : ∀ p ∈ ps', p.Prime ∧ q + 2 ≤ p ∧ p % 2 = 1 ∧ ¬ p ∣ M * q ^ x ∧ 1 ≤ ex p := by
    intro p hp
    have hp' := hps p (by simp [hp])
    have hlt := hs'.1 p hp
    refine ⟨hp'.1, by omega, hp'.2.2.1, ?_, hp'.2.2.2.2⟩
    intro hdvd
    rcases (Nat.Prime.dvd_mul hp'.1).1 hdvd with h1 | h1
    · exact hp'.2.2.2.1 h1
    · have := (Nat.prime_dvd_prime_iff_eq hp'.1 hq.1).1 (hp'.1.dvd_of_dvd_pow h1)
      omega
  rw [hn]
  rcases h with hnil | hreg | ⟨hexact, hnext⟩
  · right
    obtain ⟨b, hb, hbd⟩ := good_hasNil _ hg' hnil
    exact hb.of_dvd (hbd.trans (hN'.trans (dvd_mul_right _ _)))
      (Nat.mul_pos hM' (ppow_fsOf_pos ps' ex fun p hp => (hps' p hp).1))
  · refine hreg _ _ ps' ex hg' hN' hM' ?_ (by omega) (by omega) hlen' hs'.2 hps' (by simp)
    rw [hσM']
    have := sub_one_mul_sigma_prime_pow_le hq.1 x
    calc σ 1 M * σ 1 (q ^ x) * (B * (q - 1)) = (σ 1 M * B) * ((q - 1) * σ 1 (q ^ x)) := by ring
      _ ≤ (A * M) * (q ^ x * q) := Nat.mul_le_mul hσ this
      _ = A * q * (M * q ^ x) := by ring
  · rcases Nat.eq_or_lt_of_le hex with hx | hx
    · refine hexact _ _ ps' ex hg' hN' hM' ?_ (by omega) (by omega) hlen' hs'.2 hps' (by simp)
      rw [hσM', geom_eq hq.1, hx]
      calc σ 1 M * σ 1 (q ^ x) * (B * q ^ x) = (σ 1 M * B) * (σ 1 (q ^ x) * q ^ x) := by ring
        _ ≤ (A * M) * (σ 1 (q ^ x) * q ^ x) := Nat.mul_le_mul_right _ hσ
        _ = A * σ 1 (q ^ x) * (M * q ^ x) := by ring
    · rw [← hn]
      exact hnext N M _ ex hg hN hM hσ hq3 hqo hlen hs hps fun _ => ⟨hhead, by omega⟩

theorem chk_sound : ∀ (f : ℕ) (rs : Facts) (A B j q e : ℕ), chk rs f A B j q e = true →
    Sound rs A B j q e
  | 0, _, _, _, _, _, _, h => by simp [chk] at h
  | f + 1, rs, A, B, 0, q, 0, h => sound_zero (by simpa [chk] using h)
  | f + 1, rs, A, B, j + 1, q, 0, h => by
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at h
    rcases h with h | ⟨h1, h2⟩
    · exact sound_prune h
    · exact sound_loop ⟨h1.imp id (chk_sound f rs A B (j + 1) q 1),
        chk_sound f rs A B (j + 1) (q + 2) 0 h2⟩
  | f + 1, rs, A, B, j, q, e + 1, h => by
    simp only [chk, Bool.or_eq_true, Bool.and_eq_true] at h
    refine sound_exp ?_
    rcases h with (h | h) | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl (chk_sound f _ _ _ _ _ _ h))
    · exact Or.inr (Or.inr ⟨chk_sound f _ _ _ _ _ _ h1, chk_sound f _ _ _ _ _ _ h2⟩)

end Erdos470Research
