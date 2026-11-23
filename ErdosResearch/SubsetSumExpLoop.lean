module

public import ErdosResearch.SubsetSumFifthLoop

@[expose] public section

/-!
# The loop over the exponent of the next prime

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 69).

`SubsetSumFifthLoop` decides the leaf `n q^e` for ONE exponent `e`. Here:

* `abOK_succ`: the abundant interval test `c ≤ n q^e`, `n q^e + c ≤ ∑ D(n q^e)` is monotone in `e`, so
  once it holds it holds for every larger exponent (the step conditions do not depend on `e`).
* `eLoop`: for `e = e₀, e₀ + 1, …` (fuel `k`), stop with `true` as soon as the abundant test holds,
  otherwise require `leafOK` at `e` and go on. `not_weird_of_eLoop`: sound for EVERY `e ≥ e₀`.
* `not_abundant_limit`: if `σ(n) q (r + 1) ≤ 2 n (q − 1) r`, then `n q^e r` is not abundant for any `e`
  (the "limit deficient" pairs, where `eLoop` would never stop).
* `qeLoop`: the loop over odd `q` (composites skipped by `skipB`), with `eLoop` from `e = 1` for each one.
  Instance `not_weird_late_prefix_mul_pow_mul`: for `n = 3^3·11·13^10·17^2·23`, all primes `q < 35`
  (`q ∤ n`), EVERY exponent `e ≥ 1` and every prime `r ∤ n q^e`: `n q^e r` is not weird.

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumExpLoop

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumUniform ErdosResearch.SubsetSumLastOK
  ErdosResearch.PrimeSkip ErdosResearch.SubsetSumFifthLoop

/-- The two step conditions of `intervalGap_mul_prime_pow` (independent of the exponent). -/
def stepOK (n S c g q : ℕ) : Bool :=
  decide (q * g + 2 * c ≤ S + 1) && decide (n + 2 * c ≤ (q + 1) * S + 1)

/-- The abundant interval test for `n q^e`. -/
def abOK (n S c q e : ℕ) : Bool :=
  decide (c ≤ n * q ^ e) && decide (n * q ^ e + c ≤ ppSum n q S e)

theorem abOK_succ {n S c q e : ℕ} (hq : 1 ≤ q) (h : abOK n S c q e = true) :
    abOK n S c q (e + 1) = true := by
  simp only [abOK, Bool.and_eq_true, decide_eq_true_eq] at h ⊢
  obtain ⟨h1, h2⟩ := h
  have hp : n * q ^ (e + 1) = n * q ^ e * q := by ring
  rw [hp]
  refine ⟨le_trans h1 (Nat.le_mul_of_pos_right _ hq), ?_⟩
  simp only [ppSum]
  have := Nat.mul_le_mul_left q h2
  nlinarith

theorem abOK_of_le {n S c q e₀ : ℕ} (hq : 1 ≤ q) (h : abOK n S c q e₀ = true) :
    ∀ e, e₀ ≤ e → abOK n S c q e = true := by
  intro e he
  induction e, he using Nat.le_induction with
  | base => exact h
  | succ e _ ih => exact abOK_succ hq ih

/-- The adaptive loop over the exponent: stop at the first `e` where the abundant test holds. -/
def eLoop (n S c g q : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | e, k + 1 => (stepOK n S c g q && abOK n S c q e) || (leafOK n S c g e q && eLoop n S c g q (e + 1) k)

theorem not_weird_of_eLoop {n S c g q r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n) (hr : r.Prime) :
    ∀ k e₀, eLoop n S c g q e₀ k = true → ∀ e, e₀ ≤ e → ¬ r ∣ n * q ^ e →
      ¬ (n * q ^ e * r).Weird
  | 0, _, hl, _, _, _ => by simp [eLoop] at hl
  | k + 1, e₀, hl, e, he, hrn => by
    simp only [eLoop, Bool.or_eq_true, Bool.and_eq_true] at hl
    rcases hl with ⟨hs, hab⟩ | ⟨hleaf, hrest⟩
    · simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hs
      have hab' := abOK_of_le hq.one_le hab e he
      simp only [abOK, Bool.and_eq_true, decide_eq_true_eq] at hab'
      have hpp := pseudoperfect_mul_prime_pow_of_intervalGap hn hg h hq hqn hs.1 hs.2 e hab'.1 hab'.2
      rintro ⟨-, hnot⟩
      exact hnot (hpp.of_dvd (Dvd.intro r rfl)
        (Nat.mul_pos (Nat.mul_pos hn (pow_pos hq.pos e)) hr.pos))
    · rcases Nat.eq_or_lt_of_le he with rfl | hlt
      · exact not_weird_of_leafOK hn hg h hq hqn hleaf hr hrn
      · exact not_weird_of_eLoop hn hg h hq hqn hr k (e₀ + 1) hrest e (by omega) hrn

/-- **Limit-deficient pairs.** If `σ(n) q (r + 1) ≤ 2 n (q − 1) r` (with `σ(n) = S + n`), then `n q^e r` is
not abundant, for every exponent `e`. -/
theorem not_abundant_limit {n S q e r : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e)
    (hσ : (S + n) * q * (r + 1) ≤ 2 * n * (q - 1) * r) :
    ¬ (n * q ^ e * r).Abundant := by
  intro hab
  have hN : 0 < n * q ^ e := Nat.mul_pos hn (pow_pos hq.pos e)
  have hsum := ppSum_eq hN hr hrn (ppSum_eq hn hq hqn hS e) 1
  rw [pow_one] at hsum
  have hab' : n * q ^ e * r < ppSum (n * q ^ e) r (ppSum n q S e) 1 := by
    rw [← hsum]; exact hab
  simp only [ppSum] at hab'
  obtain ⟨q', rfl⟩ : ∃ q', q = q' + 2 := ⟨q - 2, by have := hq.two_le; omega⟩
  have hx := ppSum_exact' n (q' + 2) S e
  rw [pow_succ] at hx
  have hσ' : (S + n) * (q' + 2) * (r + 1) ≤ 2 * n * (q' + 1) * r := by
    have : q' + 2 - 1 = q' + 1 := by omega
    rwa [this] at hσ
  set T := ppSum n (q' + 2) S e
  set x := (q' + 2) ^ e
  set N := n * x
  -- σ(n q^e) (q - 1) < σ(n) q^(e+1)
  have e1 : (T + N) * (q' + 1) + (S + n) = (S + n) * x * (q' + 2) := by
    have := hx; ring_nf at this ⊢; linarith
  have h1 : (T + N) * (q' + 1) < (S + n) * x * (q' + 2) := by omega
  -- multiply by (r + 1) and use hσ'
  have h2 : (T + N) * (q' + 1) * (r + 1) < (S + n) * x * (q' + 2) * (r + 1) :=
    Nat.mul_lt_mul_of_pos_right h1 (by omega)
  have h3 : (S + n) * x * (q' + 2) * (r + 1) ≤ 2 * N * (q' + 1) * r := by
    have := Nat.mul_le_mul_right x hσ'
    calc (S + n) * x * (q' + 2) * (r + 1) = (S + n) * (q' + 2) * (r + 1) * x := by ring
      _ ≤ 2 * n * (q' + 1) * r * x := this
      _ = 2 * N * (q' + 1) * r := by simp only [N]; ring
  have h4 : (T + N) * (r + 1) * (q' + 1) < 2 * N * r * (q' + 1) := by
    calc (T + N) * (r + 1) * (q' + 1) = (T + N) * (q' + 1) * (r + 1) := by ring
      _ < 2 * N * (q' + 1) * r := lt_of_lt_of_le h2 h3
      _ = 2 * N * r * (q' + 1) := by ring
  have h5 := Nat.lt_of_mul_lt_mul_right h4
  have hNr : n * x * r = N * r := rfl
  nlinarith

/-- The loop over odd `q` with the exponent loop for each one (from `e = 1`, fuel `K`). -/
def qeLoop (P n S c g K : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | q, k + 1 => (skipB q P || n % q == 0 || eLoop n S c g q 1 K) && qeLoop P n S c g K (q + 2) k

theorem eLoop_of_qeLoop {P n S c g K : ℕ} :
    ∀ (k q₀ : ℕ), qeLoop P n S c g K q₀ k = true → ∀ q, q.Prime → ¬ q ∣ n → q₀ ≤ q →
      q < q₀ + 2 * k → q % 2 = q₀ % 2 → eLoop n S c g q 1 K = true
  | 0, q₀, _, q, _, _, h1, h2, _ => by omega
  | k + 1, q₀, hl, q, hq, hqn, h1, h2, h3 => by
    simp only [qeLoop, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    obtain ⟨hhead, htail⟩ := hl
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases hhead with (hs | hd) | hleaf
      · rw [prime_imp_not_skipB hq] at hs; exact absurd hs (by decide)
      · exact absurd (Nat.dvd_of_mod_eq_zero hd) hqn
      · exact hleaf
    · exact eLoop_of_qeLoop k (q₀ + 2) htail q hq hqn (by omega) (by omega) (by omega)

/-- **Soundness of the two loops.** For every prime `q` in the range with `q ∤ n`, every `e ≥ 1` and every
prime `r ∤ n q^e`, `n q^e r` is not weird. -/
theorem not_weird_of_qeLoop {P n S c g K q₀ k q e r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hloop : qeLoop P n S c g K q₀ k = true) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (h1 : q₀ ≤ q) (h2 : q < q₀ + 2 * k) (h3 : q % 2 = q₀ % 2) (he : 1 ≤ e) (hr : r.Prime)
    (hrn : ¬ r ∣ n * q ^ e) : ¬ (n * q ^ e * r).Weird :=
  not_weird_of_eLoop hn hg h hq hqn hr K 1 (eLoop_of_qeLoop k q₀ hloop q hq hqn h1 h2 h3) e he hrn

/-! ### Instance: the late prefix, every exponent of `q` for `q < 35` -/

set_option maxRecDepth 100000 in
/-- The 15 odd `q` with `5 ≤ q < 35`, each with the exponent loop (fuel 40). -/
theorem qeLoop_late_prefix :
    qeLoop P1000 (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) 256030928920159929 2295 5 40 5 15 = true := by
  decide +kernel

/-- **Instance.** Let `n = 3^3·11·13^10·17^2·23`. For every odd prime `q < 35` with `q ∤ n`, every exponent
`e ≥ 1` and every prime `r ∤ n q^e`, `n q^e r` is not weird. -/
theorem not_weird_late_prefix_mul_pow_mul {q e r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hq35 : q < 35)
    (hqn : ¬ q ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) (he : 1 ≤ e) (hr : r.Prime)
    (hrn : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q ^ e) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q ^ e * r).Weird := by
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have h3 : q ≠ 3 := by rintro rfl; exact hqn (by norm_num)
  have h5 : 5 ≤ q := by have := hq.two_le; omega
  exact not_weird_of_qeLoop (by norm_num) (by norm_num) intervalGap_late_prefix qeLoop_late_prefix
    hq hqn h5 (by omega) (by omega) he hr hrn

/-! ### Pairs `(q, r)` where `n q^e` stays deficient: prefix `n r`, then the exponent of `q` -/

/-- The exponent loop for the number `n q^e` itself (no further prime): stop as soon as the abundant
interval test holds; before that, every `n q^e` must be non-abundant. -/
def eLoop0 (n S c g q : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | e, k + 1 => (stepOK n S c g q && abOK n S c q e) ||
      (decide (ppSum n q S e ≤ n * q ^ e) && eLoop0 n S c g q (e + 1) k)

theorem not_weird_of_eLoop0 {n S c g q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n) :
    ∀ k e₀, eLoop0 n S c g q e₀ k = true → ∀ e, e₀ ≤ e → ¬ (n * q ^ e).Weird
  | 0, _, hl, _, _ => by simp [eLoop0] at hl
  | k + 1, e₀, hl, e, he => by
    simp only [eLoop0, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq] at hl
    rcases hl with ⟨hs, hab⟩ | ⟨hdef, hrest⟩
    · simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hs
      have hab' := abOK_of_le hq.one_le hab e he
      simp only [abOK, Bool.and_eq_true, decide_eq_true_eq] at hab'
      have hpp := pseudoperfect_mul_prime_pow_of_intervalGap hn hg h hq hqn hs.1 hs.2 e hab'.1 hab'.2
      exact fun hw => hw.2 hpp
    · rcases Nat.eq_or_lt_of_le he with rfl | hlt
      · rintro ⟨hab, -⟩
        have hsum := ppSum_eq hn hq hqn h.1 e₀
        have : n * q ^ e₀ < ppSum n q S e₀ := by rw [← hsum]; exact hab
        omega
      · exact not_weird_of_eLoop0 hn hg h hq hqn k (e₀ + 1) hrest e (by omega)

/-- The limit condition is monotone in `r`. -/
theorem limit_mono {A B R r : ℕ} (h : A * (R + 1) ≤ B * R) (hr : R ≤ r) : A * (r + 1) ≤ B * r := by
  obtain ⟨t, rfl⟩ : ∃ t, r = R + t := ⟨r - R, by omega⟩
  have hAB : A ≤ B := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith [Nat.mul_le_mul_right t hAB]

theorem not_dvd_mul_pow {n q r e : ℕ} (hq : q.Prime) (hr : r.Prime) (hrn : ¬ r ∣ n) (hrq : r ≠ q) :
    ¬ r ∣ n * q ^ e := by
  intro hd
  rcases (Nat.Prime.dvd_mul hr).1 hd with h | h
  · exact hrn h
  · exact hrq ((Nat.prime_dvd_prime_iff_eq hr hq).1 (hr.dvd_of_dvd_pow h))

/-- The loop over the last prime `r` (odd, from `r₀`) for a fixed `q`: stop as soon as the limit condition
holds (then it holds for every larger `r`); otherwise skip composites and divisors of `n`, or certify
`IntervalGap` for `n r` and run `eLoop0` on the exponent of `q`. -/
def rLoop (P n S c g K q : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | r, k + 1 => decide ((S + n) * q * (r + 1) ≤ 2 * n * (q - 1) * r) ||
      ((skipB r P || n % r == 0 ||
        (stepOK n S c g r && eLoop0 (n * r) (S + (n + r * S)) c g q 1 K)) && rLoop P n S c g K q (r + 2) k)

theorem not_weird_of_rLoop {P n S c g K q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n) :
    ∀ k r₀, rLoop P n S c g K q r₀ k = true → ∀ r, r.Prime → ¬ r ∣ n → r ≠ q → r₀ ≤ r →
      r % 2 = r₀ % 2 → ∀ e, 1 ≤ e → ¬ (n * q ^ e * r).Weird
  | 0, _, hl, _, _, _, _, _, _, _, _ => by simp [rLoop] at hl
  | k + 1, r₀, hl, r, hr, hrn, hrq, h1, h2, e, he => by
    simp only [rLoop, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hl
    have hrn' := not_dvd_mul_pow (e := e) hq hr hrn hrq
    rcases hl with hlim | ⟨hhead, hrest⟩
    · have hlim' : (S + n) * q * (r + 1) ≤ 2 * n * (q - 1) * r := limit_mono hlim h1
      exact fun hw => not_abundant_limit hn h.1 hq hqn hr hrn' hlim' hw.1
    · rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
      · rcases hhead with (hs | hd) | ⟨hst, hloop⟩
        · rw [prime_imp_not_skipB hr] at hs; exact absurd hs (by decide)
        · exact absurd (Nat.dvd_of_mod_eq_zero hd) hrn
        · simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hst
          have hG := intervalGap_mul_prime_pow hn hg h hr hrn hst.1 hst.2 1
          rw [pow_one] at hG
          have hS1 : ppSum n r₀ S 1 = S + (n + r₀ * S) := by simp [ppSum]
          rw [hS1] at hG
          have hqnr : ¬ q ∣ n * r₀ := by
            intro hd
            rcases (Nat.Prime.dvd_mul hq).1 hd with h' | h'
            · exact hqn h'
            · exact hrq ((Nat.prime_dvd_prime_iff_eq hq hr).1 h').symm
          have := not_weird_of_eLoop0 (Nat.mul_pos hn hr.pos) hg hG hq hqnr K 1 hloop e he
          rwa [show n * r₀ * q ^ e = n * q ^ e * r₀ by ring] at this
      · exact not_weird_of_rLoop hn hg h hq hqn k (r₀ + 2) hrest r hr hrn hrq (by omega) (by omega) e he

/-- The loop over odd `q` (from `q₀`, `k` values) with `rLoop` from `r = q + 2` (fuel `Kr`). -/
def pqLoop (P n S c g K Kr : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | q, k + 1 => (skipB q P || n % q == 0 || rLoop P n S c g K q (q + 2) Kr) && pqLoop P n S c g K Kr (q + 2) k

theorem rLoop_of_pqLoop {P n S c g K Kr : ℕ} :
    ∀ (k q₀ : ℕ), pqLoop P n S c g K Kr q₀ k = true → ∀ q, q.Prime → ¬ q ∣ n → q₀ ≤ q →
      q < q₀ + 2 * k → q % 2 = q₀ % 2 → rLoop P n S c g K q (q + 2) Kr = true
  | 0, q₀, _, q, _, _, h1, h2, _ => by omega
  | k + 1, q₀, hl, q, hq, hqn, h1, h2, h3 => by
    simp only [pqLoop, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    obtain ⟨hhead, htail⟩ := hl
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases hhead with (hs | hd) | hleaf
      · rw [prime_imp_not_skipB hq] at hs; exact absurd hs (by decide)
      · exact absurd (Nat.dvd_of_mod_eq_zero hd) hqn
      · exact hleaf
    · exact rLoop_of_pqLoop k (q₀ + 2) htail q hq hqn (by omega) (by omega) (by omega)

set_option maxRecDepth 100000 in
/-- The 17 odd `q` with `37 ≤ q < 71` (`35` is composite; `skipB` does not skip it and it would need more fuel): for each, `r` from `q + 2` until the limit condition holds. -/
theorem pqLoop_late_prefix :
    pqLoop P1000 (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) 256030928920159929 2295 5 10 200 37 17 = true := by
  decide +kernel

/-- **Instance: a whole two-prime family with a free exponent.** Let `n = 3^3·11·13^10·17^2·23`. For all
primes `q < r` with `q` odd and `q, r ∤ n`, and every exponent `e ≥ 1`, `n q^e r` is not weird. Three
ranges: `q < 35` by `qeLoop` (abundant from `e = 1` on), `35 ≤ q < 71` by `pqLoop` (prefix `n r`, then the
exponent of `q`; large `r` by the limit condition), `q ≥ 71` by `not_weird_tail`. No primality is proved. -/
theorem not_weird_late_prefix_mul_pow_mul_all {q e r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : ¬ q ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) (he : 1 ≤ e) (hqr : q < r) (hr : r.Prime)
    (hrn : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q ^ e * r).Weird := by
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have h3 : q ≠ 3 := by rintro rfl; exact hqn (by norm_num)
  have h5 : 5 ≤ q := by have := hq.two_le; omega
  have hrq : r ≠ q := by omega
  have hrn' := not_dvd_mul_pow (e := e) hq hr hrn hrq
  rcases Nat.lt_or_ge q 35 with hlt | hge
  · exact not_weird_late_prefix_mul_pow_mul hq hq2 hlt hqn he hr hrn'
  rcases Nat.lt_or_ge q 71 with hlt' | hge'
  · have h37 : 37 ≤ q := by
      have : q ≠ 35 := by rintro rfl; norm_num at hq
      omega
    have hrodd : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by omega)
    exact not_weird_of_rLoop (by norm_num) (by norm_num) intervalGap_late_prefix hq hqn 200 (q + 2)
      (rLoop_of_pqLoop 17 37 pqLoop_late_prefix q hq hqn h37 (by omega) (by omega))
      r hr hrn hrq (by omega) (by omega) e he
  · exact not_weird_tail (Q := 71) (by norm_num) intervalGap_late_prefix.1 hq hqn hr hrn'
      (by norm_num) hge' (by omega) (by norm_num)

end ErdosResearch.SubsetSumExpLoop
