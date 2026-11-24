module

public import ErdosResearch.SubsetSumExpLoop

@[expose] public section

/-!
# One level up: a Boolean block for the last two primes, and a loop over the prime before them

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 73).

`SubsetSumExpLoop` decided the family `n q^e r` (two more primes, free exponent of `q`) for ONE prefix,
with three hand-picked ranges of `q`. Here:

* `qBlock`: one loop over odd `q`; for each `q` (not skipped by `skipB`, not dividing `n`) it accepts
  EITHER `eLoop` (abundant from some exponent on) OR `rLoop` (prefix `n r`, then the exponent of `q`).
  This removes the hand-picked split of session 69 (e.g. the composite `35`).
* `blockOK`: `qBlock` up to `Q = q₀ + 2k` plus the region bound `not_weird_tail` for `q ≥ Q`.
  `not_weird_of_blockOK`: for all primes `q < r` (`q` odd, `q ≥ q₀`, `q, r ∤ n`) and every `e ≥ 1`,
  `n q^e r` is not weird.
* `fLoop`: the exponent `f` of the prime `p` before them, adaptive (stop when `n p^f` is abundant with an
  interval, which is monotone in `f`); before that, `blockOK` for the prefix `n p^f`.
* `pLoop`: the loop over odd `p`, and `not_weird_ptail` for `p ≥ Q` (three primes `≥ Q`).
* `subOK` / `not_weird_of_subOK`: **for all primes `p < q < r` (odd, `p ≥ p₀`, none dividing `n`) and all
  `f, e ≥ 1`, `n p^f q^e r` is not weird.** This is the `subtreeOK3` of the notes, with the last prime `r`
  to the first power (stars, `r^h` with `h ≥ 2`, are NOT covered).

No primality is proved anywhere (composites are skipped by `skipB`).
Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumBlock

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumUniform ErdosResearch.SubsetSumLastOK
  ErdosResearch.PrimeSkip ErdosResearch.SubsetSumFifthLoop ErdosResearch.SubsetSumExpLoop

/-! ### The block for the last two primes -/

/-- The loop over odd `q = q₀, q₀ + 2, …` (`k` values): `eLoop` or `rLoop` for each one. -/
def qBlock (P n S c g K Kr : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | q, k + 1 => (skipB q P || n % q == 0 || eLoop n S c g q 1 K || rLoop P n S c g K q (q + 2) Kr) &&
      qBlock P n S c g K Kr (q + 2) k

theorem not_weird_of_qBlock {P n S c g K Kr : ℕ} (hn : 0 < n) (hg : 1 ≤ g) (h : IntervalGap n S c g) :
    ∀ k q₀, qBlock P n S c g K Kr q₀ k = true → ∀ q, q.Prime → ¬ q ∣ n → q₀ ≤ q → q < q₀ + 2 * k →
      q % 2 = q₀ % 2 → q % 2 = 1 → ∀ e, 1 ≤ e → ∀ r, r.Prime → q < r → ¬ r ∣ n →
      ¬ (n * q ^ e * r).Weird
  | 0, q₀, _, q, _, _, h1, h2, _, _, _, _, _, _, _, _ => by omega
  | k + 1, q₀, hl, q, hq, hqn, h1, h2, h3, hodd, e, he, r, hr, hqr, hrn => by
    simp only [qBlock, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    obtain ⟨hhead, htail⟩ := hl
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · have hrq : r ≠ q₀ := by omega
      rcases hhead with ((hs | hd) | hel) | hrl
      · rw [prime_imp_not_skipB hq] at hs; exact absurd hs (by decide)
      · exact absurd (Nat.dvd_of_mod_eq_zero hd) hqn
      · exact not_weird_of_eLoop hn hg h hq hqn hr K 1 hel e he (not_dvd_mul_pow hq hr hrn hrq)
      · have hr2 : r % 2 = 1 := hr.eq_two_or_odd.resolve_left (by have := hq.two_le; omega)
        exact not_weird_of_rLoop hn hg h hq hqn Kr (q₀ + 2) hrl r hr hrn hrq (by omega) (by omega) e he
    · exact not_weird_of_qBlock hn hg h k (q₀ + 2) htail q hq hqn (by omega) (by omega) (by omega) hodd
        e he r hr hqr hrn

/-- `qBlock` for `q < Q = q₀ + 2k`, plus the region bound of `not_weird_tail` at `Q`. -/
def blockOK (P n S c g K Kr q₀ k : ℕ) : Bool :=
  decide (q₀ % 2 = 1) && decide (2 ≤ q₀ + 2 * k) &&
    decide ((S + n) * (q₀ + 2 * k + 1) ≤ 2 * n * (q₀ + 2 * k - 1)) && qBlock P n S c g K Kr q₀ k

/-- **The block.** Under `IntervalGap n S c g` and `blockOK`, for all primes `q < r` with `q` odd, `q ≥ q₀`,
`q, r ∤ n`, and every `e ≥ 1`, `n q^e r` is not weird. -/
theorem not_weird_of_blockOK {P n S c g K Kr q₀ k q e r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hb : blockOK P n S c g K Kr q₀ k = true) (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : ¬ q ∣ n) (hq0 : q₀ ≤ q) (he : 1 ≤ e) (hr : r.Prime) (hqr : q < r) (hrn : ¬ r ∣ n) :
    ¬ (n * q ^ e * r).Weird := by
  simp only [blockOK, Bool.and_eq_true, decide_eq_true_eq] at hb
  obtain ⟨⟨⟨hq0odd, hQ⟩, hσ⟩, hl⟩ := hb
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  rcases Nat.lt_or_ge q (q₀ + 2 * k) with hlt | hge
  · exact not_weird_of_qBlock hn hg h k q₀ hl q hq hqn hq0 hlt (by omega) hodd e he r hr hqr hrn
  · exact not_weird_tail (Q := q₀ + 2 * k) hn h.1 hq hqn hr (not_dvd_mul_pow hq hr hrn (by omega))
      hQ hge (by omega) hσ

/-! ### The prime before them: its exponent, then the loop over it -/

/-- The adaptive loop over the exponent `f` of `p`: stop when `n p^f` is abundant with an interval (then
every larger `f` is too); before that, `blockOK` for the prefix `n p^f` with `q` from `p + 2` (`Kq` values). -/
def fLoop (P n S c g K Kr Kq p : ℕ) : ℕ → ℕ → Bool
  | _, 0 => false
  | f, k + 1 => stepOK n S c g p &&
      (abOK n S c p f || (blockOK P (n * p ^ f) (ppSum n p S f) c g K Kr (p + 2) Kq &&
        fLoop P n S c g K Kr Kq p (f + 1) k))

theorem not_dvd_mul_pow' {n p q f : ℕ} (hp : p.Prime) (hq : q.Prime) (hqn : ¬ q ∣ n) (hpq : p < q) :
    ¬ q ∣ n * p ^ f := not_dvd_mul_pow hp hq hqn (by omega)

theorem not_weird_of_fLoop {P n S c g K Kr Kq p : ℕ} (hn : 0 < n) (hg : 1 ≤ g) (h : IntervalGap n S c g)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) :
    ∀ k f₀, fLoop P n S c g K Kr Kq p f₀ k = true → ∀ f, f₀ ≤ f → ∀ q, q.Prime → p < q → ¬ q ∣ n →
      ∀ e, 1 ≤ e → ∀ r, r.Prime → q < r → ¬ r ∣ n → ¬ (n * p ^ f * q ^ e * r).Weird
  | 0, _, hl, _, _, _, _, _, _, _, _, _, _, _, _ => by simp [fLoop] at hl
  | k + 1, f₀, hl, f, hf, q, hq, hpq, hqn, e, he, r, hr, hqr, hrn => by
    simp only [fLoop, Bool.and_eq_true, Bool.or_eq_true] at hl
    obtain ⟨hs, hab | ⟨hb, hrest⟩⟩ := hl
    · simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hs
      have hab' := abOK_of_le hp.one_le hab f hf
      simp only [abOK, Bool.and_eq_true, decide_eq_true_eq] at hab'
      have hpp := pseudoperfect_mul_prime_pow_of_intervalGap hn hg h hp hpn hs.1 hs.2 f hab'.1 hab'.2
      rintro ⟨-, hnot⟩
      refine hnot (hpp.of_dvd ⟨q ^ e * r, by ring⟩ ?_)
      exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos hn (pow_pos hp.pos f)) (pow_pos hq.pos e)) hr.pos
    · rcases Nat.eq_or_lt_of_le hf with rfl | hlt
      · simp only [stepOK, Bool.and_eq_true, decide_eq_true_eq] at hs
        have hG := intervalGap_mul_prime_pow hn hg h hp hpn hs.1 hs.2 f₀
        have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
        have hqodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left (by have := hp.two_le; omega)
        exact not_weird_of_blockOK (Nat.mul_pos hn (pow_pos hp.pos f₀)) hg hG hb hq
          (by have := hp.two_le; omega) (not_dvd_mul_pow' hp hq hqn hpq) (by omega) he hr hqr
          (not_dvd_mul_pow' hp hr hrn (by omega))
      · exact not_weird_of_fLoop hn hg h hp hp2 hpn k (f₀ + 1) hrest f (by omega) q hq hpq hqn e he r hr
          hqr hrn

/-- The loop over odd `p = p₀, p₀ + 2, …` (`k` values), with `fLoop` from `f = 1` (fuel `Kf`). -/
def pLoop (P n S c g K Kr Kq Kf : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | p, k + 1 => (skipB p P || n % p == 0 || fLoop P n S c g K Kr Kq p 1 Kf) &&
      pLoop P n S c g K Kr Kq Kf (p + 2) k

theorem fLoop_of_pLoop {P n S c g K Kr Kq Kf : ℕ} :
    ∀ (k p₀ : ℕ), pLoop P n S c g K Kr Kq Kf p₀ k = true → ∀ p, p.Prime → ¬ p ∣ n → p₀ ≤ p →
      p < p₀ + 2 * k → p % 2 = p₀ % 2 → fLoop P n S c g K Kr Kq p 1 Kf = true
  | 0, p₀, _, p, _, _, h1, h2, _ => by omega
  | k + 1, p₀, hl, p, hp, hpn, h1, h2, h3 => by
    simp only [pLoop, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    obtain ⟨hhead, htail⟩ := hl
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases hhead with (hs | hd) | hleaf
      · rw [prime_imp_not_skipB hp] at hs; exact absurd hs (by decide)
      · exact absurd (Nat.dvd_of_mod_eq_zero hd) hpn
      · exact hleaf
    · exact fLoop_of_pLoop k (p₀ + 2) htail p hp hpn (by omega) (by omega) (by omega)

/-- The arithmetic of the three-prime tail (`Q = Q' + 2`, `p = Q + a`). -/
theorem ptail_arith {σ T N n x Q' a : ℕ} (hN : N = n * x)
    (hx : (T + N) * (Q' + 1 + a) + σ = σ * x * (Q' + 2 + a))
    (hσ : σ * (Q' + 2) * (Q' + 3) ≤ 2 * n * (Q' + 1) * (Q' + 1)) :
    (T + N) * (Q' + 3) ≤ 2 * N * (Q' + 1) := by
  have h1 : (T + N) * (Q' + 1 + a) ≤ σ * x * (Q' + 2 + a) := by omega
  -- p / (p − 1) ≤ Q / (Q − 1)
  have hpQ : (Q' + 2 + a) * (Q' + 1) ≤ (Q' + 1 + a) * (Q' + 2) := by nlinarith
  have h2 : (T + N) * (Q' + 1 + a) * ((Q' + 3) * (Q' + 2)) ≤
      2 * N * (Q' + 1) * ((Q' + 1 + a) * (Q' + 2)) := by
    calc (T + N) * (Q' + 1 + a) * ((Q' + 3) * (Q' + 2))
        ≤ σ * x * (Q' + 2 + a) * ((Q' + 3) * (Q' + 2)) := Nat.mul_le_mul_right _ h1
      _ = σ * (Q' + 2) * (Q' + 3) * x * (Q' + 2 + a) := by ring
      _ ≤ 2 * n * (Q' + 1) * (Q' + 1) * x * (Q' + 2 + a) := by
          have := Nat.mul_le_mul_right x hσ
          exact Nat.mul_le_mul_right _ this
      _ = 2 * N * (Q' + 1) * ((Q' + 2 + a) * (Q' + 1)) := by rw [hN]; ring
      _ ≤ 2 * N * (Q' + 1) * ((Q' + 1 + a) * (Q' + 2)) := Nat.mul_le_mul_left _ hpQ
  have h3 : (T + N) * (Q' + 3) * ((Q' + 1 + a) * (Q' + 2)) ≤
      2 * N * (Q' + 1) * ((Q' + 1 + a) * (Q' + 2)) := by
    calc (T + N) * (Q' + 3) * ((Q' + 1 + a) * (Q' + 2))
        = (T + N) * (Q' + 1 + a) * ((Q' + 3) * (Q' + 2)) := by ring
      _ ≤ _ := h2
  exact Nat.le_of_mul_le_mul_right h3 (by positivity)

/-- **Three-prime tail (region bound).** If `σ(n) Q (Q + 1) ≤ 2 n (Q − 1)²` (with `σ(n) = S + n`), then
no `n p^f q^e r` with primes `Q ≤ p < q, r` (none dividing `n`) is weird, for all `f, e`. -/
theorem not_weird_ptail {n S Q p f q e r : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q.Prime) (hqn : ¬ q ∣ n) (hr : r.Prime) (hrn : ¬ r ∣ n)
    (hpq : p < q) (hrq : r ≠ q) (hpr : p < r) (hQ : 2 ≤ Q) (hQp : Q ≤ p)
    (hσ : (S + n) * Q * (Q + 1) ≤ 2 * n * (Q - 1) * (Q - 1)) :
    ¬ (n * p ^ f * q ^ e * r).Weird := by
  have hS' := ppSum_eq hn hp hpn hS f
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, p = Q' + 2 + a := ⟨p - (Q' + 2), by omega⟩
  have hx := ppSum_exact' n (Q' + 2 + a) S f
  rw [pow_succ] at hx
  have hσ' : (S + n) * (Q' + 2) * (Q' + 3) ≤ 2 * n * (Q' + 1) * (Q' + 1) := by
    have : Q' + 2 - 1 = Q' + 1 := by omega
    rw [this] at hσ; simpa [add_assoc] using hσ
  have key := ptail_arith (σ := S + n) (T := ppSum n (Q' + 2 + a) S f) (N := n * (Q' + 2 + a) ^ f)
    (n := n) (x := (Q' + 2 + a) ^ f) (Q' := Q') (a := a) rfl (by
      have e1 : (ppSum n (Q' + 2 + a) S f + n * (Q' + 2 + a) ^ f) * (Q' + 2 + a) =
          (ppSum n (Q' + 2 + a) S f + n * (Q' + 2 + a) ^ f) * (Q' + 1 + a) +
            (ppSum n (Q' + 2 + a) S f + n * (Q' + 2 + a) ^ f) := by ring
      have e2 : (S + n) * ((Q' + 2 + a) ^ f * (Q' + 2 + a)) = (S + n) * (Q' + 2 + a) ^ f * (Q' + 2 + a) := by
        ring
      omega) hσ'
  have hN : 0 < n * (Q' + 2 + a) ^ f := Nat.mul_pos hn (pow_pos hp.pos f)
  exact not_weird_tail (Q := Q' + 2) hN hS' hq (not_dvd_mul_pow hp hq hqn (by omega)) hr
    (not_dvd_mul_pow hq hr (not_dvd_mul_pow hp hr hrn (by omega)) hrq) (by omega) (by omega) (by omega)
    (by have : Q' + 2 - 1 = Q' + 1 := by omega
        rw [this]; linarith)

/-- The whole sub-tree check: `pLoop` for `p < Q = p₀ + 2k`, the three-prime tail at `Q`. -/
def subOK (P n S c g K Kr Kq Kf p₀ k : ℕ) : Bool :=
  decide (p₀ % 2 = 1) && decide (2 ≤ p₀ + 2 * k) &&
    decide ((S + n) * (p₀ + 2 * k) * (p₀ + 2 * k + 1) ≤ 2 * n * (p₀ + 2 * k - 1) * (p₀ + 2 * k - 1)) &&
    pLoop P n S c g K Kr Kq Kf p₀ k

/-- **The sub-tree below a prefix.** Under `IntervalGap n S c g` and `subOK`, for all primes `p < q < r` with
`p` odd, `p ≥ p₀`, none dividing `n`, and all exponents `f, e ≥ 1`, `n p^f q^e r` is not weird. -/
theorem not_weird_of_subOK {P n S c g K Kr Kq Kf p₀ k p f q e r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hsub : subOK P n S c g K Kr Kq Kf p₀ k = true) (hp : p.Prime)
    (hp2 : p ≠ 2) (hpn : ¬ p ∣ n) (hp0 : p₀ ≤ p) (hf : 1 ≤ f) (hq : q.Prime) (hpq : p < q)
    (hqn : ¬ q ∣ n) (he : 1 ≤ e) (hr : r.Prime) (hqr : q < r) (hrn : ¬ r ∣ n) :
    ¬ (n * p ^ f * q ^ e * r).Weird := by
  simp only [subOK, Bool.and_eq_true, decide_eq_true_eq] at hsub
  obtain ⟨⟨⟨hp0odd, hQ⟩, hσ⟩, hl⟩ := hsub
  have hpodd : p % 2 = 1 := hp.eq_two_or_odd.resolve_left hp2
  rcases Nat.lt_or_ge p (p₀ + 2 * k) with hlt | hge
  · exact not_weird_of_fLoop hn hg h hp hp2 hpn Kf 1
      (fLoop_of_pLoop k p₀ hl p hp hpn hp0 hlt (by omega)) f hf q hq hpq hqn e he r hr hqr hrn
  · exact not_weird_ptail (Q := p₀ + 2 * k) hn h.1 hp hpn hq hqn hr hrn hpq (by omega) (by omega) hQ hge hσ

/-! ### Instance: session 69's family with one Boolean -/

set_option maxRecDepth 100000 in
/-- `qBlock` from `q = 5` to `71` (33 values) for the late prefix, plus the tail at `71`. -/
theorem blockOK_late_prefix :
    blockOK P1000 (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) 256030928920159929 2295 5 40 2000 5 33 = true := by
  decide +kernel

/-- **Instance.** Session 69's theorem `not_weird_late_prefix_mul_pow_mul_all` again, now from ONE Boolean
(`blockOK`) instead of three hand-picked ranges. -/
theorem not_weird_late_prefix_block {q e r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : ¬ q ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) (he : 1 ≤ e) (hqr : q < r) (hr : r.Prime)
    (hrn : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q ^ e * r).Weird := by
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have h3 : q ≠ 3 := by rintro rfl; exact hqn (by norm_num)
  have h5 : 5 ≤ q := by have := hq.two_le; omega
  exact not_weird_of_blockOK (by norm_num) (by norm_num) intervalGap_late_prefix blockOK_late_prefix
    hq hq2 hqn h5 he hr hqr hrn

end ErdosResearch.SubsetSumBlock
