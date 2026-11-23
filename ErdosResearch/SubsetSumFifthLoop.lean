module

public import ErdosResearch.SubsetSumUniform
public import ErdosResearch.SubsetSumLastOK
public import ErdosResearch.SubsetSumLate
public import ErdosResearch.PrimeSkip
public import ErdosResearch.OddWeirdThree

@[expose] public section

/-!
# First layer of a reflective sub-tree checker: one loop over the next prime, no primality proofs

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 68).

Session 67 showed that a reflective checker can avoid primality certificates: it runs over EVERY odd `q`
and skips `q` only when `skipB q P` proves it composite (`ErdosResearch.PrimeSkip`). This file is the
first layer of the planned `subtreeOK3`. Given ONE certificate `IntervalGap n S c g` for a prefix `n`, the
Boolean `qLoop P n S c g e q₀ k` runs over `q = q₀, q₀ + 2, …` (`k` values) and decides, for each one, the
leaf `n q^e`:

* abundant leaf: the step conditions and `n q^e ∈ [c, ∑ D(n q^e) − c]`, so `n q^e` is pseudoperfect;
* deficient leaf: the step conditions and `lastOK` for `n q^e`, which covers every last prime `r` at once.

`not_weird_of_qLoop`: for every PRIME `q` in the range with `q ∤ n` and every prime `r ∤ n q^e`,
`n q^e r` is not weird. The checker itself never proves that anything is prime.

`not_weird_tail`: the region bound for the rest. If `σ(n)(Q + 1) ≤ 2 n (Q − 1)`, no `n q^e r` with primes
`q, r ≥ Q` is abundant, for every `e`. Instance `not_weird_late_prefix_mul_mul`: loop (`q < 71`) plus tail
gives a whole two-prime family. Still open: the loop over the exponent `e`, and the levels above (see the notes).

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumFifthLoop

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumUniform ErdosResearch.SubsetSumLastOK
  ErdosResearch.PrimeSkip

/-- The leaf test for the next prime `q` with exponent `e`. -/
def leafOK (n S c g e q : ℕ) : Bool :=
  decide (q * g + 2 * c ≤ S + 1) && decide (n + 2 * c ≤ (q + 1) * S + 1) &&
    ((decide (c ≤ n * q ^ e) && decide (n * q ^ e + c ≤ ppSum n q S e)) ||
      lastOK (n * q ^ e) (ppSum n q S e) c g
        ((n * q ^ e + ppSum n q S e) / (n * q ^ e - ppSum n q S e) + 1))

/-- One leaf: under `IntervalGap n S c g`, `leafOK` rules out every weird `n q^e r`. -/
theorem not_weird_of_leafOK {n S c g e q r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hq : q.Prime) (hqn : ¬ q ∣ n) (hok : leafOK n S c g e q = true)
    (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e) : ¬ (n * q ^ e * r).Weird := by
  simp only [leafOK, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq] at hok
  obtain ⟨⟨h1, h2⟩, hab | hlast⟩ := hok
  · have hpp := pseudoperfect_mul_prime_pow_of_intervalGap hn hg h hq hqn h1 h2 e hab.1 hab.2
    rintro ⟨-, hnot⟩
    exact hnot (hpp.of_dvd (Dvd.intro r rfl)
      (Nat.mul_pos (Nat.mul_pos hn (pow_pos hq.pos e)) hr.pos))
  · exact not_weird_mul_prime_of_lastOK (Nat.mul_pos hn (pow_pos hq.pos e)) hg
      (intervalGap_mul_prime_pow hn hg h hq hqn h1 h2 e) hlast hr hrn

/-- The loop over odd `q = q₀, q₀ + 2, …` (`k` values). `skipB q P` skips proven composites,
`n % q = 0` skips divisors of the prefix; every other `q` must pass `leafOK`. -/
def qLoop (P n S c g e : ℕ) : ℕ → ℕ → Bool
  | _, 0 => true
  | q, k + 1 => (skipB q P || n % q == 0 || leafOK n S c g e q) && qLoop P n S c g e (q + 2) k

theorem leafOK_of_qLoop {P n S c g e : ℕ} :
    ∀ (k q₀ : ℕ), qLoop P n S c g e q₀ k = true → ∀ q, q.Prime → ¬ q ∣ n → q₀ ≤ q →
      q < q₀ + 2 * k → q % 2 = q₀ % 2 → leafOK n S c g e q = true
  | 0, q₀, _, q, _, _, h1, h2, _ => by omega
  | k + 1, q₀, hl, q, hq, hqn, h1, h2, h3 => by
    simp only [qLoop, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq] at hl
    obtain ⟨hhead, htail⟩ := hl
    rcases Nat.eq_or_lt_of_le h1 with rfl | hlt
    · rcases hhead with (hs | hd) | hleaf
      · rw [prime_imp_not_skipB hq] at hs; exact absurd hs (by decide)
      · exact absurd (Nat.dvd_of_mod_eq_zero hd) hqn
      · exact hleaf
    · exact leafOK_of_qLoop k (q₀ + 2) htail q hq hqn (by omega) (by omega) (by omega)

/-- **Soundness of the loop.** For every prime `q` in the range of the loop with `q ∤ n`, and every prime
`r ∤ n q^e`, `n q^e r` is not weird. -/
theorem not_weird_of_qLoop {P n S c g e q₀ k q r : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hloop : qLoop P n S c g e q₀ k = true) (hq : q.Prime) (hqn : ¬ q ∣ n)
    (h1 : q₀ ≤ q) (h2 : q < q₀ + 2 * k) (h3 : q % 2 = q₀ % 2) (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e) :
    ¬ (n * q ^ e * r).Weird :=
  not_weird_of_leafOK hn hg h hq hqn (leafOK_of_qLoop k q₀ hloop q hq hqn h1 h2 h3) hr hrn

/-- Closed form of `ppSum`: `σ(n q^e) (q − 1) + σ(n) = σ(n) q^(e+1)`, without subtraction. -/
theorem ppSum_exact' (n q S : ℕ) : ∀ e,
    (ppSum n q S e + n * q ^ e) * q + (S + n) = (S + n) * q ^ (e + 1) + (ppSum n q S e + n * q ^ e)
  | 0 => by simp [ppSum]
  | e + 1 => by
    have ih := ppSum_exact' n q S e
    have h2 : ((ppSum n q S e + n * q ^ e) * q + (S + n)) * q =
        ((S + n) * q ^ (e + 1) + (ppSum n q S e + n * q ^ e)) * q := by rw [ih]
    simp only [ppSum]
    ring_nf at h2 ⊢
    linarith

/-- The arithmetic of the tail (`q = Q + 2 + a`, `r = Q + 2 + b`). -/
theorem tail_arith {σ A T x Q a b : ℕ} (hσ0 : 0 < σ)
    (hx : (T + A) * (Q + 2 + a) + σ = σ * (Q + 2 + a) * x + (T + A))
    (hσ : σ * (Q + 3) * x ≤ 2 * A * (Q + 1)) :
    T + (A + (Q + 2 + b) * T) ≤ A * (Q + 2 + b) := by
  -- σ' (q - 1) < σ q x, with q - 1 = Q + 1 + a
  have s0 : (T + A) * (Q + 1 + a) < σ * (Q + 2 + a) * x := by nlinarith
  have s1 : (T + A) * (Q + 1 + a) * (Q + 3) < 2 * A * (Q + 1) * (Q + 2 + a) := by
    have := Nat.mul_lt_mul_of_pos_right s0 (show 0 < Q + 3 by omega)
    have h' : σ * (Q + 2 + a) * x * (Q + 3) ≤ 2 * A * (Q + 1) * (Q + 2 + a) := by
      have := Nat.mul_le_mul_right (Q + 2 + a) hσ
      nlinarith
    omega
  have s2 : (T + A) * (Q + 3) < 2 * A * (Q + 2) := by
    by_contra hc
    push Not at hc
    have := Nat.mul_le_mul_right (Q + 1 + a) hc
    nlinarith
  have s3 : (T + A) * (Q + 3 + b) ≤ 2 * A * (Q + 2 + b) := by
    by_contra hc
    push Not at hc
    nlinarith
  nlinarith

/-- **Tail of the loop (region bound).** If `σ(n)(Q + 1) ≤ 2 n (Q − 1)` (with `σ(n) = S + n`), then no
`n q^e r` with primes `q, r ≥ Q` (`q ∤ n`, `r ∤ n q^e`) is even abundant, for every exponent `e`.
With `qLoop` for `q < Q` this covers every `q` (the search has `r > q`). -/
theorem not_weird_tail {n S Q q e r : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e) (hQ : 2 ≤ Q)
    (hQq : Q ≤ q) (hQr : Q ≤ r) (hσ : (S + n) * (Q + 1) ≤ 2 * n * (Q - 1)) :
    ¬ (n * q ^ e * r).Weird := by
  rintro ⟨hab, -⟩
  have hN : 0 < n * q ^ e := Nat.mul_pos hn (pow_pos hq.pos e)
  have hsum := ppSum_eq hN hr hrn (ppSum_eq hn hq hqn hS e) 1
  rw [pow_one] at hsum
  have hab' : n * q ^ e * r < ppSum (n * q ^ e) r (ppSum n q S e) 1 := by
    rw [← hsum]; exact hab
  simp only [ppSum] at hab'
  obtain ⟨Q', rfl⟩ : ∃ Q', Q = Q' + 2 := ⟨Q - 2, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, q = Q' + 2 + a := ⟨q - (Q' + 2), by omega⟩
  obtain ⟨b, rfl⟩ : ∃ b, r = Q' + 2 + b := ⟨r - (Q' + 2), by omega⟩
  have hx := ppSum_exact' n (Q' + 2 + a) S e
  rw [pow_succ] at hx
  have hσ' : (S + n) * (Q' + 3) ≤ 2 * n * (Q' + 1) := by
    have : Q' + 2 - 1 = Q' + 1 := by omega
    rw [this] at hσ; simpa [add_assoc] using hσ
  have key := tail_arith (σ := S + n) (A := n * (Q' + 2 + a) ^ e) (T := ppSum n (Q' + 2 + a) S e)
    (x := (Q' + 2 + a) ^ e) (Q := Q') (a := a) (b := b) (by omega)
    (by rw [hx]; ring) (by
      have := Nat.mul_le_mul_right ((Q' + 2 + a) ^ e) hσ'
      calc (S + n) * (Q' + 3) * (Q' + 2 + a) ^ e ≤ 2 * n * (Q' + 1) * (Q' + 2 + a) ^ e := this
        _ = 2 * (n * (Q' + 2 + a) ^ e) * (Q' + 1) := by ring)
  omega

/-! ### Instance (timing): the prefix certified in `SubsetSumLate` -/

open ErdosResearch.SubsetSumLate ErdosResearch.SubsetSumGreedy in
/-- `IntervalGap` for `n = 3^3·11·13^10·17^2·23` (`c = 2295`, `g = 5`): base `6831` plus the steps `13^10`,
`17^2` (the first half of `not_weird_late_example`). -/
theorem intervalGap_late_prefix :
    IntervalGap (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) 256030928920159929 2295 5 := by
  obtain ⟨hl, hnd, hI, hG, hst, hend, -⟩ := cert_late
  have h0 := intervalGap_of_bits l6831 hl hnd hI hG
  have h1 := intervalGap_of_stepsOK (by norm_num) [(13, 10), (17, 2)] _ _
    (by norm_num) (by simp; norm_num) hst h0
  rw [hend] at h1
  have hn : prodOf fsM * 11 ^ 1 = 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 := by decide +kernel
  rwa [hn] at h1

/-- The product of the odd primes `≤ 1000` (1379 bits); `skipB q P1000` skips the composites below `1009²`. -/
def P1000 : ℕ :=
  9795170322499541715631254099103190523061986195294684111941302664484333158189935330925975824394741160798114779557718009574594764862607633364146141495426324511681365696202008969571005479130696817479735741878598360836121705033559258113830566567596244424494957446078594154339948437568719759669451984047452774875193203553016918293330341769600505817958950019952247532601649874771492996567334907402659237040290603945562955

/-- The 33 odd `q` with `5 ≤ q < 71` in one `decide +kernel` (~1 s; 500 values, up to `1005`, took ~9 s). -/
theorem qLoop_late_prefix :
    qLoop P1000 (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) 256030928920159929 2295 5 1 5 33 = true := by
  decide +kernel

/-- **Instance: a whole two-prime family.** Let `n = 3^3·11·13^10·17^2·23`. For all primes `q < r` with `q`
odd, `q ∤ n` and `r ∤ n q`, `n q r` is not weird. The loop handles `q < 71` and `not_weird_tail` (with `Q = 71`)
handles the rest. No primality is proved anywhere: composites are skipped by `skipB`. -/
theorem not_weird_late_prefix_mul_mul {q r : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqn : ¬ q ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) (hqr : q < r) (hr : r.Prime)
    (hrn : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q * r).Weird := by
  have hodd : q % 2 = 1 := hq.eq_two_or_odd.resolve_left hq2
  have h3 : q ≠ 3 := by rintro rfl; exact hqn (by norm_num)
  have h5 : 5 ≤ q := by have := hq.two_le; omega
  have hrn' : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * q ^ 1 := by rwa [pow_one]
  rcases Nat.lt_or_ge q 71 with hlt | hge
  · have := not_weird_of_qLoop (e := 1) (by norm_num) (by norm_num) intervalGap_late_prefix
      qLoop_late_prefix hq hqn h5 (by omega) (by omega) hr hrn'
    rwa [pow_one] at this
  · have := not_weird_tail (Q := 71) (e := 1) (by norm_num) intervalGap_late_prefix.1 hq hqn hr hrn'
      (by norm_num) hge (by omega) (by norm_num)
    rwa [pow_one] at this

end ErdosResearch.SubsetSumFifthLoop
