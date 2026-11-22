module

public import ErdosResearch.SubsetSumPrimePow

@[expose] public section

/-!
# A decidable certificate for the base of the prime(-power) step

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 55).

The prime step (`SubsetSumPrimeStep.lean`) and the prime-power step (`SubsetSumPrimePow.lean`) need,
for the base `n`, an interval `[c, s − c]` inside the subset sums of `D n = properDivisors n` and a
bound `g` on their gaps. Here these two hypotheses are produced by computation:

* `ssBits l` is the bitset of the subset sums of a list `l` (bit `x` set iff `x` is a subset sum);
  `mem_subsetSums_of_testBit` is its soundness for a duplicate-free list;
* `intervalOK` and `gapOK` are Boolean checks of the interval and of the gap bound;
* `pseudoperfect_mul_prime_pow_of_cert` packages everything: one `decide +kernel` per base `n`
  settles the whole family `n p^e` for all primes `p` (and exponents `e`) meeting the linear conditions.

When the excess `∑ D(n p^e) − n p^e` is below `c`, the excess test `pseudoperfect_of_excess_mem` (its bit
in the base bitset) replaces the interval (`pseudoperfect_mul_prime_pow_of_cert'`), and
`not_weird_mul_prime_of_cert` turns a base certificate into "no `n q` is weird" for a whole family of
last primes `q`.

Examples: `pseudoperfect_315_mul_prime` (`315 p` for primes `11 ≤ p ≤ 103`), `not_weird_525_mul_prime`
and `not_weird_495_mul_prime` (no `525 q` / `495 q` with `q` prime is weird). Elementary; not a new result.
-/

namespace ErdosResearch.SubsetSumCert

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumPrimeStep
  ErdosResearch.SubsetSumPrimePow

/-- Bitset of the subset sums of a list. -/
def ssBits : List ℕ → ℕ
  | [] => 1
  | d :: l => ssBits l ||| (ssBits l <<< d)

theorem mem_subsetSums_of_testBit :
    ∀ (l : List ℕ), l.Nodup → ∀ x, (ssBits l).testBit x = true → x ∈ subsetSums l.toFinset
  | [], _, x, h => by
      have hx : x = 0 := Nat.testBit_one_eq_true_iff_self_eq_zero.1 h
      subst hx
      exact zero_mem_subsetSums _
  | d :: l, hnd, x, h => by
      rw [List.nodup_cons] at hnd
      simp only [ssBits, Nat.testBit_or, Nat.testBit_shiftLeft, Bool.or_eq_true,
        Bool.and_eq_true, decide_eq_true_eq] at h
      rw [List.toFinset_cons]
      rcases h with h | ⟨hdx, h⟩
      · exact subsetSums_mono (subset_insert _ _) (mem_subsetSums_of_testBit l hnd.2 x h)
      · obtain ⟨t, ht, hsum⟩ := mem_subsetSums_of_testBit l hnd.2 _ h
        have hdt : d ∉ t := fun hd => hnd.1 (List.mem_toFinset.1 (ht hd))
        refine ⟨insert d t, insert_subset_insert _ ht, ?_⟩
        rw [sum_insert hdt, hsum]
        omega

/-- Every `x` with `c ≤ x` and `x + c ≤ s` has its bit set in `b`. -/
def intervalOK (b c s : ℕ) : Bool :=
  (List.range (s + 1)).all fun x => !(decide (c ≤ x) && decide (x + c ≤ s)) || b.testBit x

/-- After every `x < s` some `z ∈ (x, x + g]`, `z ≤ s`, has its bit set in `b`. -/
def gapOK (b g s : ℕ) : Bool :=
  (List.range s).all fun x => (List.range g).any fun i => decide (x + 1 + i ≤ s) && b.testBit (x + 1 + i)

theorem testBit_of_intervalOK {b c s : ℕ} (h : intervalOK b c s = true) :
    ∀ x, c ≤ x → x + c ≤ s → b.testBit x = true := by
  intro x h1 h2
  simp only [intervalOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_false_iff, decide_eq_false_iff_not] at h
  rcases h x (by omega) with (h | h) | h
  · omega
  · omega
  · exact h

theorem exists_testBit_of_gapOK {b g s : ℕ} (h : gapOK b g s = true) :
    ∀ x < s, ∃ z, b.testBit z = true ∧ x < z ∧ z ≤ x + g ∧ z ≤ s := by
  intro x hx
  simp only [gapOK, List.all_eq_true, List.mem_range, List.any_eq_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  obtain ⟨i, hi, hs, hb⟩ := h x hx
  exact ⟨x + 1 + i, hb, by omega, by omega, hs⟩

/-- **Certified family step.** A duplicate-free list `l` of the proper divisors of `n` whose
subset-sum bitset passes `intervalOK` (with `c`) and `gapOK` (with `g`) gives the hypotheses of the
prime-power step, so `n p^e` is pseudoperfect under the linear conditions. -/
theorem pseudoperfect_mul_prime_pow_of_cert {n p c g e : ℕ} (l : List ℕ)
    (hl : l.toFinset = n.properDivisors) (hnd : l.Nodup)
    (hI : intervalOK (ssBits l) c l.sum = true) (hG : gapOK (ssBits l) g l.sum = true)
    (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ n) (hg : 1 ≤ g)
    (hpg : p * g + 2 * c ≤ l.sum + 1) (hnc : n + 2 * c ≤ (p + 1) * l.sum + 1)
    (hc : c ≤ n * p ^ e) (hab : n * p ^ e + c ≤ ∑ y ∈ (n * p ^ e).properDivisors, y) :
    (n * p ^ e).Pseudoperfect := by
  have hsum : ∑ y ∈ n.properDivisors, y = l.sum := by
    rw [← hl, List.sum_toFinset _ hnd, List.map_id']
  have hmem : ∀ x, (ssBits l).testBit x = true → x ∈ subsetSums n.properDivisors := by
    intro x hx
    rw [← hl]
    exact mem_subsetSums_of_testBit l hnd x hx
  refine pseudoperfect_mul_prime_pow_of_interval hn hp hpn hg ?_ ?_ (by rw [hsum]; exact hpg)
    (by rw [hsum]; exact hnc) e hc hab
  · intro x h1 h2
    rw [hsum] at h2
    exact hmem x (testBit_of_intervalOK hI x h1 h2)
  · intro x hx
    rw [hsum] at hx ⊢
    obtain ⟨z, hz, h1, h2, h3⟩ := exists_testBit_of_gapOK hG x hx
    exact ⟨z, hmem z hz, h1, h2, h3⟩

/-- The divisor list of `315 = 3^2·5·7` used in the example. -/
def l315 : List ℕ := [1, 3, 5, 7, 9, 15, 21, 35, 45, 63, 105]

theorem cert_315 :
    l315.toFinset = (315 : ℕ).properDivisors ∧ l315.Nodup ∧ l315.sum = 309 ∧
      intervalOK (ssBits l315) 3 l315.sum = true ∧ gapOK (ssBits l315) 2 l315.sum = true := by
  decide +kernel

/-- Example family: `315 p` is pseudoperfect for every prime `11 ≤ p ≤ 103`
(one kernel check for the base, then the linear conditions `2p + 6 ≤ 310` and `6p ≤ 621`). -/
theorem pseudoperfect_315_mul_prime {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (h103 : p ≤ 103) :
    (315 * p).Pseudoperfect := by
  obtain ⟨hl, hnd, hs, hI, hG⟩ := cert_315
  have hpn : ¬ p ∣ 315 := by
    intro h
    have h3 : (3 : ℕ).Prime := by norm_num
    have h5 : (5 : ℕ).Prime := by norm_num
    have h7 : (7 : ℕ).Prime := by norm_num
    have : (315 : ℕ) = 3 ^ 2 * 5 * 7 := by norm_num
    rw [this] at h
    rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · have := (Nat.prime_dvd_prime_iff_eq hp h3).1 (hp.dvd_of_dvd_pow h); omega
      · have := (Nat.prime_dvd_prime_iff_eq hp h5).1 h; omega
    · have := (Nat.prime_dvd_prime_iff_eq hp h7).1 h; omega
  have hsum1 := sum_properDivisors_mul_prime_pow_succ 0 (n := 315) (by norm_num) hp hpn
  have hsum0 : ∑ x ∈ (315 : ℕ).properDivisors, x = 309 := by
    rw [← hs, ← hl, List.sum_toFinset _ hnd, List.map_id']
  simp only [zero_add, pow_one, pow_zero, mul_one] at hsum1
  have h := pseudoperfect_mul_prime_pow_of_cert (e := 1) (c := 3) (g := 2) (p := p) l315 hl hnd hI hG
    (by norm_num) hp hpn (by norm_num) (by rw [hs]; omega) (by rw [hs]; omega)
    (by rw [pow_one]; omega) (by rw [pow_one, hsum1, hsum0]; omega)
  simpa using h

/-- **Excess test.** If `m ≤ ∑ D m` and the excess `∑ D m − m` is a subset sum of some
`A ⊆ D m` (e.g. `A = D n` for `n ∣ m`), then `m` is pseudoperfect (take the complement). -/
theorem pseudoperfect_of_excess_mem {m : ℕ} (hm : 0 < m) {A : Finset ℕ}
    (hA : A ⊆ m.properDivisors) (hle : m ≤ ∑ y ∈ m.properDivisors, y)
    (h : ∑ y ∈ m.properDivisors, y - m ∈ subsetSums A) : m.Pseudoperfect := by
  have h' := sub_mem_subsetSums (subsetSums_mono hA h)
  obtain ⟨t, ht, hsum⟩ := h'
  exact ⟨hm, t, ht, by omega⟩

/-- **Certified family step, with the top end.** As `pseudoperfect_mul_prime_pow_of_cert`, but
instead of the margin `n p^e + c ≤ ∑ D(n p^e)` it only needs `n p^e ≤ ∑ D(n p^e)` and, when the
excess is below `c`, that the excess is a subset sum of `D n` (its bit is set in `ssBits l`). -/
theorem pseudoperfect_mul_prime_pow_of_cert' {n p c g e : ℕ} (l : List ℕ)
    (hl : l.toFinset = n.properDivisors) (hnd : l.Nodup)
    (hI : intervalOK (ssBits l) c l.sum = true) (hG : gapOK (ssBits l) g l.sum = true)
    (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ n) (hg : 1 ≤ g)
    (hpg : p * g + 2 * c ≤ l.sum + 1) (hnc : n + 2 * c ≤ (p + 1) * l.sum + 1)
    (hc : c ≤ n * p ^ e) (hle : n * p ^ e ≤ ∑ y ∈ (n * p ^ e).properDivisors, y)
    (hex : ∑ y ∈ (n * p ^ e).properDivisors, y - n * p ^ e < c →
      (ssBits l).testBit (∑ y ∈ (n * p ^ e).properDivisors, y - n * p ^ e) = true) :
    (n * p ^ e).Pseudoperfect := by
  by_cases hlt : ∑ y ∈ (n * p ^ e).properDivisors, y - n * p ^ e < c
  · refine pseudoperfect_of_excess_mem (Nat.mul_pos hn (pow_pos hp.pos e))
      (properDivisors_subset_mul_pow e hp) hle ?_
    rw [← hl]
    exact mem_subsetSums_of_testBit l hnd _ (hex hlt)
  · exact pseudoperfect_mul_prime_pow_of_cert l hl hnd hI hG hn hp hpn hg hpg hnc hc (by omega)

/-- The proper divisors of `525 = 3·5^2·7`. -/
def l525 : List ℕ := [1, 3, 5, 7, 15, 21, 25, 35, 75, 105, 175]

theorem cert_525 :
    l525.toFinset = (525 : ℕ).properDivisors ∧ l525.Nodup ∧ l525.sum = 467 ∧
      intervalOK (ssBits l525) 18 l525.sum = true ∧ gapOK (ssBits l525) 2 l525.sum = true ∧
      (ssBits l525).testBit 6 = true := by
  decide +kernel

/-- **Family decider.** For a certified base `n` (list `l = D n`, interval `c`, gaps `g`) and a prime
`q ∤ n`: if, whenever `n q` is abundant, the linear conditions hold and (for an excess below `c`) the
excess bit is set, then `n q` is not weird. All hypotheses after the certificate are linear in `q`
once `l.sum` is a numeral, so each instance closes by `omega` plus one bit lookup. -/
theorem not_weird_mul_prime_of_cert {n c g q : ℕ} (l : List ℕ)
    (hl : l.toFinset = n.properDivisors) (hnd : l.Nodup)
    (hI : intervalOK (ssBits l) c l.sum = true) (hG : gapOK (ssBits l) g l.sum = true)
    (hn : 0 < n) (hq : q.Prime) (hqn : ¬ q ∣ n) (hg : 1 ≤ g)
    (hcov : n * q < l.sum + (n + q * l.sum) →
      q * g + 2 * c ≤ l.sum + 1 ∧ n + 2 * c ≤ (q + 1) * l.sum + 1 ∧ c ≤ n * q ∧
        (l.sum + (n + q * l.sum) - n * q < c →
          (ssBits l).testBit (l.sum + (n + q * l.sum) - n * q) = true)) :
    ¬ (n * q).Weird := by
  rintro ⟨habund, hnot⟩
  have hsum0 : ∑ x ∈ n.properDivisors, x = l.sum := by
    rw [← hl, List.sum_toFinset _ hnd, List.map_id']
  have hsum1 := sum_properDivisors_mul_prime_pow_succ 0 hn hq hqn
  simp only [zero_add, pow_one, pow_zero, mul_one] at hsum1
  rw [hsum0] at hsum1
  have hab : n * q < l.sum + (n + q * l.sum) := by
    have := habund
    unfold Nat.Abundant at this
    rw [hsum1] at this
    exact this
  obtain ⟨h1, h2, h3, h4⟩ := hcov hab
  apply hnot
  have h := pseudoperfect_mul_prime_pow_of_cert' (e := 1) l hl hnd hI hG hn hq hqn hg h1 h2
    (by rw [pow_one]; exact h3) (by rw [pow_one, hsum1]; omega)
    (by rw [pow_one, hsum1]; exact h4)
  simpa using h

/-- **A whole last-prime family.** No number `525 q` with `q` a prime not dividing `525` is weird:
for `q ≥ 18` it is deficient; for smaller `q` it is pseudoperfect by the certified step (`c = 18`,
`g = 2`), where `q = 17` (excess `6 < c`) uses the excess test. -/
theorem not_weird_525_mul_prime {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ 525) :
    ¬ (525 * q).Weird := by
  obtain ⟨hl, hnd, hs, hI, hG, h6⟩ := cert_525
  have hq2 := hq.two_le
  refine not_weird_mul_prime_of_cert l525 hl hnd hI hG (by norm_num) hq hqn (by norm_num) ?_
  rw [hs]
  intro hab
  refine ⟨by omega, by omega, by omega, fun hlt => ?_⟩
  obtain rfl : q = 17 := by omega
  exact h6

/-- The proper divisors of `495 = 3^2·5·11`. -/
def l495 : List ℕ := [1, 3, 5, 9, 11, 15, 33, 45, 55, 99, 165]

theorem cert_495 :
    l495.toFinset = (495 : ℕ).properDivisors ∧ l495.Nodup ∧ l495.sum = 441 ∧
      intervalOK (ssBits l495) 23 l495.sum = true ∧ gapOK (ssBits l495) 2 l495.sum = true ∧
      (ssBits l495).testBit 18 = true := by
  decide +kernel

/-- Second family: no `495 q` (`q` prime, `q ∤ 495`) is weird (`q = 17`: excess `18 < c = 23`). -/
theorem not_weird_495_mul_prime {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ 495) :
    ¬ (495 * q).Weird := by
  obtain ⟨hl, hnd, hs, hI, hG, h18⟩ := cert_495
  have hq2 := hq.two_le
  refine not_weird_mul_prime_of_cert l495 hl hnd hI hG (by norm_num) hq hqn (by norm_num) ?_
  rw [hs]
  intro hab
  refine ⟨by omega, by omega, by omega, fun hlt => ?_⟩
  obtain rfl : q = 17 := by omega
  exact h18

end ErdosResearch.SubsetSumCert
