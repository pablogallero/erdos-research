module

public import ErdosResearch.SubsetSumPairRange

@[expose] public section

/-!
# Tails with a star: every last prime power `r^k`

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 85).

The tails of sessions 68, 73 and 82 (`not_weird_tail`, `not_weird_ptail`, `not_weird_qtail`) bound the abundancy of
`… q^e r` with the factor `(r + 1)/r` for the last prime, so they cover `r^1` only. With `r^k` the factor is at most
`r/(r − 1) ≤ Q/(Q − 1)`. Here `ppSum_ratio` (`σ(N p^f)(p − 1) ≤ σ(N) p^{f+1}`) is applied once per prime, so:
* `not_weird_tail_star`: `σ(n) Q² ≤ 2n (Q − 1)²` ⇒ no `n q^e r^k` with primes `q, r ≥ Q` is even abundant;
* `not_weird_qtail_star`: the same below a prime power `p^f` (`σ(n) p Q² ≤ 2n (p − 1)(Q − 1)²`);
* `not_weird_ptail_star`: three primes `p, q, r ≥ Q` (`σ(n) Q³ ≤ 2n (Q − 1)³`).
Python (`scripts/star_row_probe.py`, late prefix): the star q-tails are at most one above the old ones (e.g. `p = 37`: 749 → 750),
and the star p-tail is `101` instead of `100`. Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumTailStar

open ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumPairRange

/-- **Two-prime star tail.** -/
theorem not_weird_tail_star {n S Q q e r k : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hq : q.Prime) (hqn : ¬ q ∣ n) (hr : r.Prime) (hrn : ¬ r ∣ n * q ^ e) (hQ : 2 ≤ Q)
    (hQq : Q ≤ q) (hQr : Q ≤ r) (hσ : (S + n) * Q * Q ≤ 2 * n * (Q - 1) * (Q - 1)) :
    ¬ (n * q ^ e * r ^ k).Weird := by
  rintro ⟨hab, -⟩
  have hN : 0 < n * q ^ e := Nat.mul_pos hn (pow_pos hq.pos e)
  have hT1 := ppSum_eq hn hq hqn hS e
  have hsum := ppSum_eq hN hr hrn hT1 k
  unfold Nat.Abundant at hab
  rw [hsum] at hab
  have h1 := ppSum_ratio n q S e hq.two_le
  have h2 := ppSum_ratio (n * q ^ e) r (ppSum n q S e) k hr.two_le
  have hq2 := hq.two_le
  have hr2 := hr.two_le
  generalize ppSum (n * q ^ e) r (ppSum n q S e) k = T2 at hab h2
  generalize ppSum n q S e = T1 at h1 h2
  generalize q ^ e = x at h1 h2 hab
  generalize r ^ k = y at h2 hab
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
  obtain ⟨v, rfl⟩ : ∃ v, r = v + 1 := ⟨r - 1, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, Q = w + 1 := ⟨Q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at h1 h2 hσ
  have hu : 0 < u := by omega
  have hv : 0 < v := by omega
  have hw : 0 < w := by omega
  have a1 : (u + 1) * w ≤ (w + 1) * u := by nlinarith
  have a2 : (v + 1) * w ≤ (w + 1) * v := by nlinarith
  have b1 : (S + n) * (u + 1) * (v + 1) ≤ 2 * n * u * v := by
    have c : (S + n) * (u + 1) * (v + 1) * (w * w) ≤ 2 * n * u * v * (w * w) :=
      calc (S + n) * (u + 1) * (v + 1) * (w * w) = (S + n) * ((u + 1) * w) * ((v + 1) * w) := by ring
        _ ≤ (S + n) * ((w + 1) * u) * ((w + 1) * v) :=
          Nat.mul_le_mul (Nat.mul_le_mul_left _ a1) a2
        _ = (S + n) * (w + 1) * (w + 1) * (u * v) := by ring
        _ ≤ 2 * n * w * w * (u * v) := Nat.mul_le_mul_right _ hσ
        _ = 2 * n * u * v * (w * w) := by ring
    exact Nat.le_of_mul_le_mul_right c (Nat.mul_pos hw hw)
  have b2 : (T2 + n * x * y) * (v * u) ≤ 2 * (n * x * y) * (v * u) :=
    calc (T2 + n * x * y) * (v * u) = ((T2 + n * x * y) * v) * u := by ring
      _ ≤ ((T1 + n * x) * (y * (v + 1))) * u := Nat.mul_le_mul_right _ h2
      _ = ((T1 + n * x) * u) * (y * (v + 1)) := by ring
      _ ≤ ((S + n) * (x * (u + 1))) * (y * (v + 1)) := Nat.mul_le_mul_right _ h1
      _ = x * y * ((S + n) * (u + 1) * (v + 1)) := by ring
      _ ≤ x * y * (2 * n * u * v) := Nat.mul_le_mul_left _ b1
      _ = 2 * (n * x * y) * (v * u) := by ring
  have := Nat.le_of_mul_le_mul_right b2 (Nat.mul_pos hv hu)
  omega

/-- **Star q-tail below a prime power `p^f`.** -/
theorem not_weird_qtail_star {n S p Q f q e r k : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q.Prime) (hqn : ¬ q ∣ n * p ^ f) (hr : r.Prime)
    (hrn : ¬ r ∣ n * p ^ f * q ^ e) (hQ : 2 ≤ Q) (hQq : Q ≤ q) (hQr : Q ≤ r)
    (hσ : (S + n) * p * Q * Q ≤ 2 * n * (p - 1) * (Q - 1) * (Q - 1)) :
    ¬ (n * p ^ f * q ^ e * r ^ k).Weird := by
  have hm : 0 < n * p ^ f := Nat.mul_pos hn (pow_pos hp.pos f)
  refine not_weird_tail_star hm (ppSum_eq hn hp hpn hS f) hq hqn hr hrn hQ hQq hQr ?_
  have h1 := ppSum_ratio n p S f hp.two_le
  have hp1 : 0 < p - 1 := by have := hp.two_le; omega
  refine Nat.le_of_mul_le_mul_right ?_ hp1
  calc (ppSum n p S f + n * p ^ f) * Q * Q * (p - 1)
      = (ppSum n p S f + n * p ^ f) * (p - 1) * (Q * Q) := by ring
    _ ≤ (S + n) * (p ^ f * p) * (Q * Q) := Nat.mul_le_mul_right _ h1
    _ = p ^ f * ((S + n) * p * Q * Q) := by ring
    _ ≤ p ^ f * (2 * n * (p - 1) * (Q - 1) * (Q - 1)) := Nat.mul_le_mul_left _ hσ
    _ = 2 * (n * p ^ f) * (Q - 1) * (Q - 1) * (p - 1) := by ring

/-- **Three-prime star tail.** -/
theorem not_weird_ptail_star {n S Q p f q e r k : ℕ} (hn : 0 < n) (hS : ∑ y ∈ n.properDivisors, y = S)
    (hp : p.Prime) (hpn : ¬ p ∣ n) (hq : q.Prime) (hqn : ¬ q ∣ n * p ^ f) (hr : r.Prime)
    (hrn : ¬ r ∣ n * p ^ f * q ^ e) (hQ : 2 ≤ Q) (hQp : Q ≤ p) (hQq : Q ≤ q) (hQr : Q ≤ r)
    (hσ : (S + n) * Q * Q * Q ≤ 2 * n * (Q - 1) * (Q - 1) * (Q - 1)) :
    ¬ (n * p ^ f * q ^ e * r ^ k).Weird := by
  refine not_weird_qtail_star hn hS hp hpn hq hqn hr hrn hQ hQq hQr ?_
  have hp2 := hp.two_le
  obtain ⟨u, rfl⟩ : ∃ u, p = u + 1 := ⟨p - 1, by omega⟩
  obtain ⟨w, rfl⟩ : ∃ w, Q = w + 1 := ⟨Q - 1, by omega⟩
  simp only [Nat.add_sub_cancel] at hσ ⊢
  have hw : 0 < w := by omega
  have a1 : (u + 1) * w ≤ (w + 1) * u := by nlinarith
  have c : (S + n) * (u + 1) * (w + 1) * (w + 1) * w ≤ 2 * n * u * w * w * w :=
    calc (S + n) * (u + 1) * (w + 1) * (w + 1) * w = (S + n) * (w + 1) * (w + 1) * ((u + 1) * w) := by ring
      _ ≤ (S + n) * (w + 1) * (w + 1) * ((w + 1) * u) := Nat.mul_le_mul_left _ a1
      _ = (S + n) * (w + 1) * (w + 1) * (w + 1) * u := by ring
      _ ≤ 2 * n * w * w * w * u := Nat.mul_le_mul_right _ hσ
      _ = 2 * n * u * w * w * w := by ring
  exact Nat.le_of_mul_le_mul_right c hw

/-- **Instance (star q-tail).** Below the late prefix `n = 3^3·23·13^10·17^2·11`: no `n·37^f·q^e·r^k` is weird for primes
`q, r ≥ 750` (`q ∤ n·37^f`, `r ∤ n·37^f·q^e`), any `f, e, k`. -/
theorem not_weird_late_prefix_37_qtail_star {f q e r k : ℕ} (hq : q.Prime)
    (hqn : ¬ q ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f) (hr : r.Prime)
    (hrn : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * q ^ e) (hq₀ : 750 ≤ q) (hr₀ : 750 ≤ r) :
    ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * 37 ^ f * q ^ e * r ^ k).Weird :=
  not_weird_qtail_star (S := 256030928920159929) (Q := 750) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix.1 (by norm_num) (by norm_num) hq hqn hr hrn
    (by norm_num) hq₀ hr₀ (by norm_num)

/-- **Instance (star p-tail).** Below the late prefix: no `n·p^f·q^e·r^k` is weird for primes `p, q, r ≥ 101`. -/
theorem not_weird_late_prefix_ptail_star {p f q e r k : ℕ} (hp : p.Prime)
    (hpn : ¬ p ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11) (hq : q.Prime)
    (hqn : ¬ q ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * p ^ f) (hr : r.Prime)
    (hrn : ¬ r ∣ 3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * p ^ f * q ^ e) (hp₀ : 101 ≤ p) (hq₀ : 101 ≤ q)
    (hr₀ : 101 ≤ r) : ¬ (3 ^ 3 * 23 * 13 ^ 10 * 17 ^ 2 * 11 * p ^ f * q ^ e * r ^ k).Weird :=
  not_weird_ptail_star (S := 256030928920159929) (Q := 101) (by norm_num)
    ErdosResearch.SubsetSumFifthLoop.intervalGap_late_prefix.1 hp hpn hq hqn hr hrn (by norm_num) hp₀ hq₀ hr₀
    (by norm_num)

end ErdosResearch.SubsetSumTailStar
