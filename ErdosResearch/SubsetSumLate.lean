module

public import ErdosResearch.SubsetSumSteps
public import ErdosResearch.SubsetSumGreedy

@[expose] public section

/-!
# Late raise: raising a prime over a large cofactor

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 57).

Session 56 raised the exponent of a prime `p` right after a bitset base `m p^e₀`, so the cofactor `m`
had to be small (its gap bound `gB` came from a bitset). Here the order is reversed: first the
prime-power steps take the base `m₀ p^e₀` to `m p^e₀` with `m = m₀ · ∏ q^f` large, then `p` is raised
over `m`. The gap bound `gB` of `D m` comes from the greedy bound on the divisors listed from the
factorisation (`SubsetSumGreedy.lean`); the sums grow with `m` while `gB` stays small, so the raise
conditions are much easier to meet.

* `intervalGap_of_bits`: a bitset certificate in `IntervalGap` form;
* `intervalGap_raise`: the chain of raises in `IntervalGap` form, from any source of the interval and gaps;
* instance **`not_weird_late_example`: no `3^3 · 11^2 · 13^10 · 17^2 · 23 · q` (`q` prime, not dividing the
  prefix) is weird.** Base `6831 = 3^3 · 11 · 23` (`c = 2295`, `g = 5`), steps `13^10`, `17^2`, then the raise
  of `11` from `1` to `2` over `m = 3^3 · 23 · 13^10 · 17^2` (264 divisors, greedy `gB = 5`). Session 56's
  plans (raise right after a bitset base) do not certify this prefix.

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumLate

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumCert ErdosResearch.SubsetSumRaise
  ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumGreedy

/-- A bitset certificate gives `IntervalGap`. -/
theorem intervalGap_of_bits {n c g : ℕ} (l : List ℕ) (hl : l.toFinset = n.properDivisors)
    (hnd : l.Nodup) (hI : intervalOK (ssBits l) c l.sum = true)
    (hG : gapOK (ssBits l) g l.sum = true) : IntervalGap n l.sum c g := by
  have hs : ∑ y ∈ n.properDivisors, y = l.sum := by
    rw [← hl, List.sum_toFinset _ hnd, List.map_id']
  have hmem : ∀ x, (ssBits l).testBit x = true → x ∈ subsetSums n.properDivisors := by
    intro x hx; rw [← hl]; exact mem_subsetSums_of_testBit l hnd x hx
  refine ⟨hs, fun x h1 h2 => hmem x (testBit_of_intervalOK hI x h1 h2), fun x hx => ?_⟩
  obtain ⟨z, hz, h1, h2, h3⟩ := exists_testBit_of_gapOK hG x hx
  exact ⟨z, hmem z hz, h1, h2, h3⟩

/-- **Chain of raises in `IntervalGap` form.** Interval and gaps on `D(m p^e₀)` (from anywhere), gaps
`≤ gB` on `D m` with `∑ D m = SB`, and `raiseOK` give the same interval and gaps on `D(m p^(e₀ + k))`. -/
theorem intervalGap_raise {m p e₀ c g gB SB SA k : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (hg : 1 ≤ g) (hA : IntervalGap (m * p ^ e₀) SA c g) (hSB : ∑ y ∈ m.properDivisors, y = SB)
    (hgapB : ∀ x < ∑ y ∈ m.properDivisors, y, ∃ z ∈ subsetSums m.properDivisors,
      x < z ∧ z ≤ x + gB ∧ z ≤ ∑ y ∈ m.properDivisors, y)
    (hok : raiseOK m p e₀ c gB SB SA k = true) :
    IntervalGap (m * p ^ (e₀ + k)) (raiseSum m p e₀ SB SA k) c g := by
  obtain ⟨hSA, hI, hG⟩ := hA
  have hrs := raiseSum_eq hm hp hpm hSA hSB
  have hcond : ∀ j < k,
      p ^ (e₀ + j + 1) * gB + 2 * c ≤ ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y + 1 ∧
      m * p ^ (e₀ + j) + 2 * c ≤ p ^ (e₀ + j + 1) * ∑ y ∈ m.properDivisors, y +
        ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y + 1 := by
    intro j hj
    simp only [raiseOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    rw [hrs j, hSB]
    exact hok j hj
  obtain ⟨hI', hG'⟩ := interval_properDivisors_raise_iter (gB := gB) hm hp hpm hg
    (fun x h1 h2 => hI x h1 (by rw [hSA] at h2; exact h2))
    (fun x hx => by rw [hSA] at hx ⊢; exact hG x hx) hgapB k hcond
  refine ⟨hrs k, fun x h1 h2 => hI' x h1 (by rw [hrs k]; exact h2), fun x hx => ?_⟩
  rw [← hrs k] at hx ⊢
  exact hG' x hx

/-- Proper divisors of the base `6831 = 3^3 · 11 · 23`. -/
def l6831 : List ℕ := [1, 3, 9, 11, 23, 27, 33, 69, 99, 207, 253, 297, 621, 759, 2277]

/-- The cofactor `m = 3^3 · 23 · 13^10 · 17^2` over which `11` is raised. -/
def fsM : List (ℕ × ℕ) := [(3, 3), (23, 1), (13, 10), (17, 2)]

theorem cert_late :
    l6831.toFinset = (6831 : ℕ).properDivisors ∧ l6831.Nodup ∧
      intervalOK (ssBits l6831) 2295 l6831.sum = true ∧ gapOK (ssBits l6831) 5 l6831.sum = true ∧
      stepsOK 2295 5 6831 l6831.sum [(13, 10), (17, 2)] = true ∧
      stepsEnd 6831 l6831.sum [(13, 10), (17, 2)] = (prodOf fsM * 11 ^ 1, 256030928920159929) ∧
      gapCert fsM 5 19274133603875979 = true ∧
      raiseOK (prodOf fsM) 11 1 2295 5 19274133603875979 256030928920159929 1 = true ∧
      raiseSum (prodOf fsM) 11 1 19274133603875979 256030928920159929 1 = 2860355677399283379 ∧
      prodOf fsM * 11 ^ (1 + 1) = 3 ^ 3 * 11 ^ 2 * 13 ^ 10 * 17 ^ 2 * 23 ∧
      0 < prodOf fsM ∧ prodOf fsM % 11 ≠ 0 := by
  decide +kernel

/-- **A family certified only with the late raise.** No `3^3 · 11^2 · 13^10 · 17^2 · 23 · q` (`q` prime, not
dividing the prefix) is weird. The prefix is deficient and `n q` is abundant only for `q ≤ 43`; every such
prime is covered by the interval (`c = 2295`, `g = 5`). -/
theorem not_weird_late_example {q : ℕ} (hq : q.Prime)
    (hqn : ¬ q ∣ 3 ^ 3 * 11 ^ 2 * 13 ^ 10 * 17 ^ 2 * 23) :
    ¬ (3 ^ 3 * 11 ^ 2 * 13 ^ 10 * 17 ^ 2 * 23 * q).Weird := by
  obtain ⟨hl, hnd, hI, hG, hst, hend, hgc, hok, hrs, hn, hm0, hm11⟩ := cert_late
  have h0 := intervalGap_of_bits l6831 hl hnd hI hG
  have h1 := intervalGap_of_stepsOK (by norm_num) [(13, 10), (17, 2)] _ _
    (by norm_num) (by simp; norm_num) hst h0
  rw [hend] at h1
  obtain ⟨hSB, hgapB⟩ := gap_properDivisors_of_gapCert (by simp [fsM]; norm_num) hgc
  have h2 := intervalGap_raise hm0 (by norm_num) (fun h => hm11 (Nat.mod_eq_zero_of_dvd h))
    (by norm_num) h1 hSB hgapB hok
  rw [hrs, hn] at h2
  have hq2 := hq.two_le
  refine not_weird_mul_prime_of_intervalGap (by norm_num) (by norm_num) h2 hq hqn ?_
  norm_num
  intro hab
  refine ⟨by omega, by omega, by omega, by omega⟩

end ErdosResearch.SubsetSumLate
