module

public import ErdosResearch.SubsetSumLastOK
public import ErdosResearch.SubsetSumUniform

@[expose] public section

/-!
# All last primes at once, with a closed-form middle range

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 75).

`SubsetSumLastOK.lastOK n S c g B` scans every `q < B`. Session 75 measured (Python, `scripts/plimit_probe.py`,
`BOUNDED=1`) that on real 3-prime prefixes of the ω = 6 search the decider is dominated by these scans: up to
`1.9·10⁹` values of `q` for one prefix, far too many for the kernel. Almost all of them lie in one interval
`[lo, hi]` where the four conditions hold at both ends, and then they hold for every `q` in between
(`SubsetSumUniform.pseudoperfect_mul_prime_of_range`). `lastOKR` checks the two ends once and scans only
`q < lo` and `hi < q < B`.

* `lastOKR n S c g B lo hi` (Boolean) and **`not_weird_mul_prime_of_lastOKR`**.

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumLastRange

open Finset ErdosResearch.SubsetSumSteps ErdosResearch.SubsetSumUniform

/-- The per-`q` conditions of `lastOK` (true when `q` needs nothing or is certified). -/
def qCond (n S c g q : ℕ) : Bool :=
  decide (q < 2) || decide (n % q = 0) || !decide (n * q < S + (n + q * S)) ||
    (decide (q * g + 2 * c ≤ S + 1) && decide (n + 2 * c ≤ (q + 1) * S + 1) &&
      decide (c ≤ n * q) && decide (n * q + c ≤ S + (n + q * S)))

/-- `lastOK` with the middle range `[lo, hi]` decided by its two ends (no scan there). -/
def lastOKR (n S c g B lo hi : ℕ) : Bool :=
  decide (S < n) && decide (n + S < B * (n - S)) &&
    decide (hi * g + 2 * c ≤ S + 1) && decide (n + 2 * c ≤ (lo + 1) * S + 1) && decide (c ≤ n * lo) &&
    decide (n * hi + c ≤ S + (n + hi * S)) &&
    (List.range lo).all (qCond n S c g) && (List.range' (hi + 1) (B - (hi + 1))).all (qCond n S c g)

/-- **Every last prime at once, middle range in closed form.** -/
theorem not_weird_mul_prime_of_lastOKR {n S c g B lo hi q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hok : lastOKR n S c g B lo hi = true) (hq : q.Prime) (hqn : ¬ q ∣ n) :
    ¬ (n * q).Weird := by
  simp only [lastOKR, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    List.mem_range'_1] at hok
  obtain ⟨⟨⟨⟨⟨⟨⟨hSn, hB⟩, h1⟩, h2⟩, h3⟩, h4⟩, hlo⟩, hhi⟩ := hok
  by_cases hmid : lo ≤ q ∧ q ≤ hi
  · exact fun hw => hw.2 (pseudoperfect_mul_prime_of_range hn hg h hq hqn hmid.1 hmid.2 h1 h2 h3 h4)
  have hq2 := hq.two_le
  have hqB : n * q < S + (n + q * S) → q < B := by
    intro hab
    by_contra hcon'
    have hcon : B ≤ q := Nat.le_of_not_lt hcon'
    obtain ⟨d, rfl⟩ : ∃ d, n = S + d := ⟨n - S, by omega⟩
    have h1 : B * d ≤ q * d := Nat.mul_le_mul_right d hcon
    rw [Nat.add_sub_cancel_left] at hB
    nlinarith
  have hc : qCond n S c g q = true := by
    rcases Nat.lt_or_ge q lo with hql | hql
    · exact hlo q hql
    · have hqh : hi < q := by omega
      by_cases hab : n * q < S + (n + q * S)
      · exact hhi q ⟨by omega, by have := hqB hab; omega⟩
      · simp [qCond, hab]
  simp only [qCond, Bool.or_eq_true, Bool.and_eq_true, decide_eq_true_eq, Bool.not_eq_eq_eq_not,
    Bool.not_true, decide_eq_false_iff_not] at hc
  refine not_weird_mul_prime_of_intervalGap hn hg h hq hqn fun hab => ?_
  rcases hc with ((h1 | h1) | h1) | h1
  · omega
  · exact absurd (Nat.dvd_of_mod_eq_zero h1) hqn
  · exact absurd hab h1
  · exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

/-- Sanity instance: the deficient point `3^16·5^11·19^8·97^3` (with `S = ∑ D`, `c = 12`, `g = 2` from session 74's plan):
`lastOK` would scan `B = 9214` values of `q`; `lastOKR` checks the two ends of `[2, 9213]` and scans nothing. -/
example : lastOKR 32580229080926276122243798828125 32573157211172536926891330131955 12 2 9214 2 9213 = true := by
  decide +kernel

end ErdosResearch.SubsetSumLastRange
