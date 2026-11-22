module

public import ErdosResearch.SubsetSumSteps

@[expose] public section

/-!
# All last primes at once, by one Boolean

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 58).

`not_weird_mul_prime_of_intervalGap` handles one last prime `q`, with a hypothesis that is only needed when
`n q` is abundant. For a deficient `n` (`∑ D n = S < n`), `n q` is abundant only when
`q (n − S) < n + S`, so a bound `B` with `n + S < B (n − S)` leaves finitely many `q`. `lastOK` checks the
conditions for every `q ∈ [2, B)` not dividing `n` (primes or not), so generated instances need no
case analysis on `q`.

* `lastOK n S c g B` (Boolean) and **`not_weird_mul_prime_of_lastOK`**.

Elementary; new only as a formalisation. Not a new result on #470.
-/

namespace ErdosResearch.SubsetSumLastOK

open Finset ErdosResearch.SubsetSumSteps

/-- The last-prime conditions for every `q < B` (`2 ≤ q`, `q ∤ n`), plus `n + S < B (n − S)` with `S < n`. -/
def lastOK (n S c g B : ℕ) : Bool :=
  decide (S < n) && decide (n + S < B * (n - S)) &&
    (List.range B).all fun q =>
      decide (q < 2) || decide (n % q = 0) || !decide (n * q < S + (n + q * S)) ||
        (decide (q * g + 2 * c ≤ S + 1) && decide (n + 2 * c ≤ (q + 1) * S + 1) &&
          decide (c ≤ n * q) && decide (n * q + c ≤ S + (n + q * S)))

/-- **Every last prime at once.** Interval and gaps on `D n` and `lastOK` give: no `n q` (`q` prime, `q ∤ n`)
is weird. -/
theorem not_weird_mul_prime_of_lastOK {n S c g B q : ℕ} (hn : 0 < n) (hg : 1 ≤ g)
    (h : IntervalGap n S c g) (hok : lastOK n S c g B = true) (hq : q.Prime) (hqn : ¬ q ∣ n) :
    ¬ (n * q).Weird := by
  simp only [lastOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    Bool.or_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true, decide_eq_false_iff_not] at hok
  obtain ⟨⟨hSn, hB⟩, hall⟩ := hok
  refine not_weird_mul_prime_of_intervalGap hn hg h hq hqn fun hab => ?_
  have hq2 := hq.two_le
  have hqB : q < B := by
    by_contra hcon'
    have hcon : B ≤ q := Nat.le_of_not_lt hcon'
    obtain ⟨d, rfl⟩ : ∃ d, n = S + d := ⟨n - S, by omega⟩
    have h1 : B * d ≤ q * d := Nat.mul_le_mul_right d hcon
    rw [Nat.add_sub_cancel_left] at hB
    nlinarith
  rcases hall q hqB with ((h1 | h1) | h1) | h1
  · omega
  · exact absurd (Nat.dvd_of_mod_eq_zero h1) hqn
  · exact absurd hab h1
  · exact ⟨h1.1.1.1, h1.1.1.2, h1.1.2, h1.2⟩

end ErdosResearch.SubsetSumLastOK
