module

public import Mathlib

@[expose] public section

/-!
# Monotonicity of the prime-power step condition in the exponents

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 78).

The staircase decider (`scripts/plimit_probe.py`) treats the set of certified exponent vectors as an up-set: if a point
`n` passes the step condition for the next prime `q`, so does every multiple `n p` (any prime `p`, new or already
dividing `n`). These lemmas prove that:

* `mul_sum_properDivisors_le`: `p · ∑ D(n) ≤ ∑ D(n p)` (the map `d ↦ p d` sends proper divisors of `n` to proper
  divisors of `n p`, injectively);
* `stepCond_mono`: the two inequalities `q g + 2c ≤ S + 1`, `n + 2c ≤ (q+1) S + 1` (Python `stepOK`) survive
  `n ↦ n p`, `S ↦ S'` whenever `p S ≤ S'`, `p ≥ 1` and `c ≥ 1`;
* `stepCond_mul`: the same with `S = ∑ D(n)`, `S' = ∑ D(n p)`.

Elementary; new only as a formalisation.
-/

namespace ErdosResearch.SubsetSumMono

theorem mul_sum_properDivisors_le (n p : ℕ) (hp : 0 < p) :
    p * ∑ d ∈ n.properDivisors, d ≤ ∑ d ∈ (n * p).properDivisors, d := by
  rw [Finset.mul_sum]
  have hinj : Set.InjOn (fun d => p * d) (n.properDivisors : Set ℕ) := by
    intro a _ b _ h
    exact Nat.eq_of_mul_eq_mul_left hp h
  rw [← Finset.sum_image (f := fun x => x) (g := fun d => p * d) (fun a ha b hb h => hinj ha hb h)]
  apply Finset.sum_le_sum_of_subset
  intro x hx
  simp only [Finset.mem_image, Nat.mem_properDivisors] at hx ⊢
  obtain ⟨d, ⟨hd, hlt⟩, rfl⟩ := hx
  refine ⟨?_, ?_⟩
  · rw [mul_comm n p]; exact Nat.mul_dvd_mul_left p hd
  · rw [mul_comm n p]; exact Nat.mul_lt_mul_of_pos_left hlt hp

theorem stepCond_mono {n S S' p q g c : ℕ} (hp : 1 ≤ p) (hc : 1 ≤ c) (hS : p * S ≤ S')
    (h1 : q * g + 2 * c ≤ S + 1) (h2 : n + 2 * c ≤ (q + 1) * S + 1) :
    q * g + 2 * c ≤ S' + 1 ∧ n * p + 2 * c ≤ (q + 1) * S' + 1 := by
  have hSS : S ≤ S' := le_trans (Nat.le_mul_of_pos_left S hp) hS
  refine ⟨by omega, ?_⟩
  have h3 : (q + 1) * (p * S) ≤ (q + 1) * S' := Nat.mul_le_mul_left _ hS
  have h4 : p * (n + 2 * c) ≤ p * ((q + 1) * S + 1) := Nat.mul_le_mul_left _ h2
  obtain ⟨p', rfl⟩ : ∃ p', p = p' + 1 := ⟨p - 1, by omega⟩
  obtain ⟨c', rfl⟩ : ∃ c', c = c' + 1 := ⟨c - 1, by omega⟩
  have h5 : 0 ≤ p' * c' := Nat.zero_le _
  nlinarith

theorem stepCond_mul {n p q g c : ℕ} (hp : 0 < p) (hc : 1 ≤ c)
    (h1 : q * g + 2 * c ≤ (∑ d ∈ n.properDivisors, d) + 1)
    (h2 : n + 2 * c ≤ (q + 1) * (∑ d ∈ n.properDivisors, d) + 1) :
    q * g + 2 * c ≤ (∑ d ∈ (n * p).properDivisors, d) + 1 ∧
      n * p + 2 * c ≤ (q + 1) * (∑ d ∈ (n * p).properDivisors, d) + 1 :=
  stepCond_mono hp hc (mul_sum_properDivisors_le n p hp) h1 h2

end ErdosResearch.SubsetSumMono
