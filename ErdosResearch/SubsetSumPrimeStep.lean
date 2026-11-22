module

public import ErdosResearch.SubsetSumGlue

@[expose] public section

/-!
# The prime step for subset sums of proper divisors

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 54).

Session 53 glued intervals of `SS(div A)`, where `SS` means subset sums. For a deficient `A` that set
has no interval centred in `[0, σ(A)]` (the middle gap), so the glue never started. The fix is to work
with the **proper** divisors. For a prime `p ∤ n`,

  `D(n p) = D(n) ∪ ({n} ∪ p · D(n))`,  where `D = properDivisors`.

Suppose `SS(D n) ⊇ [c, s − c]` with `s = ∑ D n`, and every gap of `SS(D n)` in `[0, s]` is at most `g`.
If `p g + 2c ≤ s + 1` and `n + 2c ≤ (p + 1) s + 1`, then `SS(D(n p)) ⊇ [c, s' − c]` with
`s' = s + n + p s = ∑ D(n p)`, **with the same `c`** (`interval_properDivisors_mul_prime`).
If moreover `n p ∈ [c, s' − c]`, then `n p` is pseudoperfect (`pseudoperfect_mul_prime_of_interval`).

Elementary; a building block for a Lean version of the family search, not a new result.
-/

namespace ErdosResearch.SubsetSumPrimeStep

open Finset ErdosResearch.SubsetSumGlue

lemma subsetSums_mono {s t : Finset ℕ} (h : s ⊆ t) {m : ℕ} (hm : m ∈ subsetSums s) :
    m ∈ subsetSums t := by
  obtain ⟨u, hu, rfl⟩ := hm
  exact ⟨u, hu.trans h, rfl⟩

/-- `D(n p) = D n ∪ insert n (p · D n)` for a prime `p ∤ n`, `n > 0`. -/
theorem properDivisors_mul_prime {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    (n * p).properDivisors =
      n.properDivisors ∪ insert n (n.properDivisors.image (p * ·)) := by
  have hp2 := hp.two_le
  ext d
  simp only [mem_union, mem_insert, mem_image, Nat.mem_properDivisors]
  constructor
  · rintro ⟨hd, hlt⟩
    by_cases hpd : p ∣ d
    · obtain ⟨e, rfl⟩ := hpd
      refine Or.inr (Or.inr ⟨e, ⟨?_, ?_⟩, rfl⟩)
      · rw [mul_comm n p] at hd
        exact Nat.dvd_of_mul_dvd_mul_left hp.pos hd
      · rw [mul_comm n p] at hlt
        exact Nat.lt_of_mul_lt_mul_left hlt
    · have hcop : Nat.Coprime d p :=
        Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd)
      have hdn : d ∣ n := hcop.dvd_of_dvd_mul_right hd
      rcases Nat.lt_or_ge d n with h | h
      · exact Or.inl ⟨hdn, h⟩
      · exact Or.inr (Or.inl (le_antisymm (Nat.le_of_dvd hn hdn) h))
  · rintro (⟨hd, hlt⟩ | rfl | ⟨e, ⟨he, hlt⟩, rfl⟩)
    · exact ⟨hd.mul_right p, by nlinarith⟩
    · exact ⟨dvd_mul_right d p, by nlinarith⟩
    · refine ⟨?_, ?_⟩
      · rw [mul_comm n p]; exact Nat.mul_dvd_mul_left p he
      · rw [mul_comm n p]; exact Nat.mul_lt_mul_of_pos_left hlt hp.pos

/-- Sum of `D(n p)` in terms of `s = ∑ D n`. -/
theorem sum_properDivisors_mul_prime' {n p : ℕ} (hn : 0 < n) (hp : p.Prime) (hpn : ¬ p ∣ n) :
    ∑ x ∈ (n * p).properDivisors, x =
      ∑ x ∈ n.properDivisors, x + (n + p * ∑ x ∈ n.properDivisors, x) := by
  have hnot : n ∉ n.properDivisors.image (p * ·) := by
    intro h
    obtain ⟨e, _, he⟩ := mem_image.1 h
    exact hpn ⟨e, he.symm⟩
  have hdisj : Disjoint n.properDivisors (insert n (n.properDivisors.image (p * ·))) := by
    rw [disjoint_insert_right]
    refine ⟨fun h => (Nat.mem_properDivisors.1 h).2.false, ?_⟩
    rw [disjoint_left]
    intro d hd hd'
    obtain ⟨e, _, rfl⟩ := mem_image.1 hd'
    exact hpn ((dvd_mul_right p e).trans (Nat.mem_properDivisors.1 hd).1)
  rw [properDivisors_mul_prime hn hp hpn, sum_union hdisj, sum_insert hnot,
    sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), mul_sum]

/-- **The prime step.** If the subset sums of `D n` cover `[c, s − c]` and have gaps at most `g`
on `[0, s]`, and `p g + 2c ≤ s + 1`, `n + 2c ≤ (p + 1) s + 1`, then the subset sums of `D(n p)`
cover `[c, s + n + p s − c]`. -/
theorem interval_properDivisors_mul_prime {n p c g : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ n.properDivisors, y → x ∈ subsetSums n.properDivisors)
    (hgap : ∀ x < ∑ y ∈ n.properDivisors, y, ∃ z ∈ subsetSums n.properDivisors,
      x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ n.properDivisors, y)
    (hpg : p * g + 2 * c ≤ ∑ y ∈ n.properDivisors, y + 1)
    (hnc : n + 2 * c ≤ (p + 1) * ∑ y ∈ n.properDivisors, y + 1)
    {m : ℕ} (hm1 : c ≤ m)
    (hm2 : m + c ≤ ∑ y ∈ n.properDivisors, y + (n + p * ∑ y ∈ n.properDivisors, y)) :
    m ∈ subsetSums (n * p).properDivisors := by
  set D := n.properDivisors with hD
  set s := ∑ y ∈ D, y with hs
  set E := D.image (p * ·) with hE
  have hnot : n ∉ E := by
    intro h
    obtain ⟨e, _, he⟩ := mem_image.1 h
    exact hpn ⟨e, he.symm⟩
  have hdisj : Disjoint D (insert n E) := by
    rw [disjoint_insert_right]
    refine ⟨fun h => (Nat.mem_properDivisors.1 h).2.false, ?_⟩
    rw [disjoint_left]
    intro d hd hd'
    obtain ⟨e, _, rfl⟩ := mem_image.1 hd'
    exact hpn ((dvd_mul_right p e).trans (Nat.mem_properDivisors.1 hd).1)
  have hsumE : ∑ y ∈ E, y = p * s := by
    rw [hE, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), mul_sum]
  have hsum2 : ∑ y ∈ insert n E, y = n + p * s := by rw [sum_insert hnot, hsumE]
  -- the scaled copy has gaps at most `p g`
  have hscaled : ∀ x < p * s, ∃ b ∈ subsetSums E, x < b ∧ b ≤ x + p * g ∧ b ≤ p * s := by
    intro x hx
    have hq : x / p < s := by
      rw [Nat.div_lt_iff_lt_mul hp.pos]; linarith
    obtain ⟨z, hz, hzq, hzg, hzs⟩ := hgap _ hq
    refine ⟨p * z, subsetSums_image_mul p hz, ?_, ?_, Nat.mul_le_mul_left p hzs⟩
    · have := Nat.lt_mul_div_succ x hp.pos
      calc x < p * (x / p + 1) := this
        _ ≤ p * z := Nat.mul_le_mul_left p hzq
    · have h1 : p * z ≤ p * (x / p) + p * g := by rw [← mul_add]; exact Nat.mul_le_mul_left p hzg
      have h2 : p * (x / p) ≤ x := Nat.mul_div_le x p
      omega
  have hEsub : E ⊆ insert n E := subset_insert n E
  have hshift : ∀ b ∈ subsetSums E, n + b ∈ subsetSums (insert n E) := by
    intro b hb
    have h := subsetSums_union (s₁ := {n}) (s₂ := E) (by simpa using hnot)
      (sum_mem_subsetSums {n}) hb
    rw [sum_singleton, ← insert_eq] at h
    exact h
  have hpg' : p * g + 2 * c ≤ s + 1 := hpg
  have hnc' : n + 2 * c ≤ (p + 1) * s + 1 := hnc
  have h₂ : ∀ x < ∑ y ∈ insert n E, y, ∃ b ∈ subsetSums (insert n E),
      x < b ∧ b ≤ ∑ y ∈ insert n E, y ∧ b + 2 * c ≤ x + s + 1 := by
    rw [hsum2]
    intro x hx
    rcases Nat.lt_or_ge x (p * s) with h | h
    · obtain ⟨b, hb, hxb, hbg, hbs⟩ := hscaled x h
      exact ⟨b, subsetSums_mono hEsub hb, hxb, by omega, by omega⟩
    · rcases Nat.lt_or_ge x n with h' | h'
      · refine ⟨n, ?_, h', by omega, ?_⟩
        · have := hshift 0 (zero_mem_subsetSums E)
          simpa using this
        · have : (p + 1) * s = p * s + s := by ring
          omega
      · obtain ⟨b, hb, hxb, hbg, hbs⟩ := hscaled (x - n) (by omega)
        exact ⟨n + b, hshift b hb, by omega, by omega, by omega⟩
  have hmem := glue_subsetSums hdisj h₁ h₂ hm1 (by rw [hsum2]; exact hm2)
  rw [properDivisors_mul_prime hn hp hpn]
  exact hmem

/-- Corollary: under the hypotheses of the prime step, if `n p` itself lies in `[c, s' − c]`, then
`n p` is pseudoperfect. -/
theorem pseudoperfect_mul_prime_of_interval {n p c g : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ n.properDivisors, y → x ∈ subsetSums n.properDivisors)
    (hgap : ∀ x < ∑ y ∈ n.properDivisors, y, ∃ z ∈ subsetSums n.properDivisors,
      x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ n.properDivisors, y)
    (hpg : p * g + 2 * c ≤ ∑ y ∈ n.properDivisors, y + 1)
    (hnc : n + 2 * c ≤ (p + 1) * ∑ y ∈ n.properDivisors, y + 1)
    (hc : c ≤ n * p)
    (hab : n * p + c ≤ ∑ y ∈ n.properDivisors, y + (n + p * ∑ y ∈ n.properDivisors, y)) :
    (n * p).Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ :=
    interval_properDivisors_mul_prime hn hp hpn h₁ hgap hpg hnc hc hab
  exact ⟨Nat.mul_pos hn hp.pos, t, ht, hsum⟩

/-- Complement symmetry: if `z` is a subset sum of `s`, so is `∑ s − z`. -/
lemma sub_mem_subsetSums {s : Finset ℕ} {z : ℕ} (hz : z ∈ subsetSums s) :
    ∑ y ∈ s, y - z ∈ subsetSums s := by
  obtain ⟨t, ht, rfl⟩ := hz
  refine ⟨s \ t, sdiff_subset, ?_⟩
  have h := sum_sdiff ht (f := fun x => x)
  omega

/-- **Gaps propagate.** Abstract form: a set `S ∋ total` closed under `z ↦ total − z`, containing
an old set `S₀` (gaps `≤ g` on `[0, s]`, `c ≤ s`) and the interval `[c, total − c]`, has gaps `≤ g`
on `[0, total]`. -/
theorem gap_of_interval {S S₀ : Set ℕ} {c g s total : ℕ} (hg : 1 ≤ g) (hcs : c ≤ s)
    (hsub : ∀ z ∈ S₀, z ∈ S) (htot : total ∈ S) (hsymm : ∀ z ∈ S, z ≤ total → total - z ∈ S)
    (hst : s ≤ total)
    (hgap : ∀ x < s, ∃ z ∈ S₀, x < z ∧ z ≤ x + g ∧ z ≤ s)
    (hint : ∀ x, c ≤ x → x + c ≤ total → x ∈ S) :
    ∀ x < total, ∃ z ∈ S, x < z ∧ z ≤ x + g ∧ z ≤ total := by
  intro x hx
  rcases Nat.lt_or_ge x c with h | h
  · obtain ⟨z, hz, h1, h2, h3⟩ := hgap x (by omega)
    exact ⟨z, hsub z hz, h1, h2, by omega⟩
  · rcases Nat.lt_or_ge (x + 1 + c) (total + 1) with h' | h'
    · exact ⟨x + 1, hint _ (by omega) (by omega), by omega, by omega, by omega⟩
    · -- top end: reflect
      rcases Nat.lt_or_ge total (x + g + 1) with h'' | h''
      · exact ⟨total, htot, hx, by omega, le_rfl⟩
      · obtain ⟨w, hw, h1, h2, h3⟩ := hgap (total - x - g - 1) (by omega)
        refine ⟨total - w, hsymm w (hsub w hw) (by omega), by omega, by omega, by omega⟩

/-- Gaps of `SS(D(n p))`: under the hypotheses of the prime step (plus `1 ≤ g`), the subset sums
of `D(n p)` again have gaps at most `g` on `[0, ∑ D(n p)]`, so the step can be iterated. -/
theorem gap_properDivisors_mul_prime {n p c g : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) (hg : 1 ≤ g)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ n.properDivisors, y → x ∈ subsetSums n.properDivisors)
    (hgap : ∀ x < ∑ y ∈ n.properDivisors, y, ∃ z ∈ subsetSums n.properDivisors,
      x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ n.properDivisors, y)
    (hpg : p * g + 2 * c ≤ ∑ y ∈ n.properDivisors, y + 1)
    (hnc : n + 2 * c ≤ (p + 1) * ∑ y ∈ n.properDivisors, y + 1) :
    ∀ x < ∑ y ∈ (n * p).properDivisors, y, ∃ z ∈ subsetSums (n * p).properDivisors,
      x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (n * p).properDivisors, y := by
  have hsum := sum_properDivisors_mul_prime' hn hp hpn
  have hDsub : n.properDivisors ⊆ (n * p).properDivisors := by
    rw [properDivisors_mul_prime hn hp hpn]; exact subset_union_left
  have hp1 : 1 ≤ p := hp.one_lt.le
  have hcs : c ≤ ∑ y ∈ n.properDivisors, y := by
    have : g ≤ p * g := Nat.le_mul_of_pos_left g hp.pos
    omega
  refine gap_of_interval (S₀ := subsetSums n.properDivisors) hg hcs
    (fun z hz => subsetSums_mono hDsub hz) (sum_mem_subsetSums _)
    (fun z hz _ => sub_mem_subsetSums hz) (by rw [hsum]; omega) hgap ?_
  intro x hx1 hx2
  exact interval_properDivisors_mul_prime hn hp hpn h₁ hgap hpg hnc hx1 (by rw [← hsum]; exact hx2)

/-- Sanity check of the divisor split: `D(15 · 7) = D 15 ∪ {15} ∪ 7 · D 15`. -/
example : (15 * 7).properDivisors =
    (15 : ℕ).properDivisors ∪ insert 15 ((15 : ℕ).properDivisors.image (7 * ·)) :=
  properDivisors_mul_prime (by norm_num) (by norm_num) (by norm_num)

end ErdosResearch.SubsetSumPrimeStep
