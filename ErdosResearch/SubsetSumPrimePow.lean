module

public import ErdosResearch.SubsetSumPrimeStep

@[expose] public section

/-!
# The prime-power step for subset sums of proper divisors

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 55).

Session 54 proved the prime step `D(n p) = D n ∪ {n} ∪ p · D n` (`D = properDivisors`). For a prime
power the right split is

  `D(n p^(e+1)) = D n ∪ ({n} ∪ p · D(n p^e))`,  for a prime `p ∤ n`,

so the scaled part is `p` times the *previous* level, not `p` times `D n`. The glue only needs
an interval `[c, s − c]` for the base part `D n` and gaps `≤ g` for the scaled part. Since the gap
bound `g` is preserved (`gap_of_interval`), the session-54 conditions

  `p g + 2c ≤ s + 1`  and  `n + 2c ≤ (p + 1) s + 1`  (`s = ∑ D n`)

give, for **every** exponent `e`, that `SS(D(n p^e)) ⊇ [c, ∑ D(n p^e) − c]` with gaps `≤ g`
(`interval_properDivisors_mul_prime_pow`). Hence `n p^e` is pseudoperfect as soon as
`c ≤ n p^e` and `n p^e + c ≤ ∑ D(n p^e)` (`pseudoperfect_mul_prime_pow_of_interval`).

Elementary; a building block for a Lean version of the family search, not a new result.
-/

namespace ErdosResearch.SubsetSumPrimePow

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumPrimeStep

/-- Abstract glue step: an interval part `A`, a new element `n` and a scaled copy `p · B` of a set
`B` with gaps `≤ g`. -/
theorem interval_union_insert_image {A B : Finset ℕ} {n p c g : ℕ} (hp : 0 < p)
    (hnot : n ∉ B.image (p * ·)) (hdisj : Disjoint A (insert n (B.image (p * ·))))
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ A, y → x ∈ subsetSums A)
    (hgap : ∀ x < ∑ y ∈ B, y, ∃ z ∈ subsetSums B, x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ B, y)
    (hpg : p * g + 2 * c ≤ ∑ y ∈ A, y + 1)
    (hnc : n + 2 * c ≤ p * ∑ y ∈ B, y + ∑ y ∈ A, y + 1)
    {m : ℕ} (hm1 : c ≤ m) (hm2 : m + c ≤ ∑ y ∈ A, y + (n + p * ∑ y ∈ B, y)) :
    m ∈ subsetSums (A ∪ insert n (B.image (p * ·))) := by
  set s := ∑ y ∈ A, y with hs
  set t := ∑ y ∈ B, y with ht
  set E := B.image (p * ·) with hE
  have hsumE : ∑ y ∈ E, y = p * t := by
    rw [hE, sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp h), mul_sum]
  have hsum2 : ∑ y ∈ insert n E, y = n + p * t := by rw [sum_insert hnot, hsumE]
  have hscaled : ∀ x < p * t, ∃ b ∈ subsetSums E, x < b ∧ b ≤ x + p * g ∧ b ≤ p * t := by
    intro x hx
    have hq : x / p < t := by
      rw [Nat.div_lt_iff_lt_mul hp]; linarith
    obtain ⟨z, hz, hzq, hzg, hzs⟩ := hgap _ hq
    refine ⟨p * z, subsetSums_image_mul p hz, ?_, ?_, Nat.mul_le_mul_left p hzs⟩
    · calc x < p * (x / p + 1) := Nat.lt_mul_div_succ x hp
        _ ≤ p * z := Nat.mul_le_mul_left p hzq
    · have h1 : p * z ≤ p * (x / p) + p * g := by
        rw [← mul_add]; exact Nat.mul_le_mul_left p hzg
      have h2 : p * (x / p) ≤ x := Nat.mul_div_le x p
      omega
  have hEsub : E ⊆ insert n E := subset_insert n E
  have hshift : ∀ b ∈ subsetSums E, n + b ∈ subsetSums (insert n E) := by
    intro b hb
    have h := subsetSums_union (s₁ := {n}) (s₂ := E) (by simpa using hnot)
      (sum_mem_subsetSums {n}) hb
    rw [sum_singleton, ← insert_eq] at h
    exact h
  have h₂ : ∀ x < ∑ y ∈ insert n E, y, ∃ b ∈ subsetSums (insert n E),
      x < b ∧ b ≤ ∑ y ∈ insert n E, y ∧ b + 2 * c ≤ x + s + 1 := by
    rw [hsum2]
    intro x hx
    rcases Nat.lt_or_ge x (p * t) with h | h
    · obtain ⟨b, hb, hxb, hbg, hbs⟩ := hscaled x h
      exact ⟨b, subsetSums_mono hEsub hb, hxb, by omega, by omega⟩
    · rcases Nat.lt_or_ge x n with h' | h'
      · refine ⟨n, ?_, h', by omega, by omega⟩
        simpa using hshift 0 (zero_mem_subsetSums E)
      · obtain ⟨b, hb, hxb, hbg, hbs⟩ := hscaled (x - n) (by omega)
        exact ⟨n + b, hshift b hb, by omega, by omega, by omega⟩
  exact glue_subsetSums hdisj h₁ h₂ hm1 (by rw [hsum2]; exact hm2)

/-- `D(n p^(e+1)) = D n ∪ insert n (p · D(n p^e))` for a prime `p ∤ n`, `n > 0`. -/
theorem properDivisors_mul_prime_pow_succ {n p : ℕ} (e : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) :
    (n * p ^ (e + 1)).properDivisors =
      n.properDivisors ∪ insert n ((n * p ^ e).properDivisors.image (p * ·)) := by
  have hp2 := hp.two_le
  have hpe : 0 < p ^ e := pow_pos hp.pos e
  have hsplit : n * p ^ (e + 1) = p * (n * p ^ e) := by ring
  ext d
  simp only [mem_union, mem_insert, mem_image, Nat.mem_properDivisors]
  constructor
  · rintro ⟨hd, hlt⟩
    by_cases hpd : p ∣ d
    · obtain ⟨f, rfl⟩ := hpd
      rw [hsplit] at hd hlt
      exact Or.inr (Or.inr ⟨f, ⟨Nat.dvd_of_mul_dvd_mul_left hp.pos hd,
        Nat.lt_of_mul_lt_mul_left hlt⟩, rfl⟩)
    · have hcop : Nat.Coprime d (p ^ (e + 1)) :=
        (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).2 hpd)).pow_right _
      have hdn : d ∣ n := hcop.dvd_of_dvd_mul_right hd
      rcases Nat.lt_or_ge d n with h | h
      · exact Or.inl ⟨hdn, h⟩
      · exact Or.inr (Or.inl (le_antisymm (Nat.le_of_dvd hn hdn) h))
  · have hlt1 : n < n * p ^ (e + 1) := by
      have h1 : n ≤ n * p ^ e := Nat.le_mul_of_pos_right n hpe
      have h2 : 2 * (n * p ^ e) ≤ p * (n * p ^ e) := Nat.mul_le_mul_right _ hp2
      rw [hsplit]; omega
    rintro (⟨hd, hlt⟩ | rfl | ⟨f, ⟨hf, hlt⟩, rfl⟩)
    · exact ⟨hd.mul_right _, by omega⟩
    · exact ⟨dvd_mul_right d _, hlt1⟩
    · rw [hsplit]
      exact ⟨Nat.mul_dvd_mul_left p hf, Nat.mul_lt_mul_of_pos_left hlt hp.pos⟩

lemma not_mem_image_of_not_dvd {B : Finset ℕ} {n p : ℕ} (hpn : ¬ p ∣ n) :
    n ∉ B.image (p * ·) := by
  intro h
  obtain ⟨e, _, he⟩ := mem_image.1 h
  exact hpn ⟨e, he.symm⟩

lemma disjoint_properDivisors {B : Finset ℕ} {n p : ℕ} (hpn : ¬ p ∣ n) :
    Disjoint n.properDivisors (insert n (B.image (p * ·))) := by
  rw [disjoint_insert_right]
  refine ⟨fun h => (Nat.mem_properDivisors.1 h).2.false, ?_⟩
  rw [disjoint_left]
  intro d hd hd'
  obtain ⟨e, _, rfl⟩ := mem_image.1 hd'
  exact hpn ((dvd_mul_right p e).trans (Nat.mem_properDivisors.1 hd).1)

/-- Sum of `D(n p^(e+1))` in terms of `∑ D n` and `∑ D(n p^e)`. -/
theorem sum_properDivisors_mul_prime_pow_succ {n p : ℕ} (e : ℕ) (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) :
    ∑ x ∈ (n * p ^ (e + 1)).properDivisors, x =
      ∑ x ∈ n.properDivisors, x + (n + p * ∑ x ∈ (n * p ^ e).properDivisors, x) := by
  rw [properDivisors_mul_prime_pow_succ e hn hp hpn, sum_union (disjoint_properDivisors hpn),
    sum_insert (not_mem_image_of_not_dvd hpn),
    sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left hp.pos h), mul_sum]

lemma properDivisors_subset_mul_pow {n p : ℕ} (e : ℕ) (hp : p.Prime) :
    n.properDivisors ⊆ (n * p ^ e).properDivisors := by
  intro d hd
  rw [Nat.mem_properDivisors] at hd ⊢
  refine ⟨hd.1.mul_right _, ?_⟩
  have : n ≤ n * p ^ e := Nat.le_mul_of_pos_right n (pow_pos hp.pos e)
  omega

/-- **The prime-power step.** Under the session-54 conditions on `(n, p, c, g)`, for every `e` the
subset sums of `D(n p^e)` cover `[c, ∑ D(n p^e) − c]` and have gaps at most `g`. -/
theorem interval_properDivisors_mul_prime_pow {n p c g : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) (hg : 1 ≤ g)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ n.properDivisors, y → x ∈ subsetSums n.properDivisors)
    (hgap : ∀ x < ∑ y ∈ n.properDivisors, y, ∃ z ∈ subsetSums n.properDivisors,
      x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ n.properDivisors, y)
    (hpg : p * g + 2 * c ≤ ∑ y ∈ n.properDivisors, y + 1)
    (hnc : n + 2 * c ≤ (p + 1) * ∑ y ∈ n.properDivisors, y + 1) (e : ℕ) :
    (∀ x, c ≤ x → x + c ≤ ∑ y ∈ (n * p ^ e).properDivisors, y →
        x ∈ subsetSums (n * p ^ e).properDivisors) ∧
      (∀ x < ∑ y ∈ (n * p ^ e).properDivisors, y, ∃ z ∈ subsetSums (n * p ^ e).properDivisors,
        x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (n * p ^ e).properDivisors, y) := by
  induction e with
  | zero => simpa using ⟨h₁, hgap⟩
  | succ e ih =>
    obtain ⟨-, hgapB⟩ := ih
    have hmono : ∑ y ∈ n.properDivisors, y ≤ ∑ y ∈ (n * p ^ e).properDivisors, y :=
      sum_le_sum_of_subset (properDivisors_subset_mul_pow e hp)
    have hnc' : n + 2 * c ≤ p * ∑ y ∈ (n * p ^ e).properDivisors, y +
        ∑ y ∈ n.properDivisors, y + 1 := by
      have : (p + 1) * ∑ y ∈ n.properDivisors, y =
          p * ∑ y ∈ n.properDivisors, y + ∑ y ∈ n.properDivisors, y := by ring
      have := Nat.mul_le_mul_left p hmono
      omega
    have hsum := sum_properDivisors_mul_prime_pow_succ e hn hp hpn
    have hstep : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ (n * p ^ (e + 1)).properDivisors, y →
        x ∈ subsetSums (n * p ^ (e + 1)).properDivisors := by
      intro x hx1 hx2
      rw [properDivisors_mul_prime_pow_succ e hn hp hpn]
      exact interval_union_insert_image hp.pos (not_mem_image_of_not_dvd hpn)
        (disjoint_properDivisors hpn) h₁ hgapB hpg hnc' hx1 (by rw [← hsum]; exact hx2)
    refine ⟨hstep, ?_⟩
    have hcs : c ≤ ∑ y ∈ n.properDivisors, y := by
      have : g ≤ p * g := Nat.le_mul_of_pos_left g hp.pos
      omega
    exact gap_of_interval (S₀ := subsetSums n.properDivisors) hg hcs
      (fun z hz => subsetSums_mono (properDivisors_subset_mul_pow (e + 1) hp) hz)
      (sum_mem_subsetSums _) (fun z hz _ => sub_mem_subsetSums hz)
      (sum_le_sum_of_subset (properDivisors_subset_mul_pow (e + 1) hp)) hgap hstep

/-- Corollary: under the session-54 conditions, `n p^e` is pseudoperfect as soon as it lies in
`[c, ∑ D(n p^e) − c]`. -/
theorem pseudoperfect_mul_prime_pow_of_interval {n p c g : ℕ} (hn : 0 < n) (hp : p.Prime)
    (hpn : ¬ p ∣ n) (hg : 1 ≤ g)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ n.properDivisors, y → x ∈ subsetSums n.properDivisors)
    (hgap : ∀ x < ∑ y ∈ n.properDivisors, y, ∃ z ∈ subsetSums n.properDivisors,
      x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ n.properDivisors, y)
    (hpg : p * g + 2 * c ≤ ∑ y ∈ n.properDivisors, y + 1)
    (hnc : n + 2 * c ≤ (p + 1) * ∑ y ∈ n.properDivisors, y + 1) (e : ℕ)
    (hc : c ≤ n * p ^ e) (hab : n * p ^ e + c ≤ ∑ y ∈ (n * p ^ e).properDivisors, y) :
    (n * p ^ e).Pseudoperfect := by
  obtain ⟨t, ht, hsum⟩ :=
    (interval_properDivisors_mul_prime_pow hn hp hpn hg h₁ hgap hpg hnc e).1 _ hc hab
  exact ⟨Nat.mul_pos hn (pow_pos hp.pos e), t, ht, hsum⟩

end ErdosResearch.SubsetSumPrimePow
