module

public import ErdosResearch.SubsetSumCert

@[expose] public section

/-!
# The exponent-raising step for subset sums of proper divisors

Reference: <https://www.erdosproblems.com/470>. See `notes/erdos-470.md` (session 56).

The prime-power step (`SubsetSumPrimePow.lean`) adds a *new* prime `p` to a base `n` whose proper
divisors have a certified interval. It cannot help when the base must already contain a high power
of a prime (the search's prefixes `3^10·…`): a bitset for such a base is out of reach. The other split

  `D(m p^(e+1)) = D(m p^e) ∪ ({m p^e} ∪ p^(e+1) · D m)`,  for a prime `p ∤ m`,

raises the exponent of `p` by one. Its interval part is the previous level `D(m p^e)` and its gap part
is the small set `D m`, scaled by `p^(e+1)`. With an interval `[c, ∑ D(m p^e) − c]` and gaps `≤ g` on
`D(m p^e)`, and gaps `≤ gB` on `D m`, the conditions

  `p^(e+1) gB + 2c ≤ ∑ D(m p^e) + 1`  and  `m p^e + 2c ≤ p^(e+1) ∑ D m + ∑ D(m p^e) + 1`

give the interval `[c, ∑ D(m p^(e+1)) − c]` with gaps `≤ g` again (`interval_properDivisors_raise`),
so the step iterates (`interval_properDivisors_raise_iter`). Numerically (`scripts/raise_step_probe.py`)
it is sound on 184 small cases and raises the chain probe's coverage of random `ω = 6` candidates from
14/57 to 37/57 (bitset bases up to `10^6`; 0/57 to 15/57 with bases up to `2·10^4`).

`pseudoperfect_raise_of_cert` makes it decidable: bitsets for the small sets `D(m p^e₀)` and `D m`, then
`k` raising steps whose conditions use only the recursive sum `raiseSum` (no divisors of the large
number). Example: `pseudoperfect_325_mul_three_pow_six` (`3^6 · 5^2 · 13`, base `975`, five raises).
`not_weird_mul_prime_of_raise_cert` adds a last prime `q`; instance `not_weird_3969405_mul_prime`: no
`3^8 · 5 · 11^2 · q` (`q` prime) is weird, from the bitsets of `D 5445` and `D 605` and six raises.

Elementary; a building block for a Lean version of the family search, not a new result.
-/

namespace ErdosResearch.SubsetSumRaise

open Finset ErdosResearch.SubsetSumGlue ErdosResearch.SubsetSumPrimeStep
  ErdosResearch.SubsetSumPrimePow ErdosResearch.SubsetSumCert

lemma prime_dvd_of_pow_succ_dvd {m p e f : ℕ} (hp : p.Prime) (h : p ^ (e + 1) * f ∣ m * p ^ e) :
    p ∣ m := by
  have h1 : p ^ e * (p * f) ∣ p ^ e * m := by
    have : p ^ (e + 1) * f = p ^ e * (p * f) := by ring
    rw [← this, mul_comm (p ^ e) m]; exact h
  exact (dvd_mul_right p f).trans (Nat.dvd_of_mul_dvd_mul_left (pow_pos hp.pos e) h1)

/-- `D(m p^(e+1)) = D(m p^e) ∪ insert (m p^e) (p^(e+1) · D m)` for a prime `p`, `m > 0` (the union is
disjoint when `p ∤ m`, see `raise_disjoint`). -/
theorem properDivisors_raise {m p : ℕ} (e : ℕ) (hm : 0 < m) (hp : p.Prime) :
    (m * p ^ (e + 1)).properDivisors =
      (m * p ^ e).properDivisors ∪ insert (m * p ^ e) (m.properDivisors.image (p ^ (e + 1) * ·)) := by
  have hpe : 0 < p ^ e := pow_pos hp.pos e
  have hlt : m * p ^ e < m * p ^ (e + 1) := by
    rw [pow_succ]
    have : m * p ^ e * 2 ≤ m * (p ^ e * p) := by
      rw [← mul_assoc]; exact Nat.mul_le_mul_left _ hp.two_le
    have : 0 < m * p ^ e := Nat.mul_pos hm hpe
    omega
  ext d
  simp only [mem_union, mem_insert, mem_image, Nat.mem_properDivisors]
  constructor
  · rintro ⟨hd, hdlt⟩
    obtain ⟨d₁, d₂, h₁, h₂, rfl⟩ := Nat.dvd_mul.1 hd
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 h₂
    rcases Nat.lt_or_ge i (e + 1) with hie | hie
    · have hdv : d₁ * p ^ i ∣ m * p ^ e :=
        Nat.mul_dvd_mul h₁ (pow_dvd_pow p (by omega))
      rcases Nat.lt_or_ge (d₁ * p ^ i) (m * p ^ e) with h | h
      · exact Or.inl ⟨hdv, h⟩
      · exact Or.inr (Or.inl (le_antisymm (Nat.le_of_dvd (Nat.mul_pos hm hpe) hdv) h))
    · obtain rfl : i = e + 1 := le_antisymm hi hie
      refine Or.inr (Or.inr ⟨d₁, ⟨h₁, ?_⟩, by ring⟩)
      exact Nat.lt_of_mul_lt_mul_right hdlt
  · rintro (⟨hd, hdlt⟩ | rfl | ⟨f, ⟨hf, hflt⟩, rfl⟩)
    · exact ⟨hd.trans (Nat.mul_dvd_mul_left m (pow_dvd_pow p (Nat.le_succ e))), by omega⟩
    · exact ⟨Nat.mul_dvd_mul_left m (pow_dvd_pow p (Nat.le_succ e)), hlt⟩
    · refine ⟨?_, ?_⟩
      · rw [mul_comm m]; exact Nat.mul_dvd_mul_left _ hf
      · rw [mul_comm m]; exact Nat.mul_lt_mul_of_pos_left hflt (pow_pos hp.pos _)

lemma raise_not_mem {m p : ℕ} (e : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    m * p ^ e ∉ m.properDivisors.image (p ^ (e + 1) * ·) := by
  intro h
  obtain ⟨f, _, hf⟩ := mem_image.1 h
  exact hpm (prime_dvd_of_pow_succ_dvd hp (by rw [hf]))

lemma raise_disjoint {m p : ℕ} (e : ℕ) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    Disjoint (m * p ^ e).properDivisors
      (insert (m * p ^ e) (m.properDivisors.image (p ^ (e + 1) * ·))) := by
  rw [disjoint_insert_right]
  refine ⟨fun h => (Nat.mem_properDivisors.1 h).2.false, ?_⟩
  rw [disjoint_left]
  intro d hd hd'
  obtain ⟨f, _, rfl⟩ := mem_image.1 hd'
  exact hpm (prime_dvd_of_pow_succ_dvd hp (Nat.mem_properDivisors.1 hd).1)

/-- Sum of `D(m p^(e+1))` in terms of `∑ D(m p^e)` and `∑ D m`. -/
theorem sum_properDivisors_raise {m p : ℕ} (e : ℕ) (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) :
    ∑ x ∈ (m * p ^ (e + 1)).properDivisors, x =
      ∑ x ∈ (m * p ^ e).properDivisors, x + (m * p ^ e + p ^ (e + 1) * ∑ x ∈ m.properDivisors, x) := by
  rw [properDivisors_raise e hm hp, sum_union (raise_disjoint e hp hpm),
    sum_insert (raise_not_mem e hp hpm),
    sum_image (fun x _ y _ h => Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h), mul_sum]

/-- **The exponent-raising step.** Interval `[c, ∑ D(m p^e) − c]` and gaps `≤ g` on `D(m p^e)`, plus
gaps `≤ gB` on `D m`, give the interval and the gap bound `g` on `D(m p^(e+1))`. -/
theorem interval_properDivisors_raise {m p e c g gB : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hg : 1 ≤ g)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ (m * p ^ e).properDivisors, y →
      x ∈ subsetSums (m * p ^ e).properDivisors)
    (hgapA : ∀ x < ∑ y ∈ (m * p ^ e).properDivisors, y,
      ∃ z ∈ subsetSums (m * p ^ e).properDivisors,
        x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (m * p ^ e).properDivisors, y)
    (hgapB : ∀ x < ∑ y ∈ m.properDivisors, y, ∃ z ∈ subsetSums m.properDivisors,
      x < z ∧ z ≤ x + gB ∧ z ≤ ∑ y ∈ m.properDivisors, y)
    (hpg : p ^ (e + 1) * gB + 2 * c ≤ ∑ y ∈ (m * p ^ e).properDivisors, y + 1)
    (hnc : m * p ^ e + 2 * c ≤
      p ^ (e + 1) * ∑ y ∈ m.properDivisors, y + ∑ y ∈ (m * p ^ e).properDivisors, y + 1) :
    (∀ x, c ≤ x → x + c ≤ ∑ y ∈ (m * p ^ (e + 1)).properDivisors, y →
        x ∈ subsetSums (m * p ^ (e + 1)).properDivisors) ∧
      (∀ x < ∑ y ∈ (m * p ^ (e + 1)).properDivisors, y,
        ∃ z ∈ subsetSums (m * p ^ (e + 1)).properDivisors,
          x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (m * p ^ (e + 1)).properDivisors, y) := by
  have hsum := sum_properDivisors_raise e hm hp hpm
  have hsub : (m * p ^ e).properDivisors ⊆ (m * p ^ (e + 1)).properDivisors := by
    rw [properDivisors_raise e hm hp]; exact subset_union_left
  have hstep : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ (m * p ^ (e + 1)).properDivisors, y →
      x ∈ subsetSums (m * p ^ (e + 1)).properDivisors := by
    intro x hx1 hx2
    rw [properDivisors_raise e hm hp]
    exact interval_union_insert_image (pow_pos hp.pos _) (raise_not_mem e hp hpm)
      (raise_disjoint e hp hpm) h₁ hgapB hpg hnc hx1 (by rw [← hsum]; exact hx2)
  refine ⟨hstep, ?_⟩
  have hcs : c ≤ ∑ y ∈ (m * p ^ e).properDivisors, y := by omega
  exact gap_of_interval (S₀ := subsetSums (m * p ^ e).properDivisors) hg hcs
    (fun z hz => subsetSums_mono hsub hz) (sum_mem_subsetSums _)
    (fun z hz _ => sub_mem_subsetSums hz) (sum_le_sum_of_subset hsub) hgapA hstep

/-- Iterated raising: from `D(m p^e₀)` to `D(m p^(e₀ + k))`, if the two conditions hold at every
intermediate level. -/
theorem interval_properDivisors_raise_iter {m p e₀ c g gB : ℕ} (hm : 0 < m) (hp : p.Prime)
    (hpm : ¬ p ∣ m) (hg : 1 ≤ g)
    (h₁ : ∀ x, c ≤ x → x + c ≤ ∑ y ∈ (m * p ^ e₀).properDivisors, y →
      x ∈ subsetSums (m * p ^ e₀).properDivisors)
    (hgapA : ∀ x < ∑ y ∈ (m * p ^ e₀).properDivisors, y,
      ∃ z ∈ subsetSums (m * p ^ e₀).properDivisors,
        x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (m * p ^ e₀).properDivisors, y)
    (hgapB : ∀ x < ∑ y ∈ m.properDivisors, y, ∃ z ∈ subsetSums m.properDivisors,
      x < z ∧ z ≤ x + gB ∧ z ≤ ∑ y ∈ m.properDivisors, y)
    (k : ℕ)
    (hcond : ∀ j < k,
      p ^ (e₀ + j + 1) * gB + 2 * c ≤ ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y + 1 ∧
      m * p ^ (e₀ + j) + 2 * c ≤ p ^ (e₀ + j + 1) * ∑ y ∈ m.properDivisors, y +
        ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y + 1) :
    (∀ x, c ≤ x → x + c ≤ ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y →
        x ∈ subsetSums (m * p ^ (e₀ + k)).properDivisors) ∧
      (∀ x < ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y,
        ∃ z ∈ subsetSums (m * p ^ (e₀ + k)).properDivisors,
          x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y) := by
  induction k with
  | zero => exact ⟨h₁, hgapA⟩
  | succ k ih =>
    obtain ⟨hI, hG⟩ := ih (fun j hj => hcond j (by omega))
    obtain ⟨c1, c2⟩ := hcond k (by omega)
    exact interval_properDivisors_raise hm hp hpm hg hI hG hgapB c1 c2

/-- Sanity check of the split: `D(5 · 3^2) = D(5 · 3) ∪ {15} ∪ 9 · D 5`. -/
example : (5 * 3 ^ 2).properDivisors =
    (5 * 3 ^ 1).properDivisors ∪ insert (5 * 3 ^ 1) ((5 : ℕ).properDivisors.image (3 ^ 2 * ·)) :=
  properDivisors_raise 1 (by norm_num) (by norm_num)

/-! ### A decidable certificate for a chain of raises -/

/-- `∑ D(m p^(e₀ + j))` computed from `S0 = ∑ D(m p^e₀)` and `SB = ∑ D m` by `sum_properDivisors_raise`. -/
def raiseSum (m p e₀ SB S0 : ℕ) : ℕ → ℕ
  | 0 => S0
  | j + 1 => raiseSum m p e₀ SB S0 j + (m * p ^ (e₀ + j) + p ^ (e₀ + j + 1) * SB)

theorem raiseSum_eq {m p e₀ SB S0 : ℕ} (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m)
    (h0 : ∑ y ∈ (m * p ^ e₀).properDivisors, y = S0) (hB : ∑ y ∈ m.properDivisors, y = SB) :
    ∀ j, ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y = raiseSum m p e₀ SB S0 j
  | 0 => by rw [raiseSum, add_zero]; exact h0
  | j + 1 => by
      rw [← add_assoc, sum_properDivisors_raise (e₀ + j) hm hp hpm, raiseSum,
        raiseSum_eq hm hp hpm h0 hB j, hB]

/-- The two raising conditions at every level `j < k`, as a Boolean. -/
def raiseOK (m p e₀ c gB SB S0 k : ℕ) : Bool :=
  (List.range k).all fun j =>
    decide (p ^ (e₀ + j + 1) * gB + 2 * c ≤ raiseSum m p e₀ SB S0 j + 1) &&
    decide (m * p ^ (e₀ + j) + 2 * c ≤ p ^ (e₀ + j + 1) * SB + raiseSum m p e₀ SB S0 j + 1)

/-- **Certified chain of raises.** Bitset certificates for `D(m p^e₀)` (interval `c`, gaps `g`) and for
`D m` (gaps `gB`), plus `raiseOK`, give the interval `[c, ∑ D − c]` and gaps `≤ g` on `D(m p^(e₀ + k))`,
whose sum is `raiseSum … k`. -/
theorem interval_raise_of_cert {m p e₀ c g gB k : ℕ} (lA lB : List ℕ)
    (hlA : lA.toFinset = (m * p ^ e₀).properDivisors) (hndA : lA.Nodup)
    (hI : intervalOK (ssBits lA) c lA.sum = true) (hG : gapOK (ssBits lA) g lA.sum = true)
    (hlB : lB.toFinset = m.properDivisors) (hndB : lB.Nodup)
    (hGB : gapOK (ssBits lB) gB lB.sum = true)
    (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (hg : 1 ≤ g)
    (hok : raiseOK m p e₀ c gB lB.sum lA.sum k = true) :
    ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y = raiseSum m p e₀ lB.sum lA.sum k ∧
    (∀ x, c ≤ x → x + c ≤ ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y →
        x ∈ subsetSums (m * p ^ (e₀ + k)).properDivisors) ∧
      (∀ x < ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y,
        ∃ z ∈ subsetSums (m * p ^ (e₀ + k)).properDivisors,
          x < z ∧ z ≤ x + g ∧ z ≤ ∑ y ∈ (m * p ^ (e₀ + k)).properDivisors, y) := by
  have hsA : ∑ y ∈ (m * p ^ e₀).properDivisors, y = lA.sum := by
    rw [← hlA, List.sum_toFinset _ hndA, List.map_id']
  have hsB : ∑ y ∈ m.properDivisors, y = lB.sum := by
    rw [← hlB, List.sum_toFinset _ hndB, List.map_id']
  have hmemA : ∀ x, (ssBits lA).testBit x = true → x ∈ subsetSums (m * p ^ e₀).properDivisors := by
    intro x hx; rw [← hlA]; exact mem_subsetSums_of_testBit lA hndA x hx
  have hmemB : ∀ x, (ssBits lB).testBit x = true → x ∈ subsetSums m.properDivisors := by
    intro x hx; rw [← hlB]; exact mem_subsetSums_of_testBit lB hndB x hx
  have hrs := raiseSum_eq hm hp hpm hsA hsB
  have hcond : ∀ j < k,
      p ^ (e₀ + j + 1) * gB + 2 * c ≤ ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y + 1 ∧
      m * p ^ (e₀ + j) + 2 * c ≤ p ^ (e₀ + j + 1) * ∑ y ∈ m.properDivisors, y +
        ∑ y ∈ (m * p ^ (e₀ + j)).properDivisors, y + 1 := by
    intro j hj
    simp only [raiseOK, List.all_eq_true, List.mem_range, Bool.and_eq_true,
      decide_eq_true_eq] at hok
    rw [hrs j, hsB]
    exact hok j hj
  refine ⟨hrs k, interval_properDivisors_raise_iter (gB := gB) hm hp hpm hg
    (fun x h1 h2 => hmemA x (testBit_of_intervalOK hI x h1 (by rw [hsA] at h2; exact h2)))
    (fun x hx => by
      rw [hsA] at hx ⊢
      obtain ⟨z, hz, h1, h2, h3⟩ := exists_testBit_of_gapOK hG x hx
      exact ⟨z, hmemA z hz, h1, h2, h3⟩)
    (fun x hx => by
      rw [hsB] at hx ⊢
      obtain ⟨z, hz, h1, h2, h3⟩ := exists_testBit_of_gapOK hGB x hx
      exact ⟨z, hmemB z hz, h1, h2, h3⟩)
    k hcond⟩

/-- Corollary: `m p^(e₀ + k)` is pseudoperfect when it lies in `[c, ∑ D − c]`. -/
theorem pseudoperfect_raise_of_cert {m p e₀ c g gB k : ℕ} (lA lB : List ℕ)
    (hlA : lA.toFinset = (m * p ^ e₀).properDivisors) (hndA : lA.Nodup)
    (hI : intervalOK (ssBits lA) c lA.sum = true) (hG : gapOK (ssBits lA) g lA.sum = true)
    (hlB : lB.toFinset = m.properDivisors) (hndB : lB.Nodup)
    (hGB : gapOK (ssBits lB) gB lB.sum = true)
    (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (hg : 1 ≤ g)
    (hok : raiseOK m p e₀ c gB lB.sum lA.sum k = true)
    (hc : c ≤ m * p ^ (e₀ + k)) (hab : m * p ^ (e₀ + k) + c ≤ raiseSum m p e₀ lB.sum lA.sum k) :
    (m * p ^ (e₀ + k)).Pseudoperfect := by
  obtain ⟨hrs, hI', -⟩ := interval_raise_of_cert lA lB hlA hndA hI hG hlB hndB hGB hm hp hpm hg hok
  obtain ⟨t, ht, hsum⟩ := hI' _ hc (by rw [hrs]; exact hab)
  exact ⟨Nat.mul_pos hm (pow_pos hp.pos _), t, ht, hsum⟩

/-- **Family decider after a chain of raises.** With the raise certificate for `n = m p^(e₀ + k)`
(`S = raiseSum … k = ∑ D n`), a prime `q ∤ n` gives no weird `n q` as soon as, whenever `n q` is
abundant, the prime-step conditions and the margin `n q + c ≤ ∑ D(n q)` hold. All of this is linear
in `q` once `S` is a numeral. -/
theorem not_weird_mul_prime_of_raise_cert {m p e₀ c g gB k q : ℕ} (lA lB : List ℕ)
    (hlA : lA.toFinset = (m * p ^ e₀).properDivisors) (hndA : lA.Nodup)
    (hI : intervalOK (ssBits lA) c lA.sum = true) (hG : gapOK (ssBits lA) g lA.sum = true)
    (hlB : lB.toFinset = m.properDivisors) (hndB : lB.Nodup)
    (hGB : gapOK (ssBits lB) gB lB.sum = true)
    (hm : 0 < m) (hp : p.Prime) (hpm : ¬ p ∣ m) (hg : 1 ≤ g)
    (hok : raiseOK m p e₀ c gB lB.sum lA.sum k = true)
    (hq : q.Prime) (hqn : ¬ q ∣ m * p ^ (e₀ + k))
    (hcov : let n := m * p ^ (e₀ + k); let S := raiseSum m p e₀ lB.sum lA.sum k;
      n * q < S + (n + q * S) →
        q * g + 2 * c ≤ S + 1 ∧ n + 2 * c ≤ (q + 1) * S + 1 ∧ c ≤ n * q ∧
          n * q + c ≤ S + (n + q * S)) :
    ¬ (m * p ^ (e₀ + k) * q).Weird := by
  rintro ⟨habund, hnot⟩
  obtain ⟨hrs, hI', hG'⟩ :=
    interval_raise_of_cert lA lB hlA hndA hI hG hlB hndB hGB hm hp hpm hg hok
  have hn : 0 < m * p ^ (e₀ + k) := Nat.mul_pos hm (pow_pos hp.pos _)
  have hsum1 := sum_properDivisors_mul_prime_pow_succ 0 hn hq hqn
  simp only [zero_add, pow_one, pow_zero, mul_one] at hsum1
  rw [hrs] at hsum1
  have hab : m * p ^ (e₀ + k) * q <
      raiseSum m p e₀ lB.sum lA.sum k + (m * p ^ (e₀ + k) + q * raiseSum m p e₀ lB.sum lA.sum k) := by
    have := habund
    unfold Nat.Abundant at this
    rw [hsum1] at this
    exact this
  obtain ⟨h1, h2, h3, h4⟩ := hcov hab
  apply hnot
  have h := pseudoperfect_mul_prime_pow_of_interval hn hq hqn hg hI' hG'
    (by rw [hrs]; exact h1) (by rw [hrs]; exact h2) 1 (by rw [pow_one]; exact h3)
    (by rw [pow_one, hsum1]; exact h4)
  simpa using h

/-- Proper divisors of `975 = 3 · 5^2 · 13` and of `325 = 5^2 · 13`. -/
def l975 : List ℕ := [1, 3, 5, 13, 15, 25, 39, 65, 75, 195, 325]
def l325 : List ℕ := [1, 5, 13, 25, 65]

theorem cert_975_raise :
    l975.toFinset = (325 * 3 ^ 1).properDivisors ∧ l975.Nodup ∧
      intervalOK (ssBits l975) 247 l975.sum = true ∧ gapOK (ssBits l975) 4 l975.sum = true ∧
      l325.toFinset = (325 : ℕ).properDivisors ∧ l325.Nodup ∧
      gapOK (ssBits l325) 21 l325.sum = true ∧
      raiseOK 325 3 1 247 21 l325.sum l975.sum 5 = true ∧
      325 * 3 ^ (1 + 5) + 247 ≤ raiseSum 325 3 1 l325.sum l975.sum 5 := by
  decide +kernel

/-- Example: `3^6 · 5^2 · 13 = 236925` is pseudoperfect, from the bitsets of `D 975` and `D 325` and
five raising steps (no bitset of the divisors of `236925`). -/
theorem pseudoperfect_325_mul_three_pow_six : (325 * 3 ^ (1 + 5)).Pseudoperfect := by
  obtain ⟨hlA, hndA, hI, hG, hlB, hndB, hGB, hok, hab⟩ := cert_975_raise
  exact pseudoperfect_raise_of_cert l975 l325 hlA hndA hI hG hlB hndB hGB (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) hok (by norm_num) hab

/-- Proper divisors of `5445 = 3^2 · 5 · 11^2` and of `605 = 5 · 11^2`. -/
def l5445 : List ℕ := [1, 3, 5, 9, 11, 15, 33, 45, 55, 99, 121, 165, 363, 495, 605, 1089, 1815]
def l605 : List ℕ := [1, 5, 11, 55, 121]

theorem cert_5445_raise :
    l5445.toFinset = (605 * 3 ^ 2).properDivisors ∧ l5445.Nodup ∧
      intervalOK (ssBits l5445) 23 l5445.sum = true ∧ gapOK (ssBits l5445) 2 l5445.sum = true ∧
      l605.toFinset = (605 : ℕ).properDivisors ∧ l605.Nodup ∧
      gapOK (ssBits l605) 49 l605.sum = true ∧
      raiseOK 605 3 2 23 49 l605.sum l5445.sum 6 = true ∧
      raiseSum 605 3 2 l605.sum l5445.sum 6 = 3883713 := by
  decide +kernel

/-- **A last-prime family with a high power of 3.** No `3^8 · 5 · 11^2 · q = 3969405 q` (`q` prime,
`q ∤ 3969405`) is weird: for `q ≥ 92` it is deficient; for smaller `q` it is pseudoperfect by six raises
of the exponent of 3 from the base `5445` (`c = 23`, `g = 2`, `gB = 49`) and the prime step for `q`. -/
theorem not_weird_3969405_mul_prime {q : ℕ} (hq : q.Prime) (hqn : ¬ q ∣ 605 * 3 ^ (2 + 6)) :
    ¬ (605 * 3 ^ (2 + 6) * q).Weird := by
  obtain ⟨hlA, hndA, hI, hG, hlB, hndB, hGB, hok, hS⟩ := cert_5445_raise
  have hq2 := hq.two_le
  refine not_weird_mul_prime_of_raise_cert l5445 l605 hlA hndA hI hG hlB hndB hGB (by norm_num)
    Nat.prime_three (by norm_num) (by norm_num) hok hq hqn ?_
  simp only [hS]
  norm_num
  intro hab
  refine ⟨by omega, by omega, by omega, by omega⟩

end ErdosResearch.SubsetSumRaise
