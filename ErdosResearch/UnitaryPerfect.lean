import Mathlib

/-!
# Erdős Problem 1052: unitary perfect numbers

Reference: <https://www.erdosproblems.com/1052> (prize: $10, Carlitz, Erdős and Subbarao,
as reported in Guy's *Unsolved problems in number theory*, B3).

A unitary divisor of `n` is a divisor `d ∣ n` with `Nat.Coprime d (n / d)`. A number `n ≥ 1` is
*unitary perfect* if it is the sum of its unitary divisors other than `n`. The open question is
whether there are only finitely many. Five are known: `6, 60, 90, 87360` and
`146361946186458562560000`.

`properUnitaryDivisors`, `IsUnitaryPerfect` and `erdos_1052_statement` are copied verbatim (as
definitions, not as `sorry`-ed theorems) from `FormalConjectures/ErdosProblems/1052.lean` in
google-deepmind/formal-conjectures, so that results proved here are about the same statement.

What is proved here (all already known mathematically; see `notes/erdos-1052.md`):
* `usigma_mul`: the sum of unitary divisors `σ*` is multiplicative on coprime arguments.
* `usigma_prime_pow`: `σ*(p ^ e) = 1 + p ^ e`.
* `even_of_isUnitaryPerfect`: every unitary perfect number is even.
* `eq_six_of_isUnitaryPerfect_of_card_primeFactors_le_two`: the only unitary perfect number with
  at most one odd prime factor is `6`.
* `isUnitaryPerfect_6`, `_60`, `_90`, `_87360`, `_146361946186458562560000`: the five known
  examples (the last two via multiplicativity, which keeps them fast).
-/

namespace ErdosResearch.Erdos1052

open Finset

/-! ## The statement, as in formal-conjectures -/

/-- A proper unitary divisor of $n$ is a divisor $d$ of $n$
such that $d$ is coprime to $n/d$, and $d < n$. -/
def properUnitaryDivisors (n : ℕ) : Finset ℕ :=
  {d ∈ Finset.Ico 1 n | d ∣ n ∧ d.Coprime (n / d)}

/-- A number $n > 0$ is a unitary perfect number if it is the sum of its proper unitary
divisors. -/
def IsUnitaryPerfect (n : ℕ) : Prop :=
  ∑ i ∈ properUnitaryDivisors n, i = n ∧ 0 < n

/-- Erdős Problem 1052 (open): are there only finitely many unitary perfect numbers? -/
def erdos_1052_statement : Prop :=
  {n | IsUnitaryPerfect n}.Finite

/-! ## The sum of unitary divisors -/

/-- The unitary divisors of `n`. -/
def unitaryDivisors (n : ℕ) : Finset ℕ :=
  n.divisors.filter fun d => d.Coprime (n / d)

/-- `σ*(n)`, the sum of the unitary divisors of `n`. -/
def usigma (n : ℕ) : ℕ :=
  ∑ d ∈ unitaryDivisors n, d

lemma mem_unitaryDivisors {n d : ℕ} :
    d ∈ unitaryDivisors n ↔ d ∣ n ∧ d.Coprime (n / d) ∧ n ≠ 0 := by
  simp [unitaryDivisors, and_assoc, and_comm]

lemma unitaryDivisors_eq_insert {n : ℕ} (hn : 0 < n) :
    unitaryDivisors n = insert n (properUnitaryDivisors n) := by
  ext d
  simp only [mem_unitaryDivisors, properUnitaryDivisors, mem_insert, mem_filter, mem_Ico]
  constructor
  · rintro ⟨hd, hc, -⟩
    by_cases h : d = n
    · exact Or.inl h
    · have hle := Nat.le_of_dvd hn hd
      have hpos : 0 < d := Nat.pos_of_dvd_of_pos hd hn
      exact Or.inr ⟨⟨hpos, lt_of_le_of_ne hle h⟩, hd, hc⟩
  · rintro (rfl | ⟨-, hd, hc⟩)
    · simp [Nat.div_self hn, hn.ne']
    · exact ⟨hd, hc, hn.ne'⟩

lemma n_notMem_properUnitaryDivisors (n : ℕ) : n ∉ properUnitaryDivisors n := by
  simp [properUnitaryDivisors]

/-- `n` is unitary perfect iff `σ*(n) = 2 n` and `n > 0`. -/
lemma isUnitaryPerfect_iff {n : ℕ} : IsUnitaryPerfect n ↔ usigma n = 2 * n ∧ 0 < n := by
  constructor
  · rintro ⟨h, hn⟩
    refine ⟨?_, hn⟩
    rw [usigma, unitaryDivisors_eq_insert hn,
      sum_insert (n_notMem_properUnitaryDivisors n), h]
    ring
  · rintro ⟨h, hn⟩
    refine ⟨?_, hn⟩
    rw [usigma, unitaryDivisors_eq_insert hn,
      sum_insert (n_notMem_properUnitaryDivisors n)] at h
    omega

/-! ## Multiplicativity -/

/-- `σ*` is multiplicative on coprime arguments. -/
theorem usigma_mul {a b : ℕ} (hab : a.Coprime b) :
    usigma (a * b) = usigma a * usigma b := by
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · simp [usigma, unitaryDivisors]
  rcases Nat.eq_zero_or_pos b with rfl | hb
  · simp [usigma, unitaryDivisors]
  rw [usigma, usigma, usigma, sum_mul_sum, ← sum_product']
  symm
  refine sum_nbij' (fun x => x.1 * x.2) (fun d => (d.gcd a, d.gcd b)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨x, y⟩ hxy
    simp only [mem_product, mem_unitaryDivisors] at hxy ⊢
    obtain ⟨⟨hx, hxc, -⟩, ⟨hy, hyc, -⟩⟩ := hxy
    have hdiv : a * b / (x * y) = (a / x) * (b / y) :=
      Nat.div_mul_div_comm hx hy |>.symm
    refine ⟨Nat.mul_dvd_mul hx hy, ?_, by positivity⟩
    rw [hdiv]
    have hxb : x.Coprime (b / y) :=
      (hab.coprime_dvd_left hx).coprime_dvd_right (Nat.div_dvd_of_dvd hy)
    have hya : y.Coprime (a / x) :=
      (hab.symm.coprime_dvd_left hy).coprime_dvd_right (Nat.div_dvd_of_dvd hx)
    exact Nat.Coprime.mul_left (Nat.Coprime.mul_right hxc hxb) (Nat.Coprime.mul_right hya hyc)
  · intro d hd
    simp only [mem_product, mem_unitaryDivisors] at hd ⊢
    obtain ⟨hd, hdc, -⟩ := hd
    have hsplit : d = d.gcd a * d.gcd b := by
      rw [← Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_left hd]
    have hq : a * b / d = (a / d.gcd a) * (b / d.gcd b) := by
      conv_lhs => rw [hsplit]
      exact (Nat.div_mul_div_comm (Nat.gcd_dvd_right d a) (Nat.gcd_dvd_right d b)).symm
    have hda : a / d.gcd a ∣ a * b / d := hq ▸ Dvd.intro _ rfl
    have hdb : b / d.gcd b ∣ a * b / d := hq ▸ Dvd.intro_left _ rfl
    refine ⟨⟨Nat.gcd_dvd_right _ _, ?_, ha.ne'⟩, ⟨Nat.gcd_dvd_right _ _, ?_, hb.ne'⟩⟩
    · exact (hdc.coprime_dvd_left (Nat.gcd_dvd_left _ _)).coprime_dvd_right hda
    · exact (hdc.coprime_dvd_left (Nat.gcd_dvd_left _ _)).coprime_dvd_right hdb
  · rintro ⟨x, y⟩ hxy
    simp only [mem_product, mem_unitaryDivisors] at hxy
    obtain ⟨⟨hx, -, -⟩, ⟨hy, -, -⟩⟩ := hxy
    have hya : y.Coprime a := hab.symm.coprime_dvd_left hy
    have hxb : x.Coprime b := hab.coprime_dvd_left hx
    simp only [Prod.mk.injEq]
    constructor
    · rw [Nat.Coprime.gcd_mul_right_cancel x hya, Nat.gcd_eq_left hx]
    · rw [Nat.Coprime.gcd_mul_left_cancel y hxb, Nat.gcd_eq_left hy]
  · intro d hd
    simp only [mem_unitaryDivisors] at hd
    show d.gcd a * d.gcd b = d
    rw [← Nat.Coprime.gcd_mul d hab, Nat.gcd_eq_left hd.1]
  · intro _ _
    rfl

/-! ## Prime powers -/

/-- The only unitary divisors of a prime power `p ^ e` are `1` and `p ^ e`. -/
lemma unitaryDivisors_prime_pow {p e : ℕ} (hp : p.Prime) :
    unitaryDivisors (p ^ e) = {1, p ^ e} := by
  have hpe : p ^ e ≠ 0 := pow_ne_zero _ hp.ne_zero
  ext d
  simp only [mem_unitaryDivisors, mem_insert, mem_singleton]
  constructor
  · rintro ⟨hd, hc, -⟩
    obtain ⟨i, hi, rfl⟩ := (Nat.dvd_prime_pow hp).1 hd
    rw [Nat.pow_div hi hp.pos] at hc
    rcases Nat.eq_zero_or_pos i with rfl | hi0
    · simp
    rcases Nat.eq_zero_or_pos (e - i) with h0 | hj0
    · right; rw [show i = e by omega]
    exfalso
    have hpp : p.Coprime p :=
      (hc.coprime_dvd_left (dvd_pow_self p hi0.ne')).coprime_dvd_right
        (dvd_pow_self p hj0.ne')
    exact hp.one_lt.ne' ((Nat.coprime_self p).1 hpp)
  · rintro (rfl | rfl)
    · simp [hp.ne_zero]
    · simp [Nat.div_self (Nat.pos_of_ne_zero hpe), hp.ne_zero]

/-- `σ*(p ^ e) = 1 + p ^ e` for a prime `p` and `e ≥ 1`. -/
theorem usigma_prime_pow {p e : ℕ} (hp : p.Prime) (he : 0 < e) :
    usigma (p ^ e) = 1 + p ^ e := by
  have h1 : (1 : ℕ) ≠ p ^ e := (Nat.one_lt_pow he.ne' hp.one_lt).ne
  rw [usigma, unitaryDivisors_prime_pow hp, sum_insert (by simpa using h1), sum_singleton]

lemma usigma_one : usigma 1 = 1 := by decide

/-- Splitting off the full power of a prime `p ∣ n`:
`σ*(n) = (1 + p ^ v) σ*(n / p ^ v)` with `v = n.factorization p ≥ 1`. -/
lemma usigma_split {n p : ℕ} (hp : p.Prime) (hn : n ≠ 0) (hpn : p ∣ n) :
    usigma n = (1 + p ^ n.factorization p) * usigma (n / p ^ n.factorization p) := by
  have hv : 0 < n.factorization p := hp.factorization_pos_of_dvd hn hpn
  have hcop : (p ^ n.factorization p).Coprime (n / p ^ n.factorization p) :=
    (Nat.coprime_ordCompl hp hn).pow_left _
  conv_lhs => rw [← Nat.ordProj_mul_ordCompl_eq_self n p]
  rw [usigma_mul hcop, usigma_prime_pow hp hv]

/-! ## Parity -/

/-- `σ*(m)` is even for every odd `m > 1`. -/
lemma even_usigma_of_odd {m : ℕ} (hm : Odd m) (h1 : 1 < m) : Even (usigma m) := by
  have hm0 : m ≠ 0 := by omega
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  rw [usigma_split hp hm0 (Nat.minFac_dvd m)]
  apply Even.mul_right
  have hpodd : Odd m.minFac := hm.of_dvd_nat (Nat.minFac_dvd m)
  exact (hpodd.pow).one_add

/-- Every unitary perfect number is even (Subbarao–Warren 1966; also formalised by AlphaProof
in a fork of formal-conjectures). -/
theorem even_of_isUnitaryPerfect {n : ℕ} (h : IsUnitaryPerfect n) : Even n := by
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  by_contra hev
  have hodd : Odd n := Nat.not_even_iff_odd.1 hev
  have hn1 : n ≠ 1 := by rintro rfl; simp [usigma_one] at hs
  have hn0 : n ≠ 0 := hpos.ne'
  have hp := Nat.minFac_prime hn1
  set p := n.minFac
  set v := n.factorization p
  set m := n / p ^ v
  have hsplit : usigma n = (1 + p ^ v) * usigma m := usigma_split hp hn0 (Nat.minFac_dvd n)
  have hnm : p ^ v * m = n := Nat.ordProj_mul_ordCompl_eq_self n p
  have hv : 0 < v := hp.factorization_pos_of_dvd hn0 (Nat.minFac_dvd n)
  have hmodd : Odd m := hodd.of_dvd_nat (Nat.ordCompl_dvd n p)
  clear_value p v m
  have hpv : 1 < p ^ v := Nat.one_lt_pow hv.ne' hp.one_lt
  have hm0 : m ≠ 0 := by rintro h0; rw [h0, mul_zero] at hnm; exact hn0 hnm.symm
  rcases (show m = 1 ∨ 1 < m by omega) with hm1 | hm1
  · rw [hm1, usigma_one, mul_one] at hsplit
    rw [hm1, mul_one] at hnm
    omega
  · have hpvodd : Odd (p ^ v) := hodd.of_dvd_nat (Dvd.intro _ hnm)
    obtain ⟨x, hx⟩ := hpvodd.one_add
    obtain ⟨y, hy⟩ := even_usigma_of_odd hmodd hm1
    rw [hx, hy] at hsplit
    have : n = 2 * (x * y) := by nlinarith
    exact hev (this ▸ even_two_mul _)

/-! ## At most one odd prime factor -/

/-- The only unitary perfect number with at most one odd prime factor is `6`
(Subbarao–Warren 1966; elementary). -/
theorem eq_six_of_isUnitaryPerfect_of_card_primeFactors_le_two {n : ℕ} (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card ≤ 2) : n = 6 := by
  have hev := even_of_isUnitaryPerfect h
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2n : 2 ∣ n := even_iff_two_dvd.1 hev
  set a := n.factorization 2
  set m := n / 2 ^ a
  have hsplit : usigma n = (1 + 2 ^ a) * usigma m := usigma_split Nat.prime_two hn0 h2n
  have hnm : 2 ^ a * m = n := Nat.ordProj_mul_ordCompl_eq_self n 2
  have ha : 0 < a := Nat.prime_two.factorization_pos_of_dvd hn0 h2n
  have hcop2 : Nat.Coprime 2 m := Nat.coprime_ordCompl Nat.prime_two hn0
  clear_value a m
  have hX : 2 ≤ 2 ^ a := by
    calc 2 = 2 ^ 1 := rfl
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have hm0 : m ≠ 0 := by rintro h0; rw [h0, mul_zero] at hnm; exact hn0 hnm.symm
  rcases (show m = 1 ∨ 1 < m by omega) with hm1 | hm1
  · -- `n = 2 ^ a`: `1 + 2 ^ a = 2 ^ (a + 1)` is impossible by parity.
    rw [hm1, usigma_one, mul_one] at hsplit
    rw [hm1, mul_one] at hnm
    have : Even (2 ^ a) := (Nat.even_pow' ha.ne').2 even_two
    obtain ⟨k, hk⟩ := this
    omega
  · -- `m` is an odd prime power `q ^ f`.
    have h2m : 2 ∉ m.primeFactors := by
      intro h2
      exact Nat.prime_two.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop2 (Nat.dvd_of_mem_primeFactors h2))
    have hpf : n.primeFactors = insert 2 m.primeFactors := by
      rw [← hnm, Nat.Coprime.primeFactors_mul (hcop2.pow_left a),
        Nat.primeFactors_prime_pow ha.ne' Nat.prime_two]
      rfl
    have hcm : m.primeFactors.card = 1 := by
      have hne := Nat.nonempty_primeFactors.2 hm1
      rw [hpf, card_insert_of_notMem h2m] at hcard
      have := hne.card_pos
      omega
    obtain ⟨q, f, hq, hf, hqf⟩ :=
      (isPrimePow_nat_iff m).1 (isPrimePow_iff_card_primeFactors_eq_one.2 hcm)
    rw [← hqf, usigma_prime_pow hq hf] at hsplit
    rw [← hqf] at hnm
    -- Now `(1 + X) (1 + Y) = 2 X Y` with `X = 2 ^ a`, `Y = q ^ f` and `Y` odd.
    set X := 2 ^ a
    set Y := q ^ f
    have hY : Nat.Coprime 2 Y := by rw [hqf]; exact hcop2
    have heq : (1 + X) * (1 + Y) = 2 * X * Y := by rw [← hsplit, hs, ← hnm]; ring
    have hY1 : Y ∣ 1 + X := by
      have hd : Y ∣ (1 + X) * (1 + Y) := heq ▸ Dvd.intro_left _ rfl
      exact (Nat.Coprime.dvd_of_dvd_mul_right
        (Nat.coprime_add_self_right.2 (Nat.coprime_one_right Y)) hd)
    have hX1 : 1 + X ∣ Y := by
      have hd : 1 + X ∣ 2 * X * Y := heq ▸ Dvd.intro _ rfl
      have hc2 : Nat.Coprime (1 + X) 2 := by
        rw [Nat.coprime_two_right]
        exact (Nat.even_pow' ha.ne' |>.2 even_two).one_add
      have hcX : Nat.Coprime (1 + X) X :=
        Nat.coprime_add_self_left.2 (Nat.coprime_one_left X)
      exact (Nat.Coprime.mul_right hc2 hcX).dvd_of_dvd_mul_left hd
    have hYX : Y = 1 + X := Nat.dvd_antisymm hY1 hX1
    rw [hYX] at heq
    have hX2 : X = 2 := by nlinarith
    rw [← hnm, hYX, hX2]

/-! ## The known examples -/

/-- Peeling off one prime power factor, in the form used for the examples below. -/
lemma usigma_prime_pow_mul {p e m : ℕ} (hp : p.Prime) (he : 0 < e) (hc : (p ^ e).Coprime m) :
    usigma (p ^ e * m) = (1 + p ^ e) * usigma m := by
  rw [usigma_mul hc, usigma_prime_pow hp he]

theorem isUnitaryPerfect_6 : IsUnitaryPerfect 6 := by
  rw [isUnitaryPerfect_iff]; decide

theorem isUnitaryPerfect_60 : IsUnitaryPerfect 60 := by
  rw [isUnitaryPerfect_iff]; decide

theorem isUnitaryPerfect_90 : IsUnitaryPerfect 90 := by
  rw [isUnitaryPerfect_iff]; decide

/-- `87360 = 2^6 · 3 · 5 · 7 · 13`. Via multiplicativity instead of enumerating divisors. -/
theorem isUnitaryPerfect_87360 : IsUnitaryPerfect 87360 := by
  rw [isUnitaryPerfect_iff]
  refine ⟨?_, by norm_num⟩
  rw [show (87360 : ℕ) = 2 ^ 6 * (3 ^ 1 * (5 ^ 1 * (7 ^ 1 * (13 ^ 1 * 1)))) by norm_num]
  repeat rw [usigma_prime_pow_mul (by norm_num) (by norm_num) (by norm_num)]
  rw [usigma_one]
  norm_num

/-- `146361946186458562560000 = 2^18 · 3 · 5^4 · 7 · 11 · 13 · 19 · 37 · 79 · 109 · 157 · 313`
(Wall 1975). -/
theorem isUnitaryPerfect_146361946186458562560000 :
    IsUnitaryPerfect 146361946186458562560000 := by
  rw [isUnitaryPerfect_iff]
  refine ⟨?_, by norm_num⟩
  rw [show (146361946186458562560000 : ℕ) = 2 ^ 18 * (3 ^ 1 * (5 ^ 4 * (7 ^ 1 * (11 ^ 1 *
    (13 ^ 1 * (19 ^ 1 * (37 ^ 1 * (79 ^ 1 * (109 ^ 1 * (157 ^ 1 * (313 ^ 1 * 1))))))))))) by
    norm_num]
  repeat rw [usigma_prime_pow_mul (by norm_num) (by norm_num) (by norm_num)]
  rw [usigma_one]
  norm_num

end ErdosResearch.Erdos1052
