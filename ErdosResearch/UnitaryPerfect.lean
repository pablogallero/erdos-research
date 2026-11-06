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
* `eq_sixty_or_ninety_of_isUnitaryPerfect_of_card_primeFactors_eq_three`: with exactly two odd
  prime factors, the only ones are `60` and `90`.
* `isUnitaryPerfect_of_card_primeFactors_le_three_iff`: with at most two odd prime factors, the
  unitary perfect numbers are exactly `6`, `60` and `90`.
* `not_isUnitaryPerfect_of_card_primeFactors_eq_four`: there is none with exactly three odd prime
  factors.
* `isUnitaryPerfect_of_card_primeFactors_le_four_iff`: with at most three odd prime factors, the
  unitary perfect numbers are exactly `6`, `60` and `90`.
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

/-! ## Exactly two odd prime factors -/

/-- Splitting off the full power of a prime `p ∣ m`: `m = p ^ e * r` with `p ∤ r`, and `r`
has one prime factor fewer than `m`. -/
lemma exists_split_of_dvd {m p : ℕ} (hp : p.Prime) (hm0 : m ≠ 0) (hpm : p ∣ m) :
    ∃ e r, 0 < e ∧ (p ^ e).Coprime r ∧ p ^ e * r = m ∧
      r.primeFactors.card + 1 = m.primeFactors.card := by
  refine ⟨m.factorization p, m / p ^ m.factorization p, hp.factorization_pos_of_dvd hm0 hpm,
    (Nat.coprime_ordCompl hp hm0).pow_left _, Nat.ordProj_mul_ordCompl_eq_self m _, ?_⟩
  have he : 0 < m.factorization p := hp.factorization_pos_of_dvd hm0 hpm
  have hcop : Nat.Coprime p (m / p ^ m.factorization p) := Nat.coprime_ordCompl hp hm0
  have hmr := Nat.ordProj_mul_ordCompl_eq_self m p
  set e := m.factorization p
  set r := m / p ^ e
  clear_value e r
  have hpr : p ∉ r.primeFactors := fun h =>
    hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hcop (Nat.dvd_of_mem_primeFactors h))
  rw [← hmr, Nat.Coprime.primeFactors_mul (hcop.pow_left e),
    Nat.primeFactors_prime_pow he.ne' hp, ← insert_eq, card_insert_of_notMem hpr]

/-- Arithmetic core of the case with two odd prime factors (sorted). -/
lemma arith_sorted {a P Q : ℕ} (ha : 0 < a) (hP : P % 2 = 1) (hQ : Q % 2 = 1) (hP1 : 1 < P)
    (hPQ : P < Q) (h : (1 + 2 ^ a) * (1 + P) * (1 + Q) = 2 * 2 ^ a * P * Q) :
    2 ^ a * P * Q = 60 ∨ 2 ^ a * P * Q = 90 := by
  have hP3 : 3 ≤ P := by omega
  have hQ5 : 5 ≤ Q := by omega
  rcases (show a = 1 ∨ a = 2 ∨ 3 ≤ a by omega) with rfl | rfl | ha3
  · right
    norm_num at h ⊢
    rcases (show P = 3 ∨ P = 5 ∨ 7 ≤ P by omega) with rfl | rfl | hP7
    · omega
    · omega
    · exfalso
      have hQ9 : 9 ≤ Q := by omega
      nlinarith [Nat.mul_le_mul (show 4 ≤ P - 3 by omega) (show 6 ≤ Q - 3 by omega)]
  · left
    norm_num at h ⊢
    rcases (show P = 3 ∨ 5 ≤ P by omega) with rfl | hP5
    · omega
    · exfalso
      have hQ7 : 7 ≤ Q := by omega
      nlinarith [Nat.mul_le_mul hP5 hQ7]
  · exfalso
    set X := 2 ^ a with hX
    have hX8 : 8 ≤ X := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
    clear_value X
    obtain ⟨x, rfl⟩ : ∃ x, X = x + 8 := ⟨X - 8, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, P = p + 3 := ⟨P - 3, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, Q = q + 5 := ⟨Q - 5, by omega⟩
    ring_nf at h
    nlinarith [Nat.zero_le (x * p), Nat.zero_le (x * q), Nat.zero_le (p * q),
      Nat.zero_le (x * p * q)]

/-- `(1 + 2^a)(1 + P)(1 + Q) = 2^{a+1} P Q` with `P ≠ Q` odd and `> 1` forces
`2^a P Q ∈ {60, 90}`. -/
lemma arith_two_odd {a P Q : ℕ} (ha : 0 < a) (hP : P % 2 = 1) (hQ : Q % 2 = 1) (hP1 : 1 < P)
    (hQ1 : 1 < Q) (hPQ : P ≠ Q) (h : (1 + 2 ^ a) * (1 + P) * (1 + Q) = 2 * 2 ^ a * P * Q) :
    2 ^ a * P * Q = 60 ∨ 2 ^ a * P * Q = 90 := by
  rcases lt_or_gt_of_ne hPQ with hlt | hlt
  · exact arith_sorted ha hP hQ hP1 hlt h
  · have h' : (1 + 2 ^ a) * (1 + Q) * (1 + P) = 2 * 2 ^ a * Q * P := by
      rw [mul_right_comm, h]; ring
    have := arith_sorted ha hQ hP hQ1 hlt h'
    rwa [mul_right_comm (2 ^ a) Q P] at this

/-- The only unitary perfect numbers with exactly two odd prime factors are `60` and `90`
(Subbarao–Warren 1966; elementary). -/
theorem eq_sixty_or_ninety_of_isUnitaryPerfect_of_card_primeFactors_eq_three {n : ℕ}
    (h : IsUnitaryPerfect n) (hcard : n.primeFactors.card = 3) : n = 60 ∨ n = 90 := by
  have hev := even_of_isUnitaryPerfect h
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2n : 2 ∣ n := even_iff_two_dvd.1 hev
  -- `n = 2 ^ a * m` with `m` odd and with two prime factors.
  obtain ⟨a, m, ha, hc2, hnm, hcm⟩ := exists_split_of_dvd Nat.prime_two hn0 h2n
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hnm; exact hn0 hnm.symm
  have hm2 : m.primeFactors.card = 2 := by omega
  have hm1 : 1 < m := by
    by_contra hle
    interval_cases m <;> simp at hm2
  have hmodd : m % 2 = 1 := Nat.odd_iff.1 <|
    (Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_left (dvd_pow_self 2 ha.ne') hc2))
  -- `m = p ^ e * r` and `r = q ^ f`.
  have hp := Nat.minFac_prime (show m ≠ 1 by omega)
  obtain ⟨e, r, he, hcpr, hmr, hcr⟩ := exists_split_of_dvd hp hm0 (Nat.minFac_dvd m)
  have hr1 : r.primeFactors.card = 1 := by omega
  obtain ⟨q, f, hq, hf, hqf⟩ :=
    (isPrimePow_nat_iff r).1 (isPrimePow_iff_card_primeFactors_eq_one.2 hr1)
  subst hqf
  set P := m.minFac ^ e with hPdef
  set Q := q ^ f with hQdef
  have hP1 : 1 < P := Nat.one_lt_pow he.ne' hp.one_lt
  have hQ1 : 1 < Q := Nat.one_lt_pow hf.ne' hq.one_lt
  have hPQ : P ≠ Q := by
    intro hEq
    rw [← hEq, Nat.coprime_self] at hcpr
    omega
  have hPodd : P % 2 = 1 := Nat.odd_iff.1 <|
    (Nat.odd_iff.2 hmodd).of_dvd_nat (Dvd.intro _ hmr)
  have hQodd : Q % 2 = 1 := Nat.odd_iff.1 <|
    (Nat.odd_iff.2 hmodd).of_dvd_nat (Dvd.intro_left _ hmr)
  have hsig : usigma n = (1 + 2 ^ a) * (1 + P) * (1 + Q) := by
    rw [← hnm, ← hmr, usigma_mul (by rwa [hmr]), usigma_mul hcpr, usigma_prime_pow
      Nat.prime_two ha, usigma_prime_pow hp he, usigma_prime_pow hq hf, mul_assoc]
  have heq : (1 + 2 ^ a) * (1 + P) * (1 + Q) = 2 * 2 ^ a * P * Q := by
    rw [← hsig, hs, ← hnm, ← hmr]; ring
  clear_value P Q
  have := arith_two_odd ha hPodd hQodd hP1 hQ1 hPQ heq
  rwa [mul_assoc, hmr, hnm] at this

/-! ## Exactly three odd prime factors -/

/-- Arithmetic core of the case with three odd prime factors (sorted). The case tree was
generated by a script (see `notes/erdos-1052.md`): `X ≥ 16`, or a bound on the smallest
remaining factor, is excluded by a size estimate; every other branch is linear. The only
solution over odd integers, `(X, P, Q, R) = (8, 3, 5, 9)`, is excluded by `Nat.Coprime P R`. -/
lemma arith3_sorted {X P Q R : ℕ} (hX : X = 2 ∨ X = 4 ∨ X = 8 ∨ 16 ≤ X) (hP : P % 2 = 1)
    (hQ : Q % 2 = 1) (hR : R % 2 = 1) (hP1 : 1 < P) (hPQ : P < Q) (hQR : Q < R)
    (hcop : Nat.Coprime P R)
    (h : (1 + X) * (1 + P) * (1 + Q) * (1 + R) = 2 * X * P * Q * R) : False := by
  rcases hX with rfl | rfl | rfl | hX
  · rcases (show P = 3 ∨ P = 5 ∨ P = 7 ∨ 9 ≤ P by omega) with rfl | rfl | rfl | hPB
    · ring_nf at h
      nlinarith [Nat.zero_le (Q * R)]
    · rcases (show Q = 7 ∨ Q = 9 ∨ Q = 11 ∨ Q = 13 ∨ Q = 15 ∨ Q = 17 ∨ 19 ≤ Q by omega)
        with rfl | rfl | rfl | rfl | rfl | rfl | hQB
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · obtain ⟨q, rfl⟩ : ∃ q, Q = q + 19 := ⟨Q - 19, by omega⟩
        obtain ⟨r, rfl⟩ : ∃ r, R = r + 21 := ⟨R - 21, by omega⟩
        ring_nf at h
        nlinarith [Nat.zero_le (q * r)]
    · rcases (show Q = 9 ∨ Q = 11 ∨ 13 ≤ Q by omega) with rfl | rfl | hQB
      · omega
      · omega
      · obtain ⟨q, rfl⟩ : ∃ q, Q = q + 13 := ⟨Q - 13, by omega⟩
        obtain ⟨r, rfl⟩ : ∃ r, R = r + 15 := ⟨R - 15, by omega⟩
        ring_nf at h
        nlinarith [Nat.zero_le (q * r)]
    · obtain ⟨p, rfl⟩ : ∃ p, P = p + 9 := ⟨P - 9, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, Q = q + 11 := ⟨Q - 11, by omega⟩
      obtain ⟨r, rfl⟩ : ∃ r, R = r + 13 := ⟨R - 13, by omega⟩
      ring_nf at h
      nlinarith [Nat.zero_le (p * q), Nat.zero_le (p * r), Nat.zero_le (q * r),
        Nat.zero_le (p * q * r)]
  · rcases (show P = 3 ∨ 5 ≤ P by omega) with rfl | hPB
    · rcases (show Q = 5 ∨ Q = 7 ∨ Q = 9 ∨ 11 ≤ Q by omega) with rfl | rfl | rfl | hQB
      · omega
      · omega
      · omega
      · obtain ⟨q, rfl⟩ : ∃ q, Q = q + 11 := ⟨Q - 11, by omega⟩
        obtain ⟨r, rfl⟩ : ∃ r, R = r + 13 := ⟨R - 13, by omega⟩
        ring_nf at h
        nlinarith [Nat.zero_le (q * r)]
    · obtain ⟨p, rfl⟩ : ∃ p, P = p + 5 := ⟨P - 5, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, Q = q + 7 := ⟨Q - 7, by omega⟩
      obtain ⟨r, rfl⟩ : ∃ r, R = r + 9 := ⟨R - 9, by omega⟩
      ring_nf at h
      nlinarith [Nat.zero_le (p * q), Nat.zero_le (p * r), Nat.zero_le (q * r),
        Nat.zero_le (p * q * r)]
  · rcases (show P = 3 ∨ 5 ≤ P by omega) with rfl | hPB
    · rcases (show Q = 5 ∨ 7 ≤ Q by omega) with rfl | hQB
      · obtain rfl : R = 9 := by omega
        norm_num at hcop
      · obtain ⟨q, rfl⟩ : ∃ q, Q = q + 7 := ⟨Q - 7, by omega⟩
        obtain ⟨r, rfl⟩ : ∃ r, R = r + 9 := ⟨R - 9, by omega⟩
        ring_nf at h
        nlinarith [Nat.zero_le (q * r)]
    · obtain ⟨p, rfl⟩ : ∃ p, P = p + 5 := ⟨P - 5, by omega⟩
      obtain ⟨q, rfl⟩ : ∃ q, Q = q + 7 := ⟨Q - 7, by omega⟩
      obtain ⟨r, rfl⟩ : ∃ r, R = r + 9 := ⟨R - 9, by omega⟩
      ring_nf at h
      nlinarith [Nat.zero_le (p * q), Nat.zero_le (p * r), Nat.zero_le (q * r),
        Nat.zero_le (p * q * r)]
  · obtain ⟨x, rfl⟩ : ∃ x, X = x + 16 := ⟨X - 16, by omega⟩
    obtain ⟨p, rfl⟩ : ∃ p, P = p + 3 := ⟨P - 3, by omega⟩
    obtain ⟨q, rfl⟩ : ∃ q, Q = q + 5 := ⟨Q - 5, by omega⟩
    obtain ⟨r, rfl⟩ : ∃ r, R = r + 7 := ⟨R - 7, by omega⟩
    ring_nf at h
    nlinarith [Nat.zero_le (x * p), Nat.zero_le (x * q), Nat.zero_le (x * r), Nat.zero_le (p * q),
      Nat.zero_le (p * r), Nat.zero_le (q * r), Nat.zero_le (x * p * q), Nat.zero_le (x * p * r),
      Nat.zero_le (x * q * r), Nat.zero_le (p * q * r), Nat.zero_le (x * p * q * r)]

/-- `(1 + 2^a)(1 + P)(1 + Q)(1 + R) = 2^{a+1} P Q R` has no solution with `P, Q, R` odd,
`> 1` and pairwise coprime. -/
lemma arith_three_odd {a P Q R : ℕ} (ha : 0 < a) (hP : P % 2 = 1) (hQ : Q % 2 = 1)
    (hR : R % 2 = 1) (hP1 : 1 < P) (hQ1 : 1 < Q) (hR1 : 1 < R) (hPQ : Nat.Coprime P Q)
    (hPR : Nat.Coprime P R) (hQR : Nat.Coprime Q R)
    (h : (1 + 2 ^ a) * (1 + P) * (1 + Q) * (1 + R) = 2 * 2 ^ a * P * Q * R) : False := by
  have hX : 2 ^ a = 2 ∨ 2 ^ a = 4 ∨ 2 ^ a = 8 ∨ 16 ≤ 2 ^ a := by
    rcases (show a = 1 ∨ a = 2 ∨ a = 3 ∨ 4 ≤ a by omega) with rfl | rfl | rfl | ha4
    · norm_num
    · norm_num
    · norm_num
    · right; right; right
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha4
  set X := 2 ^ a
  clear_value X
  have ne {A B : ℕ} (hA : 1 < A) (hAB : Nat.Coprime A B) : A ≠ B := by
    rintro rfl; rw [Nat.coprime_self] at hAB; omega
  have hPQ' := ne hP1 hPQ
  have hPR' := ne hP1 hPR
  have hQR' := ne hQ1 hQR
  -- Sort `P, Q, R`; the arithmetic core needs the smallest and largest to be coprime.
  rcases lt_or_gt_of_ne hPQ' with h1 | h1 <;> rcases lt_or_gt_of_ne hPR' with h2 | h2 <;>
    rcases lt_or_gt_of_ne hQR' with h3 | h3
  · exact arith3_sorted hX hP hQ hR hP1 h1 h3 hPR h
  · exact arith3_sorted hX hP hR hQ hP1 h2 h3 hPQ (by convert h using 1 <;> ring)
  · omega
  · exact arith3_sorted hX hR hP hQ hR1 h2 h1 hQR.symm (by convert h using 1 <;> ring)
  · exact arith3_sorted hX hQ hP hR hQ1 h1 h2 hQR (by convert h using 1 <;> ring)
  · omega
  · exact arith3_sorted hX hQ hR hP hQ1 h3 h2 hPQ.symm (by convert h using 1 <;> ring)
  · exact arith3_sorted hX hR hQ hP hR1 h3 h1 hPR.symm (by convert h using 1 <;> ring)

/-- There is no unitary perfect number with exactly three odd prime factors. -/
theorem not_isUnitaryPerfect_of_card_primeFactors_eq_four {n : ℕ} (h : IsUnitaryPerfect n)
    (hcard : n.primeFactors.card = 4) : False := by
  have hev := even_of_isUnitaryPerfect h
  rw [isUnitaryPerfect_iff] at h
  obtain ⟨hs, hpos⟩ := h
  have hn0 : n ≠ 0 := hpos.ne'
  have h2n : 2 ∣ n := even_iff_two_dvd.1 hev
  -- `n = 2 ^ a * m` with `m` odd and with three prime factors.
  obtain ⟨a, m, ha, hc2, hnm, hcm⟩ := exists_split_of_dvd Nat.prime_two hn0 h2n
  have hm0 : m ≠ 0 := by rintro rfl; rw [mul_zero] at hnm; exact hn0 hnm.symm
  have hm3 : m.primeFactors.card = 3 := by omega
  have hm1 : m ≠ 1 := by rintro rfl; simp at hm3
  have hmodd : Odd m := Nat.odd_iff.2 <| Nat.odd_iff.1 <|
    (Nat.coprime_two_left.1 (Nat.Coprime.coprime_dvd_left (dvd_pow_self 2 ha.ne') hc2))
  -- `m = p ^ e * r`, `r = q ^ f * s`, `s = t ^ g`.
  have hp := Nat.minFac_prime hm1
  obtain ⟨e, r, he, hcpr, hmr, hcr⟩ := exists_split_of_dvd hp hm0 (Nat.minFac_dvd m)
  have hr0 : r ≠ 0 := by rintro rfl; rw [mul_zero] at hmr; exact hm0 hmr.symm
  have hr1 : r ≠ 1 := by rintro rfl; simp at hcr; omega
  have hq := Nat.minFac_prime hr1
  obtain ⟨f, s, hf, hcqs, hrs, hcs⟩ := exists_split_of_dvd hq hr0 (Nat.minFac_dvd r)
  have hs1 : s.primeFactors.card = 1 := by omega
  obtain ⟨t, g, ht, hg, htg⟩ :=
    (isPrimePow_nat_iff s).1 (isPrimePow_iff_card_primeFactors_eq_one.2 hs1)
  subst htg
  set P := m.minFac ^ e with hPdef
  set Q := r.minFac ^ f with hQdef
  set R := t ^ g with hRdef
  have hP1 : 1 < P := Nat.one_lt_pow he.ne' hp.one_lt
  have hQ1 : 1 < Q := Nat.one_lt_pow hf.ne' hq.one_lt
  have hR1 : 1 < R := Nat.one_lt_pow hg.ne' ht.one_lt
  have hPQ : Nat.Coprime P Q := hcpr.coprime_dvd_right (Dvd.intro _ hrs)
  have hPR : Nat.Coprime P R := hcpr.coprime_dvd_right (Dvd.intro_left _ hrs)
  have hPodd : P % 2 = 1 := Nat.odd_iff.1 <| hmodd.of_dvd_nat (Dvd.intro _ hmr)
  have hrodd : Odd r := hmodd.of_dvd_nat (Dvd.intro_left _ hmr)
  have hQodd : Q % 2 = 1 := Nat.odd_iff.1 <| hrodd.of_dvd_nat (Dvd.intro _ hrs)
  have hRodd : R % 2 = 1 := Nat.odd_iff.1 <| hrodd.of_dvd_nat (Dvd.intro_left _ hrs)
  have hsig : usigma n = (1 + 2 ^ a) * (1 + P) * (1 + Q) * (1 + R) := by
    rw [← hnm, ← hmr, ← hrs, usigma_mul (by rwa [hrs, hmr]), usigma_mul (by rwa [hrs]),
      usigma_mul hcqs, usigma_prime_pow Nat.prime_two ha, usigma_prime_pow hp he,
      usigma_prime_pow hq hf, usigma_prime_pow ht hg]
    ring
  have heq : (1 + 2 ^ a) * (1 + P) * (1 + Q) * (1 + R) = 2 * 2 ^ a * P * Q * R := by
    rw [← hsig, hs, ← hnm, ← hmr, ← hrs]; ring
  clear_value P Q R
  exact arith_three_odd ha hPodd hQodd hRodd hP1 hQ1 hR1 hPQ hPR hcqs heq

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

/-! ## At most two odd prime factors: the classification -/

/-- Classification of unitary perfect numbers with at most three prime factors (i.e. at most two
odd prime factors): they are exactly `6`, `60` and `90`. -/
theorem isUnitaryPerfect_of_card_primeFactors_le_three_iff {n : ℕ}
    (hcard : n.primeFactors.card ≤ 3) : IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 := by
  constructor
  · intro h
    rcases (show n.primeFactors.card ≤ 2 ∨ n.primeFactors.card = 3 by omega) with h2 | h3
    · exact Or.inl (eq_six_of_isUnitaryPerfect_of_card_primeFactors_le_two h h2)
    · exact Or.inr (eq_sixty_or_ninety_of_isUnitaryPerfect_of_card_primeFactors_eq_three h h3)
  · rintro (rfl | rfl | rfl)
    · exact isUnitaryPerfect_6
    · exact isUnitaryPerfect_60
    · exact isUnitaryPerfect_90

/-- Classification of unitary perfect numbers with at most four prime factors (i.e. at most three
odd prime factors): they are exactly `6`, `60` and `90`. -/
theorem isUnitaryPerfect_of_card_primeFactors_le_four_iff {n : ℕ}
    (hcard : n.primeFactors.card ≤ 4) : IsUnitaryPerfect n ↔ n = 6 ∨ n = 60 ∨ n = 90 := by
  rcases (show n.primeFactors.card ≤ 3 ∨ n.primeFactors.card = 4 by omega) with h3 | h4
  · exact isUnitaryPerfect_of_card_primeFactors_le_three_iff h3
  · constructor
    · intro h
      exact (not_isUnitaryPerfect_of_card_primeFactors_eq_four h h4).elim
    · rintro (rfl | rfl | rfl)
      exacts [isUnitaryPerfect_6, isUnitaryPerfect_60, isUnitaryPerfect_90]

end ErdosResearch.Erdos1052
