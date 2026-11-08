# Erdős #470: odd weird numbers ($10)

Statement (erdosproblems.com/470, checked 2026-11-08): `n` is *weird* if `σ(n) ≥ 2n` and `n` is not
pseudoperfect. (i) Are there odd weird numbers? (ii) Are there infinitely many primitive weird
numbers? The $10 is for (i) (Guy B2). Lean: `FormalConjectures/ErdosProblems/470.lean` uses
Mathlib's `Nat.Weird` (abundant ∧ ¬ pseudoperfect). Both parts are still `sorry` there, as are the
variants `odd_weird_10_pow_21` (Fang) and the Liddy–Riedl variant.

## Why switch from #1052 (decision of 2026-11-08, session 8)

Session 7 concluded that something new on #1052 needs ≥ 9 odd primes (Wall 1988 covers ≤ 8), which
is far beyond search (k = 7 alone is 12.9M nodes). I re-filtered the teorth/erdosproblems
`problems.yaml` (downloaded 2026-11-08): **54** open/falsifiable prize problems. Almost all of them are
deep analytic, combinatorial or geometric problems. The elementary ones are:
- #470 ($10): 2 comments, none mathematical; one user "currently working on" it; formal statement present.
- #647 (£25 ≈ $44): crowded (18 comments, 4 users working on it), and it is a search for one
  `n > 24` that Erdős himself thought very doubtful. Dropped.
- #708, #710, #711: asymptotic questions; #711 has partial progress by van Doorn 2026. Not
  elementary-finite.

#470 has the same "exclude small ω" structure as #1052, so the session 1–7 method transfers.

## What is known (literature)

- Benkoski–Erdős 1974, Math. Comp. 28, 617–623 (zbMATH Zbl 0279.10005, confirmed): weird numbers
  have positive density.
- Fang, arXiv:2207.12906 (abstract read; LaTeX source skimmed): no odd weird number below `10^21`.
  Also none below `10^28` with abundance below `10^14`. The method is a tree search on `pred(N) = N/(largest prime)`.
- Liddy & Riedl 2018, *An algorithm to determine all odd primitive abundant numbers with d prime
  divisors*, Honors Research Projects 728, Univ. of Akron (cited by erdosproblems.com and
  formal-conjectures): an odd weird number has ≥ 6 distinct prime factors. **Not read** (not on
  zbMATH / OpenAlex; ideaexchange.uakron.edu is not one of my sources).
- Amato–Hasler–Melfi–Parton, J. Number Theory 2019 (Zbl 1437.11167; arXiv:1802.07178): primitive
  abundant numbers counted by Ω; odd PANs counted up to Ω = 8.
- Hisamoto, arXiv:2607.25278 (2026, main theorem read): abundancy index > 633 ⇒ semiperfect. It does
  not help with odd numbers, whose abundancy is small for small ω.
- OpenAlex lists a Zenodo deposit (2026) titled "Non-existence of odd weird numbers: a complete
  proof". It is not peer-reviewed, the site still lists #470 as open, and I did not read it. Ignored.

## Feasibility of something new: "no odd weird number with ω = 6"

Reduction: an odd weird `n` is a multiple of an odd primitive non-deficient `m`, and `m` must itself
be weird (a multiple of a pseudoperfect number is pseudoperfect). So "ω ≥ 7" ⇔ every odd primitive
abundant number with ω = 6 is pseudoperfect (with ω ≤ 5 handled by Liddy–Riedl).
- My count (`/tmp` Python, not committed): odd primitive abundant numbers with ω = 3: **8**; with
  ω = 4: **576**. The ω = 5 run did not finish within a few minutes in naive Python.
- Growth is doubly exponential: the last prime `q` ranges up to `σ(M)/(2M − σ(M))` for the deficient
  prefix `M`, which is astronomically large when `σ(M)/M` is close to 2.
- Useful idea for the last prime (mine, not checked against Liddy–Riedl): for `m = Mq` with `q` prime,
  larger than every prime factor of `M`, and `q ∤ M`, `m` is pseudoperfect if and only if
  `∃ k ≥ 1` with `M − k` a subset sum of the proper divisors of `M` and `kq` a subset sum of the
  divisors of `M` (since `kq ≤ σ(M) < 2M`). That handles all `q` for a fixed `M` with one
  subset-sum table, but the number of prefixes `M` with ω = 5 is still enormous.
- Verdict: ω = 6 needs a serious C/GMP computation (days, uncertain), and it cannot be checked in
  Lean. **Not attempted this session.**

## Session 8 (2026-11-08): proved, failed, next step

**Proved (Lean; no sorry; axioms `propext`, `Classical.choice`, `Quot.sound`; `lake build` OK, 7360
jobs; module ~10 s):** `ErdosResearch/OddWeird.lean`
- `sigma_mul_prod_sub_one_le`: `σ(n)·∏_{p|n}(p−1) ≤ n·∏_{p|n} p` for every `n`.
- `deficient_of_odd_of_card_primeFactors_le_two`, `not_weird_of_odd_of_card_primeFactors_le_two`:
  an odd number with ω ≤ 2 is deficient, so it is not weird.
- Classical (trivial). It is a base for the next cases, not a new result.

**Failed:** two `omega` calls (fixed by naming the hypotheses and giving `s.card = 1/2` explicitly).

**Next step (in order):**
1. ω = 3 in Lean: an odd abundant `n` with ω = 3 is a multiple of one of the 8 odd PANs with ω = 3
   (smallest 945 = 3³·5·7). Prove each one is pseudoperfect with an explicit subset (`decide`), plus
   "multiple of a pseudoperfect is pseudoperfect" (scale the subset). The finiteness/enumeration
   step can reuse the sorted-factor bounds from `UnitaryPerfectFinite.lean`.
2. Write a fast enumerator (C or optimised Python) and count odd PANs with ω = 5. That shows whether
   ω = 6 (new) is within reach at all, using the last-prime subset-sum reduction above.
3. If ω = 6 is out of reach (likely), the realistic deliverable is formalising Liddy–Riedl (ω ≤ 5)
   in Lean, which is a `sorry` in formal-conjectures. Publishing anything needs Pablo's approval.

## Daily summary (2026-11-08, session 8)

- **Approaches tried:** (a) re-filtering all open prize problems in order to switch; (b) literature on
  #470 (erdosproblems.com, arXiv, zbMATH, OpenAlex; Semantic Scholar answered "429 Too Many
  Requests"); (c) counting odd primitive abundant numbers by ω; (d) Lean base for #470.
- **What failed and why:** nothing new on #1052 is reachable by search (Wall 1988), hence the switch.
  The naive ω = 5 count is too slow in Python. ω = 6 (a new result) looks infeasible without a
  large, unverifiable computation.
- **Advances:** in Lean, without `sorry`: odd ω ≤ 2 ⇒ deficient ⇒ not weird, and the general bound
  `σ(n)/n ≤ ∏ p/(p−1)`. Classical. No new mathematical result.
- **Quota consumed:** one `lean-research` session. I can't see the exact token count from inside
  the session; PGAL should take it from its own accounting. About 10 network queries (GitHub raw,
  erdosproblems.com, arXiv, zbMATH, OpenAlex), 3 compilations of the module and 1 full `lake build`.
  Mathlib came from the cache and was not compiled. No money spent.

## Session 9 (2026-11-08): proved, failed, next step

**Proved (Lean; no sorry; axioms `propext`, `Classical.choice`, `Quot.sound`; full `lake build` OK,
7361 jobs; new module ~15 s):** `ErdosResearch/OddWeirdThree.lean` (imported from the root)
- `Nat.Pseudoperfect.of_dvd`: a positive multiple of a pseudoperfect number is pseudoperfect.
- The 8 odd primitive abundant numbers with ω = 3 are pseudoperfect, each with an explicit subset of
  divisors: 945, 1575, 2205 (r = 7), 7425 (r = 11), 78975, 131625, 342225, 570375 (r = 13).
  The subsets were found with a small Python DFS and are checked in Lean by `norm_num` + `rfl`.
- `pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_three`, plus
  `not_weird_of_odd_of_card_primeFactors_le_three`: **an odd number with ω ≤ 3 is not weird.**
- Method: sort the primes p < q < r. From `σ(n)∏(p−1) ≤ n∏p` and abundance we get p = 3, q = 5,
  r ∈ {7, 11, 13}. Then the exponent vector either dominates one of the 8 PANs (so n is a multiple
  of it), or it lies in a "box" where σ(n) ≤ 2n. The general lemma `box` combines one ratio bound per
  prime: exact `σ(p^e)/p^e` for a fixed exponent, `< p/(p−1)` for a free one. There are 6 boxes and 2
  fully fixed cases (315, 3⁴·5²·13).
- Classical: Liddy–Riedl prove ω ≥ 6. It is new only as a formalisation, and it closes a sub-case of
  the `sorry` in formal-conjectures `erdos_470.parts.i` (which uses the same Mathlib `Nat.Weird`).

**Failed (minor):** `omega` does not identify `2 + 1` with `3` inside products after
`obtain rfl : x = 2` (fixed by stating the helper with `(2 + 1)`). `interval_cases z <;> norm_num at …`
closed goals and broke the bullet structure (fixed by `first | omega | (exfalso; revert hr; norm_num)`).

**Next step (in order):**
1. ω = 4 in Lean. The same scheme works, but there are 576 PANs and many more boxes, so generate the
   case tree with a script (as for #1052) or write a reflective checker: a decidable
   "dominates a PAN with a certificate, or box bound" check over exponent vectors, with the subsets
   supplied as data. First decide the prime 4-tuples in Lean from the bound `2∏(p−1) < ∏p`.
2. A fast enumerator for odd PANs with ω = 5 (C, `__int128` or GMP). This is needed to judge ω = 6.
   Liddy–Riedl did ω ≤ 5, so ω = 5 is feasible. ω = 6 would be new, but the count probably blows up
   doubly exponentially.
3. Honest assessment unchanged: the realistic deliverable is formalising the small-ω cases. Nothing
   new mathematically so far.

## Daily summary (2026-11-08, session 9)

- **Approaches tried:** formalising ω = 3 via the "PAN multiple or deficient box" case split.
- **What failed and why:** only tactic details (see above). No mathematical dead ends this session.
- **Advances:** Lean, without `sorry`: odd ω ≤ 3 ⇒ not weird, plus `Pseudoperfect.of_dvd`. Classical,
  and new as a formalisation only.
- **Quota consumed:** one `lean-research` session (exact tokens: from PGAL's accounting). No network
  queries; 3 module compilations and 1 full `lake build`; Mathlib from the cache. No money spent.

## Session 10 (2026-11-08): proved, failed, next step

**Proved (Lean; no sorry; axioms `propext`, `Classical.choice`, `Quot.sound`; full `lake build` OK,
7365 jobs; clean rebuild of the project's own modules 435 s on 2 cores, 5.2 GB peak):**
`not_weird_of_odd_of_card_primeFactors_le_four`, **an odd number with ω ≤ 4 is not weird**
(also `…_eq_four` and `pseudoperfect_of_odd_of_abundant_of_card_primeFactors_eq_four`). Files:
- `OddWeirdFourData.lean` (generated by `scripts/odd_pan_search.py 4 --lean`): the 584 odd primitive
  abundant numbers with ω ≤ 4 (8 with ω = 3, 576 with ω = 4, matching the session 8 count). Each
  comes with its factorization and a short list `X` of proper divisors with sum `σ(b) − 2b`, so that
  the *other* proper divisors sum to `b` (2310 numbers in total). The first format, listing the
  whole subset (36k numbers), took too long to elaborate.
- `OddWeirdFourCore.lean`: `certOK` (primality by trial division, σ from the factorization, and the
  divisors in `X`) and its soundness; the checker `chk` with soundness `chk_sound`. At each node,
  either a stride-2 bound `A/B · ∏(q+2i)/(q+2i−1) < 2` shows every completion is deficient, or the
  next prime `q` is chosen. Its exponent is either a *region* `x ≥ e` (bound `q/(q−1)`) or exact,
  and the bases' factorizations are consumed as primes are chosen (`step`); an emptied
  factorization means a base divides the prefix. `Sound` is the statement a node certifies, with
  combinators `sound_prune`, `sound_loop`, `sound_exp`.
- `OddWeirdFourChunks.lean` (generated by `scripts/odd_weird_chunks.py`): the search (65032 calls)
  split into 72 `decide +kernel` theorems of ≤ 1403 calls each, assembled into
  `sound_top : Sound R0 1 1 4 3 0` with the combinators.
- `OddWeirdFour.lean`: `sound_top` applied to the sorted prime factors of `n`.
- Classical (Liddy–Riedl: ω ≥ 6). New only as a formalisation. It closes another sub-case of the
  `sorry` in formal-conjectures `erdos_470.parts.i`.

**Failed, and why:**
- The first certificate format (full subset, 36k numbers) hit the heartbeat limit while elaborating
  (47 s); lists with 584 entries also need `maxRecDepth` raised. Fixed by the complement format.
- A single `decide +kernel` over the whole search ran out of memory (`std::bad_alloc`, cgroup
  limit 8 GB), even with fuel 300 instead of 100000. A subtree of 7.5k calls already needed
  5.5 GB: the kernel keeps every intermediate term in its cache. Scanning all 584 bases at every
  node (48M steps) was the first culprit; the consumed-factorization lists (`step`) brought that down
  to 2.3M steps, but it was still too much. Fixed by chunking: each theorem gets its own kernel
  cache. Lean also elaborates theorems in parallel, so the generated file sets
  `Elab.async false`.
- A filter that dropped bases divisible by any skipped `q` was wrong for composite `q` (it removed
  the bases with 9 ∣ b), and the search failed. Now the filtering happens only when a prime is chosen.

**Next step (in order):**
1. ω = 5 in Lean with the same pipeline (`odd_pan_search.py 5`, then a chunk generator for `j = 5`).
   First measure the search size: see "ω = 5 feasibility" below. The generator and `sound_top` are
   written for `j = 4`; parametrise them by `j`.
2. ω = 6 would be the first new result (beyond Liddy–Riedl). It needs a different leaf test: a
   prefix with a deficient part and a large last prime cannot be certified by a finite base list,
   so it needs the last-prime reduction from session 8. Only worth starting if ω = 5 is cheap.
3. Honest assessment unchanged: everything so far is classical; the formalisation is the deliverable.

### ω = 5 feasibility (measured this session)

`python3 scripts/odd_pan_search.py 5` did not finish within 15 minutes. For ω = 4 the same script takes
under 1 s: 8700 nodes in the abundance-leaf version, 65032 calls in the `chk` version. The script
factors every prefix by trial division, which becomes slow once the last primes get large. Before
anything in Lean: rewrite the count with the exact ratio carried along (no factoring) and measure
nodes, maximum prime and the number of bases. The kernel checked ~25k `chk` calls per minute here (65k in 153 s), so ~1M calls would take ~40 min,
too close to the 60-min CI limit. Above that, shrink the search first or split the build. Ideas for shrinking: drop the q-loop for the last prime (j = 1), where most of the work is
(1.0M of 1.4M list steps at ω = 4); there, only the primes in the finite base list can close a node.

## Daily summary (2026-11-08, session 10)

- **Approaches tried:** a reflective checker, "multiple of a certified base, or deficient", over sorted
  odd prime powers, for ω = 4. Certificates as complements (divisors left out), the bases as
  consumable factorizations, and the kernel check split into chunks assembled with combinators.
- **What failed and why:** one big `decide +kernel` exceeds the 8 GB memory limit (the kernel term
  cache); full-subset certificates were too slow to elaborate; one wrong filter (composite q). The
  ω = 5 count in naive Python does not finish within 15 min.
- **Advances:** in Lean, without `sorry`: odd ω ≤ 4 ⇒ not weird. Classical (Liddy–Riedl ω ≥ 6); new as a
  formalisation only. No new mathematical result.
- **Quota consumed:** one `lean-research` session (exact tokens: from PGAL's accounting). No network
  queries. About 15 module compilations, 3 full `lake build`s (one of them clean for the project's
  own modules, 435 s); Mathlib from the cache, never compiled. No money spent.
