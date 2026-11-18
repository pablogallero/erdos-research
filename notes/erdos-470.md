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

## Session 11 (2026-11-09): the last prime as a family

**Idea:** in the ω = 4 and ω = 5 searches almost all the work is the loop over the last prime `q`.
A deficient prefix `M` makes every prime `q ≤ σ(M)/D` (with `D = 2M − σ(M)`) give a *different*
primitive abundant number `Mq`, so a finite list of bases cannot cover them. Instead, decide all `q`
at once ("family" node):
- `Mq` (q prime, q ∤ M) is pseudoperfect **iff** there are `a ∈ P` and `k = D + a` with
  `kq ∈ P ∪ (M + P)`, where `P` = the subset sums of the proper divisors of `M`. Proof: the subset is
  `B ∪ q·A` with `ΣA = M − k`, `ΣB = kq`, and `M − k ∈ P ⇔ k − D ∈ P` by the symmetry
  `x ↦ σ(M) − M − x` of `P`.
- `P` is computed exactly: a bitset below `C = 2^15`, plus the interval `[c, σ(M) − M − c] ⊆ P`,
  proved by the chain condition over the sorted divisors (`d ≤ hi − lo + 1` extends the interval).
  For most `q`, `a = 0` works because `Dq` lies inside `P` or `M + P`. Only the primes in three
  windows of width ≈ `C/D` (near 0, near the gap `(σ−M, M)` and near `σ`) are tested one by one.
- If `Mq` is deficient but the region bound `U·q/(q−1) ≥ 2`, go through the exponents of `q`. Once
  `N = Mq^e` is abundant, test `σ(N) − 2N` as a base-`q` sum `Σ q^i s_i` with `s_i ∈ SS(div M)` and
  `s_e ∈ P` (digit DFS). An undecided test returns False, and the parent then splits the exponent.

**Results (Python, `scripts/odd_weird_family.py K`; exact arithmetic, not checked by Lean):**
- ω = 4: True, 911 nodes (vs 65032 `chk` calls in session 10), 0.1 s, so it agrees with the Lean proof.
- **ω = 5: True**, 447944 nodes, 234873 families, 104123 individually tested primes, 87788 exponent
  cases, about 2.5 min. So there is no odd weird number with exactly 5 distinct prime factors (given ω ≤ 4).
  This independently re-checks Liddy–Riedl's ω ≥ 6 (classical, *not new*). Note: this is the ω = 5 count
  that did not finish in session 10.
- ω = 6: **not feasible here.** In 25 min it did 4.4M nodes (≈ 1600 nodes/s), all inside `3^1` and
  `3^2`. The `3^1` subtree alone is ≈ 3.3M nodes, and the exponent of 3 went up to 21 at ω = 5. My
  estimate is ≥ 10^8 nodes, i.e. ≥ 15–20 h of pure Python. 90% of the time goes to `Pstruct`
  (generating and sorting the divisors of `M` for the chain condition). No C compiler or numpy is
  available (only `python3` and the Lean toolchain without `clang`), and background jobs are capped at 2 h.

**Lean (no sorry; standard axioms; full `lake build` OK, 7366 jobs; module ~7 s):** new
`ErdosResearch/OddWeirdLastPrime.lean`, imported from the root:
- `pseudoperfect_of_compl`: some proper divisors summing to `σ(n) − 2n` ⇒ pseudoperfect.
- `pseudoperfect_mul_prime`: the sufficient direction of the criterion above (`B ∪ q·A`).
- `sum_properDivisors_mul_prime`, `pseudoperfect_mul_prime_of_sum_divisors` (the `a = 0` test:
  divisors of `M` summing to `σ(Mq) − 2Mq`), plus a sanity example `945 = 135·7`.
- Classical and elementary. These are building blocks for a Lean version of the family search, not a new result.

**Failed, and why:**
- First family version: infinite loops. (i) With a region prefix (`U > R`), the family failed
  every time and the parent's exponent loop never ended; fixed by going through the exponents of `q`
  inside the family. (ii) `U ≥ 2` made the `q`-loop endless; fixed by failing fast.
- The `a` loop capped at 5000 missed `3^4·5^3·19^3·31` (it needs `a ≈ 7.8k`); fixed by choosing `a`
  analytically by interval intersection.
- An unsound clause `r − N ∈ P` in the exponent test was caught on re-reading the proof and removed. The exponent
  test with a full `Pstruct` of `M q^e` was too slow for large `e`; it was replaced by the digit DFS.
- Finding the holes bit by bit cost 55 s at ω = 4; with `bit_length` it is 0.1 s.

**Next step (in order):**
1. ω = 5 in Lean with families. Bottleneck: 235k families, each needing the interval certificate of
   `P(M)` (thousands of sorted divisors), which is far too much for `decide +kernel` (≈ 25k simple
   calls/min, 3 GB data limit for `lean` now). It would need a *multiplicative* interval lemma that
   avoids sorting the divisors. Sketch: if `SS(S₁) ⊇ [c, T₁−c]` and `SS(S₂)` has consecutive gaps
   `≤ T₁ − 2c + 1`, then `SS(S₁ ∪ S₂) ⊇ [c, T₁+T₂−c]`, applied prime by prime (`div(A p^e) = ⋃ p^i div A`).
   The middle gap `(σ−M, M)` of deficient `A` is the obstacle. Write that out on paper first.
2. ω = 6 (would be new): only with a much faster engine. Options: (a) the multiplicative lemma
   above also makes Python ≈ 10× faster (no sorting); (b) a resumable run split by the exponent of 3
   (`3^1` ≈ 3.3M nodes ≈ 35 min), spread over several sessions, with a checkpoint file. Even then it
   would be evidence only, not Lean-checked; label it that way.
3. Honest assessment: everything proved so far is classical. The only route to something new is
   ω = 6, and it is not close.

## Daily summary (2026-11-09, session 11)

- **Approaches tried:** collapsing the last-prime loop into "family" nodes, with an exact
  description of the subset sums of the divisors (bitset + interval + symmetry), in Python; the
  general last-prime lemmas in Lean.
- **What failed and why:** pure-Python ω = 6 (≥ 10^8 nodes estimated, divisor sorting dominates; no
  C/numpy here); several infinite loops and one unsound clause in early versions (fixed, see above).
- **Advances:** ω = 5 checked by computer (Python, not Lean) in 2.5 min. It confirms Liddy–Riedl (classical).
  New Lean module `OddWeirdLastPrime.lean` (general lemmas, no sorry). No new mathematical result.
- **Quota consumed:** one `lean-research` session (exact tokens from PGAL's accounting); ≈ 1 h of
  CPU on Python runs (one 25-min ω = 6 measurement); 3 Lean compilations + 1 full `lake build`
  (20 s, everything else cached); arXiv API queried once; no money spent.

## Session 13 (2026-11-13): faster family search, resumable ω = 6 run

**Lost work, noted:** the session 12 notes (in PGAL's progress file) describe a faster
`odd_weird_family.py` with a checkpoint at `/tmp/pgal-sesion/omega6.ck`, but neither is in this
branch: the script was the session 11 version, and `/tmp/pgal-sesion` only kept `progreso.md`. So the
session 12 PR was apparently not merged, and checkpoints outside the repo do not survive. I redid the
speed-up independently. **The ω = 6 checkpoint now lives in the repo:** `notes/data/omega6.ck`.

**Done (Python only; no Lean changes):** `scripts/odd_weird_family.py`
- `Pstruct0` (90 % of the time): (1) chain condition at C speed: `max(map(sub, rest, accumulate(...)))`
  (same condition `d ≤ S − 2c + 1`); (2) divisors of the prefix `f[:-1]` cached and only the last prime
  power multiplied in; (3) after the interval `[c, sp−c]` is known, bitset updates only for divisors
  `< c`, and the bits in `[c, C)` are set directly. This is exact: `sp − c ≥ C`, and a hole `x < c` can only be
  filled by sums of divisors `≤ x`.
- Checks: ω = 4 and ω = 5 give identical node/family/prime/exponent counts (447944 nodes); 20000 random
  factorisations give a `Pstruct0` identical to the session 11 version (8793 non-trivial).
  ω = 5: 130 s → 66 s on this machine.
- Resumable: `odd_weird_family.py K CKFILE` appends every subtree of depth ≤ 3 decided True (the key is
  `repr((f, un, ud, j, q0))`) and skips it on restart. These lines are facts, independent of the code version
  (modulo bugs), so speed-ups do not invalidate the file.
- Helper worker: `START3=E odd_weird_family.py K CKFILE` starts the top-level exponent loop of 3 at `E`.
  It writes to the same file but **never records the root** (its root answer is not a proof); the main
  run reloads the file at depth ≤ 1 before doing a node itself. Tested on ω = 5: helper `START3=2`,
  then the main run finishes True from the shared checkpoint (4979 nodes, 0.3 s).

**ω = 6 run (evidence only, not Lean):** main run (3^1) plus helper (`START3=2`) on the two cores, until about 02:47 UTC.
Status at the end of the session: see "ω = 6 status" below.

**Failed / pitfalls:** the first helper version would have written the root as True (unsound); caught
before running it on ω = 6. `ps`/`pkill` are missing here: kill via `/proc/*/cmdline`.

### ω = 6 status (end of session 13, 02:45 UTC)

- Run time: ≈ 25 min on one core with the session-11 code, then 74 min on 2 cores. Checkpoint
  `notes/data/omega6.ck`: 3208 lines, 200 KB.
- **3^1 done** (exact node `([(3, 1)], 4, 3, 5, 5)`: no odd weird number `3·m` with ω = 6;
  evidence, not Lean). About 25 min. Exponent of 5 up to 19.
- 3^2: all (3^2, 5^b) for b ≤ 22 done, still running (5^23 and beyond, and then 7, 11, … as the second prime).
- 3^3: b ≤ 20 done (helper).
- Rate ≈ 2.7k nodes/s per core. Each 3^a takes ≈ 30–60 min on one core, and the exponent of 5 grows with `a`.
  The exponent of 3 went up to 21 at ω = 5, so the whole run is likely **≥ 10–20 core-hours**, i.e. several sessions.

**Next step (in order):**
1. Resume, unchanged: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` (it
   continues in 3^2) and helper `START3=4 timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck`
   (3^3 is left to the main run). Stop both before the cutoff, and **the checkpoint must go into the PR**
   (outside the repo it is lost). With more cores: one helper per exponent of 3.
2. If 3^a keeps getting slower: the multiplicative interval lemma (session 11/12 sketch) to avoid sorting
   divisors. `Pstruct0` is still about 70 % of the time (bitset phase 1 plus `max(map(...))` over every divisor).
3. Honest assessment, unchanged: everything proved so far is classical. ω = 6 would be new (Liddy–Riedl give
   ω ≥ 6), but only as computer evidence; a Lean version is not in sight.

## Daily summary (2026-11-13, session 13)

- **Approaches tried:** re-implementing the speed-up of the family search (session 12 had been lost);
  a resumable ω = 6 run with the checkpoint inside the repo and two workers sharing it.
- **What failed and why:** session 12's work was not in the branch (unmerged PR / `/tmp` not
  persistent), so a session was lost; I redid it. The first helper version would have recorded an
  unproved root (caught before use). The main run duplicated the helper's work in 3^2 until it reloaded at depth ≤ 2.
- **Advances:** ω = 5 in 66 s (2×), with identical counts. ω = 6: 3^1 done; 3^2 and 3^3 well advanced. No new
  theorem, and no Lean changes (`lake build` OK, 7366 jobs; no sorry/axioms).
- **Quota consumed:** one `lean-research` session (tokens per PGAL's accounting); ≈ 2.8 h of CPU (2 cores,
  Python); 1 `lake build` (cached); no external APIs; no money spent.

## Session 16 (2026-11-16): Palomar first, then ω = 6 resumed

Most of the session went to Pablo's Palomar priority (`notes/palomar.md`): Lean/Mathlib v4.35.0, module
system everywhere, Challenge/Solution with `not_weird_of_odd_of_card_primeFactors_le_four` as one of the three
compared theorems, `lake comparator` OK locally. No mathematical change to #470.

**ω = 6 run (evidence only, not Lean):** resumed unchanged from `notes/data/omega6.ck` (3208 lines at the start)
with the main run plus a helper `START3=4`, both under `timeout` from 14:47 to about 15:51 UTC.
- Checkpoint now 5503 lines. **3^2 done** (node `([(3, 2)], 13, 9, 5, 5)`) and **3^3 done** (`([(3, 3)], 40, 27, 5, 5)`),
  in addition to 3^1 (session 13). 3^4: all (3^4, 5^b) with b ≤ 15 done.
- So, as computer evidence (Python, not Lean): no odd weird number with ω = 6 has 3-adic valuation 1, 2 or 3.
- Rate as before (≈ 2.7k nodes/s per core). Once the main run reached 3^4 it duplicated the helper's work
  until reloading at depth ≤ 2.

**Next step (in order):**
1. Resume: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` (continues in 3^4) and a
   helper `START3=5` (not 4: the main run is already in 3^4). The checkpoint must go into the PR.
2. Unchanged: the multiplicative interval lemma to speed up `Pstruct0`; everything proved so far is classical.

## Daily summary (2026-11-16, session 16)

- **Approaches tried:** redoing the Palomar package (third time); resuming the ω = 6 family search.
- **What failed and why:** sessions 14–15 never reached main, so the port was redone from scratch. A waiter loop
  matched its own command line (fixed by building the pattern at runtime). No mathematical failure.
- **Advances:** Palomar package complete locally (build + comparator OK). ω = 6: 3^2 and 3^3 finished; 3^4 up to 5^15.
- **Quota consumed:** one session; ≈ 2.1 h of CPU (2 cores, Python, 64 min); 3 `lake build`s + 1 `lake comparator`
  (no Mathlib compilation); GitHub/zbMATH/schema API reads only; no money spent.

## Session 17 (2026-11-16): Lean CI fix, then ω = 6 resumed

First, the Lean CI on main was red because `lean.yml` was invalid YAML (details in `notes/palomar.md`).
Fixed by quoting one step name. No mathematical change to #470.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (5503 lines) with the main run
(in 3^4) plus a helper `START3=5`, both under `timeout 4800`, from 21:41 to 23:01 UTC.
- Checkpoint now 6359 lines. 3^4: every (3^4, 5^b) with b ≤ 23 is done, and the main run was inside 5^24.
  3^5: (3^5, 5^b) with b ≤ 4 is done, and the helper was inside 5^5.
- Still holds as computer evidence: no odd weird number with ω = 6 and v_3 ∈ {1, 2, 3}.
  3^4 is not finished yet: the bound on b is still being reached.

**Next step (in order):**
1. Resume with the same two commands: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck`
   and helper `START3=5 timeout T python3 …`. The checkpoint must go into the PR.
2. Unchanged: the multiplicative interval lemma to speed up `Pstruct0`. Everything proved so far is classical.

## Daily summary (2026-11-16, session 17)

- **Approaches tried:** checked the CI of the Palomar package now on main; resumed the ω = 6 family search.
- **What failed and why:** the Lean workflow on main (8c7c6f49) failed with 0 jobs. An unquoted `": "` in a
  step name made the YAML invalid. Fixed. The Palomar preflight on that commit was already green.
- **Advances:** the CI fix; ω = 6 checkpoint 5503 → 6359 lines (3^4 up to 5^23, 3^5 up to 5^4).
- **Quota consumed:** one session; ≈ 2.7 h of CPU (2 cores, Python, 80 min); 1 `lake build` (cached);
  GitHub API reads only; no money spent.

## Session 18 (2026-11-16/17): Palomar handed over, then ω = 6 resumed

**Palomar:** main `0005a6dba7f327312141cd958a5640632dddeb7d` has both workflows green: "Lean" (run 43978396168)
and "Palomar preflight", mode full (run 43978398173). Pablo was notified on board card #106 with the full SHA and
the path `comparator.json` (repo root). Nothing was submitted to Palomar. No Lean changes this session.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (6359 lines) with the main run plus a
helper `START3=5`, both under `timeout 5000`, from 23:52 to 01:15 UTC.
- Checkpoint now 7627 lines. **3^4 is finished** (root `[(3, 4)]` recorded): together with earlier sessions,
  no odd weird number with ω = 6 and v_3 ∈ {1, 2, 3, 4} (computer evidence).
  3^5: every (3^5, 5^b) with b ≤ 10 is done; both workers were inside 5^11.
- **Inefficiency found:** after finishing 3^4, the main run entered 3^5 and duplicated the helper's subtree
  (the workers do not share progress in memory; some checkpoint lines appear twice, which is harmless).

**Next step (in order):**
1. Resume with main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` (it will skip
   finished 3^5 subtrees) and helper **`START3=6`** (not 5) so the two do not overlap. The checkpoint must go
   into the PR.
2. Unchanged: the multiplicative interval lemma to speed up `Pstruct0`. Everything proved so far is classical.

## Daily summary (2026-11-17, session 18)

- **Approaches tried:** verified the CI of main for Palomar; resumed the ω = 6 family search.
- **What failed and why:** nothing broke. Part of the 3^5 work was done twice (see above).
- **Advances:** Palomar hand-over to Pablo (card #106); 3^4 finished for ω = 6; checkpoint 6359 → 7627 lines.
- **Quota consumed:** one session; ≈ 2.8 h of CPU (2 cores, Python, 83 min); GitHub API reads only; no build;
  no money spent.

## Session 19 (2026-11-17): ω = 6 continued

**Palomar:** no reply from Pablo on card #106 yet. Main has moved on to `7cd609e` (merge of #18). On that commit
"Lean" and "Palomar preflight" are both green. The Palomar files have not changed since `0005a6db…`, so the hand-over
still holds. No Lean changes this session.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (7627 lines) with the main run (in 3^5)
plus a helper `START3=6`, both under `timeout 5300`, from 02:09 to 03:37 UTC. With `START3=6` the two runs did not
overlap.
- Checkpoint now 8242 lines. 3^5: every (3^5, 5^b) with b ≤ 13 is done, and the main run was inside 5^14 (17^14).
  3^6: every (3^6, 5^b) with b ≤ 6 is done, and the helper was inside 5^7 (17^10).
- Cost per (3^a, 5^b) subtree grows with b: about 15–20 min of one core each for 3^5 at b ≈ 12–14.

**Next step (in order):**
1. Resume with the same pair: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck`
   and helper `START3=6`. When the main run finishes 3^5, stop it and restart it with `START3=7` so it does not
   duplicate the helper. The checkpoint must go into the PR.
2. Unchanged: the multiplicative interval lemma to speed up `Pstruct0`. At the current rate the open range of v_3
   will take many sessions, so the speed-up matters more than more CPU. Everything proved so far is classical.

## Daily summary (2026-11-17, session 19)

- **Approaches tried:** resumed the ω = 6 family search with the two workers on disjoint subtrees.
- **What failed and why:** nothing failed.
- **Advances:** checkpoint 7627 → 8242 lines; 3^5 done up to 5^13, 3^6 done up to 5^6.
- **Quota consumed:** one session, ≈ 2.9 h of CPU (2 cores, Python, 88 min). Reads only, to the GitHub API and the
  board. No build, no money spent.

## Session 20 (2026-11-17): ω = 6 continued

**Palomar:** no reply from Pablo on card #106. Main is now `f2b6d3a` (merge of #19). "Lean" and "Palomar preflight"
are both green on it, and the Palomar files are unchanged, so the hand-over still holds. No Lean changes this session.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (8242 lines) with the main run (in 3^5)
plus a helper `START3=6`, both under `timeout 5100`, from 04:26 to 05:51 UTC.
- Checkpoint now 8791 lines. 3^5: every (3^5, 5^b) with b ≤ 16 is done, and the main run was inside 5^17 (17^12).
  3^6: every (3^6, 5^b) with b ≤ 11 is done, and the helper was inside 5^12 (17^4).
- Each (3^a, 5^b) subtree still costs about 15–25 min of one core. Finished roots: v_3 ∈ {1, 2, 3, 4}.

**Next step (in order):**
1. Resume with the same pair: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` and helper
   `START3=6`. When the main run finishes 3^5, restart it with `START3=7`. The checkpoint must go into the PR.
2. The multiplicative interval lemma to speed up `Pstruct0`. CPU alone will need many more sessions.

## Daily summary (2026-11-17, session 20)

- **Approaches tried:** resumed the ω = 6 family search with the two workers on disjoint subtrees.
- **What failed and why:** nothing failed.
- **Advances:** checkpoint 8242 → 8791 lines; 3^5 done up to 5^16, 3^6 done up to 5^11.
- **Quota consumed:** one session, ≈ 2.8 h of CPU (2 cores, Python, 85 min). Reads only, to the GitHub API and the
  board. No build, no money spent.

## Session 21 (2026-11-17): ω = 6 continued

**Palomar:** no reply from Pablo on card #106. Main is now `77f6bef` (merge of #20), and both "Lean" and "Palomar
preflight" are green on it. The Palomar files are unchanged. No Lean changes this session.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (8791 lines) with the main run (in 3^5)
plus a helper `START3=6`, both under `timeout 5100`, from 06:41 to 08:06 UTC.
- Checkpoint now 9213 lines. 3^5: every (3^5, 5^b) with b ≤ 19 is done, and the main run was inside 5^20.
  3^6: every (3^6, 5^b) with b ≤ 14 is done, and the helper was inside 5^15 (17^12).
- Finished roots: v_3 ∈ {1, 2, 3, 4}. Max b done so far: 3^1 → 19, 3^2 → 24, 3^3 → 28, 3^4 → 26 (b is bounded, so
  these roots are complete).

**Next step (in order):**
1. Resume with the same pair: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` and helper
   `START3=6`. When the main run finishes 3^5, restart it with `START3=7`. The checkpoint must go into the PR.
2. The multiplicative interval lemma to speed up `Pstruct0`. CPU alone will need many more sessions.

## Daily summary (2026-11-17, session 21)

- **Approaches tried:** resumed the ω = 6 family search with the two workers on disjoint subtrees.
- **What failed and why:** nothing failed.
- **Advances:** checkpoint 8791 → 9213 lines; 3^5 done up to 5^19, 3^6 done up to 5^14.
- **Quota consumed:** one session, ≈ 2.8 h of CPU (2 cores, Python, 85 min). Reads only, to the GitHub API and the
  board. No build, no money spent.

## Session 22 (2026-11-17): ω = 6 continued

**Palomar:** no reply from Pablo on card #106. Main is now `9888c19` (merge of #21), and both "Lean" and "Palomar
preflight" are green on it. The Palomar files are unchanged. No Lean changes this session.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (9213 lines) with the main run (in 3^5)
plus a helper `START3=6`, both under `timeout 5340`, from 08:58 to 10:27 UTC.
- Checkpoint now 9567 lines. 3^5: every (3^5, 5^b) with b ≤ 21 is done, and the main run was inside 5^22.
  3^6: every (3^6, 5^b) with b ≤ 17 is done, and the helper was inside 5^18.
- Finished roots: v_3 ∈ {1, 2, 3, 4}. Max b done so far: 3^1 → 19, 3^2 → 24, 3^3 → 28, 3^4 → 26.
- Pace: about 2–3 values of b per root per 90-min session. Each b gets slower as it grows, so CPU alone will not
  finish 3^5 and 3^6 soon, and v_3 ≥ 7 is still untouched.

**Next step (in order):**
1. Resume with the same pair: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` and helper
   `START3=6`. When the main run finishes 3^5, restart it with `START3=7`. The checkpoint must go into the PR.
2. The multiplicative interval lemma to speed up `Pstruct0`. Given the pace above, it is now the priority over raw CPU.

**Daily summary:**
- **Approaches tried:** only the resumable ω = 6 family search, on 2 cores.
- **What failed and why:** nothing failed.
- **Advances:** checkpoint 9213 → 9567 lines; 3^5 done up to 5^21, 3^6 done up to 5^17.
- **Quota consumed:** one session, ≈ 3 h of CPU (2 cores, Python, 89 min). Reads only, to the GitHub API and the
  board. No build, no money spent.

## Session 23 (2026-11-17): faster family search, ω = 6 continued

**Palomar:** no reply from Pablo on card #106. Main is now `f595018` (merge of #22), and both "Lean" and "Palomar
preflight" are green on it. The Palomar files are unchanged. No Lean changes this session.

**Speed-up of `scripts/odd_weird_family.py` (exact, same search):** a cProfile of ω = 5 (112 s under the profiler)
showed `isprime` at 20 s (10.5M calls, almost all on small q), the chain condition `max(map(sub, …))` at 28 s,
`divisors` + sort at 19 s and the phase-1 bitset loop at 22 s.
- `isprime`: an exact sieve of Eratosthenes below 2^24 (Miller–Rabin above that, as before).
- Chain condition: checked by hops instead of three full C passes. From index j, every divisor up to
  `S_j − 2c + 1` (found with `bisect_right`, since the divisors are sorted) passes, because S only grows. The
  next index either passes with its own S or is a genuine violation, so the condition is exactly the old one.
  S is kept incrementally with slice sums, so no prefix-sum list is built.
- Checks: ω = 4 and ω = 5 give the same node/family/q/star counts (911/560/1087/278 and
  447944/234873/104123/87788). On 20000 random prefixes the old and new `Pstruct0` agree.
  ω = 5 under the profiler: 112 s → 67 s (≈ 1.7×).
- The multiplicative interval lemma was **not** implemented. After this change the remaining cost is the
  phase-1 bitset loop (22 s) and `divisors` + sort (18 s). The lemma would only help with the second, and it
  needs a careful soundness proof for the middle gap. It is lower priority now.

**ω = 6 run (evidence only, not Lean):** resumed from `notes/data/omega6.ck` (9567 lines). The old script ran
11:14–11:34 UTC; then both workers were restarted with the faster script under `timeout 3900` (11:34–12:39 UTC).
The restart lost only the depth-3 subtree each worker was in the middle of.
- Checkpoint now 10069 lines (9567 → 9576 in the first 20 min, → 10069 in the next 65 min).
  3^5: every (3^5, 5^b) with b ≤ 24 is done (main was inside 5^25). 3^6: every (3^6, 5^b) with b ≤ 21 is done
  (helper was inside 5^22).
- Finished roots: v_3 ∈ {1, 2, 3, 4}. Max b on finished roots: 3^1 → 19, 3^2 → 24, 3^3 → 28, 3^4 → 26.
  So 3^5 should be close to finishing (a few more b).

**Next step (in order):**
1. Resume with the same pair: main `timeout T python3 scripts/odd_weird_family.py 6 notes/data/omega6.ck` and helper
   `START3=6`. When the main run finishes 3^5 (record `([(3, 5)], …)`), restart it with `START3=7`. The checkpoint
   must go into the PR.
2. More speed: the phase-1 bitset loop and `divisors` + sort are what is left. Possible approach: carry the low
   bitset of SS(div(prefix)) down the DFS. Below C the subset sums of the proper divisors equal those of all the
   divisors once M ≥ C, so each child adds only its new divisors below C.

**Daily summary:**
- **Approaches tried:** profiling and two exact speed-ups of the family search; the resumable ω = 6 search on 2 cores.
- **What failed and why:** nothing failed. A first profile with `nice -n 19` got no CPU and was killed by its
  `timeout` before printing (rerun with `timeout -s INT`, which lets cProfile print).
- **Advances:** ≈ 1.7× faster search with identical counts; checkpoint 9567 → 10069 lines; 3^5 up to 5^24, 3^6 up to 5^21.
- **Quota consumed:** one session, ≈ 3 h of CPU (2 cores, Python, ~85 min, plus ~8 min of profiling/tests).
  Reads only, to the GitHub API and the board. No build, no money spent.

## Session 24 (2026-11-17/18): ω = 6 continued (no code or Lean changes)

**Palomar:** no reply on card #106. Main is `e7eaa49b`, and both "Lean" and "Palomar preflight" are green on it.

**Done:** resumed the pair (main + helper `START3=6`, both under `timeout 5100`, 23:01–00:26 UTC).
Checkpoint `notes/data/omega6.ck` 10069 → 10512 lines. 3^5 done for 5^b with b ≤ 27 (now inside b = 28);
3^6 done for b ≤ 24 (now inside b = 25). Finished roots: v_3 ∈ {1,2,3,4}. Still evidence only, not Lean.

**Next step (in order):** unchanged from session 23: (1) resume the same pair; when the main run records
`([(3, 5)], …)`, restart it with `START3=7`; the checkpoint must go into the PR. (2) Carry the low bitset down
the DFS for speed (at ~3 b per root per session, CPU alone needs many more sessions).

**Daily summary:**
- **Approaches tried:** only the resumable ω = 6 search on 2 cores.
- **What failed and why:** nothing.
- **Advances:** checkpoint +443 lines; 3^5 up to 5^27, 3^6 up to 5^24.
- **Quota consumed:** one session, ≈ 2.8 h of CPU (2 cores × ~85 min, Python). Reads only (GitHub API, board).
  No build, no money spent.

## Session 25 (2026-11-18): ω = 6 continued (no code or Lean changes)

**Done:** resumed the pair (main + helper `START3=6`, both under `timeout 5300`, 01:16–02:44 UTC).
Checkpoint `notes/data/omega6.ck` 10512 → 10956 lines. 3^5 done for 5^b with b ≤ 29 (now inside b = 30);
3^6 done for b ≤ 28 (now inside b = 29). Finished roots: v_3 ∈ {1,2,3,4}. Still evidence only, not Lean.
Palomar: no reply on card #106; main `1314c236` has "Lean" and "Palomar preflight" green.

**Next step (in order):** unchanged: (1) resume the same pair; when the main run records `([(3, 5)], …)`,
restart it with `START3=7`; the checkpoint must go into the PR. (2) Carry the low bitset down the DFS for speed.

**Daily summary:**
- **Approaches tried:** only the resumable ω = 6 search on 2 cores.
- **What failed and why:** nothing.
- **Advances:** checkpoint +444 lines; 3^5 up to 5^29, 3^6 up to 5^28.
- **Quota consumed:** one session, ≈ 2.9 h of CPU (2 cores × ~88 min, Python). Reads only (GitHub API, board).
  No build, no money spent.

## Session 26 (2026-11-18): ω = 6 continued (no code or Lean changes)

- Palomar: no reply on card #106. On main `10e5fdb4`, both "Lean" and "Palomar preflight" are green.
- ω = 6 (evidence only, not Lean): checkpoint `notes/data/omega6.ck` went from 10956 to 12497 lines (11689 after removing duplicates).
  **3^5 is finished**, so the roots v_3 ∈ {1,…,5} are done. For 3^6 the whole 5-branch is done (5^b, b ≤ 31),
  and the 7-branch is done for 7^c with c ≤ 6. For 3^7, 5^b is done for b ≤ 6.
- Trap: after the main run finished 3^5 it moved into 3^6 and duplicated the helper. I killed it and restarted it
  with `START3=7`.
- **Checkpoint format (review of this PR).** `notes/data/omega6.ck` is written by `scripts/odd_weird_family.py 6 CKFILE`
  (function `search`). Each line is `repr((f, un, ud, j, q0))` of a subtree of depth ≤ 3 that the search decided True
  (no odd weird number in it): `f` = prefix [(prime, exponent)], `un/ud` = the reduced upper bound on σ(n)/n used for
  the rest, `j` = primes still to place, `q0` = smallest allowed next prime. The loader reads it into a set and skips
  those subtrees. The same prefix `f` appears with two different `un/ud` on purpose: `search1` calls each prefix twice,
  once with the region bound q/(q−1) (“exponent ≥ e”) and once with the exact ratio σ(q^e)/q^e. These are different
  subproblems, not contradictory results. **Duplicates:** 811 lines were exact repeats, written when two workers
  (main run + `START3` helper) finished the same subtree concurrently (the overlap trap noted in sessions 18 and 26).
  They were removed in this session (12500 → 11689 lines, same set of keys, every line parses with `ast.literal_eval`).
  Order is first occurrence; the loader does not depend on order.
- **Reliability.** This is evidence only, not a proof: no Lean check. The checkpoint only skips work; the claim
  “no odd weird number with ω = 6” needs a single run without `START3` to finish with `6 True` against this file.
  Sound only as far as the script is (ω = 4 agrees with Lean; ω = 5 agrees with Liddy–Riedl).
- Next step: run helper `START3=6` and a second run with `START3=7`, both under `timeout`. When one of them
  finishes its root, restart it with `START3=8`. The faster path is to carry the low bitset down the DFS.

## Session 27 (2026-11-18): ω = 6 continued (no code or Lean changes)

- Palomar: no reply on card #106. On main `81722651c2f5e16b53c2e6197e4a6bc56a60ab27`, both "Lean" and "Palomar preflight" are green.
- ω = 6 (evidence only, not Lean): checkpoint `notes/data/omega6.ck` went from 11689 to 13096 lines (after dedupe).
  **3^6 is finished** (key `([(3, 6)], 1093, 729, 5, 5)` recorded), so the roots v_3 ∈ {1,…,6} are done.
  For 3^7, the 5-branch is done for 5^b with b ≤ 15. For 3^8, it is done for b ≤ 2.
- Trap repeated: the `START3=6` run finished its root at ~06:35 and moved into 3^7, overlapping the `START3=7` run
  for ~15 min. That produced 184 duplicate lines, which I removed (first-occurrence order, same key set). I then stopped
  that run and restarted it with `START3=8`. Fix worth making: an env var `STOP3` so that a helper stops after its root.
- Next step: run `START3=7` and `START3=8`, both under `timeout`. When one of them finishes its root, restart it with `START3=9`.
  Faster path: carry the low bitset down the DFS.

**Daily summary:**
- **Approaches tried:** only the resumable ω = 6 search on 2 cores.
- **What failed and why:** nothing mathematical. Workers overlapped once (see trap).
- **Advances:** the 3^6 root is closed; 3^7 is up to 5^15; 3^8 is up to 5^2.
- **Quota consumed:** one session, ≈ 3 h of CPU (2 cores × ~90 min, Python). Reads only (GitHub API, board).
  No build, no money spent.
