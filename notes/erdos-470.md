# Erdős #470: odd weird numbers ($10)

Statement (erdosproblems.com/470, checked 2026-11-08): `n` is *weird* if `σ(n) ≥ 2n` and `n` is not
pseudoperfect. (i) Are there odd weird numbers? (ii) Are there infinitely many primitive weird
numbers? The $10 is for (i) (Guy B2). Lean: `FormalConjectures/ErdosProblems/470.lean` uses
Mathlib's `Nat.Weird` (abundant ∧ ¬ pseudoperfect). Both parts are still `sorry` there, as are the
variants `odd_weird_10_pow_21` (Fang) and the Liddy–Riedl variant.

**2026-11-23, parity bug fixed (`notes/omega6-invalidated.md`):** every ω = 6 result below (roots, checkpoints,
ROOTTEST verdicts) comes from the buggy `family` and is **not evidence**. ω = 4 (1996 nodes) and ω = 5 (706995 nodes) were
re-checked True with the fix. The workers restart from 3^1 (generation v2, no seed).

**ω = 6 search, operative rule since 2026-11-22 (overrides every "Next"/"resume START3=…"/"launch-next" line below):**
the search runs by itself in pgal's StatefulSet `owf` (2 workers, `run-root.sh worker`, erdos-research #58), with its data in
`/lean/state/owf`. A session NEVER runs `owf`, `odd_weird_family.py`, `START3`, `STOP3`, `ROOTTEST` or `launch-next`; it only
runs `sh scripts/owf-queue.sh read` (read-only). Full flow: `notes/omega6-job.md`. The commands below are a record of what earlier sessions did.

**ω = 6 checkpoint location (since session 31):** the repo stores only **`notes/data/omega6.ck.gz`**; the plain
`notes/data/omega6.ck` is no longer tracked (it is gitignored). Every older session below that says
`notes/data/omega6.ck` means the decompressed file: run `gunzip -kf notes/data/omega6.ck.gz` before resuming and
`gzip -9 -c notes/data/omega6.ck > notes/data/omega6.ck.gz` afterwards. Before running the C binary after any change
to the search code, `sh scripts/validate-owf.sh` must print `ALL OK`.

**Split since session 50 (1 MB file limit):** `omega6.ck.gz` is **frozen** at 36729 lines; new lines go to
**`omega6-2.ck.gz`** (lines 36730 onwards of the plain file). To run: `zcat notes/data/omega6.ck.gz
notes/data/omega6-2.ck.gz > /tmp/pgal-sesion/omega6.ck`; afterwards `tail -n +36730 /tmp/pgal-sesion/omega6.ck |
gzip -9 -c > notes/data/omega6-2.ck.gz` (never rewrite the frozen file). When `omega6-2.ck.gz` nears 1 MB, freeze it
too and start `omega6-3.ck.gz` the same way.

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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):**
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):** unchanged from session 23: (1) resume the same pair; when the main run records
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

**Next step (in order; history — for the ω = 6 search see `notes/omega6-job.md`):** unchanged: (1) resume the same pair; when the main run records `([(3, 5)], …)`,
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

## Session 28 (2026-11-18): ω = 6 continued, `STOP3` added (no Lean changes)

- `scripts/odd_weird_family.py`: new optional env var `STOP3=E`. A worker stops (exit 0, root never recorded) once
  the root exponent 3^E is finished, so helpers no longer drift into the next root. Search logic unchanged; ω = 4
  still gives 911 nodes and True. Test: `STOP3=1` on ω = 4 stops after 3^1 as expected.
- ω = 6 (evidence only, not Lean): ran `START3=7 STOP3=7` and `START3=8 STOP3=8` for ~88 min each.
  Checkpoint `notes/data/omega6.ck` 13096 → 13633 lines, **0 duplicates** (thanks to STOP3).
  3^7: 5-branch done for 5^b with b ≤ 20. 3^8: done for b ≤ 4. Finished roots still v_3 ∈ {1,…,6}.
- Next step: resume with `START3=7 STOP3=7` and `START3=8 STOP3=8` under `timeout`. When one exits with
  "STOP3 reached", start `START3=9 STOP3=9`. Speed-up still pending: carry the low bitset down the DFS.

**Daily summary:**
- **Approaches tried:** resumable ω = 6 search on 2 cores, plus a small tooling fix (STOP3).
- **What failed and why:** nothing.
- **Advances:** 3^7 from 5^15 to 5^20; 3^8 from 5^2 to 5^4.
- **Quota consumed:** ≈ 3 h CPU (2 cores × 88 min, Python). Board read only. No build, no money spent.

## Session 29 (2026-11-18): ω = 6 continued (no code or Lean changes)

- Palomar: card #106 is still open with no reply. The Palomar files are unchanged.
- ω = 6 (evidence only, not Lean): ran `START3=7 STOP3=7` and `START3=8 STOP3=8` under `timeout 5300` (~88 min each).
  Checkpoint `notes/data/omega6.ck` 13633 → 14425 lines, **0 duplicates**. 3^7: 5^b done for b ≤ 25.
  3^8: 5^b done for b ≤ 10. Finished roots are still v_3 ∈ {1,…,6}. Neither worker reached "STOP3".
- Next step: as in session 28 (resume both workers; start `START3=9 STOP3=9` when one prints "STOP3 reached").
  Speed-up still pending: carry the low bitset down the DFS.

**Daily summary:**
- **Approaches tried:** resumable ω = 6 search on 2 cores.
- **What failed and why:** nothing.
- **Advances:** 3^7 from 5^20 to 5^25; 3^8 from 5^4 to 5^10.
- **Quota consumed:** ≈ 3 h CPU (2 cores × 88 min, Python). Board read only. No build, no money spent.

## Session 31 (2026-11-18/19): C/GMP port of the family search; ω = 6 continued with it (no Lean changes)

Task from Pablo (mail "Erdos"): port `odd_weird_family.py` to C/GMP with the same checkpoint, validate on ω = 4/5,
continue ω = 6 with it, optionally carry the bitset down the DFS, and estimate how many roots 3^E are left.
(Session 30 had done a port, but it never reached the repo; this one was written again from scratch.)

- **New `scripts/odd_weird_family.c`** (build: `sh scripts/build-odd-weird-family.sh /tmp/owf`, i.e.
  `gcc -O2 -o /tmp/owf scripts/odd_weird_family.c -lgmp`; the binary is not committed). It is a line-by-line port:
  same node order, counters, failure list, START3/STOP3, and the same checkpoint keys (Python repr), so both
  versions share `notes/data/omega6.ck`. Hot spot (sorted divisors + `Pstruct0`) runs in `unsigned __int128`
  when σ < 2^126, in fixed 256-bit integers when σ < 2^254 (primes < 2^64), and in mpz otherwise; the bitset
  shift-or only touches words that can change (exact: bits above T+d are zero, bits ≥ c are set afterwards).
  The divisor list of (q, e) is (q, e−1)'s list merged with base·q^e (incremental).
- **Validation:** ω = 4 identical counters (911 nodes). ω = 5 identical counters
  (447944 / 234873 / 104123 / 87788) and a **byte-identical checkpoint** with Python, on all three paths
  (auto, `PSLOW=1` = mpz only, `PSLOW=2` = w256). Cross-resume Python→C and C→Python (cut after 12 s / 6 s)
  finish True with the same key set as a full run. ω = 6 (3^8 slice, 1.5M nodes, 590k families): auto and
  mpz-only give identical counters and checkpoint; in a 90 s run, Python's new keys are an exact prefix of C's.
  **Reproducible check (mandatory after any change to either version):** `sh scripts/validate-owf.sh` builds the C
  binary in a temp dir and, for K = 4 and 5, compares Python vs C (auto, `PSLOW=1`, `PSLOW=2`) result line,
  counters, failure list and checkpoint bytes, then does both cross-resumes (timeout-cut run finished by the other
  version, same key set as a full run). Exits non-zero on any mismatch. Last run: `ALL OK` in 1 min 46 s.
- **Speed:** ω = 5 in 5.2 s CPU vs 36 s Python (≈ 7×). In ω = 6 / 3^8 (σ often > 2^126) the w256 path took a
  500k-node slice from 12.2 s to 7.6 s CPU; overall ≈ 4–5× Python there.
- **Bitset carried down the DFS (optional): not done.** Session 30 measured only ≈ 8 % for it, and the sorted
  merge would have to be redone and revalidated; the 256-bit path was the better use of the time.
- **ω = 6 (evidence only):** C workers `START3=7 STOP3=7` (→ **3^7 finished**), then `START3=8 STOP3=8` and
  `START3=9 STOP3=9`. Finished roots: v_3 ∈ {1,…,7}. See progreso for the 5^b reached.
- **Estimate of the remaining roots.** The top-level loop over v_3 = E stops at the first E whose *region*
  subtree (`search([(3,E)], …, un/ud = 3/2, j = 5, q0 = 5)`) is True. `ROOTTEST=E` runs just that call.
  Calibration on ω = 5: False for E ≤ 22 in ≤ 4k nodes, True at 23 (18k nodes), exactly where the real run closes.
  ω = 6: **False (rigorous, deterministic) for E = 8, 12, 16, 20, 25, 30, 35, 36, 37, 38, 40** (≤ 1.5M nodes,
  ≤ 2 min each); E = 45 and 50 are still running after 2.2M nodes / 4 min without failing (inconclusive).
  So the loop goes past E = 40 unless one of the untested E ≤ 39 is True (on ω = 5 the pattern was monotone).
  Estimate (rough): what is established is only a **lower bound**: the loop does not close at E = 40 (rigorous),
  so **at least ≈ 33 roots remain after 3^7** (unless an untested E ≤ 39 closes, which the monotone ω = 5 pattern
  makes unlikely). There is **no measured upper bound**: E = 45 and 50 are unresolved, and E ≈ 41–50 (≈ 33–42 roots)
  is an extrapolation, not a measurement; the closing exponent could be higher. Per root the C version needs very
  roughly 2–3 core-hours (3^8/3^9 advance ≈ 8–9 values of b per 35 min per worker; b goes to ≈ 26–31 and later
  b are heavier; large E not measured), so the order of magnitude is **≈ 100 core-hours, possibly more**. The first
  thing to tighten it is to let `ROOTTEST=45` / `ROOTTEST=50` finish.
- **Checkpoint format change:** `omega6.ck` grew past 1 MB (17599 lines, 0 duplicates; 3^8 done for 5^b with b ≤ 25,
  3^9 for b ≤ 18 at the stop), so the repo now stores **`notes/data/omega6.ck.gz`** (gzip -9) and ignores the plain
  file. Before running: `gunzip -kf notes/data/omega6.ck.gz`; after: `gzip -9 -c notes/data/omega6.ck > notes/data/omega6.ck.gz`.
  The plain file is deleted from the repo in this change (`git rm notes/data/omega6.ck`, done in follow-up 2; the
  earlier `git rm --cached` did not survive into the PR), so only the `.gz` is tracked.
  **Integrity check of the `.gz` (done on 2026-11-19):** `gzip -t` OK; it decompresses to 17599 lines with 0
  duplicate lines; every one of the 14425 lines of the previously tracked `omega6.ck` is present, plus 3174 new
  lines (keys from 3^7 to its end and from 3^8 / 3^9). Commands: `zcat … | sort | uniq -d | wc -l` → 0;
  `comm -23 old new` → 0; `comm -13 old new` → 3174.

### Session 31 follow-up 2 (review, 2026-11-19)

- **Single canonical checkpoint:** `notes/data/omega6.ck` is now deleted in the diff (`git rm`); only
  `notes/data/omega6.ck.gz` is tracked. The old plain file stays in git history (commit 5598d477).
- **Verifiable evidence:** new plain-text `notes/data/omega6-evidence.txt` with the sha256 of the `.gz` and of its
  decompressed content, the line count (17599), 0 duplicates, the proof that the previous checkpoint (14425 lines,
  sha256 given) is an exact byte prefix of the new one (+3174 lines: 768 in 3^7, 1105 in 3^8, 1301 in 3^9), the
  backup procedure, and the real output of `sh scripts/validate-owf.sh` (`ALL OK`, exit 0) together with the
  sha256 of the validated `.py`, `.c` and script.
- **Backup:** the checkpoint is append-only. The backup before a run is the committed file plus a session-local
  copy. The prefix check above shows that no line was lost when session 31 resumed ω = 6 with C.
- **ROOTTEST (C, one core each, region subtree of root 3^E):**
  - E = 45: **False** after 7,066,159 nodes (789 s). The loop does not close at 45 (rigorous for this algorithm).
  - E = 50: no failure after 20.6M nodes (80 min, at 5^8); stopped at 02:38 UTC for lack of time, inconclusive.
  - E = 60: visits **exactly the same nodes** as E = 50: all 83 progress lines (every 200k nodes, up to 16.6M nodes)
    have identical node and family counts and prefixes. Stopped at 16.6M nodes. E = 45 diverges from E = 50 at 2.8M nodes.
  - Observation (not proved): from some E on, the region subtree no longer depends on E. So either it is True for
    all large E (the loop closes at the first such E, plausibly between 46 and 50), or it is False for all of them,
    and then the top-level loop over v_3 never closes and the search does not terminate for ω = 6.
- **Estimate of the remaining roots, with its margin:**
  - Lower bound: the loop does not close at any tested E ≤ 45, so it runs over 3^8 … 3^46 at least, i.e.
    **≥ 39 roots after 3^7**. This is rigorous for the tested E; an untested E in 41–44 could still close, but the
    monotone ω = 5 pattern makes that unlikely.
  - Upper bound: **not available**. If E = 50 turns out True, the loop closes at some E ≤ 50, so there are **39–43
    roots** (central ≈ 41). If E = 50 is False, the same-tree observation suggests that no larger E closes either, and
    then the number of roots is unbounded (the method would need a different stopping argument).
  - Cost: the region subtree alone of a large root takes > 70 min of one C core. With the earlier 2–3 core-hours per
    root, that gives **≥ ≈ 80–120 C core-hours** if the loop closes by E = 50, and no bound otherwise.
- **Next step for the estimate:** let `ROOTTEST=50` finish (several core-hours, under `timeout`, across sessions if
  needed; it has no checkpoint of its own). Its answer decides between "39–43 roots" and "the loop does not terminate".

### Session 32 (2026-11-19): 3^8 finished; ROOTTEST=50 made resumable (no code or Lean changes)

- C binary built from `scripts/odd_weird_family.c` with sha256 b0841f9c… (the version that `validate-owf.sh`
  validated), so no re-validation was needed.
- **3^8 finished** (`START3=8 STOP3=8`, about 36 min, 19.96M nodes, `nfail 0`). Roots v_3 ∈ {1..8} are done.
  Then `START3=9 STOP3=9` ran until the end of the session.
- **ROOTTEST is now resumable:** given a CKFILE, `ROOTTEST=E /tmp/owf 6 CKFILE` records the True subtrees at depth
  1–3. Their keys (prefix `[(3,E), …]`, ratio 3/2 at depth 1) are exactly the keys that the main search builds for
  the region subtree of root 3^E. So they are sound facts, and the main search could reuse them. They are kept
  apart in `notes/data/roottest50.ck.gz` so that the ω = 6 evidence stays separate. Merging them into
  `omega6.ck` later is valid. Nothing is recorded at depth 0 under ROOTTEST: it calls `search` with L = 1, and a
  True result at L = 1 is the region answer for 3^50, which is a valid fact.
- ROOTTEST=50 ran 5200 s this session (22.4M nodes, no failure) and reached `[(3,50),(5,9),(17,8),…]`; it is still
  inconclusive. Its checkpoint `roottest50.ck.gz` has 569 lines (0 duplicates), so the next session resumes it
  instead of starting from scratch (session 31 lost 80 min of the same work).
- 3^9 (about 28 min this session): depth-2 subtrees done for 5^b with b ≤ 22 (it was b ≤ 18).
- Checkpoint `omega6.ck.gz`: 17599 → 18825 lines, 0 duplicates, and the old file is an exact byte prefix. Every line
  is complete (the workers were killed by PID; the file is flushed after each line).
- Lost: one core sat idle for about 22 min after 3^8 finished (around 03:44) until I noticed at 04:06. Check more
  often than every 25 min, or chain `START3=E+1` automatically.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** (1) keep going with ROOTTEST=50 (resumes) on one core and `START3=9 STOP3=9` on the other. When 3^9
  finishes, start 10. (2) If ROOTTEST=50 turns out False, stop the ω = 6 loop: it does not terminate by this
  method (see session 31 follow-up 2).

### Session 33 (2026-11-19, 05:25–06:55 UTC): 3^9 finished; ROOTTEST=50 continued (no code or Lean changes)

- C binary from `scripts/odd_weird_family.c` with sha256 b0841f9c… (validated version), so no re-validation.
- **3^9 finished** (`START3=9 STOP3=9`, ~40 min this session, 19.35M nodes, `nfail 0`). Roots v_3 ∈ {1..9} are done.
  Then `START3=10 STOP3=10` ran ~50 min: depth-2 subtrees done for 5^b with b ≤ 15 (the log reached 5^16).
- ROOTTEST=50 (resumed from its checkpoint) ran 90 min, about 9.6M more nodes with no failure, and reached
  `[(3,50),(5,11),(17,14),…]`. Still inconclusive. Its checkpoint grew from 569 to 723 lines.
- Checkpoints: `omega6.ck.gz` 18825 → 20893 lines; `roottest50.ck.gz` 569 → 723 lines. 0 duplicates in both, each old
  file is an exact byte prefix of the new one, and both end in a newline.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` (it picks up from its checkpoint) and `START3=10 STOP3=10`. When 3^10 finishes, start 11.
  ROOTTEST=50 advances only about 1 b of 5 per 90 min, so it may need several sessions. Consider giving it both cores.

### Session 34 (2026-11-19, 07:45–09:15 UTC): 3^10 and ROOTTEST=50 continued (no code or Lean changes)

- C binary from `scripts/odd_weird_family.c` with sha256 b0841f9c… (validated version), so no re-validation.
- `START3=10 STOP3=10`, 90 min, ~31.6M nodes, no failure: depth-2 subtrees of 3^10 now done for 5^b with b ≤ 25
  (log reached 5^26). 3^10 is not finished yet. Roots v_3 ∈ {1..9} remain the finished ones.
- ROOTTEST=50 (resumed), 90 min, ~8.2M nodes, no failure: depth-2 subtrees done for 5^b with b ≤ 12 (now at 5^13, 19^7).
  Still inconclusive.
- Checkpoints: `omega6.ck.gz` 20893 → 21595 lines; `roottest50.ck.gz` 723 → 884 lines. 0 duplicates in both, each
  old file is an exact byte prefix of the new one, and both end in a newline.
  sha256 (decompressed): omega6 2c523c15…, roottest50 57663962….
- Failed: nothing. Pace is the limit (3^10: ~10 b of 5 per 90 min; ROOTTEST=50: ~2 b per 90 min).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume both runs exactly as before (`ROOTTEST=50` on rt50.ck; `START3=10 STOP3=10` on omega6.ck; when 3^10
  prints "STOP3 reached", start 11). Speed work (profile w256 path; bitset carry) is still the way to shorten this.

### Session 35 (2026-11-19, 10:03–11:36 UTC): 3^10 finished; 3^11 and ROOTTEST=50 continued (no code or Lean changes)

- C binary from `scripts/odd_weird_family.c` with sha256 b0841f9c… (validated version), so no re-validation.
- **3^10 finished** (`START3=10 STOP3=10`, 12.78M nodes in this run, `nfail 0`, "STOP3 reached" at ~10:52).
  Roots v_3 ∈ {1..10} are done. Then `START3=11 STOP3=11` ran ~43 min (~35M nodes, no failure): depth-2 subtrees
  of 3^11 done for 5^b with b ≤ 12 (the log reached 5^13).
- ROOTTEST=50 (resumed), 93 min, ~7.2M nodes, no failure: depth-2 subtrees done for 5^b with b ≤ 14 (now at 5^15, 17^12).
  Still inconclusive.
- Checkpoints: `omega6.ck.gz` 21595 → 23378 lines; `roottest50.ck.gz` 884 → 1029 lines. 0 duplicates in both, each old
  file is an exact byte prefix of the new one, and both end in a newline.
  sha256 (decompressed): omega6 b80c5ce3…, roottest50 28fa1943….
- Failed: nothing. Pace is still the limit.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` on rt50.ck and `START3=11 STOP3=11` on omega6.ck; when 3^11 finishes, start 12.

### Session 36 (2026-11-19, 12:26–13:58 UTC): 3^11 and ROOTTEST=50 continued (no code or Lean changes)

- C binary from `scripts/odd_weird_family.c` with sha256 b0841f9c… (validated version), so no re-validation (ω = 4
  build smoke test: 911 nodes, True).
- `START3=11 STOP3=11`, 90 min, ~32.6M nodes, no failure: depth-2 subtrees of 3^11 done for 5^b with b ≤ 22 (the log
  reached 5^23). 3^11 is not finished. Roots v_3 ∈ {1..10} are still the finished ones.
- ROOTTEST=50 (resumed), 90 min, ~5.4M nodes, no failure: depth-2 subtrees done for 5^b with b ≤ 16 (now at 5^17).
  Still inconclusive. One stretch of ~15 min without progress lines (slow node, process was running).
- Checkpoints: `omega6.ck.gz` 23378 → 24074 lines; `roottest50.ck.gz` 1029 → 1168 lines. 0 duplicates in both, each old
  file is an exact byte prefix of the new one, and both end in a newline. Snapshots were taken with `head -n N` of the
  live file, so they never include a half-written line.
  sha256 (decompressed): omega6 5b6a59eb…, roottest50 6dc69e1a….
- Failed: nothing. Pace is still the limit.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` on rt50.ck and `START3=11 STOP3=11` on omega6.ck; when 3^11 finishes, start 12.

### Session 37 (2026-11-19, 14:46–16:16 UTC): 3^11 and ROOTTEST=50 continued (no code or Lean changes)

- C binary from `scripts/odd_weird_family.c` with sha256 b0841f9c… (validated version), so no re-validation (ω = 4
  build smoke test: 911 nodes, True). Board empty (no reply from Pablo); Palomar files unchanged.
- `START3=11 STOP3=11`, 89 min, ~23M nodes, no failure: depth-2 subtrees of 3^11 done for 5^b with b ≤ 29 (the log
  reached 5^30). 3^11 is not finished. Roots v_3 ∈ {1..10} are still the finished ones.
- ROOTTEST=50 (resumed), 89 min, ~5.8M nodes, no failure: depth-2 subtrees done for 5^b with b ≤ 17 (now at 5^18,
  17^11). Still inconclusive.
- Checkpoints: `omega6.ck.gz` 24074 → 24613 lines; `roottest50.ck.gz` 1168 → 1251 lines. 0 duplicates in both, each old
  file is an exact byte prefix of the new one, both end in a newline (snapshots with `head -n N`).
  sha256 (decompressed): omega6 05d3cf63…, roottest50 0d3792b7….
- Failed: nothing. Pace is still the limit (3^11 is a slow root: ~3 sessions so far).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` on rt50.ck and `START3=11 STOP3=11` on omega6.ck; when 3^11 finishes, start 12.

### Session 38 (2026-11-19/20, 23:00–00:38 UTC): 3^11 finished, 3^12 started, ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- **3^11 finished** (`STOP3 reached`, 11.35M nodes in this run, nfail 0), so the roots v_3 ∈ {1..11} are done. About 10 idle
  core-minutes were lost before I saw it. `START3=12 STOP3=12` then ran for 37 min (~35M nodes, no failure). The log reached
  5^13, so subtrees are done for b ≤ 12 according to the log.
- ROOTTEST=50 (resumed), 98 min, ~4.4M nodes, no failure. The log reached (5,19),(17,13), so 5^b is done for b ≤ 18. Still
  inconclusive.
- Checkpoints: `omega6.ck.gz` 24613 → 26318 lines; `roottest50.ck.gz` 1251 → 1329 lines. 0 duplicates, the old files are exact
  byte prefixes, and snapshots were taken with `head -n N`. sha256 (decompressed): omega6 a29c302f…, roottest50 9bb3cfe2….
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=12 STOP3=12`, and check every 10 min so that 3^13 starts as soon as 3^12 finishes.

### Session 39 (2026-11-20, 01:25–02:51 UTC): 3^12 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=12 STOP3=12`, 85 min, ~30M nodes, no failure. The log reached (5,22), so 5^b is done for b ≤ 21. 3^12 is not finished,
  so the finished roots are still v_3 ∈ {1..11}.
- ROOTTEST=50 (resumed), 85 min, ~3.8M nodes, no failure. The log reached (5,20),(17,12), so 5^b is done for b ≤ 19. Still
  inconclusive.
- Checkpoints: `omega6.ck.gz` 26318 → 26956 lines; `roottest50.ck.gz` 1329 → 1403 lines. 0 duplicates, the old files are exact
  byte prefixes, and the final file ends with a newline. sha256 (decompressed): omega6 5a8401cd…, roottest50 197314ac….
- Failed: nothing. Pace is the only limit: ~10 b per session on 3^12, ~1 b per session on ROOTTEST=50.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=12 STOP3=12`, and check every 10 min so that 3^13 starts as soon as 3^12 finishes.

### Session 40 (2026-11-20, 03:40–05:13 UTC): 3^12 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=12 STOP3=12`, 92 min, ~24M nodes, no failure. The log reached (5,28),(17,13), so 5^b is done for b ≤ 27. 3^12 is not
  finished, so the finished roots are still v_3 ∈ {1..11}.
- ROOTTEST=50 (resumed), 92 min, ~4.0M nodes, no failure. The log reached (5,21),(17,13), so 5^b is done for b ≤ 20. Still
  inconclusive.
- Checkpoints: `omega6.ck.gz` 26956 → 27393 lines; `roottest50.ck.gz` 1403 → 1478 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 790714ae…, roottest50 7c041605….
- Failed: nothing. Pace is the only limit (~6 b per session on 3^12 at high b, ~1 b per session on ROOTTEST=50).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=12 STOP3=12`, check every 10 min, start `START3=13 STOP3=13` when 3^12 finishes.

### Session 41 (2026-11-20, 05:58–07:28 UTC): 3^12 finished, 3^13 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- **3^12 finished** at 06:18 (`STOP3 reached: 3^12 done`, n 5449571 in that run, nfail 0), so the finished roots are v_3 ∈ {1..12}.
- `START3=13 STOP3=13` from 06:18, 69 min, no failure. The log reached (5,16), so 5^b is done for b ≤ 15.
- ROOTTEST=50 (resumed), 89 min, ~2.8M nodes, no failure. The log reached (5,22),(17,7), so 5^b is done for b ≤ 21. Still
  inconclusive.
- Checkpoints: `omega6.ck.gz` 27393 → 29220 lines; `roottest50.ck.gz` 1478 → 1548 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 bdb5cc56…, roottest50 c21d72eb….
- Failed: nothing. Pace is the only limit (~16 b per session on a fresh root, ~1 b per session on ROOTTEST=50).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=13 STOP3=13`; check every 10 min and start `START3=14 STOP3=14` when 3^13 finishes.

### Session 42 (2026-11-20, 08:15–09:45 UTC): 3^13 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=13 STOP3=13`, 89 min, ~25.6M progress count, no failure. The log reached (5,23), so 5^b is done for b ≤ 22. 3^13 not
  finished; finished roots still v_3 ∈ {1..12}.
- ROOTTEST=50 (resumed), 89 min, ~2.0M nodes, no failure. The log is still at (5,22) (now (17,15)). Still inconclusive.
- Checkpoints: `omega6.ck.gz` 29220 → 29762 lines; `roottest50.ck.gz` 1548 → 1555 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 8bb6dcbc…, roottest50 0087d5ee….
- Failed: nothing. ROOTTEST=50 is now very slow inside 5^22 (7 keys in a session).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume both runs as before; start `START3=14 STOP3=14` when 3^13 finishes.

### Session 43 (2026-11-20, 10:33–12:01 UTC): 3^13 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=13 STOP3=13`, 88 min, ~19.6M progress count, no failure. The log reached (5,27), so 5^b is done for b ≤ 26. 3^13 not
  finished; finished roots still v_3 ∈ {1..12}.
- ROOTTEST=50 (resumed), 88 min, ~3.4M nodes, no failure. **5^22 finished** (~11:10); the log reached (5,23),(17,11). Still
  inconclusive.
- Checkpoints: `omega6.ck.gz` 29762 → 30087 lines; `roottest50.ck.gz` 1555 → 1628 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 17302a67…, roottest50 876cdb13….
- Failed: nothing. Pace only (~4 b per session on 3^13 at high b, ~1 b per session on ROOTTEST=50).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume both runs as before; start `START3=14 STOP3=14` when 3^13 finishes.

### Session 44 (2026-11-20/21, 23:00–00:30 UTC): 3^13 finished, 3^14 started, ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=13 STOP3=13`: **3^13 finished** at ~23:30 ("STOP3 reached", n = 6231060 in this run, nfail 0), so finished roots are
  now v_3 ∈ {1..13}. Then `START3=14 STOP3=14` for ~59 min, no failure; the log reached (5,14), so 5^b is done for b ≤ 13.
- ROOTTEST=50 (resumed), 89 min, ~1.2M nodes, no failure. The log is at (5,23),(17,14). Still inconclusive.
- Checkpoints: `omega6.ck.gz` 30087 → 31891 lines; `roottest50.ck.gz` 1628 → 1632 lines. 0 duplicates, the old files are exact
  byte prefixes. sha256 (decompressed): omega6 c0196a5e…, roottest50 4bfb1805….
- Failed: nothing. Pace only (ROOTTEST=50 inside 5^23 is very slow: 4 keys this session).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=14 STOP3=14`; start `START3=15 STOP3=15` when 3^14 finishes.

### Session 45 (2026-11-21, 01:19–02:50 UTC): 3^14 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=14 STOP3=14`, 90 min, ~24M progress count, no failure. The log reached (5,20), so 5^b is done for b ≤ 19. 3^14 not
  finished; finished roots still v_3 ∈ {1..13}.
- ROOTTEST=50 (resumed), 90 min, ~3.6M nodes, no failure. **5^23 finished** (~02:05); the log reached (5,24),(17,12). Still
  inconclusive.
- Checkpoints: `omega6.ck.gz` 31891 → 32342 lines; `roottest50.ck.gz` 1632 → 1706 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 d1a69736…, roottest50 1c6cdcd3….
- Failed: nothing. Pace only. Watch the size: `omega6.ck.gz` is now 649 KB (+~8 KB/session); split it before 1 MB.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=14 STOP3=14`; start `START3=15 STOP3=15` when 3^14 finishes.

### Session 46 (2026-11-21, 03:36–05:08 UTC): 3^14 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=14 STOP3=14`, 91 min, ~19.6M progress count, no failure. The log reached (5,25),(17,15), so 5^b is done for b ≤ 24.
  3^14 not finished; finished roots still v_3 ∈ {1..13}.
- ROOTTEST=50 (resumed), 91 min, ~1.2M nodes, no failure; the log is still inside (5,24) (reached (17,15)). Still inconclusive;
  5^24 is very slow (3 new keys), like 5^22 and 5^23 were.
- Checkpoints: `omega6.ck.gz` 32342 → 32714 lines; `roottest50.ck.gz` 1706 → 1709 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 f77e4507…, roottest50 59eb1ec3….
- Failed: nothing. Pace only. `omega6.ck.gz` is now 645 KiB (660 KB); split it before 1 MB.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `ROOTTEST=50` and `START3=14 STOP3=14`; start `START3=15 STOP3=15` when 3^14 finishes.

### Session 47 (2026-11-21, 05:55–07:24 UTC): 3^14 and ROOTTEST=50 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=14 STOP3=14`, 88 min, ~17.2M progress count, no failure. The log reached (5,29), so 5^b is done for b ≤ 28.
  3^14 not finished; finished roots still v_3 ∈ {1..13}.
- ROOTTEST=50 (resumed), 88 min, ~0.8M nodes, no failure; still inside (5,24) (log at (17,16)). Still inconclusive;
  only 1 new key, so 5^24 is the slowest slice so far.
- Checkpoints: `omega6.ck.gz` 32714 → 33015 lines; `roottest50.ck.gz` 1709 → 1710 lines. 0 duplicates, the old files are exact
  byte prefixes, and both end with a newline. sha256 (decompressed): omega6 2794de1a…, roottest50 b2be0063….
- Failed: nothing. Only slow progress. `omega6.ck.gz` is now 669 KB; split it before it reaches 1 MB.
- Assessment: ROOTTEST=50 has stalled in 5^24 (≈ 4 keys in 3 sessions). With one core it may take many more sessions to finish.
  Consider giving both cores to 3^14/3^15, or profiling ROOTTEST in 5^24, before spending more CPU on it.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `START3=14 STOP3=14` (b ≥ 29 left) and `ROOTTEST=50`; start `START3=15 STOP3=15` when 3^14 finishes.

### Session 48 (2026-11-21, 08:09–09:40 UTC): 3^14 finished; 3^15 and 3^16 started (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- **Decision:** ROOTTEST=50 was NOT resumed. It had stalled in 5^24 (≈ 4 keys in 3 sessions), so its core went to roots that
  make real progress. Its checkpoint `roottest50.ck.gz` is unchanged (1710 lines).
- `START3=14 STOP3=14`: **3^14 finished** at 08:29 (`n` 3908304 in this last stretch, nfail 0), so the roots v_3 ∈ {1..14} are done.
- `START3=15 STOP3=15`, 90 min, no failure: log at (5,16),(17,8), so 5^b is done for b ≤ 15.
- `START3=16 STOP3=16` (started 08:29), 70 min, no failure: log at (5,15),(17,8), so 5^b is done for b ≤ 14.
- Checkpoint: `omega6.ck.gz` 33015 → 35844 lines (725 KB). 0 duplicates, the old file is an exact byte prefix, and it ends with a
  newline. sha256 (decompressed): fd263be6…. **About 3–4 sessions left before 1 MB:** split it (e.g. `omega6.ck.gz` frozen plus
  `omega6-2.ck.gz` for new lines, concatenated with `zcat a b > plain` before running) at the start of the next session or the one after.
- Failed: nothing.
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** resume `START3=15 STOP3=15` and `START3=16 STOP3=16`; when one prints "STOP3 reached", start the next free exponent (17).
  ROOTTEST=50 stays parked unless it gets profiled.

### Session 49 (2026-11-21, 10:25–11:56 UTC): 3^15 and 3^16 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- `START3=15 STOP3=15`, 89 min, no failure: log at (5,21), so 5^b is done for b ≤ 20. Not finished.
- `START3=16 STOP3=16`, 89 min, no failure: log at (5,22), so 5^b is done for b ≤ 21. Not finished.
- Finished roots still v_3 ∈ {1..14}. ROOTTEST=50 stays parked (`roottest50.ck.gz` unchanged, 1710 lines).
- Checkpoint: `omega6.ck.gz` 35844 → 36729 lines (748 KB). 0 duplicates, the old file is an exact byte prefix, and it ends
  with a newline. sha256 (decompressed): 41ad8d0d….
- Failed: nothing. Only slow progress (≈ 6 b per root per session).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** split the checkpoint before it reaches 1 MB (freeze `omega6.ck.gz`, put new lines in `omega6-2.ck.gz`, run on
  `zcat a b > plain`). Then resume `START3=15 STOP3=15` and `START3=16 STOP3=16`, and start 17 when one prints "STOP3 reached".

### Session 50 (2026-11-21/22, 23:00–00:28 UTC): checkpoint split; 3^15 and 3^16 continued (no code or Lean changes)

- C binary with sha256 b0841f9c… (validated version); ω = 4 build smoke test: 911 nodes, True. Board empty.
- **Checkpoint split** (the .gz was at 748 KB): `omega6.ck.gz` frozen at 36729 lines (byte-unchanged); new lines in
  `omega6-2.ck.gz` (614 lines, 18.6 KB). `zcat omega6.ck.gz omega6-2.ck.gz` is byte-identical to the live plain file
  (37343 lines, 0 duplicates, ends with a newline; sha256 5b490ca9…). Procedure at the top of this file.
- `START3=15 STOP3=15`, 87 min, no failure: log at (5,25), so 5^b is done for b ≤ 24. Not finished.
- `START3=16 STOP3=16`, 87 min, no failure: log at (5,26), so 5^b is done for b ≤ 25. Not finished.
- Finished roots still v_3 ∈ {1..14}. ROOTTEST=50 stays parked (`roottest50.ck.gz` unchanged, 1710 lines).
- Failed: nothing. Only slow progress (≈ 4 b per root per session).
- **Next (superseded 2026-11-22: sessions never run the search, see `notes/omega6-job.md`):** `zcat` both parts into the plain file, resume `START3=15 STOP3=15` and `START3=16 STOP3=16`; start 17 when one prints
  "STOP3 reached". Afterwards write `tail -n +36730 plain | gzip -9 -c > notes/data/omega6-2.ck.gz`.

## Session 51 (2026-11-22): the search moves out of sessions (task from Pablo)

- The ω = 6 search now runs as Kubernetes Jobs, one per root 3^E (max 2), with its checkpoint in the persistent volume.
  Sessions only run `scripts/owf-queue.sh status | export | launch-next`. Details, outcomes and deployment are in `notes/omega6-job.md`.
- Nothing has been applied to the cluster: the image, namespace/PVC names and `deploy/owf/quota.yaml` are waiting on Pablo (board card #143).
- No ω = 6 computation was run in this session (by design). The queue starts at 3^15 and 3^16 from the state of session 50.
- **Next:** once deployed, run only the three queue commands above. Until then, no ω = 6 run; work on Lean or the multiplicative interval lemma.

## Session 52 (2026-11-22, 03:31–~03:45 UTC): chain-condition lemma in Lean (no search run)

- Board: card #143 (deploy the ω = 6 Job) still open with no answer, so no queue command was run and, by the operative
  rule, no `owf` either. Used the session for Lean, as planned in session 51.
- New `ErdosResearch/SubsetSumChain.lean` (imported from the root; no sorry; axioms propext/choice/Quot.sound;
  full `lake build` OK, 9067 jobs; `check-lean-sources.py` OK; module ~5 s). It formalises the soundness of the
  interval certificate used by `odd_weird_family.{py,c}` (`Pstruct0`'s chain condition):
  - `ChainOK` (decidable): each element, read from the largest, is ≤ 1 + sum of the rest;
  - `subsetSum_of_chainOK_list` / `subsetSum_of_chainOK_finset`: then every `m ≤` total is a subset sum;
  - `Complete.cons`, `complete_append`: a base certified another way (the search's bitset of small divisors) extended by
    the chain condition, which is exactly the shape the search uses for odd prefixes;
  - `pseudoperfect_of_chainOK`: chain + not deficient ⇒ pseudoperfect (never applies to odd `n`; sanity examples on 12 and 945).
- Classical: zbMATH confirms Stewart, *Sums of distinct divisors*, Amer. J. Math. 1954 (Zbl 0056.27004); Srinivasan 1948
  (practical numbers) was not found in zbMATH, so it is cited from memory only. New only as formalisation. It is one building block towards a Lean version of the family search; the multiplicative interval
  lemma (session 12 sketch) is still open.
- Failed (minor): declaring `theorem List.foo` inside a namespace made `List.sum` resolve to the wrong namespace;
  `Finset.sort` does not reduce under `decide` (used explicit lists); the lemma is `List.sum_toFinset`, not `Finset.…`.
- **Next:** if #143 is answered, only `scripts/owf-queue.sh status | export | launch-next`. Otherwise: (1) the
  bitset-base half in Lean (a decidable check that a short list is complete, `decide +kernel`), then the multiplicative
  interval lemma.

## Session 53 (2026-11-22, 04:26–~05:10 UTC): interval gluing lemma in Lean (no search run)

- Board: card #143 (deploy the ω = 6 Job) still open with no answer, so by the standing rule no queue command and no `owf`.
- New `ErdosResearch/SubsetSumGlue.lean` (imported from the root; no sorry; standard axioms). It is the additive core of
  the *multiplicative interval lemma* (session 11 sketch), written for `SS(s)` = subset sums of a finset `s`:
  - `glue`: `A ⊇ [c, T − c]`, `0 ∈ B`, and after every `x < U` an element `b ∈ B`, `b ≤ U`, `b ≤ x + (T − 2c) + 1`
    ⇒ `A + B ⊇ [c, T + U − c]` (take the largest `b ≤ m − c`, capped at `U`);
  - `subsetSums_union` (disjoint ⇒ `SS s₁ + SS s₂ ⊆ SS (s₁ ∪ s₂)`), `subsetSums_image_mul` (`k·SS s ⊆ SS (k·s)`);
  - `glue_subsetSums` / `glue_subsetSums_complete`: the interval step `SS(s₁ ∪ s₂) ⊇ [c, T + U − c]`;
  - `divisors_mul_prime`: `div(n p) = div n ∪ p·div n`, disjoint, for a prime `p ∤ n`.
- Elementary and classical; a building block, not a new result. **Still open (paper first):** the middle gap
  `(σ(A) − A, A)` of a deficient `A`, i.e. how to choose `c` so that `p·div A` has gaps `≤ T − 2c + 1` once the bitset
  base is small. First idea (checked below, it only reaches abundant `A`): with `s₁ = div A` (interval `[c, σ(A) − c]`) and `s₂ = p·div A`, the gaps of
  `SS(s₂)` are `p·(gaps of SS(div A))`; the large gaps of `SS(div A)` sit only below `c` and above `σ(A) − c`
  (symmetry), so the condition reduces to `p·c ≲ σ(A) − 2c`, i.e. it holds for primes `p < (σ(A) − 2c)/c`.
- Checks: full `lake build` OK (9068 jobs, 0 warnings); `#print axioms` = propext/choice/Quot.sound;
  `scripts/check-lean-sources.py` OK.
- **Numerical check of the sketch (throwaway Python, not the ω = 6 search):** odd `A < 6000`, primes `3 ≤ p < 60`, `p ∤ A`.
  With `c = c(A)` the smallest `c` such that `SS(div A) ⊇ [c, σ(A) − c]`, and `g` the largest gap of `SS(div A)`, the glue
  condition `p·g ≤ σ(A) − 2c + 1` held in 125 cases, and in **exactly** those 125 cases `SS(div(Ap)) ⊇ [c, σ(A)(1+p) − c]`
  was true (0 unsound, as the lemma guarantees; also 0 missed in this range). **But** a base interval with `2c ≤ σ(A)` exists
  only for 10 values of `A` (945, 1575, 2205, 2835, 3465, 4095, 4725, 5355, 5775, 5985), all abundant. For the *deficient*
  prefixes the search actually handles, `SS(div A)` has no centred interval at all (the middle gap), so the first glue step
  never starts there. This confirms that the middle gap is the real obstacle, not the gluing.
- Failed: the first full-build call hung for 30 min on a stray `cat` reading stdin (my mistake; killed, then the build ran in ~25 s
  because everything else was cached). Lean compiled on the first try; one unused hypothesis (`U ∈ B`) was removed.
- **Next:** if #143 is answered, only `scripts/owf-queue.sh status | export | launch-next`. Otherwise: (1) a glue variant for
  a deficient `A`, with two intervals (`[c, A' ]` and its mirror `[σ − A', σ − c]`) plus the gap between them, i.e. what
  `Pstruct0` stores (bitset + interval + symmetry). Check numerically first how it propagates through `p·div A`. (2) Only then
  formalise the prime step with `glue_subsetSums` + `subsetSums_image_mul` + `divisors_mul_prime`.

## Session 54 (2026-11-22, 05:53–~06:10 UTC): the prime step on proper divisors (no search run)

- Board: card #143 (deploy the ω = 6 Job) still open with no answer, so by the standing rule no queue command and no `owf`.
- **Idea that removes session 53's obstacle:** work with the *proper* divisors `D(M)`, not `div M`. For a prime `p ∤ M`,
  `D(Mp) = D(M) ∪ {M} ∪ p·D(M)`. Glue `A = SS(D M)` (centred interval `[c, s − c]`, `s = σ(M) − M`) with
  `B = SS({M} ∪ p·D M)`. The gaps of `B` are at most `p·g` (scaled copy) and `M − p s` (jump to the shifted copy), so the
  middle gap of `div M` never appears. Result: `SS(D(Mp)) ⊇ [c, s' − c]` with `s' = s + M + p s`, **and the same `c`**.
- New `ErdosResearch/SubsetSumPrimeStep.lean` (imported from the root; no sorry; axioms propext/choice/Quot.sound; full
  `lake build` OK, 9069 jobs, no warnings in the new module; `check-lean-sources.py` OK):
  - `properDivisors_mul_prime`, `sum_properDivisors_mul_prime'` (`∑ D(np) = s + (n + p s)`);
  - `interval_properDivisors_mul_prime`: if `SS(D n) ⊇ [c, s − c]`, the gaps of `SS(D n)` on `[0, s]` are `≤ g`,
    `p g + 2c ≤ s + 1` and `n + 2c ≤ (p + 1) s + 1`, then `SS(D(np)) ⊇ [c, s' − c]`;
  - `gap_of_interval` / `gap_properDivisors_mul_prime`: the gap bound `g` carries over to `D(np)` (old gaps below `c`, the
    interval in the middle, complement symmetry `sub_mem_subsetSums` at the top), so **the step can be iterated** prime by prime
    with fixed `(c, g)`;
  - `pseudoperfect_mul_prime_of_interval`: if also `c ≤ np` and `np + c ≤ s'`, then `np` is pseudoperfect.
- Numerical check (`scripts/prime_step_check.py 4000 80`, exact bitsets, ~1 min): of 1994 odd deficient `M < 4000`, **1968** have
  a centred interval on `D(M)` (session 53 found none on `div M`). Over pairs `(M, p)`, `p < 80`, `p ∤ M`, the condition holds in
  1079 cases, **0 unsound** (as the lemma guarantees), 1247 missed (it is conservative, mainly because `g` is the global max gap,
  which comes from the low end).
- Elementary; new only as a formalisation. A building block for a Lean version of the family search, not a new result on #470.
- **Next:** if #143 is answered, only `scripts/owf-queue.sh status | export | launch-next`. Otherwise: (1) prime powers
  (`D(M p^e)`, e.g. as `p^e·D(M) ∪ …`, or by gluing `p^i·SS(D M)` layers), (2) a decidable base check (bitset for `SS(D M)`
  below `c` plus the chain condition) that produces `(c, g)` by `decide +kernel` for one concrete prefix, then use
  `pseudoperfect_mul_prime_of_interval` to settle a whole family of last primes `q` at once. Measure first how many of the search's
  families (`Pstruct0` cases) the condition covers.

## Session 55 (2026-11-22, 06:50–~07:15 UTC): the prime-power step (no search run)

- Board: card #143 (deploy the ω = 6 Job) still open with no answer, so by the standing rule no queue command and no `owf`.
- **Split for prime powers:** for a prime `p ∤ n`, `D(n p^(e+1)) = D(n) ∪ {n} ∪ p·D(n p^e)`: the scaled part is `p` times the
  *previous level*, not `p·D(n)`. The glue only needs the interval `[c, s − c]` on the base `D(n)` and gaps `≤ g` on the scaled
  part, and `gap_of_interval` keeps the gap bound `g`. So the **same** session-54 conditions `p g + 2c ≤ s + 1`,
  `n + 2c ≤ (p + 1) s + 1` (`s = ∑ D n`) work for every exponent (the second one only gets easier, since `∑ D(n p^e) ≥ s`).
- New `ErdosResearch/SubsetSumPrimePow.lean` (imported from the root; no sorry; axioms propext/choice/Quot.sound; full
  `lake build` OK, 9070 jobs; no warnings in the new module; `check-lean-sources.py` OK):
  - `interval_union_insert_image` (abstract glue step `A ∪ {n} ∪ p·B`, `B` only needs gaps);
  - `properDivisors_mul_prime_pow_succ`, `sum_properDivisors_mul_prime_pow_succ`;
  - `interval_properDivisors_mul_prime_pow`: for every `e`, `SS(D(n p^e)) ⊇ [c, ∑ D(n p^e) − c]` with gaps `≤ g`;
  - `pseudoperfect_mul_prime_pow_of_interval`: if also `c ≤ n p^e` and `n p^e + c ≤ ∑ D(n p^e)`, `n p^e` is pseudoperfect.
- Numerical check: `scripts/prime_step_check.py 600 40 3` (new optional argument `E`): whenever the condition holds, the interval
  and the gap bound hold for `e = 1, 2, 3` (**0 unsound**); 58 pseudoperfect certificates over all `e`. E = 1 output unchanged.
- Elementary; new only as a formalisation. Not a new result on #470.
- **Decidable base certificate:** new `ErdosResearch/SubsetSumCert.lean` (imported from the root; same checks, full `lake build`
  OK, 9071 jobs; axioms propext/choice/Quot.sound):
  - `ssBits l` = subset-sum bitset of a list (`b ||| b <<< d`, GMP-accelerated in the kernel); soundness
    `mem_subsetSums_of_testBit` (duplicate-free list);
  - Boolean checks `intervalOK b c s`, `gapOK b g s`, with soundness lemmas;
  - `pseudoperfect_mul_prime_pow_of_cert`: one `decide +kernel` on the base `n` (list = `D n`, interval, gaps) plus linear
    conditions in `p` ⇒ `n p^e` pseudoperfect;
  - `pseudoperfect_of_excess_mem` (**excess test**: `m ≤ ∑ D m` and `∑ D m − m ∈ SS(A)`, `A ⊆ D m` ⇒ pseudoperfect) and
    `pseudoperfect_mul_prime_pow_of_cert'`, which uses the excess test when the excess is below `c`, so only plain
    abundance `n p^e ≤ ∑ D(n p^e)` is needed;
  - examples: `pseudoperfect_315_mul_prime` (`315 p`, primes `11 ≤ p ≤ 103`) and **`not_weird_525_mul_prime`**: no `525 q`
    (`q` prime, `q ∤ 525`) is weird. That is a whole last-prime family settled in Lean by one kernel check of 525's bitset
    (`c = 18`, `g = 2`; `q = 17` has excess 6 < c and uses the excess test). Each base check takes a few seconds.
  - `not_weird_mul_prime_of_cert` (**family decider**): base certificate + hypotheses linear in `q` ⇒ `¬ (n q).Weird`; each
    instance is `omega` plus at most one bit lookup. `not_weird_525_mul_prime` and `not_weird_495_mul_prime` use it.
- **Coverage (new `scripts/cert_coverage.py LIM W`, exact):** odd deficient `M < 3·10^5`, all primes `q > P(M)` with `Mq` abundant.
  ω(M) = 3: 87 families, 655 primes; the interval alone covers 649, and with the excess test **all 655**. ω(M) = 4: 165
  families, 4167 primes, **all covered** by the interval alone. Bias: small `M` only, exponent of `q` = 1.
  ω(M) = 5, `M < 10^6`: 258 families, 19843 primes; interval alone 19842, with the excess test **all 19843**
  (`python3 scripts/cert_coverage.py 1000000 5`, ~3 min).
- **Chain probe (Python only, `scripts/chain_cert_probe.py [LIMB]`):** for the search's prefixes with large exponents, a full
  bitset of `D(n)` is impossible, but `interval_properDivisors_mul_prime_pow` keeps `(c, g)`. So: a bitset only for a small base `b`
  (a sub-product of `N`, `b ≤ LIMB`), then add the remaining prime powers one at a time (ascending or descending order). On 57
  random abundant ω = 6 candidates `N = prefix · q`: LIMB = 2·10^4 certifies 0, LIMB = 10^6 certifies 14. Failures (e.g.
  `3^10·7^2·17^6·29^10·37·q`): every dense base needs the high power of 3, and every 3-free base is sparse (`c`, `g` in the thousands).
- **Idea for those (not checked yet):** raise an exponent inside the chain with the other split
  `D(m p^(e+1)) = D(m p^e) ∪ {m p^e} ∪ p^(e+1)·D(m)` (`p ∤ m`). This is again `interval_union_insert_image`, with multiplier `p^(e+1)`, interval part
  `D(m p^e)` and gap part `D(m)`. Condition: `p^(e+1) g_m + 2c ≤ ∑D(m p^e) + 1`. Measure it in the probe before formalising.
- **Next (if #143 still unanswered):** (1) a Lean *chain* certificate: a recursive `∑D` (from `sum_properDivisors_mul_prime_pow_succ`)
  plus a list of (prime, exponent) steps checked by `decide +kernel` from a bitset base; (2) the exponent-raising split above, measured
  with the chain probe first; (3) a generator emitting `not_weird_mul_prime_of_cert` instances per prefix.

## Session 56 (2026-11-22, 07:59–~08:20 UTC): the exponent-raising step and step lists (no search run)

- Board: card #143 (deploy the ω = 6 Job) still open with no answer, so by the standing rule no queue command and no `owf`.
- **Measured first (new `scripts/raise_step_probe.py [LIMB]`, Python only):** the split `D(m p^(e+1)) = D(m p^e) ∪ {m p^e} ∪
  p^(e+1)·D(m)` with conditions `p^(e+1) g_B + 2c ≤ ∑D(m p^e) + 1`, `m p^e + 2c ≤ p^(e+1) ∑D(m) + ∑D(m p^e) + 1` (`g_B` = max gap
  of `SS(D m)`, from a bitset). Soundness by bitsets: odd `m < 400`, `p ≤ 13`, `e ≤ 3`: 184 cases with the condition true,
  **0 unsound** (interval and gap bound). Coverage of the session-55 chain probe (same 57 random ω = 6 candidates, seed 1):
  base bitset ≤ 2·10^4: old chain 0 → with one raised prime 15; base ≤ 10^6: 14 → **37**. Only one prime is raised (the one whose
  high exponent kills the bitset), right after the base; then the old prime-power steps. Remaining failures are like
  `3^1·5^6·13^3·19^10·29^3·q` (two high exponents: 19^10 and 5^6/13^3) and `3^6·7^15·17^4·23^15·37^10·q`.
- **Lean (new `ErdosResearch/SubsetSumRaise.lean`, imported from the root; no sorry; axioms propext/choice/Quot.sound; full
  `lake build` OK, 9072 jobs; no warnings in the module; `check-lean-sources.py` OK):**
  - `properDivisors_raise` (the split; holds for any prime `p`, disjoint when `p ∤ m`: `raise_disjoint`), `sum_properDivisors_raise`;
  - `interval_properDivisors_raise`: interval `[c, ∑ − c]` + gaps `≤ g` on `D(m p^e)` and gaps `≤ gB` on `D m` ⇒ the same on
    `D(m p^(e+1))` (an instance of `interval_union_insert_image` plus `gap_of_interval`); `interval_properDivisors_raise_iter`;
  - decidable form: `raiseSum` (recursive `∑D`, `raiseSum_eq`), `raiseOK`, `interval_raise_of_cert`, `pseudoperfect_raise_of_cert`,
    and the family decider **`not_weird_mul_prime_of_raise_cert`** (raise chain to `n`, then the prime step for the last prime `q`);
  - instances: `pseudoperfect_325_mul_three_pow_six` and **`not_weird_3969405_mul_prime`: no `3^8·5·11^2·q` (`q` prime, `q ∤ n`) is
    weird** (bitsets of `D 5445` and `D 605`, six raises; `q ≥ 92` deficient, the 19 primes 7, 13 … 89 by the prime step). The whole
    file compiles in ~6 s.
- Elementary; new only as a formalisation. Not a new result on #470 (ω = 6 is still open here; Liddy–Riedl's ω ≥ 6 is unread).
- **Step lists (second part of the session; new `ErdosResearch/SubsetSumSteps.lean`, imported from the root; same checks; full
  `lake build` OK, 9073 jobs; module ~2 min, almost all in the kernel's `properDivisors 11583`):**
  - `ppSum` (recursive `∑D(n q^f)`, `ppSum_eq`), `stepsEnd`, `stepsOK` (one Boolean for a list of prime-power steps `(q, f)`),
    `IntervalGap n S c g` (interval + gaps + `∑D n = S`), `intervalGap_of_stepsOK`, `intervalGap_of_raise_cert`, and the last-prime
    decider `not_weird_mul_prime_of_intervalGap`;
  - instance **`not_weird_mul_prime_example`: no `3^4·11^10·13·17^10·23^10·q` (`q` prime, `q ∤` prefix) is weird.** Base `11583`
    (`c = 69`, `g = 5`), `D 1053` (`gB = 61`), nine raises of 11, steps `17^10`, `23^10`; `nq` abundant only for `q ≤ 57`.
    The prefix is deficient with three exponents equal to 10: far beyond any bitset.
  - plan finder `scripts/raise_steps_plan.py LIMB` (random deficient 5-prime prefixes, max exponent ≥ 6, every last prime covered);
    with LIMB = 2·10^4 it finds 6 such prefixes in the first ~3000 trials (seed 2). Run it under `ulimit -v`: a first version
    without the `m ≤ LIMB` guard was OOM-killed (bitset of `D m` for a huge `m`).
- **Next (if #143 still unanswered):** (1) a generator that, for the **real** search prefixes (decode the checkpoint keys; check
  first what the key `(f, un, ud, j, q0)` stores), finds a plan with `raise_steps_plan.py` logic and emits one `cert_…` +
  `not_weird_…` instance per prefix; measure what fraction of prefixes get a plan. Avoid `properDivisors` of the base in the kernel
  (2 min for 11583): prove `l.toFinset = D b` once per base by a faster route (e.g. `Nat.divisors_mul` / a product of the prime-power
  divisor lists), or keep bases below ~5000. (2) Raising two primes needs a gap bound for `D m` with `m` large (not a bitset);
  look for a recursive gap bound. (3) Honest view: these are family certificates for individual prefixes; covering all of ω = 6 this way
  still needs the prefix tree (the Job's search) and, for prefixes without a plan, the bitset fallback.

## Session 57 (2026-11-22, 09:02–~09:20 UTC): greedy gap bound + late / multiple raises (no search run)

- Board: card #143 (deploy the ω = 6 Job) still open with no answer, so by the standing rule no queue command and no `owf`.
- **Correction to session 56:** the "~2 min" for `SubsetSumSteps.lean` was a measurement artefact. Profiled now: the whole
  module takes ~14 s, the `cert_11583_steps` kernel check 6.8 s, and kernel `properDivisors 11583` alone 2.8 s. A faster
  `l.toFinset = D b` proof is therefore not needed for bases of this size (item (1) of session 56's "Next" is dropped).
- **Measured first (Python only).** New `scripts/raise_late_probe.py [LIMB]` (same 57 random ω = 6 candidates as session 56):
  - "late raise" (steps first, then raise `p` over the large cofactor `m`) with `gB` obtained from a bitset-based chain on `m₀`:
    37 → 37, no gain. Every attempt failed in the step chain on the small cofactor `m₀` (too sparse) or because `m₀` > LIMB;
  - the same with `gB` taken from the **greedy bound** `max(1, maxᵢ dᵢ − (d₁+…+dᵢ₋₁))` on the sorted proper divisors of `m`
    (`GREEDY=1`): **37 → 52 of 57** (LIMB 1e6). The 5 left are `3^15·7^6·19^10·23^2·41^15·q` (two exponents of 15).
  - The greedy bound equals the exact maximum gap (bitset) for all 14999 odd `m < 30000` (0 unsound, all tight).
- **Family plans.** New `scripts/raise_late_plan.py LIMB [TRIALS]` (seed 3; random deficient 5-prime prefixes, max exponent ≥ 6,
  every last prime `q` covered by the last-prime decider): LIMB = 2·10^4, 262 prefixes: session 56's `plan()` 19, plus one late
  raise 59, **plus multiple raises (`MULTI=1`) 210**. Multi-raise means: base `∏ p^{e0_p}` with `e0_p ∈ {0,1,2}`, steps for the
  primes with `e0_p = 0`, then raise every other prime to its full exponent, one after another, with `gB` = greedy bound of the
  current cofactor. Soundness against exact bitsets (small prefixes, n ≤ 3·10^5, chains with ≥ 1 raise): 157 checked, 0 unsound
  (throwaway script, not in the repo; the Lean lemmas below are what matter).
- **Lean (no sorry; axioms propext/choice/Quot.sound; full `lake build` OK, 9075 jobs; no warnings in the new modules;
  `check-lean-sources.py` OK):**
  - new `ErdosResearch/SubsetSumGreedy.lean`: `greedyGap`, **`gap_greedy`** (for any list without repetitions: after each
    `x <` total there is a subset sum `z` with `x < z ≤ x + greedyGap l`, `z ≤` total); `prodOf`/`divsOf` (divisors listed from
    the factorisation; `divsOf_toFinset` via `Nat.divisors_mul`, `Nat.divisors_prime_pow`), a local insertion sort `sortDesc`
    (Mathlib's `List.insertionSort`/`mergeSort` do not reduce under `decide` from a `module`: not exposed / well-founded),
    `descOK` (linear Nodup check), and the Boolean **`gapCert fs G S`** with `gap_properDivisors_of_gapCert`
    (`∑ D m = S` and gaps ≤ `G` for `m = prodOf fs`; the kernel never scans `m`). Sanity `gap_example` (`D(3·5^6·13^3)`, G = 4).
  - new `ErdosResearch/SubsetSumLate.lean`: `intervalGap_of_bits`, **`intervalGap_raise`** (raise chain in `IntervalGap` form,
    from any source of interval/gaps), and the instance **`not_weird_late_example`: no `3^3·11^2·13^10·17^2·23·q` (`q` prime,
    `q ∤` prefix) is weird** (base `6831`, `c = 2295`, `g = 5`; steps `13^10`, `17^2`; raise of `11` from 1 to 2 over
    `m = 3^3·23·13^10·17^2`, 264 divisors, greedy `gB = 5`; `nq` abundant only for `q ≤ 43`). Session 56's plans do not certify
    this prefix. The module compiles in well under a minute.
- Elementary; new only as a formalisation. Not a new result on #470 (ω = 6 still open here).
- **Next (if #143 still unanswered):** (1) a generator `scripts/late_cert_gen.py` that turns a `multi_plan` into a Lean instance
  (cert conjunction + `intervalGap_raise` per raised prime; the `m · p^e = …` equalities by `decide +kernel`), tested on 3–5 of the
  210 prefixes; watch the kernel cost of `sortDesc` (quadratic). Measured in a scratch file: `gapCert` for
  `3^6·17^4·23^15` (560 divisors) and `3^6·17^4·23^15·37^2` (1680 divisors) both pass by `decide +kernel`, in ~1–2.5 min each
  (timings noisy here: 68–156 s, not monotone in size); 264 divisors stays in the seconds. (2) If quadratic sorting
  is too slow, generate the divisors already sorted (merge of sorted lists with fuel) or let the generator supply the sorted list
  and check `descOK` + membership. (3) Honest view unchanged: these are family certificates for given prefixes; covering all of
  ω = 6 still needs the prefix tree (the Job's search).

## Session 58 (2026-11-22, 10:13–~11:05 UTC): generator of family certificates, all last primes at once, merged divisors, fast bitset checks (no search run)

- Board: card #143 (deploy the ω = 6 Job) still unanswered, so by the standing rule no queue command and no `owf`.
- **Lean (no sorry, no native_decide; axioms propext/choice/Quot.sound; full `lake build` OK, 9079 jobs; no warnings in the new
  modules; `check-lean-sources.py` OK):**
  - new `ErdosResearch/SubsetSumLastOK.lean`: Boolean `lastOK n S c g B` and **`not_weird_mul_prime_of_lastOK`**. For deficient
    `n` (`S = ∑ D n < n`) `nq` is abundant only if `q(n−S) < n+S`, so with `n+S < B(n−S)` the Boolean checks the last-prime
    conditions for every `q ∈ [2, B)` with `q ∤ n` (composites included: no primality test in the kernel). Generated instances
    need no `omega` case analysis on `q`.
  - new `ErdosResearch/SubsetSumDivsDesc.lean`: decreasing divisors by merging (`mergeF` with fuel, `mergeAll`, `divsDesc`,
    `divsDesc_perm`); `gapCertM` + **`gap_properDivisors_of_gapCertM`** (same conclusion as `gapCert`); `baseOK`/`baseList` +
    **`baseList_properDivisors`** (proper divisors of a bitset base from its factorisation; kernel `properDivisors b` scans up
    to `b`). The merge order is never trusted (fuel exhausted ⇒ append; `descOK` is checked).
    Reason: with the insertion sort, an instance whose cofactors have 660 and 1452 divisors was killed at the 8 GB limit (exit
    137) even after splitting the certificate; with `gapCertM` it compiles in 24 s.
  - new `ErdosResearch/SubsetSumBitsFast.lean`: `intervalOKB` / `gapOKB` (masks `2^w − 1`, `>>>`, `|||` via `orShifts`; GMP in
    the kernel) with soundness, and `intervalGap_of_bitsB`. Reason: `intervalOK`/`gapOK` test bit by bit (≈ s² bit operations),
    and bases near 10^6 ran out of memory. Sanity: on `l315`/`l525` the fast and old checks agree, including two cases that must
    be false (`c = 17`, `g = 1` for 525).
  - new `ErdosResearch/OddWeirdPlans.lean`, **generated** by `scripts/late_cert_gen.py 1000000 40 2000 100000` (regeneration is
    byte-identical): 40 theorems `not_weird_i`: no `N·q` weird (`q` prime, `q ∤ N`) for 40 random deficient 5-prime prefixes `N`
    (same random family as `MULTI=1 raise_late_plan.py`, seed 3; e.g. `5^6·11^2·13^2·17^2·23^10`). Each instance is split
    into `cert_i_base` (`baseOK`, bitset with fast checks, `stepsOK`, `stepsEnd`), per raise `cert_i_gapj` (`gapCertM`) and
    `cert_i_raisej`, and `cert_i_last` (`lastOK`), each by `decide +kernel`, with `set_option Elab.async false`.
    Module: 152 s (≈ 4 s per instance), 163 KB.
- **New `scripts/late_cert_gen.py LIMB COUNT MAXDIV MAXB`** (Python; uses `multi_plan` from `raise_late_plan.py`; does not run
  the search). `DRY=1` only counts; `MINDIV=N` keeps instances whose largest cofactor has > N divisors (timing tests).
  Coverage on 1322 random deficient prefixes (repeats included), no size limits: LIMB 2·10^4: 1002 plans (all emittable;
  492 with MAXDIV 300 / B ≤ 5000); LIMB 10^5: 1116; **LIMB 10^6: 1293 (97.8 %)**. Every plan also passes `lastOK`. (The generator's "tried" count can include repeats of
  prefixes without a plan; the distinct count is below.)
- **Failed:** one big `decide +kernel` conjunction per instance ⇒ out of memory (fixed by splitting into declarations + merged
  divisors); bit-by-bit bitset checks ⇒ out of memory for bases near 10^6 (fixed by mask checks); a non-f-string in the
  generator (caught by the first heavy test).
- Elementary; new only as a formalisation. Not a new result on #470 (ω = 6 still open here).
- **Uncovered prefixes at LIMB 10^6** (throwaway script, not in the repo; counted over distinct prefixes): 26. 25 of them
  have `v_3 = 1` and neither 5 nor 7 (σ/n ≈ 1.69–1.75), e.g. `3·11^8·13·17·23^10`; the other is `11·13·17^8·19^3·23^10`.
  Per candidate base the dominant failure is the prime-power step condition (then `b > LIMB`, then no centred interval);
  allowing `e0_p ∈ {0..3}` covers none of them. (The root `3^1` of the ω = 6 search is already finished, so this
  pattern is not where the search is still open.)
- **Next (if #143 still unanswered):** (1) for the `3^1`, 5- and 7-free prefixes: a step condition with the greedy gap of the
  current number instead of the base `g` (the base gap is too coarse there), measured in Python first. (2) Wire the decider in
  as a fast path of the search (a family decided by a plan = a Lean-checkable leaf), so the Job's output could later be
  replayed as Lean instances. This changes the search code ⇒ `scripts/validate-owf.sh` is mandatory, and the Job image must be
  rebuilt (Pablo). (3) Honest view unchanged: these certify given prefixes; all of ω = 6 still needs the prefix tree.

## Session 60 (2026-11-22/23, 23:00–~00:30 UTC): the decider on the OPEN part of the search; one real node in Lean

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): **root 3^15 DONE** (20:58 UTC, nfail 0), so the
  finished roots are v_3 ∈ {1..16}. owf-0 is on 3^18 and owf-1 on 3^17. `omega6-2.ck.gz` 2108 → 5265 lines (126 KB), frozen
  prefix OK. No owf run.
- **Coverage measured where the search is still open** (new `scripts/highv3_coverage_probe.py`, Python only):
  `multi_plan` decides **every** sampled deficient 5-prime prefix with v_3 ∈ {17,18,19,20,25,30}: 300/300 at LIMB 10^5 and
  300/300 at LIMB 2·10^4, < 0.1 s each. The sample includes the real node `3^17·5^24·17^4·257^4·113149` from owf-1's
  progress log. The last prefix prime is chosen so that abundance stays reachable, but the sample is NOT the search's real
  node distribution, so treat these numbers as indicative only.
  Caveat: the other node from the log, `3^18·5^17·19^2·97^3·2647`, is already **abundant** (σ/n ≈ 2.00025). The
  decider does not apply to abundant prefixes (they need pseudoperfectness of the prefix itself, cf. `Pseudoperfect.of_dvd`).
- **Lean (no sorry/native_decide; axioms propext/choice/Quot.sound):** new `ErdosResearch/OddWeirdRealPrefix.lean`, generated
  by new `scripts/real_prefix_cert.py '3^17*5^24*17^4*257^4*113149'` (byte-identical on rerun; uses `multi_plan`/`build`/`emit`
  of `late_cert_gen.py`): **`not_weird_0`: no `3^17·5^24·17^4·257^4·113149·q` is weird** (q prime, q ∤ prefix). Plan: base
  21675 = 3·5^2·17^2 (c = 283, g = 6), steps 257^4 and 113149, raises of 3, 5 and 17 (cofactors with 90, 540 and 4500 divisors),
  `lastOK` with B = 140293. Module: **327–419 s** (419 s in the full `lake build`, 9080 jobs, OK), imported from the root. It is a single node of the open search, not the whole root.
- **Failed:** (1) the first build hit a kernel "deep recursion" in `gapCertM` on the 4500-divisor cofactor. Fixed with
  `set_option maxRecDepth 1000000`, which the script emits. (2) My first probe put the abundant node into `allq`
  (`max(1, 2n−σ)` ⇒ q-loop up to σ: never ends), which was a probe bug. (3) Trap: a `/proc/*/cmdline` kill loop matching
  `*highv3*` killed my own shell (the pattern was in its command line). Match on `python3*…` or keep PIDs.
- Honest view: kernel cost per real node is minutes (cofactor divisors and B both grow with the exponents), and the
  open roots have millions of nodes. So Lean replay of a whole root by per-node instances is not realistic. A Lean
  ω = 6 proof would need the reflective-checker route of `OddWeirdFourCore` with the plan decider as its leaf test.
- **Next:** (1) `read` again; alert Pablo on exit 5. (2) Measure, in Python, a reflective leaf: `multi_plan` cost vs a cheap
  necessary condition, to judge whether a `chk`-style checker for one sub-root (e.g. 3^17·5^24) is feasible in the kernel.
  (3) Abundant 5-prime prefixes: how often are they pseudoperfect via a small explicit subset (cheap Lean leaf)?

**Session 60 follow-up (review, 2026-11-23 ~00:50 UTC):** the checker's `lake build` timed out at 1200 s. The only new
Lean was `OddWeirdRealPrefix.lean` (327–419 s of kernel, `maxRecDepth 1000000`, 4500-divisor cofactor), so it was
**taken out of the repo and out of the root imports**. The generator `scripts/real_prefix_cert.py` stays, so the module
can be regenerated on demand (`python3 scripts/real_prefix_cert.py '3^17*5^24*17^4*257^4*113149' > /tmp/x.lean`), but it
must not go into the default build. Rule from now on: no module may add more than ~1 min to `lake build`; heavy
certificates stay outside the default targets. Local `lake build` OK again (9079 jobs, same as main), check-lean-sources OK.
Data files in the diff: `omega6-2.ck.gz` (2108 → 5265 lines) and `omega6-roots.txt` (+ root 15 DONE) are the output
of `sh scripts/owf-queue.sh read`. They change because the pgal `owf` StatefulSet keeps working. Checked: gzip -t OK,
0 duplicates, the old file is a byte-exact prefix, every line is a checkpoint tuple (digits, brackets, commas) with no
other content and no secrets. Palomar: already in main and green (see notes/palomar.md, re-check 2026-11-23).
Next step unchanged (session 60 "Next"), but any Lean certificate must be cheap (< 1 min) before it enters the build.

**Session 60 follow-up 2 (review, 2026-11-23 ~02:30 UTC):** the checker's clean `lake build` still timed out after the
module was removed. Measured per-module times (`notes/build-times.md`): here the build is serial, OddWeirdPlans takes 471 s
and the Palomar chain alone ≈ 990 s. `SubsetSum*` + `OddWeirdPlans` moved to the non-default lib `ErdosResearchExtra`
(built explicitly by the Lean CI), and `Solution.lean` imports only what it needs. Clean serial `lake build` now OK in 1065 s. **New research Lean goes into
`ErdosResearchExtra.lean`, not the root.**

## Session 61 (2026-11-23, 03:46–~05:15 UTC): read + faster Palomar build (no owf run)

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): **roots 3^17 (00:43 UTC) and 3^18 (03:38 UTC) DONE**, nfail 0
  ⇒ finished roots v_3 ∈ {1..18}. owf-0 on 3^20, owf-1 on 3^19. `omega6-2.ck.gz` 5265 → 9524 lines (228 KB); checked: gzip -t
  OK, 0 duplicates with the frozen file, old file is a byte-exact prefix, only tuple characters.
- No #470 Lean this session. The time went to the build margin (card #156), see `notes/build-times.md` and
  `notes/erdos-1052.md` session 61.
- **Next:** unchanged from session 60 (`read` first; then measure a reflective leaf in Python; cheap certificates for
  abundant 5-prime nodes). Remaining roots grow ≈ 90M nodes each (17, 18), ≈ 3 h per root per worker.

## Session 62 (2026-11-23, 05:37–~06:10 UTC): read; cheap Lean leaf for ABUNDANT 5-prime nodes (no owf run)

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): no new root finished (finished roots v_3 ∈ {1..18}).
  owf-0 on 3^20 (log at (5,14),(19,8)), owf-1 on 3^19 (log at (5,23),(17,5)). `omega6-2.ck.gz` 9524 → 10513 lines (254 KB),
  frozen prefix OK, 0 dropped lines.
- **Measured first (Python, new `scripts/abundant_greedy_probe.py CASES [SEED]`):** abundant 5-prime prefixes shaped like the
  open roots (3^E, E ∈ {17..30}; the last prime is random below the abundance threshold), plus the real node
  `3^18·5^17·19^2·97^3·2647` from session 60. A certificate is a strictly decreasing list of proper divisors of N summing to N.
  Plain greedy (largest first) gives 177/200. Greedy until the remainder is ≤ 2^20, then an exact big-int-bitset subset sum over
  the unused divisors, gives **500/500** (seeds 7 and 11), with 153 elements on average and at most 585. Every list is asserted
  (sum, distinct, proper divisor). The sample is not the search's real distribution, so this is indicative only.
- **Lean (no sorry/native_decide; in `ErdosResearchExtra`, NOT the default build):** new `ErdosResearch/OddWeirdAbundantLeaf.lean`:
  `ppOK n l` (Bool: decreasing, each `d < n ∧ n % d = 0`, sum = n; only GMP arithmetic, no divisor enumeration of n),
  `pseudoperfect_of_ppOK`, and the instance **`pseudoperfect_real_abundant_node`** (241-element list) with
  `not_weird_of_real_abundant_node_dvd` (no multiple of `3^18·5^17·19^2·97^3·2647` is weird). The module compiles in ≈ 20 s
  (the `decide +kernel` is instant). The list was pasted from `python3 -I scripts/abundant_greedy_probe.py 1 7 emit` (wrapped to 96 chars).
- Consequence for a Lean ω = 6 route: abundant nodes are cheap leaves (milliseconds each). The expensive ones are still the
  deficient nodes (plan decider, minutes per node in the kernel; session 60).
- **Next:** (1) `read` first; alert Pablo on exit 5. (2) Measure, in Python, a reflective `chk`-style checker for one small
  sub-root, with `ppOK` (abundant) and the plan decider (deficient) as leaves. Count the leaves and estimate the kernel cost of
  `gapCertM` per deficient leaf; if that is minutes, look for a cheaper deficient leaf (e.g. reuse one base interval across
  the sibling last primes). NEVER run owf in a session.

## Session 63 (2026-11-23, 07:03–~07:50 UTC): one certificate per 4-prime sub-tree (no owf run)

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): no new root finished (finished roots v_3 ∈ {1..18}).
  owf-0 on 3^20 (log at (5,20),(17,12)), owf-1 on 3^19 (log at (5,27),(17,1)) at 07:48. `omega6-2.ck.gz` 10513 → 11278 lines,
  frozen prefix OK, 0 dropped lines. Board unchanged; Palomar files unchanged.
- **Measured (Python, new `scripts/subroot_leaf_probe.py PREFIX4 LIMB MAXLEAVES REPO`):** replays only the SHAPE of the last
  two levels of `search1`/`family` below a fixed deficient 4-prime prefix (same bounds and exponent loop; every pp test is
  assumed to pass, so it decides nothing and is not the search). Census of the leaves a Lean checker would need:
  `3^20·5^18·19^4·97^3` (from owf-0's log): 1112 abundant + 1262 deficient 5-prime leaves (the 5th prime runs over every
  prime up to qtop ≈ 9179, then beyond); `3^18·5^17·19^2·97^3`: 521 + 566; `3^19·5^25·29^7·73`: 0 + 13.
  With session 60's per-leaf instances (minutes each) that is days per 4-prime prefix: per-leaf certificates are hopeless.
- **Speed fix in the probe:** `allq` (raise_steps_plan.py) loops over every q < σ/(2n−σ), which is ~10^7–10^8 for
  near-perfect leaves (session 60's "never-ending q loop"). `allq_fast` gives the same truth value in closed form (every
  condition is linear in q, so the good q form an interval; scan only for the first prime outside it). Checked equal to
  `allq` on 20000 random inputs (`CHECKALLQ=1`). multi_plan then decides all 1262 deficient leaves above in 31 s.
- **Key finding (`UNIFORM=1`):** all sibling leaves use the same plan shape (base 855, step 97, then the 5th prime q, then
  raises of 3, 5, 19). Reordering — certify the 4-prime prefix M4 ONCE (`IntervalGap M4 S4 c g` by base+steps+raises), then
  the prime-power step by q (conditions `q g + 2c ≤ S4 + 1`, `M4 + 2c ≤ (q+1) S4 + 1`, valid for every exponent) — decides
  EVERY leaf: abundant leaves by `c ≤ M5 ≤ ∑D(M5) − c` (pseudoperfect), deficient ones by the last-prime test (`allq`),
  and (`STARS=1`) the 6th prime with exponent ≥ 2 by a second step + interval test. Result: 4 hand-picked prefixes + 40
  random deficient 4-prime prefixes shaped like the open roots (seed 63; 2623 leaves): **44/44 uniform, 0 failing leaves**;
  with STARS on 18 of them, 18/18 (≈ 200 star leaves). Indicative only: the random prefixes are not the search's distribution.
- **Lean (in `ErdosResearchExtra`, NOT the default build; no sorry/native_decide; standard axioms; module ≈ 15 s):** new
  `ErdosResearch/SubsetSumUniform.lean`: `intervalGap_mul_prime_pow` (IntervalGap survives n ↦ n q^e for every e),
  `pseudoperfect_mul_prime_pow_of_intervalGap` (abundant leaf), `not_weird_mul_prime_pow_mul_prime_of_intervalGap`
  (deficient leaf, 6th prime r^1), `pseudoperfect_star_of_intervalGap` (6th prime r^f). These are the generic
  ingredients; q, e, r stay symbolic, so one sub-tree = one kernel certificate of M4 + inequalities in q.
  Full `lake build` OK (9066 jobs), `lake build ErdosResearchExtra` OK (9065), check-lean-sources OK. Elementary; new only
  as a formalisation.
- **Range lemma (Lean, same module):** `pseudoperfect_mul_prime_of_range`: the abundant-leaf conditions are linear in q, so
  four inequalities at the ends q₀, q₁ give "n q pseudoperfect for EVERY prime q ∈ [q₀, q₁], q ∤ n" with no per-prime work.
  Python check: for `3^20·5^18·19^4·97^3` with (c, g) = (57, 2), all 1112 abundant leaves (q = 101 … 9173) satisfy the four
  end conditions; same for `3^18·5^17·19^2·97^3` (521 leaves, q = 101 … 3931). So the abundant half of a sub-tree is ONE
  lemma application once `IntervalGap M4` is certified.
- **Not done / open:** (a) the side conditions per leaf are still numeric (q, e, r concrete); to get ONE theorem per sub-tree
  they must be proved for all primes q in a range at once (they are linear in q for fixed e except the `allq` part, which
  is linear in r for fixed q, e) — or checked by a reflective loop over the leaves (cheap: only GMP arithmetic, no divisors).
  (b) the per-prefix certificate of M4 still needs `gapCertM` on cofactors with thousands of divisors (session 60: minutes).
  (c) Region nodes (exponent "≥ e") of the search are not modelled separately; the probe takes each exact exponent.
- **Next:** (1) `read` first; alert Pablo on exit 5. (2) A reflective `subtreeOK M4 S4 c g` that runs the j = 2 loop of the
  search (primes q by a cheap primality-free stride, exponent loop) and only checks the linear side conditions, with a
  soundness proof built on the four session-63 lemmas; time it in the kernel on `3^1·5^2·11·13` (16 leaves), then on
  `3^18·5^17·19^2·97^3` (1087 leaves). (3) Measure how many distinct M4 certificates one root needs (= number of 4-prime
  prefixes with room for 2 primes). NEVER run owf in a session.

## Session 64 (2026-11-23, 08:42–~10:15 UTC): one certificate per 3-prime sub-tree; certificate count per root (no owf run)

- `sh scripts/owf-queue.sh read` (twice, exit 0, no FOUND/CLOSED/ERROR): **root 3^19 DONE** (nfail 0) ⇒ finished roots v_3 ∈ {1..19}.
  owf-0 on 3^20 (log at (5,24),(17,12)), owf-1 on 3^21 (log at (5,9),(17,18)) at 09:39. `omega6-2.ck.gz` 11278 → 13054 lines,
  frozen prefix OK, 0 dropped lines. Board/Palomar unchanged. No Lean changes this session.
- **How many M4 certificates per root (session 63 Next (3)):** new `scripts/m4_count_probe.py E SAMPLE SEED CK.gz…` takes the
  depth-3 checkpoint keys of root 3^E and replays only the SHAPE of `search1`/`family` below each (pp tests assumed; finished
  roots have nfail 0, so this is the real control flow; it decides and writes nothing). Root 3^16: 2554 depth-3 keys;
  252 keys replayed (stopped by me) give 18618 four-prime prefixes with j = 2 ⇒ **≈ 1.9·10^5 M4 certificates per root** (upper
  estimate: region and exact keys share subtrees). At ≥ seconds of kernel time each, that is days per root: per-M4 certificates
  are too many.
- **Key finding: certify the 3-prime prefix M3 instead.** `scripts/subroot_leaf_probe.py` has a new `J=3` mode (prefix with 3
  primes; every extra prime of a leaf is a prime-power step with the same (c, g), i.e. `stepsOK` from SubsetSumSteps; `J=2`
  unchanged, re-checked on session 63's prefixes: 16 and 1087 leaves, 0 failing). With `UNIFORM=1 STARS=1`, ONE
  `IntervalGap M3` (small base ≤ 10^6, then raises only; no steps needed) decides every leaf of the 3-prime sub-tree:
  root 3^16 (7 prefixes = the sample of the count probe): 7/7, e.g. `3^16·5^11·19^8` 28475 leaves + 2077 stars,
  `3^16·5^3·17^5` 68572 leaves + 4539 stars, **0 failing**. Roots 3^17/3^18 (14 random checkpoint prefixes, seed 641):
  12/12 that finished, 0 failing (up to 28062 leaves); 2 (`3^18·5^16·17^11`, `3^18·5^13·17^10`, ≈ 155k leaves) did not
  finish the Python check in 300 s; rerun with more time: both pass, 155277 leaves + 9976 stars and 154288 + 9663 stars,
  plan (283, 6, base 21675, raises 3, 5, 17), **0 failing** (≈ 6 min each). So 14/14 random prefixes pass.
  Plans are tiny: (c, g) ∈ {(23,2), (37,2), (57,2), (68,2), (79,3), (283,6), (899,3)}, bases 819 … 22743.
  ⇒ ≈ 2.5k certificates per root (the depth-3 keys), each a small base bitset + 2–3 raises, ≈ 75× fewer than M4.
- **Lean side:** nothing new needed for one leaf: `IntervalGap M3` + `stepsOK c g M3 S3 [(p,e),(q,f)]` (SubsetSumSteps) +
  `not_weird_mul_prime_of_intervalGap` / the interval test already compose. 2-prime prefixes (`J=4`, `3^16·5^9`): the
  Python enumeration did not finish in 580 s, so this was not measured.
- **Honest gap (unchanged):** the leaf certificates are the cheap part. A Lean replay of a root still needs a reflective checker
  proving that the search's ENUMERATION covers every ω = 6 odd abundant number in the sub-tree (the chk-style soundness of
  sessions 4/10, with bounds as in `search1`/`family`, the star loop and region nodes). That is the main remaining work.
- **Next:** (1) `read` first; alert Pablo on exit 5. (2) Reflective `subtreeOK3 M3 S3 c g j q0 un ud` in ErdosResearchExtra:
  runs the j = 3 → 1 loops of `search1`/`family` with `stepsOK` and the leaf tests as the only checks (no primality: odd
  stride, steps are sound for composites? NO, `intervalGap_mul_prime_pow` needs q prime; so either test primality with a cheap
  kernel certificate or prove a composite-q variant); soundness from SubsetSumSteps/Uniform. Measure it first in Python on
  `3^17·5^2·43^2` (20 leaves) and `3^18·7^13·19^8` (53 leaves). NEVER run owf in a session.

## Session 67 (2026-11-23, 12:48–~13:40 UTC): no primality certificates needed in a reflective checker (no owf run)

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): no new root (finished roots v_3 ∈ {1..19}). owf-0 on 3^20
  (103.0M nodes, log at (5,29),(17,11)), owf-1 on 3^21 (61.4M nodes, log at (5,18),(17,14)). `omega6-2.ck.gz` 13054 → 14144
  lines, frozen prefix OK, 0 dropped lines. Board: #143/#156 open, no reply. Palomar files unchanged.
- **Resolves session 64's open point** ("steps need q prime: certify primality or prove a composite-q variant?"): neither is needed.
  A checker that runs over EVERY odd q and skips q only when a cheap test PROVES q composite covers all primes. The extra
  composites are decided too, which is sound and only costs time; a composite that fails a check would need a factor hint. The test is one gcd with a primorial P:
  skip iff `gcd q P ≠ 1 ∧ ¬ q ∣ P`. Lean (ErdosResearchExtra, not the default build; no sorry/native_decide; standard axioms;
  ≈ 12 s): new `ErdosResearch/PrimeSkip.lean`, `not_prime_of_skip` (valid for ANY P), Boolean `skipB`, `prime_imp_not_skipB`.
- **Measured (Python, `COMPOSITE=W` in `scripts/subroot_leaf_probe.py`; `cand()` = "odd, coprime to the odd primes ≤ W, and
  coprime to the prefix" replaces `isprime` in the enumeration, the region loop and the leaf tests; default unchanged):**

  | prefix (J=3) | W | leaves (prime-only run) | leaves | failing |
  |---|---|---|---|---|
  | `3^17·5^2·43^2` | 0 | 20 | 50 | 16 (at composites such as 49) |
  | same | 7 / 30 | 20 | 20 / 20 | 0 / 0 |
  | `3^18·7^13·19^8` | 7 / 30 / 100 | 53 | 63 / 53 / 53 | 0 |
  | `3^16·5^11·19^8` | 30 | 28475 (+2077 stars) | 36103 | 5026 (all at composites, e.g. 4661 = 59·79) |
  | same | 100 | 28475 | 29158 | 532 (all at composites ≥ 101², e.g. 10201, 10403) |
  | same | **1000** | 28475 | **28475** | **0** (2079 stars: 2 harmless composites) |

  Two effects show up for small W. First, a composite q fails a leaf test (a spurious failure, which a hint can fix). Second, the
  `family` region loop returns False on a composite, so the search drops to exact exponents and the tree grows. With W = 1000,
  composites appear only from 1009² ≈ 10^6, and the enumeration is exactly the prime one. In Lean this is a single GMP gcd
  with a ≈ 1400-bit primorial per q, so it is cheap.
  | `3^18·5^16·17^11` | −1 (primes) | — | 154288 (+9663 stars) | 0 |
  | same | **1000** | 154288 | 154299 (+9703 stars) | **0** (11 + 40 composites, all pass) |

  (Correction to session 64: 154288 + 9663 stars belongs to `3^18·5^16·17^11`. The 155277 + 9976 pair belongs to
  `3^18·5^13·17^10`, so session 64 swapped the two.) This is indicative only: it covers 4 prefixes, it replays the shape
  with pp tests assumed, and it is not the search.
- **Next:** (1) `read` first, and alert Pablo on exit 5. (2) Reflective `subtreeOK3` in ErdosResearchExtra: the `search1`/`family` loops
  below a 3-prime prefix with `skipB q P₁₀₀₀` as the only primality device, `stepsOK`-style steps and the leaf tests; its
  soundness rests on `prime_imp_not_skipB` and SubsetSumSteps/Uniform. Start with `3^17·5^2·43^2` (20 leaves) and time it in the kernel.
  (3) Add a hint list (composites to skip, each with a factor) in case a larger q range ever shows a composite failure.
  NEVER run owf in a session.

## Session 68 (2026-11-23, 14:21–~14:50 UTC): first layer of the reflective checker (loop + tail) in Lean (no owf run)

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): **root 3^20 DONE** (13:47 UTC, 109.6M nodes, nfail 0), so the
  finished roots are v_3 ∈ {1..20}. owf-0 is on 3^22 (22.6M nodes), owf-1 on 3^21 (75.4M nodes). `omega6-2.ck.gz` 14144 → 15890 lines
  (392 KB), frozen prefix OK, 0 duplicates; `omega6-roots.txt` gains root 20. Palomar files unchanged.
- **New `ErdosResearch/SubsetSumFifthLoop.lean`** (ErdosResearchExtra only, not the default build; ≈ 25–38 s; no sorry/native_decide;
  axioms propext/choice/Quot.sound; check-lean-sources OK; Extra build OK, 9067 jobs; default build OK, 9066 jobs):
  - `leafOK n S c g e q` (Boolean): the prime-power step conditions for `q`, then either the abundant interval test for `n q^e`
    or `lastOK` for `n q^e`, with `B = (N + S')/(N − S') + 1`. `not_weird_of_leafOK`: under `IntervalGap n S c g`, no `n q^e r`
    is weird (`r` prime, `r ∤ n q^e`). The abundant case goes through `Nat.Pseudoperfect.of_dvd`.
  - `qLoop P n S c g e q₀ k`: every odd `q` from `q₀` (`k` values), skipping `skipB q P` (proven composite) and `q ∣ n`.
    `not_weird_of_qLoop`: sound for every prime `q` in the range. **No primality is proved anywhere** (session 67 idea, now used).
  - `ppSum_exact'` (closed form σ(n q^e)(q − 1) + σ(n) = σ(n) q^(e+1), no subtraction) and **`not_weird_tail`**: if
    `σ(n)(Q + 1) ≤ 2n(Q − 1)`, then no `n q^e r` with primes `q, r ≥ Q` is abundant, for EVERY `e`. This is the region bound
    that closes the loop.
  - Instance **`not_weird_late_prefix_mul_mul`**: for `n = 3^3·11·13^10·17^2·23` (IntervalGap from `cert_late`, c = 2295, g = 5):
    for all primes `q < r` with q odd, q ∤ n, r ∤ n q, `n q r` is not weird. The loop covers q < 71 (k = 33, ~1 s) and the tail
    covers Q = 71 (σ/n ≈ 1.9408). That is a whole two-prime family (exponent 1 for q) from ONE certificate. Elementary; new only
    as a formalisation.
- **Kernel timings** (`P1000` = product of the odd primes ≤ 1000, 1379 bits): `qLoop` over 50 q took 1.5 s; over 500 q (q < 1005)
  it took 9.3 s with e = 1 and 17.4 s with e = 3. That is ≈ 18–35 ms per q, dominated by the `lastOK` ranges (Σ B ≈ 15k).
  Python simulation (`/tmp`, throwaway): all 500 q pass for e = 1, 2, 3.
- **Failed (minor):** a parity proof via `.elim` on an implication; q = 2 does not divide an odd n, so the instance needs `q ≠ 2`.
- **Next:** (1) `read` first (alert Pablo on exit 5; on CLOSED, start the paper task with the literature check first). (2) The loop
  over the exponent e of q: `not_weird_tail` already covers every e for q ≥ Q. For q < Q, either a per-e loop up to the point where
  `n q^e` stops changing the regime (ratio → σ(n)/n · q/(q−1)), or a region lemma for e ≥ e₀ like the search's (exponent region
  `x ≥ e`). (3) One level up: loop over the 4th prime with an `IntervalGap` step for each (`intervalGap_mul_prime_pow`), so a
  3-prime prefix gets ONE certificate (`subtreeOK3`), timed on `3^17·5^2·43^2`. (4) Lean `lastOK` is the hot spot: replace the
  `List.range B` scan by the closed form of session 63 (`allq_fast`) if instances get slow. NEVER run owf in a session.

## Session 69 (2026-11-23, 15:54–~16:15 UTC): the exponent loop, a whole n·q^e·r family in Lean (no owf run)

- `sh scripts/owf-queue.sh read` (exit 0, no FOUND/CLOSED/ERROR): no new root (v_3 ∈ {1..20} done). owf-0 is on 3^22 (43.6M nodes),
  owf-1 on 3^21 (87.0M). `omega6-2.ck.gz` 15890 → 16506 lines (410 KB), frozen prefix OK. Palomar unchanged.
- **New `ErdosResearch/SubsetSumExpLoop.lean`** (ErdosResearchExtra only; ≈ 43 s; no sorry/native_decide; axioms
  propext/choice/Quot.sound; check-lean-sources OK; Extra OK, 9068 jobs; default OK, 9066 jobs):
  - `abOK_succ` / `abOK_of_le`: the abundant interval test for `n q^e` is **monotone in e** (the step conditions do not depend
    on e). So one success covers every larger exponent.
  - `eLoop` (with `leafOK` before stopping) and `qeLoop` (over odd q, `skipB`): sound for EVERY e ≥ 1.
  - `not_abundant_limit`: if σ(n) q (r+1) ≤ 2n(q−1) r, then `n q^e r` is not abundant for any e. `limit_mono`: the condition is
    monotone in r.
  - `eLoop0` (exponent loop for `n q^e` itself: deficient until the abundant test holds), `rLoop` (for fixed q: r from q+2,
    stop at the first r where the limit holds; otherwise IntervalGap for `n r` by one step, then `eLoop0` on q), `pqLoop` (over q).
  - Instance **`not_weird_late_prefix_mul_pow_mul_all`**: for n = 3^3·11·13^10·17^2·23, all primes q < r with q odd, q, r ∤ n, and
    **every exponent e ≥ 1**, `n q^e r` is not weird. There are three ranges: q < 35 by `qeLoop` (σ(n)/n·(q+1)/q ≥ 2, already
    abundant at e = 1), 37 ≤ q < 71 by `pqLoop` (n q^e is deficient for every e; Python: 143 prime pairs, max e = 3), and q ≥ 71
    by `not_weird_tail`. Kernel: ~10 s for both loops. Session 68 had e = 1 only.
- **Failed (minor):** `pqLoop` from q = 35 is false: 35 = 5·7 divides P1000, so `skipB` does not skip it, and its r loop needs
  > 200 steps (R ≈ 940). Fix: start at 37 and prove q ≠ 35 from primality. Also, in `not_abundant_limit` I first did
  `rw [pow_succ]` after `set`, which left `(q'+2)^e` unfolded.
- Elementary; new only as a formalisation. Not a new result on #470.
- **Next:** (1) `read` first (alert Pablo on exit 5; on CLOSED, start the paper task with the literature check first). (2) One level
  up: `subtreeOK3`, i.e. a loop over the 4th prime p with exponent f, an `IntervalGap` step for each `n p^f`, then the
  `qeLoop`/`pqLoop`/tail block from this session as the leaf. Exponent-f regions work the same way (abundant monotone,
  limit-deficient pairs). Time it on `3^17·5^2·43^2`. (3) If a block gets slow, use a cheaper `lastOK` (session 63's closed form).
  NEVER run owf in a session.

## Session 72 (2026-11-23, 23:00 UTC): v2 workers not deployed, so nothing to read (no owf run, no Lean)

- `sh scripts/owf-queue.sh read` returned **exit 8**: `/lean/state/owf/v2` does not exist. Per the standing rule: stop and tell
  Pablo → board card **#175**.
- Read-only look at `/lean/state/owf` (generation 1, which had the parity bug): the old workers are **still running**
  (owf-0 on 3^22, at (5,28),(17,13); owf-1 on 3^23, at (5,19),(17,11); omega6.ck modified 22:59). Roots 21 DONE at
  18:54 (skip 110). None of this is evidence (see `notes/omega6-invalidated.md`). The pgal side of session 71 (replicas 0,
  new image from main f1cfed4, OWF_FIRST=1, OWF_GEN=v2, replicas 2) has not been done yet. It is outside this repo.
- Decision: no repo data changes (there is no v2 data to export), and no new Lean, given the short session and the
  pending redeploy.
- **Next:** `read`. If it still gives exit 8, check card #175 and continue with Lean `subtreeOK3` (session 69 "Next", item 2),
  which does not depend on the workers. If it gives exit 0, commit `notes/data/omega6-v2.ck.gz` and `omega6-v2-roots.txt`.
  Alert Pablo on exit 5. NEVER run owf in a session.

## Session 73 (2026-11-23/24, 23:59–~00:40 UTC): `subtreeOK3` in Lean, general form (no owf run)

- `sh scripts/owf-queue.sh read` → **exit 8** again (`/lean/state/owf/v2` missing). Commented on card **#175**; no owf, no
  cluster changes, no data changes.
- New `ErdosResearch/SubsetSumBlock.lean` (ErdosResearchExtra only; no sorry/native_decide; axioms propext/choice/Quot.sound;
  module 97 s, no warnings; Extra OK 9069 jobs, default `lake build` OK 9066 jobs; check-lean-sources OK):
  - `qBlock`: ONE loop over odd `q`; each `q` passes `eLoop` (abundant from some exponent on) OR `rLoop` (prefix `n r`, then
    the exponent of `q`). This replaces session 69's three hand-picked ranges (the composite 35 just needs `rLoop` fuel 2000).
  - `blockOK` + `not_weird_of_blockOK`: `qBlock` below `Q = q₀ + 2k` and `not_weird_tail` at `Q`. For all primes `q < r`
    (`q` odd, `q ≥ q₀`, `q, r ∤ n`) and every `e ≥ 1`: `n q^e r` is not weird.
  - `fLoop` (exponent `f` of the previous prime `p`, adaptive: stop at the first `f` where `n p^f` is abundant with an interval,
    monotone by `abOK_of_le`; before that, `blockOK` for `n p^f` from `q = p + 2`), `pLoop` (odd `p`, `skipB`),
    `not_weird_ptail` (three-prime region bound: `σ(n) Q (Q+1) ≤ 2 n (Q−1)²` ⇒ no `n p^f q^e r` with primes `Q ≤ p < q, r`
    is weird; uses `p/(p−1) ≤ Q/(Q−1)` and then `not_weird_tail` on `n p^f`).
  - **`not_weird_of_subOK`**: under `IntervalGap n S c g` and the Boolean `subOK`, for all primes `p < q < r` (`p` odd,
    `p ≥ p₀`, none dividing `n`) and all `f, e ≥ 1`, `n p^f q^e r` is not weird. This is the soundness of `subtreeOK3`.
    **Not covered:** the last prime squared or higher (`r^h`, `h ≥ 2`, the "stars"), and `p` whose `n p^f` stays deficient
    for every `f` (then `fLoop` runs out of fuel and returns `false`, which is sound but incomplete).
  - Instance `not_weird_late_prefix_block`: session 69's family from ONE `decide +kernel` on `blockOK` (`q` from 5 to 71,
    `K = 40`, `Kr = 2000`).
- **Failed / not done:** no `subOK` instance. `#eval` of `fLoop` on the late prefix (`p = 37`, `Kq = 100`, `Kr = 2000`) did
  not finish in 400 s (interpreted). Reason: for `p` just past the abundance threshold, `σ(n p)/(n p) ≈ 1.99`, so the
  `q`-tail needs `Q` in the hundreds and every `q` below runs `rLoop` with large fuel. The late prefix (5 primes) is also not
  what the search needs (3-prime prefixes `M3`).
- Elementary; new only as a formalisation. Not a new result on #470.
- **Next:** (1) `read` (exit 8 ⇒ check #175; exit 0 ⇒ commit `omega6-v2.ck.gz` + `omega6-v2-roots.txt`; exit 5 ⇒ alert Pablo).
  (2) Measure `fLoop` cost in Python first (port `eLoop`/`rLoop`/`lastOK`, or reuse `scripts/subroot_leaf_probe.py` counts):
  how many `(p, f, q)` and `r` steps per 3-prime prefix. (3) Cheaper `rLoop`: replace the `r` loop by the closed limit bound
  (`allq_fast`, session 63) so that `rLoop` does not iterate r one by one. (4) Stars (`r^h`, `h ≥ 2`): a fourth layer, or
  `pseudoperfect_star_of_intervalGap`. (5) IntervalGap for a real `M3` (`3^17·5^2·43^2`) via `late_cert_gen.py`, then a `subOK`
  instance. NEVER run owf in a session.

## Session 74 (2026-11-24, 01:25–~02:30 UTC): `subOK` measured on real prefixes; the limit-deficient gap; staircase decider (no owf run)

- `sh scripts/owf-queue.sh read` → **exit 8** again (`/lean/state/owf/v2` missing). Comment on card **#175**. No owf, no cluster,
  no data changes. Palomar: done since session 18, unchanged.
- New `scripts/subok_cost_probe.py` (Python): exact port of session 73's Booleans (`subOK`/`pLoop`/`fLoop`/`blockOK`/`qBlock`/
  `eLoop`/`rLoop`/`eLoop0`/`leafOK`/`lastOK`, same short-circuit order) with kernel-work counters. `lastOK` in closed form
  (`SELFTEST=1`: 20000 random cases, 0 mismatches vs. the literal loop). It reproduces `blockOK_late_prefix = true`
  (91k `lastOK` q-steps, ~2.2k loop iterations). `--plan 'p^e*…' LIMB` takes (c, g) for a real prefix from session 64's `plan4`.
- **Findings on `subOK` (session 73):**
  1. `skipB q P1000` does NOT skip squarefree composites whose prime factors all divide `P1000` (15, 21, 35, 533 = 13·41, …),
     because `P % q = 0`. On the late prefix, `p = 35` fails at `q = 533`. Fix: also skip when some small `s < q` divides `q`
     (`SKIP=small`, same results as an exact primality oracle). Lean: `skipS` + `prime_imp_not_skipS` (below).
  2. **Main gap:** a prime `p` is *limit-deficient* when `σ(n) p ≤ 2 n (p − 1)`; then `n p^f` is deficient for EVERY `f`, so
     `fLoop` never stops (fuel ⇒ false). On real 3-prime prefixes this is almost every `p`: `3^17·5^2·43^2` (σ/n = 1.904,
     c = 37, g = 2, three-prime tail Q = 63) has p ∈ {47, 53, 59, 61}, all four limit-deficient, all `ffuel`. So `subOK` as
     written covers essentially nothing in the search.
  3. Small bases (3·5·7, 3·5·11, …) also fail `stepOK` (p·g + 2c > S + 1). This is an artefact of tiny S; real prefixes have S ≈ 10^12+.
- New `scripts/plimit_probe.py` (Python): a **staircase decider** for the sub-tree below a prefix (all primes p < q < r, all
  f, e ≥ 1, `r^1`; stars still excluded). Tools: (a) abundant with interval via the IntervalGap chain n → p^f → q^e (→ r),
  which is an up-set in (f, e) because the excess grows (A(f+1) = p·A(f) + σ(m)); (b) **limit strips**: `σ(m) p ≤ 2 m (p − 1)` ⇒
  `m p^f` not abundant for every f (a whole row/column); with a free r it bounds r (`not_abundant_limit`); (c) `lastOK` at
  deficient corner points with a free r. Per (p, q): the pair limit `σ(n)/n · p/(p−1) · q/(q−1)` ≤ 2 ⇒ r is bounded and each
  (p, q, r) is a 2-D staircase; > 2 ⇒ 2-D staircase with free r. Non-limit-deficient p use the exponent loop (like `fLoop`)
  with a q-level decider (q limit-deficient ⇒ r bounded plus a 1-D line in e; otherwise an e-loop with `lastOK` points).
  - `3^17·5^2·43^2`: **all 4 p closed**; work 4 exact points, 9 strips, 38 triples (< 0.1 s).
    **Brute-force cross-check** (`scripts/plimit_bruteforce.py`; p ≤ 61, q < 400, f, e ≤ 8, r < 4000; 12.4M points, 3710 abundant): **0 uncovered** (every
    abundant point has its own interval certificate, or its r-free prefix is certified by abOK/lastOK).
  - `3^18·7^13·19^8` (σ/n = 1.847, c = 56, g = 3): all 4 p closed, but 57947 exact points and 153k r-steps (3 s in Python):
    too many for one `decide +kernel`, unless the points get cheaper (most are 1-D lines in a strip, `rsteps` dominates).
  - Near-perfect prefixes `3^16·5^11·19^8` (σ/n = 1.979) and `3^18·5^16·17^11` (σ/n = 1.992): the first 16 (resp. 40) p are
    trivial (n·p is already abundant with an interval at f = 1), but the first limit-deficient p (97, resp. 257, thresholds
    95.9999 and 255.9999: the Fermat family of session 70) did not finish in 15 min (resp. ~10 min, killed): the pair region
    runs q into the thousands, with a free r. These are exactly the configurations that make the real search slow too.
  - **`FASTSTRIP=1` (swapped loops in the strips with free r):** for each f, with M = m p^f deficient, σ = σ(M), D = 2M − σ:
    M r is abundant ⇔ r D < σ, and certified (abOK of M r) ⇔ stepOK and r D ≤ σ − c. Both are r-intervals (closed form, cf.
    `pseudoperfect_mul_prime_of_range`, session 63), and certification is monotone in f, so stop at the first f where every
    prime r < R is certified. `3^18·7^13·19^8`: **57947 exact points → 32 f-steps, and ≤ 12 window r (0 < excess < c)** to test one
    by one; same result (all p closed). `3^17·5^2·43^2` unchanged (4 points). Final version: no list of primes r; per f only
    the interval ends (`cert_lo`, `cert_hi` = min((σ − c)/D, (S + 1 − 2c)/g), `ab_hi` = (σ − 1)/D) plus the window
    (cert_hi, ab_hi] scanned for primes; stop when cert_hi ≥ the largest prime r < R. `3^18·7^13·19^8`: 32 f-steps, **0 window
    primes**, 0.0 s.
  - Near-boundary `3^16·5^11·19^8`, p = 97 (ρ_p = σ(n)/n · 97/96 = 1.99978): two-prime tail Q = 18429, 2085 q, 1117 with pair
    limit > 2. With the closed-form strips, **all 1117 free-r staircases pass** (q up to 9209; every q takes ≤ 0.01 s).
    The first q with pair limit ≤ 2 (q = 9221, L2 = 1.99999986) has an r bound R ≈ 1.4·10^7, i.e. ~10^6 separate (p, q, r)
    staircases: **not feasible as written**. Fix (not done): the same swap one level up: for bounded r, run the (f, e)
    staircase with closed-form r-ranges per point (abundant ⇔ r < σ/D, certified ⇔ r ≤ (σ − c)/D), target "every prime
    r < R certified". A 5-min run confirms it: through q = 9209 quickly, then no progress on q = 9221.
  Indicative only (Python, few prefixes; brute force only on the first one).
- New `ErdosResearch/SubsetSumStrip.lean` (ErdosResearchExtra only; no sorry/native_decide): `not_abundant_of_limit` (the strip
  lemma: `σ(m) p ≤ 2 m (p − 1)`, `p ∤ m` ⇒ `m p^f` not abundant for all f) and `skipS`/`prime_imp_not_skipS` (small-divisor
  composite test). Elementary; new only as a formalisation.
- **Not done / failed:** no Lean staircase checker yet. With bounded r near the boundary (q = 9221 for p = 97 above), the probe
  makes one staircase per r (~10^6) and does not finish. First version of the probe: an unbounded q loop for p that are not
  limit-deficient (fixed: exponent loop), and an r list built by trial division up to 1.7·10^7 (fixed: closed form).
- **Next:** (1) `read` (exit 8 ⇒ #175; exit 0 ⇒ commit `omega6-v2.ck.gz` + `omega6-v2-roots.txt`; exit 5 ⇒ alert).
  (2) Python: bounded-r triples by the same swap: an (f, e) staircase with closed-form r-ranges per point, target "every prime
  r < R certified" (rows/columns whose r-limit stays below R are strips again). Then `3^16·5^11·19^8` in full, and the
  Fermat-type `3^18·5^16·17^11` (p = 257). Brute-force `3^18·7^13·19^8` as was done for the first prefix.
  (3) Count how many 3-prime prefixes per root are "easy" (like 3^17·5^2·43^2 and 3^18·7^13·19^8) vs near-boundary.
  (4) Lean: `stairOK` with soundness from `not_abundant_of_limit`, `not_abundant_limit`, `abOK_of_le` (in both exponents;
  needs `abOK` monotone in an exponent that is not the last, i.e. a commuted chain), the range lemma
  `pseudoperfect_mul_prime_of_range` for the strips, `lastOK`; and `skipB || skipS` in the loops. NEVER run owf in a session.
- **Verification of Extra (review follow-up, 2026-11-24 ~02:50 UTC):** the default `lake build` does NOT compile
  `SubsetSumStrip` (only `ErdosResearchExtra.lean` imports it), so it was checked on the Extra target:
  `/opt/lean-locked/bin/lake build ErdosResearchExtra` → rc 0, "Build completed successfully (9070 jobs)"; the module itself,
  elaborated from scratch with `lake env lean ErdosResearch/SubsetSumStrip.lean` → rc 0, no errors and no warnings (27 s), against
  Lean v4.35.0 + Mathlib v4.35.0. `#print axioms`: `not_abundant_of_limit` = [propext, Classical.choice, Quot.sound],
  `prime_imp_not_skipS` = [propext, Quot.sound]. No sorry/native_decide. The GitHub CI builds Extra in the lean.yml step
  "Build non-default research modules" (`lake build ErdosResearchExtra`); that run is what certifies this PR.

## Session 75 (2026-11-24, 03:51–~04:45 UTC): bounded-r pairs by one staircase; real-prefix census; closed-form `lastOKR` (no owf run)

- `sh scripts/owf-queue.sh read` → **exit 8** again (`/lean/state/owf/v2` missing). Comment on card **#175** (the old generation-1
  workers, with the parity bug, are still running: root 22 DONE 01:48, omega6.ck written 03:51). No owf, no data changes. Palomar
  unchanged (done since session 18).
- **`BOUNDED=1` in `scripts/plimit_probe.py` (`stair_bounded`):** a pair (p, q) with pair limit L2 < 2 is now ONE (f, e) staircase
  for all primes r ∈ (q, R) at once, instead of one staircase per r. Per point M = n p^f q^e (always deficient here): M r abundant
  ⇔ r ≤ (σ−1)/D, certified ⇔ r ∈ [cert_lo, cert_hi] (the closed forms of `strip_fast`); bad r = odd primes not dividing n, found
  with a sieve (`bytearray.find`). Row e only needs r < R_e (its limit bound, `not_abundant_limit`), column f likewise; e* / f* =
  first row/column whose bound exceeds the largest bad r < R; a point where every relevant r is certified ends its line
  (certification is monotone in each exponent); the box [f*, f_row) × [e*, e_col) is checked point by point.
  - Same verdicts as session 74 on `3^17·5^2·43^2` and `3^18·7^13·19^8` (all p closed).
  - **`3^16·5^11·19^8`, p = 97: closed in 0.8 s** (session 74: did not finish, q = 9221 with R ≈ 1.4·10^7). Whole 3-prime
    sub-tree (all 53 p): closed, 2.1 s. **`3^18·5^16·17^11` (Fermat type, p = 257): all 128 p closed, 43 s.**
- New `scripts/plimit_bounded_check.py` (brute-force soundness check of `stair_bounded`: for every pair it closes, every abundant
  n p^f q^e r with f, e ≤ FE and r a bad prime < R must have its own certificate). `3^18·7^13·19^8` FE 8: 8653 abundant, 0
  uncertified; `3^17·5^2·43^2` FE 10: 3710/0; `3^16·5^11·19^8` p = 97 (FE 5, every 10th pair, 300 smallest + 300 largest r):
  926318/0; `3^18·5^16·17^11` p = 257, 263 (FE 4, every 20th pair, RMAX 200): 1390250/0. **Mutation test** (`CG=3e12,2` makes
  certificates fail; a decider forced to answer True): the checker flags 1314/1314, so it can see unsoundness.
- New `scripts/plimit_root_census.py` (read-only): samples REAL exact deficient 3-prime prefixes of a root from the generation-1
  checkpoint (only the prefix SHAPE, which the parity bug does not change; copied read-only to /tmp) and runs the decider (stars still
  excluded). Roots 3^16 / 3^20 / 3^22 have 1846 / 2146 / 2186 such prefixes. Sample 15 each, seed 75, 90 s timeout:
  **41/45 closed within 90 s** (most in 0.5–4 s); the 4 timeouts were rerun without the 90 s cap: `3^16·5^18·17^4` closed (134 s),
  `3^20·5^21·17^7` closed (176 s), `3^20·5^26·17^13` closed (320 s); `3^22·7^11·13^2` did not finish in 900 s, stuck at p = 19: `decide_q` (q limit-deficient
  under a non-limit-deficient p) still iterated r one by one up to R. **Fix:** with `BOUNDED=1` that branch is now `strip_fast`
  (closed-form r-ranges per e, as in session 74's strips) ⇒ `3^22·7^11·13^2` **closed in 1.0 s**; the three test prefixes give the
  same verdicts. Not yet brute-checked: this new use of `strip_fast` in `decide_q` (a throwaway check timed out building a
  sieve up to R; cap R next time).
  **0 failing p in every prefix that finished.** Indicative (Python, sample of 45, stars excluded).
- **Kernel cost:** the slow prefixes are dominated by `lastOK` q-scans (`lastq` = 5.6·10^7 to 1.9·10^9 per prefix), which are
  literal loops in Lean. New `ErdosResearch/SubsetSumLastRange.lean` (ErdosResearchExtra only; no sorry/native_decide; axioms
  propext/Classical.choice/Quot.sound; module 39 s; `lake build ErdosResearchExtra` OK, 9071 jobs; check-lean-sources OK):
  `qCond`, `lastOKR n S c g B lo hi` (the 4 range conditions at the two ends, scan only q < lo and hi < q < B) and
  **`not_weird_mul_prime_of_lastOKR`** (from `pseudoperfect_mul_prime_of_range` + `not_weird_mul_prime_of_intervalGap`).
  Sanity instance: `3^16·5^11·19^8·97^3` with B = 9214 checks two ends and scans nothing. Elementary; new only as a formalisation.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit `omega6-v2.ck.gz` + `omega6-v2-roots.txt`; 5 ⇒ alert). (2) Python: count the kernel
  work with `lastOKR` instead of `lastOK` (scan length = q < lo plus (hi, B)), so the census reports a realistic Lean cost per prefix.
  (3) Stars (r^h, h ≥ 2) in the staircase (session 63's `pseudoperfect_star_of_intervalGap`). (4) Lean `stairOK` for one pair (p, q)
  with bounded r (soundness from `not_abundant_limit`, `abOK_of_le`, the range lemma), then `subOK` with `lastOKR`. NEVER run owf in a session.

## Session 76 (2026-11-24, 05:46–~06:40 UTC): strip_fast brute-checked; lastOKR cost; stars reduced to one test per point (no owf run)

- `sh scripts/owf-queue.sh read` → **exit 8** again (`/lean/state/owf/v2/omega6.ck` missing). Comment on card **#175**. No owf, no
  data changes. Palomar unchanged (done since session 18).
- **(1) Soundness check of `strip_fast`, including session 75's new `decide_q` branch** (the open item). New
  `scripts/plimit_strip_check.py`: spies on every `strip_fast` call that returns True and, for f ≤ FE and the RMAX smallest + RMAX
  largest bad r in [r_lo, R) (found by trial division from both ends; R is never sieved), checks that every abundant point has its
  own IntervalGap certificate. It also checks that the 20 bad r just above R are never abundant.
  `3^22·7^11·13^2` p = 19 (FE 6, RMAX 200, 4038 calls): **9354475 abundant, 0 uncertified, 0 abundant above R**;
  `3^16·5^11·19^8` (17 p, FE 4): 385895/0; `3^18·5^16·17^11` (p = 19…47, 257, 263; FE 4): 2488545/0.
  **Mutation:** `CHECKCG=c,g` (verify with a stricter c) flags 3980 and 11063 points, so the checker can see unsoundness. (`CG` + `FORCE=1`
  does not work as a mutation: with a large c the decider fails before it reaches strip_fast.)
- **(2) Kernel work with `lastOKR`.** `scripts/plimit_probe.py` now also counts `lastqR`, the q values Lean's `lastOKR` scans (q < lo
  plus (hi, B)) at the same points, next to `lastq` (`lastOK`). BOUNDED=1 FASTSTRIP=1, whole 3-prime sub-trees:

  | prefix | time | pts | lastq (lastOK) | lastqR (lastOKR) |
  |---|---|---|---|---|
  | 3^16·5^11·19^8 | 1 s | 14848 | 296674 | 2 |
  | 3^18·5^16·17^11 | 40 s | 79307 | 5.49·10^7 | 10 |
  | 3^16·5^18·17^4 | 65 s | 77378 | 1.86·10^9 | 11 |
  | 3^20·5^21·17^7 | 91 s | 79238 | 5.58·10^7 | 10 |
  | 3^20·5^26·17^13 | 130 s | 79240 | 5.60·10^7 | 10 |

  So with `lastOKR` the last-prime scans vanish. Reason: when lastOK is True, every q in the scanned ends either divides n or makes nq
  non-abundant. The Lean cost per prefix is now set by ≈ 8·10^4 points (GMP chain + stepOK) and ≈ 2.6·10^4 pairs. The per-point kernel
  cost is not measured yet (it needs a Lean `stairOK`).
- **(3) Stars r^h, h ≥ 2: one test per deficient point.** Excess E(h) = σ(M)σ(r^h) − 2M r^h of M r^h (r ∤ M) satisfies
  E(h+1) = r E(h) + σ(M). Hence: (a) M r abundant and certified ⇒ every M r^h certified (same stepOK, excess only grows);
  (b) E(h) ≥ 1 and c ≤ σ(M) ⇒ E(h+1) ≥ c, so only the first abundant h0 can lack a certificate; (c) a star that is not already
  abundant at h = 1 needs σ(M) ≤ rD < 2M (D = 2M − σ(M)), so there is **exactly one candidate r* = ⌈σ/D⌉**.
  Lean (ErdosResearchExtra only; no sorry/native_decide; axioms propext/Classical.choice/Quot.sound; module 23 s; `lake build
  ErdosResearchExtra` OK, 9072 jobs; default `lake build` OK, 9066; check-lean-sources OK): new `ErdosResearch/SubsetSumStar.lean`,
  pure algebra with s for σ(M): `starExcess_succ`, `starExcess_ge_of_pos`, `starExcess_ge_of_ge`, `star_window`, **`star_r_unique`**.
  Not yet linked to `Nat.sigma`/`IntervalGap`, which will be done with `pseudoperfect_star_of_intervalGap` in the checker.
  Numerical check of the algebra (throwaway, /tmp): 57448 random (M, r), 0 violations.
  New `scripts/plimit_star_probe.py` (limit-deficient p only, p, q over the decide_p ranges, f, e ≤ 5): every r* that is a bad prime > q
  has a certified first abundant star: `3^16·5^11·19^8` 7224/7224, `3^22·7^11·13^2` 266/266, `3^18·5^16·17^11` 33992/33992,
  `3^16·5^18·17^4` 34906/34906, `3^20·5^26·17^13` 34147/34147, `3^17·5^2·43^2` 18/18, `3^18·7^13·19^8` 70/70. **0 uncertified.**
  Not covered: non-limit-deficient p (decide_p's f-loop), points with f or e > 5, and the boundary r* ∈ {R−1, R} on limit strips
  at large f (r*(f) → ⌈λ/(1−λ)⌉ as f → ∞). Indicative.
- **Failed (minor):** the star probe first looped forever on non-limit-deficient p (no two-prime tail exists), and trial division on huge r*
  was slow (Miller–Rabin now). The CG/FORCE mutation was useless (see (1)).
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) Stars in the decider itself: the r* test at every enumerated
  deficient point, plus the strip boundary (one r, a 2-D (f, h) staircase) and the f-loop p; brute-check against
  `plimit_star_probe.py`. (3) Lean `stairOK` for one bounded pair (`not_abundant_limit`, `abOK_of_le`, the range lemma,
  `lastOKR`, star lemmas), to measure the per-point kernel cost. NEVER run owf in a session.

## Session 77 (2026-11-24, 07:25–~07:45 UTC): star lemmas linked to σ; star probe covers the f-loop p (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 (`/lean/state/owf/v2/omega6.ck` missing). Comment on card #175. No owf run and no
  data changes. Palomar: done since session 18, unchanged.
- **Lean** (ErdosResearchExtra only; no sorry/native_decide; `star_prime_unique` uses only propext/Classical.choice/Quot.sound; module 28 s,
  0 warnings; `lake build ErdosResearchExtra` OK, 9072 jobs; check-lean-sources OK; the default build does not import this module):
  `ErdosResearch/SubsetSumStar.lean` gains `sigma_mul_prime_pow` (σ(M r^h) = σ(M)·geom r h for r prime, r ∤ M), `starExcess_eq`,
  `abundant_iff_starExcess_pos`, and **`star_prime_unique`**: for deficient M, at most one prime r ∤ M has M r not abundant while
  some M r^h is abundant. The session-76 algebra now speaks about `Nat.sigma`. Elementary; new only as a formalisation.
- **Python:** `scripts/plimit_star_probe.py` has a new mode `FLOOP=1` (optional `FCAP`). For a non-limit-deficient p it loops over f = 1..f0−1
  (n p^{f0} is the first abundant power, so nothing below it needs a star). For each f, q runs over (p, Q_f) with ρ_f Q_f² ≤ 2 (Q_f − 1)².
  Results (LIMB 10^5, every p, 0 uncertified everywhere, nothing skipped, no f-capped p):

  | prefix | FE | star candidates | certified |
  |---|---|---|---|
  | 3^17·5^2·43^2 | 5 | 18 | 18 |
  | 3^18·7^13·19^8 | 5 / 10 | 70 / 290 | all |
  | 3^22·7^11·13^2 | 5 / 10 | **1916** (session 76, without the f-loop p: 266) / 4306 | all |
  | 3^16·5^11·19^8 | 5 / 10 | 7224 / 29462 | all |
  | 3^18·5^16·17^11, 3^16·5^18·17^4, 3^20·5^26·17^13 | 5 | 33992, 34906, 34147 (no f-loop p) | all |

  These results are indicative only (sampled exponents, Python). Still not covered: the strip boundary r* ∈ {R−1, R} at large f, and e > FE.
  **Mutation test** (`CHECKC=x` replaces c = 37 in the certificate test with x): on `3^22·7^11·13^2`, x = 10^12 and 10^18 still give 0
  uncertified (the first abundant excesses are huge, σ ≈ 10^40). x = 10^31 flags 474/1916 and x = 10^39 flags 1241/1916, so the probe does
  detect failures, and the real certificates (c = 37) have a very large margin.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) Stars inside the decider (`plimit_probe.py`):
  the r* test at each enumerated deficient point plus the strip boundary, checked against `plimit_star_probe.py FLOOP=1`, plus a mutation
  test. (3) Lean `stairOK` for one bounded pair, to measure the per-point kernel cost. NEVER run owf in a session.

## Session 78 (2026-11-24, 08:30–~09:35 UTC): stars inside the staircase decider; stepOK monotonicity in Lean (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 (`/lean/state/owf/v2/omega6.ck` missing). Comment on card #175. No owf run and no data
  changes. Palomar: done since session 18, unchanged.
- **`scripts/plimit_probe.py STARS=1`** (needs `BOUNDED=1 FASTSTRIP=1`): the decider now also covers the 6th prime as a star r^h (h ≥ 2).
  Facts used (Lean `SubsetSumStar.lean`): E(h+1) = r E(h) + σ(M); at a deficient M only r* = ⌈σ/D⌉ can have M r* non-abundant but
  some M r*^h abundant (`star_prime_unique`), and only its first abundant h0 needs a test (E(h0) ≥ c, stepOK(M, r*), c ≤ M r*^h0, σ(M) ≥ c).
  Where each piece is checked:
  * free-r points (`point()`: `decide_q` exponent loop, free-r staircase box): `star_fail` at the point (Miller–Rabin for r*; a "probable
    prime" answer is treated as prime, so the test can only get stricter).
  * bounded 1-D lines (`strip_fast`: row strips and `decide_q`'s limit-deficient branch): along the line, σ/D increases to
    L = A/(B−A), so r*(f) = ⌈L⌉ = r∞ once σ/D > ⌈L⌉ − 1. So: `star_fail` at every f before that, then `check_r(r∞)` once.
  * bounded 2-D pairs (`stair_bounded`): T = {σ/D > r∞ − 1} is an up-set where r* = r∞. Outside T there are finitely many rows and columns
    (1-D, recursive) plus a finite box (`star_fail` per point); then `check_r(r∞)`.
  * `check_r(r)`: V_h = {x : M(x) r^h abundant} and the certified set C_h are up-sets (ratio and excess grow in every exponent; chain and
    stepOK monotone, the same assumption as the r^1 staircase). It checks that every minimal point of V_h (h = 2..H) is in V_1 or C_h. H is
    the largest h0 over the minimal points of U = {ρ r > 2(r−1)}. Minimal points come from a staircase with exact row/column limits.
  * First version (`STARPERR=1`, kept): `check_r` for every bad prime r in [σ0/D0, sup σ/D + 1). It is correct but loops up to ~10^9 r
    on near-perfect strips (it hung at p = 19 of `3^22·7^11·13^2`). Before that, a "+1 on every r-bound" variant never terminated:
    the star-only primes near the bound are never certified at h = 1, so lines never reach "full" (reverted).
  * The two-/three-prime tails (Q, Q3) are already star-safe: Q(Q+2) ≤ (Q+1)^2.
- **Results (LIMB 10^5, all p):**

  | prefix | STARS=0 | STARS=1 |
  |---|---|---|
  | 3^17·5^2·43^2 | 4 p, 0 failing | 0 failing, 0.0 s |
  | 3^18·7^13·19^8 | 0 failing | 0 failing, 0.0 s |
  | 3^22·7^11·13^2 | 0 failing, 0.7 s | 0 failing, 1.6 s (STARPERR: 12 s, same verdict) |
  | 3^16·5^11·19^8 (near-boundary) | 0 failing, 9.7 s | 0 failing, 2.3 s |
  | 3^18·5^16·17^11 (Fermat-type) | 128 p, 0 failing, 93 s | 0 failing, 142 s |

  **Census** (`plimit_root_census.py` with `STARS=1`, the same sample as session 75: roots 3^16/3^20/3^22, 15 each, seed 75, 120 s cap, on a
  read-only /tmp copy of the gen-1 checkpoint; only prefix SHAPES are used, and the parity bug does not change them): **44/45 closed within
  120 s, 0 failing**. The timeout `3^20·5^26·17^13` (320 s without stars in session 75) was rerun uncapped: **closed** (128 p, 0 failing, 214 s). So **45/45 closed** with stars.
- **Mutation tests** (`CHECKC=x` makes the star test stricter; the r^1 logic is unchanged). On `3^22·7^11·13^2`, x = 10^31: the decider
  fails exactly p ∈ {19, 23, 29, 31, 37, 41, 43, 47}, the same p the independent brute-force probe (`plimit_star_probe.py FLOOP=1`, FE 5)
  flags per p, and STARPERR gives the same set. x = 10^12: both 0. On `3^16·5^11·19^8`: x = 10^24 gives 0/0; x = 10^32 and 10^39 give
  34 p flagged by the probe and 34 failing in the decider, and **0 flagged by the probe but passed by the decider**. So the star layer
  detects failures, and its verdicts agree with brute force on the sampled exponents. All of this is indicative only (Python).
- **Monotonicity (paper proof, closes the assumption used since session 74):** stepOK(n, S, c, g, q) is
  `q g + 2c ≤ S + 1 ∧ n + 2c ≤ (q+1) S + 1` with S = ∑D(n). Raising any exponent replaces n by n p with S' = σ(np) − np ≥ p S
  (σ(np)/(np) ≥ σ(n)/n). Then S' ≥ S, and (q+1)S' + 1 ≥ p((q+1)S) + 1 ≥ p(n + 2c − 1) + 1 ≥ np + 2c (as 2c(p−1) ≥ p−1, which
  needs c ≥ 1). The step of a prime only depends on the part of the chain before it. So every chain condition, c ≤ N, and the excess (E(f+1) = p E(f) + σ(rest))
  are monotone in every exponent, and the certified sets are up-sets.
- **Lean** (ErdosResearchExtra only; no sorry/native_decide; axioms propext/Classical.choice/Quot.sound; module 15 s;
  `lake build ErdosResearchExtra` OK, 9073 jobs; check-lean-sources OK; the default build does not import it): new
  `ErdosResearch/SubsetSumMono.lean` has `mul_sum_properDivisors_le` (p·∑D(n) ≤ ∑D(n p)), `stepCond_mono` and `stepCond_mul` (the two
  stepOK inequalities survive n ↦ n p, for c ≥ 1). Elementary; new only as a formalisation.
- **Failed:** see the two discarded variants above.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) Lean `stairOK` for one bounded pair, to measure the
  per-point kernel cost (r^1 part first; then the star layer: `star_fail` = one test per point, `check_r` = minimal-point lists). (3) Use
  `stepCond_mul` in that `stairOK` soundness proof (the up-set step). NEVER run owf in a session.

## Session 79 (2026-11-24, 10:22–~10:45 UTC): one staircase point, every last prime r at once, in Lean (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` missing). Comment on card #175. The old
  gen-1 workers (parity bug) are still running: root 23 DONE at 06:41 UTC, which is not evidence. No owf run, no data changes. Palomar: done
  since session 18, unchanged.
- **Lean** (ErdosResearchExtra only; no sorry/native_decide; standard axioms; module ≈ 20 s; `lake build ErdosResearchExtra` OK, 9074 jobs; check-lean-sources OK; the default build does not import it): new
  `ErdosResearch/SubsetSumPoint.lean`. This is the r^1 part of `stairOK` for ONE point. For a deficient M with `IntervalGap M S c g` and D = M − S,
  M r is abundant ⇔ r D < σ(M) = S + M. Every condition of `not_weird_mul_prime_of_intervalGap` is monotone in r, so the Boolean
  `pointOK M S c g r₀ r₁` checks them only at the two ends: r₀ (step condition `M + 2c ≤ (r₀+1) S + 1`, `c ≤ M r₀`) and r₁
  (`σ ≤ (r₁+1) D`, `r₁ g + 2c ≤ S + 1`, `r₁ D + c ≤ σ`). `not_weird_mul_prime_of_pointOK` then gives ¬(M r).Weird for EVERY prime
  r ≥ r₀, r ∤ M, with no scan. (If the window (σ−c)/D < r < σ/D has a prime, `pointOK` is false and `lastOKR` remains the fallback.)
  Instance **`not_weird_late_prefix_mul_prime`**: no 3^3·11·13^10·17^2·23·r is weird, for any prime r (r₀ = 2, r₁ = 32; one
  `decide +kernel`, cost negligible next to the certificate it reuses). It is the same family as session 68's `not_weird_late_prefix_mul_mul` but one
  level shorter, and it is a closed form. Elementary; new only as a formalisation.
- **Per-point kernel cost:** the r^1 part of a point is now O(1) GMP comparisons, so the cost per point is dominated by building
  `IntervalGap` for M (by steps from the prefix certificate, `intervalGap_mul_prime_pow`, also O(1) per step).
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) `stairOK` for one bounded pair (p^f, q^e):
  loop over the staircase points, `intervalGap_mul_prime_pow` twice plus `pointOK` at each point, limit rows/columns via
  `not_abundant_of_limit`, up-set step via `stepCond_mul`; measure the kernel time on `3^16·5^11·19^8`, p = 97. (3) Then the star layer.
  NEVER run owf in a session.

## Session 80 (2026-11-24, 11:22–~11:40 UTC): staircase points after steps; the up-set is free (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` missing). Comment on card #175. The old
  gen-1 workers (parity bug, not evidence) are still running; last root DONE: 3^23 (06:41 UTC). No owf run, no data changes. Palomar:
  done since session 18, unchanged.
- **Lean** (ErdosResearchExtra only; no sorry/native_decide; standard axioms; module ≈ 20 s, 0 warnings; `lake build ErdosResearchExtra`
  OK, 9075 jobs; check-lean-sources OK; the default build does not import it): new `ErdosResearch/SubsetSumStairPoint.lean`.
  - `stepPointOK n S c g r₀ r₁ l` = `stepsOK` along a list of prime-power steps `l` + `pointOK` at the end point;
    `not_weird_of_stepPointOK`: IntervalGap n + Boolean ⇒ ¬(M r).Weird for every prime r ≥ r₀, r ∤ M (M = n·∏ steps).
  - `stepAbOK` + `pseudoperfect_of_stepAbOK` (abundant point: c ≤ M, M + c ≤ ∑D M ⇒ M pseudoperfect), via
    `pseudoperfect_of_intervalGap`.
  - **`not_weird_of_upset`:** if the minimal abundant point n p^f₀ q^e₀ is pseudoperfect, then every n p^f q^e m (f ≥ f₀, e ≥ e₀,
    m ≥ 1) is not weird. So the region above the staircase needs NO step conditions: one pseudoperfect point per minimal corner
    (simpler than the `stepCond_mul` route planned in session 79).
  - Instances on the late prefix n = 3^3·23·13^10·17^2·11 (c, g) = (2295, 5): `not_weird_late_prefix_pair_point` (deficient
    point n·37·307: every prime r, r₁ = 6686), `pseudoperfect_late_prefix_pair_point` (n·37·41), `not_weird_late_prefix_37_41`
    (no n·37^f·41^e·m weird, f, e ≥ 1). The (p, q) were picked by a throwaway scan in /tmp (not in the repo). Elementary; new only
    as a formalisation.
- **Not done:** the quantification over all (f, e) of a pair (finite set of deficient points below the staircase + limit rows /
  columns, where for fixed f all e stay deficient and r must be handled in closed form per f, as in `strip_fast`), and stars.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) Lean limit row: for fixed f with
  σ(M_f) q ≤ 2 M_f (q−1), decide every (e, r) in closed form (generalise `pointOK` to a row: D_e = M_f q^e − S_e grows
  monotonically in e; find the monotone direction of each condition first, in Python). (3) Then `stairOK` = corners (`stepAbOK`) +
  finite deficient points (`stepPointOK`) + rows/cols, timed on `3^16·5^11·19^8`, p = 97. (4) Stars. NEVER run owf in a session.

## Session 81 (2026-11-24, 12:33–~13:10 UTC): limit row in Lean; generic `pairOK` closes whole pairs (p, q) (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2` missing). Comment on card #175. No owf run, no data
  changes. Palomar: done since session 18, unchanged.
- **Monotone directions (paper, then Lean):** fix `m` (= n p^f) with `IntervalGap m S c g` and a prime q ∤ m. With
  `T_e = σ(m q^e)`, `M_e = m q^e`: `T_{e+1} = q T_e + σ(m)`, `M_{e+1} = q M_e`. Then
  (a) `σ(m) q (r₁+2) ≤ 2 (r₁+1) m (q−1)` (limit with margin) ⇒ `(r₁+2) T_e < 2 (r₁+1) M_e` for EVERY e (via `ppSum_exact'`), which
  gives deficiency and "abundant only for r ≤ r₁" on the whole row; (b) `2 r₁ M + c ≤ (r₁+1) T`, `(r₀+2) M + 2c ≤ (r₀+1) T + 1`
  (needs c ≥ 1), `r₁ g + 2c ≤ S + 1`, `c ≤ M r₀` all propagate from e to e+1 (they are the remaining `pointOK` conditions
  rewritten in T). The q-step conditions do not depend on e (`intervalGap_mul_prime_pow`). One `r₁ = ⌊L⌋` (L = limit of
  σ/D along the row) serves the whole row from some e₀ on: the window ((σ_e − c)/D_e, σ_e/D_e) shrinks to 0 below L.
- **Lean** (ErdosResearchExtra only; no sorry/native_decide; standard axioms; module 38 s (12 s CPU), 0 warnings;
  `lake build ErdosResearchExtra` OK 9076 jobs; default `lake build` OK 9066; check-lean-sources OK): new
  `ErdosResearch/SubsetSumRow.lean`.
  - `rowOK m S c g q r₀ r₁ e₀` (checked at e₀ only) + **`not_weird_of_rowOK`**: ¬(m q^e r).Weird for every e ≥ e₀ and every prime
    r ≥ r₀, r ∤ m q^e. `stepRowOK` / `not_weird_of_stepRowOK`: the same after prime-power steps from a prefix certificate.
  - Instances below the late prefix n = 3^3·23·13^10·17^2·11 ((c, g) = (2295, 5)): `not_weird_late_prefix_row` (n·37·307^e·r,
    e ≥ 3, r₁ = 7196), `not_weird_late_prefix_row_two` (e = 2, point, r₁ = 7195), `not_weird_late_prefix_row_all` (all e ≥ 1),
    `pseudoperfect_late_prefix_corner` (n·37²·307), and **`not_weird_late_prefix_pair_all`: no n·37^f·307^e·r is weird for ALL
    f, e ≥ 1 and every prime r** (row f = 1 is limit-deficient; for f ≥ 2 the corner (2, 1) is abundant and pseudoperfect ⇒ up-set).
    This is the first whole 2-D pair of the staircase in Lean. (p, q) chosen by a throwaway scan in /tmp/s81 (not in the repo).
  - Elementary; new only as a formalisation. Not a new result on #470.
- **Shapes of real pairs (Python, read-only; throwaway wrapper /tmp/s81/tools/shape.py around `plimit_probe.stair`,
  `BOUNDED=1 FASTSTRIP=1`, LIMB 1e5):** free-r pairs by (e_inf, f_inf): `3^16·5^11·19^8`: (1,1) 1544, (1,2) 585, (1,3) 12,
  (2,2) 1; `3^22·7^11·13^2`: (1,1) 22, (1,2) 4, (2,2) 2. So e_inf = 1 (no limit row in e) is ≈ 99.9 % / 93 %. (The bounded
  pairs, L2 < 2, go through `stair_bounded` and are not counted here.)
- **Lean, generic pair** (same checks; `ErdosResearch/SubsetSumPair.lean`, 16 s): `pairOK n S c g p q F fr ec e0 r1` for shape
  e_inf = 1: columns f < F (`stepRowOK` from e₀(f) + `stepPointOK` points below), corners (fr, 1) and (F, ec) (`stepAbOK` +
  `not_weird_of_upset`), box [F, fr) × [1, ec) point by point (`stepAbOK || stepPointOK`); **`not_weird_of_pairOK`**: ¬(n p^f q^e r).Weird
  for ALL f, e ≥ 1 and every prime r ∤ n p^f q^e. Instances: (37, 307) again from one Boolean (`not_weird_late_prefix_pairOK`), and
  (41, 167) (`not_weird_late_prefix_pairOK_41_167`: F = 1, corners (2,1), (1,2), deficient box point (1,1) with r₁ = 472739).
- **Failed (minor):** the first version used `nlinarith` (94 s, 80 s of it in nlinarith); replaced by `linarith` with explicit
  product hints (each inequality is linear once multiplied by q) ⇒ 38 s.
- **Not covered:** stars r^h (h ≥ 2); shape e_inf ≥ 2 (limit rows in e: same lemma with p, q swapped, the number then written
  n·q^e·p^f); bounded pairs (L2 < 2, `stair_bounded`: r bounded over the whole pair); a generator from `plimit_probe` to
  `pairOK` data; the loops over p and q (a sub-tree = all pairs below a 3-prime prefix).
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) A generator `scripts/pair_cert_gen.py` (from `plimit_probe.stair`'s
  data) emitting `pairOK` instances; time the kernel on all free-r pairs of one p of `3^16·5^11·19^8` (watch the 1-min/module rule; use
  ErdosResearchExtra). (3) Shape e_inf ≥ 2 by symmetry. (4) Bounded pairs in Lean (`stair_bounded`). (5) Stars. NEVER run owf in a session.

## Session 82 (2026-11-24, 23:00–~23:40 UTC): pair generator; whole q-ranges and q-tails per p in Lean (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` missing). Comment on card #175: the old
  gen-1 workers (parity bug) are still running (roots 24 and 25 DONE at 13:46 and 17:44; omega6.ck written at 22:59). That is not evidence.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **Generator `scripts/pair_cert_gen.py`** (Python, exact; no search, no owf): an exact port of the Lean Booleans `stepsOK`/`ppSum`/
  `stepsEnd`/`pointOK`/`rowOK`/`stepAbOK`/`pairOK` (r₀ = 2), plus a parameter search (F, f_r, e_c, e₀(f), r₁ minimal) and a Lean emitter.
  `SELFTEST=1` reproduces both hand-made session-81 instances (same r₁ = 7196/6686/7195). It is self-contained and does not import
  `plimit_probe` (whose `stair` data does not map 1-1 onto pairOK's parameters).
  First measurement: one `pairOK` theorem per pair costs **≈ 0.3 s of kernel** (62 pairs for p = 37 in ≈ 25 s).
- **Key observation:** almost all free-r pairs have the trivial shape (1, 1, 1) (the corner n p q is already abundant with an interval). Late
  prefix, p < 400, q < 5000: 1439 of 1460. So per p:
  - if `n p` is already abundant with an interval: one theorem covers EVERY q (`not_weird_of_stepAbOK_single`);
  - otherwise one **q-range** `[q₀, q₁]` (`rangeOK`: the step for p, then session 63's four end inequalities at n p, linear in q)
    covers all trivial pairs at once;
  - **q-tail** `not_weird_qtail`: σ(n)·p·(Q+1) ≤ 2n(p−1)(Q−1) ⇒ no n p^f q^e r with primes q, r ≥ Q is weird (all f, e). Proof:
    σ(n p^f)(p−1) ≤ σ(n) p^{f+1} (`ppSum_ratio`) and session 68's `not_weird_tail` at m = n p^f. This removes almost all
    bounded pairs;
  - p ≥ Q3 (three-prime tail, session 73 `not_weird_ptail`) needs nothing;
  - only the leftover pairs get a `pairOK`.
- **Counts (`RANGES=1`, DRY; free-r = L2 > 2):**

  | prefix | Q3 | n p abundant | ranges (pairs) | `pairOK` | e_inf ≥ 2 | q-tails (max Q) | bounded pairs left (q < Q) |
  |---|---|---|---|---|---|---|---|
  | late 3^3·11·13^10·17^2·23 | 100 | 29, 31 | 7 (122) | 21 | 0 | 14 (749) | 232 |
  | real 3^16·5^11·19^8 (c, g) = (12, 2) | 287 | 16 p (23..89) | 18 (1542) | 599 | 1 = (109, 797) | 37 (18429) | 2507 |

  Real prefix: 1542 + 599 + 1 = 2142 free-r pairs, the same as session 81's census. Without the q-tail there are ≈ 824k bounded pairs; with it, 2507.
  Kernel estimate for the free-r part of the real prefix: 599 × 0.3 s ≈ 3 min, plus the ranges and abundant p (seconds). This needs a Lean
  IntervalGap for 3^16·5^11·19^8, which does not exist yet.
- **Lean** (ErdosResearchExtra only; no sorry/native_decide; standard axioms; `lake build ErdosResearchExtra` OK 9079 jobs; default
  `lake build` OK 9066; check-lean-sources OK):
  - `ErdosResearch/SubsetSumPairRange.lean` (≈ 15 s): `rangeOK` + **`not_weird_of_rangeOK`** (all primes q ∈ [q₀, q₁], all f, e, m ≥ 1),
    `not_weird_of_stepAbOK_single`, `ppSum_ratio`, **`not_weird_qtail`**.
  - `ErdosResearch/SubsetSumPairGen.lean` (GENERATED, `RANGES=1 LEAN=late python3 -I scripts/pair_cert_gen.py 272154582410129991
    256030928920159929 2295 5 29 400 5000`, byte-identical on rerun; ≈ 35 s): below the late prefix, 2 `ab` + 14 `qtail` + 7 `range` +
    21 `pair` theorems. Together with `not_weird_ptail` (p ≥ 100), they cover every pair (p, q) with p < q primes > 23 of that sub-tree, with r to the
    first power, EXCEPT the 232 bounded pairs below their q-tails. The stars r^h (h ≥ 2) are also outside. There is no single combined
    theorem yet: it is 44 separate statements. Elementary; new only as a formalisation.
- **Failed (minor):** with no p cutoff the module took 68 s (67 q-tails for p ≥ Q3, which are useless), so the generator now stops at Q3.
  The first DRY run used the wrong n (typo): its numbers were discarded. `lake env lean` on a module whose dependency had changed
  gave "unknown identifier" (stale olean); `lake build` the dependency first.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit omega6-v2 files; 5 ⇒ alert). (2) Bounded pairs below the q-tail in Lean (`stair_bounded`:
  r bounded per pair; there are 232 / 2507 of them, so measure their kernel cost with a Lean `boundedOK` for one pair). (3) A combined
  theorem per prefix (all p, q at once: p-loop with `ab`/`range`/`qtail` + the pairOK leftovers). (4) A Lean IntervalGap for a real 3-prime
  prefix (3^16·5^11·19^8: base + raises as in session 58). (5) e_inf ≥ 2 by symmetry; stars. NEVER run owf in a session.

## Session 83 (2026-11-25, 00:23–~01:00 UTC): IntervalGap for real prefixes; quadrant lemma; ALL bounded pairs below the late prefix in Lean (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` not readable). Comment on card #175.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **IntervalGap for real prefixes** (session 82, item 4). New generator `scripts/prefix_ig_gen.py LIMB NAME 'prefix' ...`
  (multi_plan → bitset base + steps + raises, like `late_cert_gen.py` but it stops at the IntervalGap, without lastOK; byte-identical on rerun).
  Generated `ErdosResearch/OddWeirdPrefixIG.lean` (≈ 20 s): `intervalGap_real : IntervalGap (3^16·5^11·19^8) S 57 2` (base 855,
  raises 3, 5, 19; largest cofactor 204 divisors) and `intervalGap_r22 : IntervalGap (3^22·7^11·13^2) S 79 3` (base 819).
  The pair layer gives the same counts with c = 57 as with session 82's c = 12 (`pair_cert_gen.py … 57 2 23 287 5000`:
  16 abundant p, 18 ranges / 1542 pairs, 126 pairOK, 1539 bounded leftovers below q < 5000).
- **Quadrant lemma for bounded pairs** (session 82, item 2). For a bounded pair (σ(n) p q < 2n(p−1)(q−1)), the largest abundant r,
  R(f, e), is nondecreasing and bounded, so it is constant on a quadrant. `∑ D(n p^f q^e)` is symmetric (`ppSum_swap`), so session 81's
  `rowInv` propagates along f as well as e. Lean `ErdosResearch/SubsetSumQuad.lean` (≈ 23 s): `quadOK` (one Boolean at the corner
  (f₀, e₀), plus the 2-D limit with one r₁) + **`not_weird_of_quadOK`** (no n p^f q^e r is weird, for ALL f ≥ f₀, e ≥ e₀ and all primes
  r ≥ r₀); helpers `ppSum_mono`, `step2_mono`, `row_limit`, `ppSum_swap`. **`boundedOK` + `not_weird_of_boundedOK`**: a whole bounded
  pair from one Boolean (quadrant + rows f < f₀ via rowOK in q + columns e < e₀ via rowOK in p + finitely many points; tables
  `e0r`, `f0c`, `r1`). Instances `not_weird_late_prefix_53_151` (by hand) and `…_53_151'` (via boundedOK).
- **Generator `scripts/quad_probe.py`** (measurement + Lean emitter; `LEAN=late|real`, `NS=namespace`, slice `K0 K1`):
  - late prefix: **232/232 bounded pairs** certified (1527 cells); real prefix 3^16·5^11·19^8 with (c, g) = (57, 2): **2507/2507**
    (17052 cells, ≈ 6.8 per pair).
  - **Lean, all 232 bounded pairs below the late prefix:** `ErdosResearch/SubsetSumQuadGenA.lean` / `…GenB.lean` (116 theorems each,
    ≈ 45 s / 40 s; GENERATED, byte-identical on rerun). Each says that no `n·p^f·q^e·r` is weird, for all f, e ≥ 1 and every prime r.
  - Kernel cost measured on the real prefix (slice of 200 pairs, 2071 cells, in /tmp, NOT committed): 105 s including ≈ 17 s load, so
    ≈ 0.04 s/cell. All 2507 pairs ≈ 12 min, i.e. ≈ 12 modules: feasible, but too much to add to CI without a decision.
- **State of the late prefix's 3-prime sub-tree (last prime r to the first power):** every pair (p, q) of primes > 23, p < q, not dividing n,
  now has a Lean theorem: abundant p / q-ranges / q-tails / pairOK (`SubsetSumPairGen`, 44 theorems), bounded pairs (`SubsetSumQuadGenA/B`,
  232), p ≥ 100 (`not_weird_ptail`). The q-tails of this prefix are all < 749, far below the probe's QHI = 100000. These are still
  separate statements, not one combined theorem. Not covered: stars r^h (h ≥ 2).
- All Lean of this session: ErdosResearchExtra only; no sorry/native_decide; standard axioms; `lake build ErdosResearchExtra` OK
  (9083 jobs); default `lake build` OK (9066); check-lean-sources OK. Elementary; new only as formalisation.
- **Failed (minor):** stale olean again after changing SubsetSumQuad (`lake build` the dependency first); `rw [a, b] at h₁ h₂ …`
  fails if one hypothesis lacks the pattern (split the rewrites).
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit omega6-v2 files; 5 ⇒ alert). (2) One combined theorem for the late prefix's sub-tree
  (reflective: a p/q loop whose leaf is ab/range/qtail/pairOK/boundedOK, so that the 276 statements become one Boolean). (3) The real prefix:
  pairs + bounded pairs ≈ 12–15 min of kernel. Decide first whether CI can afford it (Extra), or cut cells. (4) Stars r^h. NEVER run owf.

## Session 84 (2026-11-25, 01:46–~02:20 UTC): the late prefix's whole 3-prime sub-tree as ONE theorem; stars at one point (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` not readable). Comment on card #175.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **Decision:** combine the 276 statements of sessions 82–83 by *dispatch*, not by reflection. A reflective Boolean would re-run
  every pairOK/boundedOK check in one kernel term (≈ 60–90 s more, against the "< ~1 min per module" rule). The dispatch reuses the
  existing theorems, and the kernel only checks a cheap window Boolean.
- Lean (ErdosResearchExtra only; no sorry/native_decide; standard axioms `propext, Classical.choice, Quot.sound`; 0 warnings;
  `lake build ErdosResearchExtra` OK 9085 jobs; default `lake build` OK 9066; check-lean-sources OK):
  - `ErdosResearch/SubsetSumWindow.lean` (hand-written, ≈ 18 s): `windowOK lo hi P L` (every odd x ∈ [lo, hi) is `skipS x P`
    or in `L`) and `mem_of_windowOK` (every prime q > 2 in the window is in L; no primality test in the kernel); helpers
    `not_dvd_mul_pow`, `not_dvd_mul`.
  - `ErdosResearch/SubsetSumLateTree.lean` (GENERATED by new `scripts/late_tree_gen.py`, byte-identical on rerun; ≈ 44 s):
    `late_p_P` for each prime 29 ≤ P < 100 (ab, or range + window of pair/bounded leaves + q-tail), and
    **`not_weird_late_subtree`**: for all primes 23 < p < q < r not dividing n = 3^3·23·13^10·17^2·11 and all f, e ≥ 1,
    **n·p^f·q^e·r is not weird** (p ≥ 100 via `not_weird_ptail` with Q = 100). The generator parses the theorem names/params of
    `SubsetSumPairGen` and `SubsetSumQuadGenA/B` and asserts in Python that every prime of each window has a leaf.
    `windowOK` checks the same thing in Lean (skip list 3..23 is enough because every window ends below 29² = 841).
  - So this is the first complete 3-prime sub-tree below a 5-prime prefix in Lean, with the last prime to the first power.
    **Not covered:** stars r^h (h ≥ 2), so this is not yet "the search's sub-tree" in full. Elementary; new only as formalisation.
- **Stars at one point (Lean, ErdosResearchExtra; ≈ 32 s, 0 warnings; standard axioms):** new
  `ErdosResearch/SubsetSumPointStar.lean`. `pointStarOK M S c g r₀ r₁ fuel` = session 79's `pointOK` plus the only star-only
  candidate r* = r₁ + 1 (even and > 2, or step conditions + `firstOK`: walk (T_h, N_h) = (∑D(M r^h), M r^h) to the first abundant
  h and check the certificate there). **`not_weird_mul_prime_pow_of_pointStarOK`**: ¬(M r^k).Weird for EVERY prime r ≥ r₀, r ∤ M, and
  EVERY k ≥ 1. Proof: r ≤ r₁ ⇒ certified at h = 1, then `cert_mono` (T_{h+1} = σ + r T_h, N_{h+1} = r N_h); r ≥ r₁ + 2 ⇒ invariant
  (r−1)T_h + σ ≤ (r−1)N_h (`not_abundant_of_far`) ⇒ never abundant; r = r₁ + 1 ⇒ `firstOK_sound`. Instance
  `not_weird_late_prefix_mul_prime_pow` (r* = 33, first abundant at h = 2, certified; fuel 4). Also `stepPointStarOK` +
  `not_weird_of_stepPointStarOK` (prefix steps, then `pointStarOK`), instance `not_weird_late_prefix_37_307_mul_prime_pow`
  (n·37·307·r^k, all primes r, all k ≥ 1; r* = 6687, h = 2). Python check of the late prefix with `plimit_probe.py STARS=1
  BOUNDED=1 FASTSTRIP=1` (p = 29..97): 0 failing p, 287 star point tests + 1117 star families. This is the star analogue of
  `pointOK`; rows/quadrants (`rowOK`, `quadOK`) do not have star versions yet, so the 276 pair leaves still cover r^1 only.
- **Failed (minor):** `mem_of_windowOK` with no range left `lo` as a metavariable, so omega failed (fixed by passing `lo`). `set_option … in`
  must come before the docstring.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit omega6-v2 files; 5 ⇒ alert). (2) Stars r^h for the late prefix: point level done
  (`pointStarOK`, `stepPointStarOK`). Next, star versions of `rowOK`/`quadOK`. Careful: there r₁ is only an UPPER bound shared by the whole
  row/quadrant, so r* = r₁ + 1 no longer holds. Each point has its own r*_e = ⌈σ_e/D_e⌉, which converges to r∞ = ⌈L⌉ (session 78's
  Python handles this with per-point tests until r* stabilises, then `check_r(r∞)`). Measure first in Python how many row points have
  r*_e ≠ r∞, then design the Lean row lemma, regenerate the leaves with star versions and reuse the same dispatch. (3) The real
  prefix 3^16·5^11·19^8: same pipeline (pair_cert_gen + quad_probe + late_tree_gen generalised to a prefix argument); ≈ 12–15 min
  of kernel ⇒ split into ≤ 1 min modules, or ask Pablo whether CI (Extra) can afford it. NEVER run owf.

## Session 85 (2026-11-25, 03:11–~03:45 UTC): stars on whole rows, quadrants, pairs and tails in Lean (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` not readable). Comment on card #175.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **Measured first (Python, new `scripts/star_row_probe.py`):** for every line of the late prefix's 276 leaves (755 rows/columns
  of pairOK/boundedOK leaves, 232 quadrants, 92 relevant deficient points), the star-only candidate r*_e = ⌈σ_e/D_e⌉ is already the
  limit r∞ = ⌈L⌉ at the line's start: **0 transient points**. r* is constant on each 8×8 quadrant box, and at all 232 quadrant corners r*
  equals ⌈L₂⌉ (so it is constant on the whole quadrant). Where r∞ is prime, the first abundant power is h = 2 at the start, and that corner is certified.
  **Why (explains session 84's worry):** `rowOK` gives session 79's `pointOK` at EVERY point of the row with the SAME r₁. `pointOK`
  forces r ≤ r₁ to be certified at h = 1 and r ≥ r₁ + 2 to be "far", so the only candidate on the whole row is R = r₁ + 1. It is not
  only an upper bound.
- **Lean (ErdosResearchExtra only; no sorry/native_decide; standard axioms; module ≈ 40 s, 0 warnings; `lake build
  ErdosResearchExtra` OK 9087 jobs; default `lake build` OK 9066; check-lean-sources OK):** new `ErdosResearch/SubsetSumRowStar.lean`:
  - `not_weird_pow_of_pointOK` (pointOK decides every M r^k except the candidate r = r₁ + 1, which is left to a hypothesis);
    `pointOK_of_rowOK`; `rowOK_of_quadOK`.
  - `rowStarOK` = rowOK && (R even ∨ R ∣ m ∨ skipS R L ∨ corner m·q^{e₀}·R² pseudoperfect (stepAbOK) ∨ R = q); **`not_weird_of_rowStarOK`**
    / `not_weird_of_stepRowStarOK`: ¬(m q^e r^k).Weird for every e ≥ e₀, every prime r ≥ r₀ with r ∤ m q^e, and **every k ≥ 1** (k ≥ 2 with prime R:
    `not_weird_of_upset` from the corner).
  - `quadStarOK` (the same candidate test on top of quadOK, corner n p^{f₀} q^{e₀} R²) + **`not_weird_of_quadStarOK`** (whole quadrant, every k).
  - Instances below the late prefix: rows n·37·349^e (R = 1879 prime, corner) and n·37·307^e (R = 7197 = 3·2399, skipS); quadrants
    (37, 449) (R = 2267 prime) and (37, 389) (R = 10325, skipS [5]).
  - `ROWSTAR=1 python3 -I scripts/star_row_probe.py`: the Booleans hold on ALL lines of the late prefix: rows 388 even, 242 skipS,
    29 R | m, 94 corners, 2 R = q; quadrants 115 even, 71 skipS, 9 R | n, 37 corners; 0 FAIL. Elementary; new only as formalisation.
- **Failed (minor):** `positivity` cannot use the local `0 < n` (use `Nat.mul_pos`); `hRq ▸` rewrote the wrong side (use `rw [hRq]`).
  The first ROWSTAR run showed 2 failures, where R equals the row's own prime q; fixed by adding the `R = q` branch.
- **Also this session (same rules; Extra OK 9089 jobs, default OK 9066, check-lean-sources OK, standard axioms, 0 warnings in new modules):**
  - `ErdosResearch/SubsetSumTailStar.lean` (≈ 32 s): `not_weird_tail_star` (σ(n)Q² ≤ 2n(Q−1)² ⇒ no n q^e r^k with primes q, r ≥ Q even
    abundant), `not_weird_qtail_star` (below p^f), `not_weird_ptail_star` (three primes ≥ Q, σ(n)Q³ ≤ 2n(Q−1)³). Proof: `ppSum_ratio` once
    per prime. Instances on the late prefix: q-tail p = 37 with Q = 750; p-tail Q = 101 (both checked by `norm_num`).
  - `ErdosResearch/SubsetSumPairStar.lean` (≈ 17 s): `pairStarOK`/**`not_weird_of_pairStarOK`** and `boundedStarOK`/**`not_weird_of_boundedStarOK`**
    (same lists as pairOK/boundedOK with stepRowStarOK, quadStarOK and session 84's stepPointStarOK). Instances (37, 307) and (53, 151) for
    every power r^k. Probe: session 84's `firstOK` point test also passes at the 215 deficient points whose odd candidate is composite
    (plus the 92 prime ones), so `stepPointStarOK` needs no skipS branch here.
- **Still missing for "stars below the late prefix" in Lean (updated):** only regenerating the generated modules (PairGen, QuadGenA/B,
  LateTree) with pairStarOK/boundedStarOK/star tails (windows end at the star tails: q-tails +≤ 1, p-tail 101), giving `not_weird_late_subtree_star`. Measured (throwaway /tmp script): moving the q-tails to the star values adds exactly ONE
  new pair, (89, 107) (107 ∈ [Q, Q*) = [107, 108)), which needs its own leaf; p-tail 100 → 101 adds nothing (100 is not prime).
  **Decision:** regeneration not started this session (3 emitters + late_tree_gen parser + 4 modules ≈ 3 min of build; too risky
  to leave half-done before the 04:46 cut-off).
- **Superseded by the line above (kept for the record):** (a) regenerate the 276 leaves with star Booleans: rows → `stepRowStarOK`,
  points → `stepPointStarOK` (session 84), quadrants → `quadStarOK`. The pairOK/boundedOK wrappers need star versions (`pairStarOK`, `boundedStarOK`:
  the same lists, with the star Booleans). (b) Star tails: the q-tail and the 3-prime p-tail use (Q+1)/Q for r; for r^h the factor is Q/(Q−1).
  Python: q-tails shift by ≤ 1 (e.g. p = 37: Q 749 → 750), the p-tail Q3 100 → 101. So new lemmas `not_weird_qtail_star`/`not_weird_ptail_star` (ratio
  σ/N < ρ·(Q/(Q−1))²) and the windows end one higher. (c) rangeOK and abundant corners already allow any cofactor m (stars included).
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit omega6-v2 files; 5 ⇒ alert). (2) (pairStarOK/boundedStarOK and star tails are DONE, see above)
  regenerate SubsetSumPairGen/QuadGenA/B/LateTree with star versions (check kernel time stays < ~1 min per module), giving
  `not_weird_late_subtree_star` (all k). (3) Then the real prefix 3^16·5^11·19^8 (≈ 12–15 min of kernel ⇒ split modules or ask Pablo).
  NEVER run owf. Do not commit `.lake`.

## Session 86 (2026-11-25, 04:34–~05:00 UTC): the late prefix's whole 3-prime sub-tree with stars, as ONE Lean theorem (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` not readable). Comment on card #175.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **Done (Lean, ErdosResearchExtra only; no sorry/native_decide; axioms propext/Classical.choice/Quot.sound; 0 warnings in the
  new/changed modules; `lake build ErdosResearchExtra` OK 9093 jobs; default `lake build` OK 9066; check-lean-sources OK):**
  - New `scripts/late_star_gen.py` (`pair` / `quadA` / `quadB`; byte-identical on rerun): rewrites every generated leaf of
    sessions 82–83 into its star version, with the **same certificate parameters**, `pairOK` → `pairStarOK`, `boundedOK` →
    `boundedStarOK`, skip list `LSKIP` = odd primes < 260 (every odd composite candidate < 263² is skipped) and `fuel := 12`.
    Star q-tails: least Q with (S+n)·p·Q² ≤ 2n(p−1)(Q−1)² (`not_weird_qtail_star`); only p = 89 moves (107 → 108), and its new
    bounded pair **(89, 107)** gets a leaf from `quad_probe.pair` (same pipeline).
    Generated: `ErdosResearch/SubsetSumPairGenStar.lean` (21 pairs + 14 star q-tails + (89, 107), 30 s),
    `SubsetSumQuadGenAStar.lean` (116 bounded pairs, 48 s), `SubsetSumQuadGenBStar.lean` (116, 43 s).
  - `scripts/late_tree_gen.py` gains `STAR=1` (the default output is still byte-identical to `SubsetSumLateTree.lean`):
    generated `ErdosResearch/SubsetSumLateTreeStar.lean` (44 s) with **`not_weird_late_subtree_star`**: for all primes
    23 < p < q < r not dividing n = lateN = 3^3·23·13^10·17^2·11 and all **f, e, k ≥ 1**, n·p^f·q^e·r^k is not weird. It dispatches
    to the star leaves, the abundant/range theorems of `SubsetSumPairGen` (any cofactor, reused as they are), the star q-tails
    and `not_weird_ptail_star` (Q = 101). So session 84's gap ("stars r^h, h ≥ 2, not covered") is closed for this prefix.
  - **Fix in `SubsetSumRowStar.quadStarOK`:** new branch `R = q ∧ 1 ≤ e₀` (as in `rowStarOK`; then R ∣ n·p^f·q^e, so R cannot be
    the last prime). It was needed exactly by the new pair (89, 107): its quadrant candidate is R = r₁ + 1 = 107 = q. The two
    session-85 quadrant instances still hold (an earlier branch fires).
  - Elementary; new only as a formalisation. Still only ONE (late, not real) 3-prime prefix.
- **Failed (minor):** first kernel run of `SubsetSumPairGenStar` failed only on (89, 107) (the missing R = q branch above);
  an indentation slip in the `late_tree_gen.py` edit (caught before generating).
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit omega6-v2 files; 5 ⇒ alert). (2) The real prefix 3^16·5^11·19^8 with the same
  pipeline (pair layer + bounded pairs + star rewrite + tree), generalising `late_tree_gen.py`/`late_star_gen.py` from
  the hard-coded late prefix to a PREFIXES table (as `quad_probe.py` already has). Session 83 estimated ≈ 12–15 min of kernel for the
  bounded pairs alone: split into modules of < ~1 min each and measure the total before committing; if it exceeds what the
  CI can absorb, ask Pablo (card) before adding it to ErdosResearchExtra. NEVER run owf. Do not commit `.lake`.

## Session 87 (2026-11-25, 05:45–~06:15 UTC): Lean kernel-cost census of real prefixes; `pairOK2` (shape e_inf ≥ 2) (no owf run)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` not readable). Comment on card #175.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **Decision:** instead of generating the real prefix 3^16·5^11·19^8 (≈ 12–15 min of kernel, needs Pablo's OK for CI), first
  measure what the Lean pipeline would cost on MANY real prefixes, i.e. whether a Lean replay of ω = 6 is feasible at all.
- **New `scripts/lean_cost_census.py CKFILE E SAMPLE SEED LIMB`** (Python; read-only on a /tmp COPY of the gen-1 checkpoint, which is
  used only for prefix SHAPES because it comes from the buggy code): per sampled exact deficient 3-prime prefix, (c, g) from multi_plan,
  pair layer (`pair_cert_gen.py RANGES=1`), bounded pairs (`quad_probe.py`), cost model 0.3 s/pairOK + 0.04 s/bounded cell
  (sessions 82–83). Output: `notes/data/lean-cost-census-s87.txt` (30 prefixes, roots 3^16/3^20/3^22, seed 3).
  - Census fix: for p with `n p` deficient but `n p^f` eventually abundant (q-tail None), the q's to scan stop at
    max_{f<F} Q_f (F = first f with `stepAbOK`; q ≥ Q_f is `not_weird_tail` on `n p^f`), not at QHI. Before the fix,
    3^16·7^7·13^6 looked like 78k pairOK; after it, 3^20·7^12·13 needs QH = 883 and 83 pairOK. No prefix had an uncertified gap.
  - **Result:** every sampled prefix is closable by the existing pieces plus `pairOK2` (no failures). Kernel estimate per prefix
    is 2 s to 4630 s, mean ≈ 930 s. The heavy ones are 5^b·17^h prefixes ((c, g) = (283, 6), ≈ 14k bounded pairs, ≈ 90k cells) and
    5^b·19^h (≈ 2.5k bounded pairs). Roots have 1846 / 2146 / 2186 exact deficient 3-prime prefixes (E = 16 / 20 / 22).
    ⇒ ≈ 500 kernel-hours per root, ≈ 2·10^4 h for ~40 roots. **A Lean replay of ω = 6 with this design is infeasible by
    3–4 orders of magnitude.** Bounded pairs dominate (≈ 85 % of the estimate). Per-theorem overhead is not the issue: 0.04 s/cell is
    the GMP check itself. A gain would need mathematical aggregation over q (closed-form q-ranges of bounded pairs, like
    `lastOKR` did for lastOK), not engineering.
- **Shape e_inf ≥ 2** (the row e = 1 is limit-deficient in p): appears in 25 of the 30 prefixes, with 1–7 pairs each, and `pairOK` cannot take it.
  - New Lean `ErdosResearch/SubsetSumPair2.lean` (ErdosResearchExtra only; no sorry/native_decide; axioms propext/Classical.choice/
    Quot.sound; 36 s): `pairOK2` (start row `er`; rows e < er = limit rows in p via `stepRowOK` with p and q swapped; corner
    (fr, er); box [F, fr) × [er, ec)) and **`not_weird_of_pairOK2`** (all f, e ≥ 1, every prime r). With er = 1 it is `pairOK`.
  - Instance **`not_weird_real_prefix_109_797`**: the only non-bounded pair of the real prefix 3^16·5^11·19^8 that `pairOK` could not
    take (er = 2, f₀ = 6). So that prefix's whole pair layer is now coverable.
  - `scripts/pair2_probe.py` (Python twin + finder `find2`): on 6 prefixes (the real one, 3^20·5^20·17^4 with 7 such pairs, …), every
    old pairOK pair still passes with er = 1, and all 15 e_inf ≥ 2 pairs pass with er = 2.
  - `lake build ErdosResearchExtra` OK (9094 jobs); check-lean-sources OK. The default build is unchanged (it does not import the module).
    Elementary; new only as a formalisation.
- **Failed:** nothing in Lean (compiled first try). The census overcount described above was fixed.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit omega6-v2 files; 5 ⇒ alert). (2) Strategic: Lean can certify single real
  sub-trees, but not the whole ω = 6 search. If v2 closes, ω = 6 is computational evidence (validated C/Python), not a Lean theorem,
  unless a q-aggregation for bounded pairs cuts the cost ≥ 1000×. Measure in Python first: per p, do consecutive bounded q share
  (f₀, e₀) and a monotone r₁ formula, so that a q-range lemma covers them? First data (real prefix 3^16·5^11·19^8, per p: bounded q, quadrant corner (f₀, e₀), rows, cols): p = 97: 968 bounded q, 719 with shape (4, 2, 3 rows, 1 col) and 215 with (5, 2, 4, 1), interleaved near the q-tail; p = 101: 239 q, (3, 2) 128 + (4, 2) 100; p = 199: 26/27 q are (2, 2). So shapes are nearly constant over long q-runs, but r₁ varies with q. A q-range lemma would need its conditions to be monotone in q, so that only the endpoints are checked (as `pointOK` is in r); that is not checked yet. (3) Otherwise, consider the shortlist of other problems
  (docs/candidatos-siguiente-problema.md; still waiting for Pablo). NEVER run owf. Do not commit `.lake`.

## Session 88 (2026-11-25, 06:57–~07:30 UTC): lifting census: prefix exponents aggregate only 13–24× (no owf run, no Lean)

- **Read:** `sh scripts/owf-queue.sh read` → exit 8 again (`/lean/state/owf/v2/omega6.ck` not readable). Comment on card #175.
  No owf run, no data changes. Palomar: done since session 18, unchanged.
- **Question:** session 87 found that a Lean replay of ω = 6 costs ≈ 1.4·10^4 kernel-hours. Is there an aggregation that saves
  ≥ 1000×? Session 87's census already hinted at one: prefixes with the same primes but different exponents have almost the
  same pair layer (every 3^a·5^b·17^h has 14131–14135 bounded pairs). So, before q-aggregation, I measured aggregation over the
  **prefix exponents** ("lifting": one certificate for all exponents above thresholds, valid for every ratio ρ = σ(n)/n in
  [ρ₀, L), L = ∏ p/(p−1)).
- **New `scripts/lift_census.py CKFILE triples | flips CAP NS SEED | families TH…`** (Python; read-only on a /tmp COPY of the
  gen-1 checkpoint, prefix SHAPES only; never runs owf). Output: `notes/data/lift-census-s88.txt`.
  - **triples:** the 51339 exact deficient 3-prime prefixes of roots 3^1..3^28 use only **20 prime triples** (19 per root from
    3^6 on). (3,5,17) has 9530 and (3,5,19) has 7225. Three triples have L > 2, namely (3,5,7), (3,5,11) and (3,5,13): there n is
    eventually abundant, so they have finitely many deficient prefixes (1519 in total).
  - **flips** (pair categories pab / bounded / free / q-tail for q < 3000, at ρ versus at L): once the relative gap (L−ρ)/L < 10^-6, the
    category map equals the limit one (115/117 sampled prefixes with 0 flips, max 1). At gaps of 10^-3 to 10^-2 the median is 11
    flips; at 10^-2 to 10^-1 it is 1122. So the pair layer does stabilise in the exponents. Caveat: only q < 3000 was checked, and
    pairs near the q-tail can flip at any gap (the tail moves with ρ).
  - **families** (exponent e of p FREE iff p^(e+1) ≥ TH, otherwise fixed): 51339 prefixes give 4078 families (TH 10^6), 6681 (10^7)
    and 9500 (10^8). Only 10–14 families are all-free. Most prefixes have one small exponent somewhere (e.g. 19^1, 47^2), so the
    gap stays ≥ 10^-6 and the family keeps that exponent fixed.
  - **Kernel estimate** (session-87 cost per prefix by triple, charged ONCE per family, which is optimistic: a uniform
    certificate must hold on a whole ρ-interval and is likely to cost more than one prefix): 14344 h → **592 h (TH 10^6, 24×)**,
    1074 h (10^7, 13×), 1613 h (10^8, 9×).
- **Conclusion (decision):** lifting gives 1–1.5 orders of magnitude, not 3. Session 87's q-runs (two shapes over ~1000 q for
  p = 97) suggest at most about another order from q-aggregation. Even combined, that leaves ≥ 50–100 kernel-hours plus new
  ρ-interval lemmas that do not exist yet. **I stop developing the Lean replay of the full ω = 6 search.** If the v2 workers close
  ω = 6, the result is computational evidence (validated C/Python), and the Lean modules certify only sample sub-trees. That
  is honest and enough for a "partial result" note, which would in any case only reproduce Liddy–Riedl's ω ≥ 6 → ω ≥ 7 as
  evidence. Nothing here is a new theorem.
- **Failed:** the first probe (bounded-pair r₁ at L vs at the prefix) was too slow (trial division up to q-tails ≈ 10^7 at L)
  and compared the wrong direction (bounded at L ⇒ bounded at ρ, not the converse). It was replaced by the category map with a sieve.
- **Next:** (1) `read` (exit 8 ⇒ #175; 0 ⇒ commit the omega6-v2 files; 5 ⇒ alert). (2) #470 Lean work is parked: only maintenance and
  the paper task if v2 closes. (3) The research value now lies in another problem: `docs/candidatos-siguiente-problema.md` is still
  waiting for Pablo's choice. Do not start a candidate without it. NEVER run owf. Do not commit `.lake`.

## Session 89 (2026-11-25, 08:14–~08:20 UTC): upkeep only (no owf run, no Lean, no data changes)

- `sh scripts/owf-queue.sh read` → exit 8 again (/lean/state/owf/v2/omega6.ck missing). Comment on card #175.
- Board: #175 (v2 deploy) and #192 (choice of the next problem) still unanswered. Per session 88's decision, #470 Lean work stays
  parked and no shortlist candidate is started without Pablo's choice, so this session adds no research.
- main `7a601f854f…`: "Lean" and "Palomar preflight" both green (GitHub API). Palomar package unchanged since session 18.
- **Next:** unchanged from session 88.

## Session 90 (2026-11-25, 09:11–~09:20 UTC): upkeep only (no owf run, no Lean, no data changes)

- `sh scripts/owf-queue.sh read` → exit 8 again (/lean/state/owf/v2/omega6.ck missing). Comment on card #175.
- Board: #175 (v2 deploy) and #192 (choice of the next problem) still unanswered, so per session 88 nothing new is started.
- main `26f5ce3f4842e2a254e8027a9e8a9fe6c822d3ad`: "Lean" and "Palomar preflight" both green (GitHub API). Palomar package
  unchanged since session 18.
- **Next:** unchanged from session 88.

## Session 91 (2026-11-25, 10:08–~10:15 UTC): upkeep only (no owf run, no Lean, no data changes)

- `sh scripts/owf-queue.sh read` → exit 8 again (/lean/state/owf/v2/omega6.ck missing). Comment on card #175.
- Board: #175 (v2 deploy) and #192 (choice of the next problem) still unanswered, so per session 88 nothing new is started.
- main `b70ebf3a68649ba2cfd30db3fb6b3dcf13b7abcb`: "Lean" and "Palomar preflight" both green (GitHub API). Palomar package
  unchanged since session 18.
- **Next:** unchanged from session 88.

## Session 92 (2026-11-25, 20:14–~20:40 UTC): v2 workers running; next work chosen (Mathlib upstream)

- `sh scripts/owf-queue.sh read` → **exit 0** (the v2 workers are deployed). Generation-2 roots **3^1…3^8 DONE**, nfail 0
  (root 8: 142.8M nodes, 12:57→19:34 for roots 1–8 on 2 workers). owf-0 is on 3^10, owf-1 on 3^9. No FOUND/CLOSED/ERROR.
  Files `notes/data/omega6-v2.ck.gz` (22284 lines, 433 KB, gzip OK, 0 dups) and `omega6-v2-roots.txt` are new and must be in the PR.
  Card #175 closed. **Size:** the single .gz was going to exceed `read`'s 900 KB cap within about a day, so `read`
  now writes fixed parts of 40000 lines (`omega6-v2.ck.gz`, `omega6-v2-2.ck.gz`, …; frozen once full). Tested on a fake volume:
  split into 3 parts at 10000 lines, the concatenation equals the volume, a rerun is idempotent (byte-identical), an append
  rewrites only the last parts, and a tampered frozen part makes it exit 4. A real `read` afterwards gave exit 0 (22369 lines, 1 part).
- Pace: the v2 root costs grow (≈ 2.5 h of worker time for root 8), and the loop closes at E ≥ 42 (root-loop-3.md),
  so expect several days to weeks. Nothing to do in sessions but `read`.
- Next work (card #192 closed, decided by me as the task asked): **Mathlib upstream** of the general lemmas, see
  `notes/mathlib-upstream.md` and `ErdosResearch/Upstream.lean`. Card #197 asks Pablo to approve a Mathlib PR.

## Session 93 (2026-11-25, 23:00 UTC): read only (no owf run)

- `sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. Gen-2 roots **3^1…3^9 DONE** (root 9 at 20:33, 101.9M nodes,
  nfail 0). owf-0 on 3^10 (86.2M nodes, at (5,24),(17,11)), owf-1 on 3^11 (71.2M nodes, at (5,19),(19,10)).
  `omega6-v2.ck.gz` 22369 → 25502 lines (500 KB, part 1 of ≤ 40000 lines), `omega6-v2-roots.txt` + root 9.
- Session work went to the Mathlib upstream (see notes/mathlib-upstream.md, session 93).

## Session 94 (2026-11-26, 00:00–~00:20 UTC): read only for #470

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. Gen-2 roots 3^1…3^9 DONE (nfail 0); owf-0 on 3^10
(log at (5,27),(17,9)), owf-1 on 3^11 (log at (5,23),(17,8)). `notes/data/omega6-v2.ck.gz` 25502 → 26046 lines (515 KB,
part 1). No #470 Lean changes. The session's work went to the second Mathlib patch (notes/mathlib-upstream.md, session 94).

## Session 95 (2026-11-26, 01:06–~01:15 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. Gen-2 roots 3^1…3^9 DONE (nfail 0); owf-0 on 3^10
(111.0M nodes, log at (5,29),(19,11)), owf-1 on 3^11 (98.8M nodes, log at (5,26),(17,5)). `notes/data/omega6-v2.ck.gz`
26046 → 26482 lines (528 KB, part 1). Roots file unchanged. Card #197 (Mathlib PR) still unanswered, so nothing new
started: both Mathlib patches are ready and #470 Lean stays parked.

## Session 96 (2026-11-26, 12:32–~12:40 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. **Gen-2 roots 3^1…3^13 DONE** (nfail 0; 3^10 02:03, 3^11 04:22,
3^12 08:23, 3^13 11:20 UTC). owf-0 on 3^14 (82.0M nodes, log at (5,21),(17,5)), owf-1 on 3^15 (39.6M nodes, log at (5,11),(17,16)).
`notes/data/omega6-v2.ck.gz` 26482 → 37016 lines (764 KB, still part 1; part 2 starts automatically at 40000 lines, ≈ 825 KB).
Pace: ≈ 1.2·10^8 nodes and ≈ 3–5 h per root per worker; with the closing exponent ≥ 42 (session 70) that is ≥ 29 roots left,
i.e. roughly ≥ 2–3 days of the 2 workers, probably more as roots grow. Card #197 (Mathlib PR) still unanswered: nothing new started.

## Session 97 (2026-11-26, 13:27–~13:35 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. No new root since session 96 (3^1…3^13 DONE, nfail 0).
owf-0 on 3^14 (91.0M nodes, log at (5,23),(17,4)), owf-1 on 3^15 (55.0M nodes, log at (5,15),(17,3)).
`notes/data/omega6-v2.ck.gz` 37016 → 37472 lines (775 KB, part 1). Roots file unchanged. Card #197 (Mathlib PR) still
unanswered: nothing new started (Mathlib patches ready; #470 Lean replay parked since session 88).

## Session 98 (2026-11-26, 14:24–~14:30 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. No new root since session 96 (3^1…3^13 DONE, nfail 0).
owf-0 on 3^14 (99.0M nodes, log at (5,24),(17,12)), owf-1 on 3^15 (67.0M nodes, log at (5,17),(17,11)).
`notes/data/omega6-v2.ck.gz` 37472 → 37723 lines (782 KB, part 1). Roots file unchanged. Card #197 (Mathlib PR) still
unanswered: nothing new started (Mathlib patches ready and re-checked, see notes/mathlib-upstream.md session 98).

## Session 99 (2026-11-26, 15:21–~15:30 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. No new root since session 96 (3^1…3^13 DONE, nfail 0).
owf-0 on 3^14 (107.8M nodes, log at (5,26),(17,8)), owf-1 on 3^15 (77.2M nodes, log at (5,19),(17,11)).
`notes/data/omega6-v2.ck.gz` 37723 → 38036 lines (790 KB, part 1; gzip -t OK, 0 dups, old file exact prefix). Roots file
unchanged. Card #197 (Mathlib PR) still unanswered: nothing new started (Mathlib patches ready; #470 Lean replay parked).

## Session 100 (2026-11-26, 16:17–~16:25 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. No new root since session 96 (3^1…3^13 DONE, nfail 0).
owf-0 on 3^14 (115.2M nodes, log at (5,27),(19,7)), owf-1 on 3^15 (86.2M nodes, log at (5,21),(17,7)).
`notes/data/omega6-v2.ck.gz` 38036 → 38284 lines (797 KB, part 1; gzip -t OK, 0 dups, old file exact prefix). Roots file
unchanged. Card #197 (Mathlib PR) still unanswered: nothing new started (Mathlib patches ready; #470 Lean replay parked).

## Session 101 (2026-11-26, 17:14–~17:20 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. No new root since session 96 (3^1…3^13 DONE, nfail 0).
owf-0 on 3^14 (123.6M nodes, log at (5,29),(17,8)), owf-1 on 3^15 (93.8M nodes, log at (5,22),(17,15)).
`notes/data/omega6-v2.ck.gz` 38284 → 38515 lines (804 KB, part 1; gzip -t OK, 0 dups, old file exact prefix). Roots file
unchanged. Card #197 (Mathlib PR) still unanswered: nothing new started (Mathlib patches ready; #470 Lean replay parked).

## Session 102 (2026-11-26, 18:12–~18:20 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. **Root 3^14 DONE** (17:47:55 UTC, 127.9M nodes, nfail 0) ⇒
gen-2 roots 3^1…3^14 done. owf-0 now on 3^16 (23.4M nodes, log at (5,8),(17,7)), owf-1 on 3^15 (103.0M nodes, log at (5,24),(17,12)).
`notes/data/omega6-v2.ck.gz` 38515 → 40000 lines (835 KB; gzip -t OK, 0 dups, old file exact prefix): **part 1 is now full and
frozen**; the next `read` starts `omega6-v2-2.ck.gz` automatically. Roots file + root 14. Card #197 (Mathlib PR) still unanswered:
nothing new started (Mathlib patches ready; #470 Lean replay parked since session 88).

## Session 103 (2026-11-26, 19:09–~19:15 UTC): read only (no owf run, no Lean)

`sh scripts/owf-queue.sh read` → exit 0, no FOUND/CLOSED/ERROR. No new root since session 102 (3^1…3^14 DONE, nfail 0).
owf-0 on 3^16 (42.8M nodes, log at (5,12),(17,14)), owf-1 on 3^15 (109.6M nodes, log at (5,25),(17,16)).
Part 1 `notes/data/omega6-v2.ck.gz` frozen at 40000 lines (byte-identical to HEAD); **new part 2 `notes/data/omega6-v2-2.ck.gz`**
(396 lines, 10 KB; gzip -t OK, 0 duplicates across both parts). Roots file unchanged. Card #197 (Mathlib PR) still unanswered:
nothing new started (Mathlib patches ready; #470 Lean replay parked since session 88).
