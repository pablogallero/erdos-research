# Erdős #470: odd weird numbers ($10)

Statement (erdosproblems.com/470, checked 2026-11-08): `n` is *weird* if `σ(n) ≥ 2n` and `n` is not
pseudoperfect. (i) Are there odd weird numbers? (ii) Are there infinitely many primitive weird
numbers? The $10 is for (i) (Guy B2). Lean: `FormalConjectures/ErdosProblems/470.lean` uses
Mathlib's `Nat.Weird` (abundant ∧ ¬ pseudoperfect). Both parts are still `sorry` there, as are the
variants `odd_weird_10_pow_21` (Fang) and the Liddy–Riedl variant.

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
