# #470, ω = 6: does the loop over the exponent of 3 close, and when? (2026-11-23)

Task from Pablo (mail "Erdos", 2026-11-23): (1) profile why `ROOTTEST=50` got stuck at 5^24; (2) a mathematical bound
on the power of 3, or a way to handle "3^≥E" at once; (3) with numbers, the E where the loop closes, or why it does not.
Constraint: the `owf` workers are not touched, and no long runs (one core, `nice 19`, short `timeout`). Everything below
was run on one core, niced, for at most a few minutes each, with the binary and data in `/tmp` (never `/lean/state/owf`).

## 0. Summary

1. **There is a soundness bug in the search (Python and C), and it changes the answer.** In `family`, the star loop
   starts at `q = max(q0, qtop+1)` and steps by 2. When `qtop` is odd, it visits only even numbers, so it tests no
   prime in the window and returns True. Reproducer: `python3 -I scripts/star_parity_repro.py`. It shows a family
   that returns True with 0 star tests, although it contains the abundant number 3^24·5^12·17^6·257^4·65521, which no
   test covers. Fix (one line each, prototype only, NOT applied to the repo scripts): after computing that start,
   add 1 if it is even.
   - With the fix, ω = 4 and ω = 5 are still True (nodes 911 → 1996 and 447944 → 706995; nfail 0), so the
     published conclusions for ω ≤ 5 stand (ω ≤ 4 is also in Lean, which does not use this code).
   - **The ω = 6 checkpoint (roots v_3 ≤ 21 "done") was produced by the buggy code**, so it is not evidence until it
     is re-run or re-checked with the fix. The workers are still running the buggy binary. That is Pablo's decision
     (board card), and it was not touched here.
2. **A bound on the power of 3, and the closing exponent.** For m coprime to 6, 3^a·m is abundant iff
   3^a·(3σ(m) − 4m) ≥ σ(m). So it is deficient for every a if σ(m)/m < 4/3, and otherwise it becomes abundant exactly
   from a = E0(m) = ⌈log_3(σ(m)/(3σ(m) − 4m))⌉. The region test "3^≥E" (ROOTTEST=E) is **necessarily False for every
   E < E0(m)** for any m with ω(m) = K − 1 (proof in §2). The loop therefore cannot close before E* = max E0(m).
   - **Calibration (ω = 5):** the worst m comes from the Fermat primes, m = 5^12·17^6·257^4·65521, with E0 = 24. With
     the fixed binary, ROOTTEST is False for E = 22, 23 and True for E = 24, 25, 26 (≈ 30k nodes). The closing exponent
     is exactly E* = 24. The buggy binary said 23.
   - **ω = 6:** the same Fermat family gives m = 5^24·17^18·257^7·65537^3·4294967231 (and others) with **E0 = 42**.
     So the loop runs at least over 3^1 … 3^41 and cannot close before E = 42 (rigorous for the fixed algorithm).
     By the ω = 5 calibration, the expected closing exponent is **E* ≈ 42**. It could be a bit higher if another
     family of m is worse; I only scanned the Fermat family exhaustively (q within 3·10^6 of 2^32, exponents ≤ 70).
   - **Whether it closes at all:** E* is finite unless there is an exact "limit configuration": at most 4 primes ≥ 5,
     with exponents in {1, 2, …} ∪ {∞} (at least one ∞), and value exactly ∏ = 4/3 (§3). Exhaustive search within caps
     (`scripts/three_limit_configs.py`: first 3 primes ≤ 3000, finite exponents ≤ 6, last prime solved exactly with no
     cap) found **none**. The closest is the Fermat product 5·17·257 (·65537), at a relative distance 2^-16 (2^-32).
     This is evidence, not a proof.
3. **Why ROOTTEST=50 got stuck at 5^24.** Inside the region 3^≥50, the loop over the exponent of 5 can only close when
   every near-tie of the type 3^50·5^b·17^c·257^d·65537^f·q is already decided at the exact exponent b. The same
   computation (`FREE=5`) gives **b ≥ 27**: the 5-loop must reach 5^27. Inside 5^24, the loop over 17 must reach
   **17^16** (`FREE=17`, worst m = 5^24·257^7·65537^3·4294967231). The checkpoint has 17^c done for c ≤ 15 at 5^24,
   so it stopped exactly at the first hard exponent. The cost per node also explodes there: 74.9 % of the time is
   `divisors256` (gprof), because the prefix 3^50·5^24·17^c has 51·25·(c+1) ≈ 20k divisors, and every family sorts
   them again. A second effect: False subtrees are never written to the checkpoint, so each resume repeats the
   failing region subtrees 17^≥1 … 17^≥15 before getting back to new work. Hence "1 new key per session".

## 1. Profiling (§1 of the task)

Tools: `scripts/roottest_branch_profile.py` (sampling profile from the `progress` lines: one sample per 200k nodes,
so the share of samples is the share of nodes per branch) and gprof (`gcc -O2 -pg`; `NODELIMIT` makes it exit
cleanly). All on one core with `nice -n 19`, binary in `/tmp`, checkpoint copied to `/tmp`.

- **Workers' logs (read-only, no CPU):** root 3^22 (78.6M nodes sampled): 85 % of nodes are below 3·5·17, and 43 %
  below 3·5·17·257. Each 5^b costs ≈ 4M nodes whatever b is (the tree shape does not depend on b), but the node rate
  drops from ≈ 33k/s (5^1) to ≈ 2.3k/s (5^23), because the numbers grow (u128 → 256-bit → mpz) and so do the divisor lists.
- **ROOTTEST=50 resumed from `roottest50.ck` (1710 keys), 200k nodes, gprof:** `divisors256` 74.9 %, `search1`
  (self) 22.8 %, the rest < 2 %. 'fam' 23890, 'qchk' 5742, 'star' 6181, nfail 0.
- **The same resume, 8 min (`timeout 480`):** progress `200000 … 27 s [(3,50),(5,24),(17,4),(257,1),(15937,1)]`,
  then `400000 … 214 s [(3,50),(5,24),(17,15),(257,2),(89989,1)]`, and **0 new checkpoint keys** in total
  (≈ 0.6M nodes over both runs). The exact subtrees 17^c (c ≤ 15) are skipped from the checkpoint, but the region
  subtrees 17^≥c are False (their closing exponent is 16), so they are never recorded and get re-explored on every resume.
  The run spends its whole budget redoing them before reaching 17^16. That is the "stall". The cost per node is
  dominated by `divisors256` (previous item): ≈ 200k nodes took 187 s at 17^4…17^15, against ≈ 30k nodes/s at small exponents.

Which branches explode, and why: the Fermat primes. (3/2)·(5/4)·(17/16)·(257/256)·(65537/65536) = 2(1 − 2^-32), so
with these primes the bound used by the pruning is just below 2, and nothing can be pruned by the bound. The search
has to raise the exponents of 5, 17 and 257 until the exact ratio decides each near-tie (§3 gives the exponents). That
is the same reason why §2's worst m are all of the form 5^b·17^c·257^d·65537^f·q with q just below 2^32.

## 2. The bound on the power of 3 and why the region test fails below E0

σ(3^E)/3^E = (3^{E+1} − 1)/(2·3^E) = 3/2 − 1/(2·3^E) < 3/2. Write ρ(m) = σ(m)/m and Δ(m) = 3σ(m) − 4m (an integer;
Δ ≠ 0 because 3 ∤ m). Then σ(3^a m) ≥ 2·3^a m ⇔ (3^{a+1} − 1)σ(m) ≥ 4·3^a m ⇔ 3^a·Δ(m) ≥ σ(m).
- If Δ(m) < 0 (ρ(m) < 4/3), 3^a·m is deficient for all a: these m are handled by the bound 3/2 for any E.
- If Δ(m) > 0, 3^a·m is deficient for a < E0(m) and abundant for a ≥ E0(m), where E0(m) = ⌈log_3(σ(m)/Δ(m))⌉.
  In terms of G = 3ρ(m)/4 − 1: E0 = ⌈log_3((1 + G)/(3G))⌉ ≈ log_3(1/G) − 1.

**Claim:** for m with ω(m) = K − 1 and Δ(m) > 0, ROOTTEST=E (region 3^≥E) is False for every E < E0(m) (fixed
algorithm). Reason: n = 3^{E0}·m is abundant and lies in the region. The region search can only certify n by (a) a
bound < 2, impossible because the bound is ≥ σ(n)/n ≥ 2; or (b) a pseudoperfect, abundant tested number dividing n.
Every tested number has 3-part exactly 3^E, so it divides 3^E·m, which is deficient. So the family that contains n
returns False (the star loop reaches the prime of n, the exact number is not abundant and the region bound is ≥ 2).
(The parity bug breaks exactly this step: with it, some of those families return True.)

So **E* = sup_m E0(m)** is a lower bound for the closing exponent. It is also the closing exponent as long as every
abundant 3^E·m is pseudoperfect (which the search tests), and for ω = 5 it is exact (24, measured).

### Numbers (`scripts/three_e0_fermat.py`, exact integer verification of each m)

| case | worst m found | closing exponent |
|---|---|---|
| ω = 5, loop over 3 (`KF=3`) | 5^12·17^6·257^4·65521 | **3^24** (fixed ROOTTEST: False at 23, True at 24) |
| ω = 6, loop over 3 | 5^24·17^18·257^7·65537^3·4294967231 (also 5^26·17^15·257^10·65537^3·4294967291, …) | **3^42** (lower bound) |
| ω = 6, loop over 5 inside 3^≥50 (`FREE=5 E3=50`) | 17^17·257^7·65537^3·4294967291 | **5^27** (same for E3 = 45) |
| ω = 6, loop over 17 inside 3^50·5^24 (`FREE=17`) | 5^24·257^7·65537^3·4294967231 | **17^16** |

Scan: the 135045 primes q in [2^32 − 3·10^6, 2^32), exponents ≤ 70; a 20000-wide window already gives 42.
Heuristic for why ≈ 42: G0(q) = (1 − 2^-32)(1 + 1/q) − 1 ≥ 5/2^64 ≈ 2.7·10^-19 (q = 2^32 − 5). The exponents of
5, 17, 257 and 65537 then subtract Σ p^{-(e+1)}, and a few thousand such sums land within ≈ 10^-23 of G0, so G ≈ 10^-21
and E0 ≈ log_3(10^21) ≈ 42–44.

## 3. Treating "3^≥E" at once, and when the loop never closes

**Never closes ⇔ E* = ∞ ⇔ ρ(m) accumulates at 4/3 from above** (ω(m) = 5). Take a sequence and pass to a subsequence:
each prime is either fixed with a fixed exponent, fixed with exponent → ∞ (factor ↑ p/(p − 1), from below), or → ∞
(factor ↓ 1, from above). Approach from above needs at least one prime → ∞, and the limit of the other ≤ 4 primes must
be exactly 4/3, with at least one infinite exponent (all finite is impossible because 3 ∤ m). Conversely, such a
configuration plus a prime q → ∞ tuned to it gives G → 0⁺. **Search:** `scripts/three_limit_configs.py 3000 6 4`
→ 0 configurations (the closest is 5^∞·17^∞·257^∞, 2^-16 below). `600 4 5` (5 primes) → 0 as well. A 5-prime exact
configuration would not make E* infinite, but it would make the current search loop forever, because the region bound
is exactly 2 and the code prunes only on < 2. These are caps, not a proof.

**Handling 3^≥E in one tree (proposal, not implemented):** keep the region node 3^≥E (bound 3/2). When a family has
all its non-3 exponents exact and its star test finds M·q^e deficient at 3^E but region-abundant, do not return False.
Instead *lift*: compute a* = E0(M′q^e) (with M = 3^E·M′), test 3^{a*}·M′·q^e for pseudoperfection (all n in the family
with v_3 ≥ a* are multiples of it, and those with v_3 < a* are deficient), and iterate e until a*(e) equals the value
for the limit q/(q − 1). This replaces the infinite loop over roots by one region tree, whose size for large E does
not depend on E (the session-31 observation: E = 50 and E = 60 visit the same nodes). The cost is about the cost of one
large root. It needs code changes plus `validate-owf.sh`, and possibly a new image for the workers: Pablo's decision.

## 4. What this means for the workers (not touched)

- With the bug, the "done" roots of ω = 6 are not a proof. Fixing it costs ≈ 1.6–2.2× more nodes (ω = 4: 2.2×,
  ω = 5: 1.6×).
- Even with the fix, the root-by-root loop has to reach at least 3^42. At ≈ 4–5 h per root per worker for the current
  roots (and growing), that is 20+ more roots, i.e. ≥ 100 worker-hours. Lifting (§3) would avoid that.
- Options for Pablo (board card): (a) stop, fix (one line in .py and .c), validate, rebuild the image and restart from
  zero; (b) keep the current run as a non-proof estimate only; (c) fix + lifting, then a single region tree.

## 5. Reproduce (one core, short)

```
python3 -I scripts/star_parity_repro.py                                  # bug, ~1 s
KF=3 HI=1e-7 LO=1e-16 python3 scripts/three_e0_fermat.py 65000 60        # ω = 5: E0 = 24
python3 scripts/three_e0_fermat.py 3000000 70                            # ω = 6: E0 = 42 (~35 s)
FREE=5 E3=50 python3 scripts/three_e0_fermat.py 3000000 70               # 5-loop inside 3^≥50: 27
FREE=17 E3=50 python3 scripts/three_e0_fermat.py 3000000 70              # 17-loop: 16
python3 scripts/three_limit_configs.py 3000 6 4                          # exact 4/3 configurations: 0
python3 scripts/roottest_branch_profile.py /lean/state/owf/logs/root-22.log   # sampling profile (read-only)
# fixed-binary calibration (prototype in /tmp, the repo .c is unchanged):
#   add `if (mpz_even_p(q)) mpz_add_ui(q, q, 1);` after `if (mpz_cmp(q0, q) > 0) mpz_set(q, q0);` in family()
#   for E in 22 23 24 25; do ROOTTEST=$E nice -n 19 taskset -c 1 ./owf_fix 5; done
```
