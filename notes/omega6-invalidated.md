# #470: results invalidated by the star-loop parity bug (2026-11-23)

Task from Pablo (mail "Erdos", 2026-11-23, "Arréglalo tú"). Background: `notes/root-loop-3.md` §0.

## The bug

In `family` (`scripts/odd_weird_family.py` and `scripts/odd_weird_family.c`), the loop over primes q > qtop (star loop)
started at `q = max(q0, qtop + 1)` and stepped by 2. When `qtop` is odd, that start is even, so the loop visited only even
numbers. It never tested a prime in the window, and it could return True (family "covered") without any test. A True
answer could therefore hide an abundant number with no pseudoperfection check, so a "True" from the buggy code is not a proof.

**Fix (this branch):** one line in each version. After the start is computed, add 1 if it is even.
- Regression test: `python3 -I scripts/star_parity_repro.py` (exit 0 = fixed). (1) Python: the family
  `[(3,23),(5,12),(17,6),(257,2)]` with q0 = 259 must not return True with 0 star tests. (2) C: `ROOTTEST=23 owf 5`
  must print False. 3^24·5^12·17^6·257^4·65521 is abundant there and not covered. With the old code both parts
  print "BUG REPRODUCED", with the fix both print OK.
- `sh scripts/validate-owf.sh` (Python against C, K = 4 and 5, all C paths, cross-resume): **ALL OK** (output below).
  ω = 4: 1996 nodes (911 before the fix). ω = 5: 706995 nodes (447944 before). Both True, nfail 0, and the C checkpoint
  is byte-identical to the Python one.

## Invalidated (made with the buggy code; kept, marked "con fallo", not evidence)

| what | where now | note |
|---|---|---|
| ω = 6 root results 3^1 … 3^20 ("DONE", nfail 0) | `notes/data/omega6-roots-con-fallo.txt` (renamed from `omega6-roots.txt`) | Each "DONE" may contain families that were wrongly declared True. |
| ω = 6 checkpoint used as the seed of the workers: `notes/data/omega6.ck.gz` (36729 lines, sha256 `10fca855…7feb`) + `notes/data/omega6-2.ck.gz` (16506 lines, sha256 `b06118e2…b53e`) | **removed from the repo** (`git rm`). Still in the git history: `git show 40ea5a3:notes/data/omega6.ck.gz` (and `…omega6-2.ck.gz`) | Every key is a subtree "decided True" by the buggy code. It must not be reused as a seed. |
| ω = 6 checkpoint evidence (hashes, line counts, validation output from session 31) | `notes/data/omega6-evidence-con-fallo.txt` | It refers to the buggy code (`b0841f9c…`). |
| `ROOTTEST=50` checkpoint (region subtree of 3^50, sessions 32–47) | `notes/data/roottest50-con-fallo.ck.gz` | Same buggy code. |
| The workers' volume, generation 1: `/lean/state/owf/{omega6.ck, omega6-roots.txt, claims.txt, logs/}` (roots up to 3^20 DONE, 3^21/3^22 in progress) | left untouched at the top level of the volume. The fixed workers use the subdirectory `v2/` | Not deleted. Nothing reads it any more. |
| Anything derived from those: the "finished roots v_3 ∈ {1..20}" counts in `progreso.md`, `notes/erdos-470.md` (sessions 12–70) and `notes/omega6-job.md`; the per-root node counts; ROOTTEST verdicts from the old binary (e.g. "ω = 5 closes at 23", "E = 8 … 45 False") | the notes stay as history | Read them as "buggy code". The *lower* bounds from `notes/root-loop-3.md` §2 (E* ≥ 42, from E0(m)) do not depend on the search, so they stand. |

Unchanged by the bug (no search code involved): the Lean files (`ErdosResearch/*.lean`, including ω ≤ 4 for odd weird
numbers and all of #1052), and the Python/Lean certificate probes of sessions 52–69 (they use their own code, not `family`).

## Kept (re-checked with the fixed code)

- **ω = 4:** True with the fixed Python and the fixed C (1996 nodes, nfail 0). It is also proved in Lean
  (`not_weird_of_odd_of_card_primeFactors_le_four`), which does not use this code.
- **ω = 5:** True with the fixed Python and the fixed C (706995 nodes, nfail 0). Evidence only, not Lean. It agrees with
  Liddy–Riedl.
- **ω ≤ 3:** proved in Lean (`OddWeirdThree.lean`, session 9) by explicit pseudoperfect certificates and size bounds.
  It never used `odd_weird_family`, so the bug does not affect it. (The search with K ≤ 3 is not run by `validate-owf.sh`.)
- ω = 5 closing exponent of the loop over 3: **24** with the fixed binary (`ROOTTEST=23` False, `ROOTTEST=24` True,
  re-run 2026-11-23). The buggy binary said 23.

## Restart (generation v2)

- `deploy/owf/Dockerfile`: no seed checkpoint (the `COPY notes/data/omega6*.ck.gz` line is gone). The build checks
  that `owf 4` gives `4 True {'n': 1996,` so a binary without the fix cannot be built into the image.
- `deploy/owf/run-root.sh`: data in `$OWF_DATA/$OWF_GEN` (default `/data/v2`), starting from an empty checkpoint.
  `OWF_FIRST` defaults to 1. Generation 1 at the top of the volume is never read. Tested locally (K = 4, roots 1 and 2,
  then `export`).
- `scripts/owf-queue.sh read`: reads `/lean/state/owf/v2` and writes `notes/data/omega6-v2.ck.gz` +
  `notes/data/omega6-v2-roots.txt` (FROZEN = 0). Fixed an awk idiom that dropped every line when the frozen prefix is empty.
  Tested on a fake volume (copy, dedupe/garbage, FOUND alert).
- pgal side (`deploy/owf.yaml`: `replicas: 0` now; then the new image, `OWF_FIRST=1`, `replicas: 2`) is not in this repo.
  It needs its own PR in pgal. Order: stop the workers first, then merge this PR, build the image, then restart.

## Single tree for 3^≥E (lifting): tried, not adopted

See `notes/root-loop-3.md` §6. The workers stay on the root-by-root method (with the fix).

## validate-owf.sh output (fixed code; the script now runs star_parity_repro.py first)

```
star_parity_repro: OK (Python and C)
K=4 python: 4 True {'n': 1996, 'fam': 1409, 'qchk': 1916, 'star': 784, 'skip': 0}
K=4 C (PSLOW=auto): same counters, same failures, byte-identical checkpoint (1223 lines)
K=4 C (PSLOW=1): same counters, same failures, byte-identical checkpoint (1223 lines)
K=4 C (PSLOW=2): same counters, same failures, byte-identical checkpoint (1223 lines)
K=5 python: 5 True {'n': 706995, 'fam': 426462, 'qchk': 212839, 'star': 194276, 'skip': 0}
K=5 C (PSLOW=auto): same counters, same failures, byte-identical checkpoint (15048 lines)
K=5 C (PSLOW=1): same counters, same failures, byte-identical checkpoint (15048 lines)
K=5 C (PSLOW=2): same counters, same failures, byte-identical checkpoint (15048 lines)
cross-resume Python->C: cut at 1791 lines, C finished True, same key set
cross-resume C->Python: cut at 1249 lines, Python finished True, same key set
ALL OK
```
