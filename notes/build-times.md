# Build times of the Lean modules (measured 2026-11-23, session 60 follow-up 2)

Why: the PGAL checker runs a clean `lake build` with a 1200 s limit, and it timed out (also on main, with no Lean
changes, in session 59 at 600 s). Here lake builds **one module at a time** (`/opt/lean-locked/bin/lake`, flock + nice),
so the wall time is about the **sum** of the module times. Each module pays about 15–20 s just to load Mathlib.

Per-module time (`lake env lean FILE`, sequential, Lean v4.35.0, this machine):

| module | s | needed by `Solution` (Palomar) |
|---|---|---|
| OddWeirdPlans (40 generated certificates) | **471** | no → **removed from the root import** |
| OddWeirdFourChunks (72 `decide +kernel`) | 279 | yes |
| UnitaryPerfectFourOdd (generated case tree) | 235 | yes |
| UnitaryPerfect | 95 | yes |
| UnitaryPerfectSixOdd | 67 | yes |
| UnitaryPerfectFiveOdd | 65 | yes |
| OddWeirdThree | 46 | yes |
| OddWeirdFourData | 41 | yes |
| SubsetSumRaise / Steps / Late | 38 / 36 / 33 | no |
| OddWeirdFourCore | 35 | yes |
| OddWeird | 33 | yes |
| UnitaryPerfectFinite / Bound | 31 / 29 | yes / no |
| SubsetSumPrimeStep / PrimePow / Cert | 27 / 24 / 24 | no |
| OddWeirdFour | 23 | yes |
| SubsetSumGreedy / BitsFast / DivsDesc / Chain / Glue / LastOK | 21 / 19 / 19 / 18 / 18 / 18 | no |
| Challenge / Solution | 20 / 17 | yes |
| OddWeirdLastPrime / Sidon | 17 / 5 | no |

Sums: everything 1804 s; default build without OddWeirdPlans **1333 s**; the modules `Solution` needs alone **≈ 990 s**.

## Changes (this follow-up)

- `ErdosResearch.lean` no longer imports `ErdosResearch.OddWeirdPlans`. The file stays in the repo and builds on demand
  with `lake build ErdosResearch.OddWeirdPlans` (~8 min). Same rule as for OddWeirdRealPrefix: heavy certificates stay
  out of the default targets.
- `Solution.lean` imports only `UnitaryPerfectSixOdd`, `UnitaryPerfectFinite` and `OddWeirdFour` instead of the whole root.
  It no longer pulls in research modules. Names and types are unchanged.

- Then (same follow-up) the research modules not needed by `Solution` (all `SubsetSum*` plus `OddWeirdPlans`, ≈ 770 s
  serial) moved to a new **non-default** lib `ErdosResearchExtra` (root `ErdosResearchExtra.lean`, declared in
  lakefile.toml). `.github/workflows/lean.yml` builds it explicitly after the default `lake build`, so the GitHub CI still
  checks every module. Default build now ≈ 1040 s serial by the table (Palomar chain + Sidon, UnitaryPerfectBound,
  OddWeirdLastPrime). Incremental `lake build` OK (9066 jobs), `lake build ErdosResearchExtra` OK (9061 jobs),
  check-lean-sources OK, lean.yml parses.

## Result and what is left

- **After the split: clean serial `timeout 1200 lake build` OK in 1065 s (9066 jobs, rc 0)**, 2026-11-23 02:27–02:45 UTC on
  this machine. The margin is only ~11 %.

- Before the split: a clean serial `timeout 1200 lake build` on this machine **still timed out** (rc 124 at 1200 s, at job 9067/9078).
  After that, an incremental `lake build` finished OK (9078 jobs, 75 s). check-lean-sources OK.
- The floor is the Palomar chain itself (≈ 990 s serial, with FourOdd + FourChunks = 514 s). So a 1200 s serial
  clean-build limit cannot be met with real margin without either (a) a higher checker limit or a parallel / olean-cached
  checker (Pablo/PGAL, outside the repo), or (b) speeding up OddWeirdFourChunks and UnitaryPerfectFourOdd (for example, a
  reflective checker like `fchk` instead of the generated tree in FourOdd). That would take a session of its own.
- On GitHub (4 cores, 60 min) the Lean CI is green on main.
