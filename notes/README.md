# Notes

One file per problem or line of attack: the statement, what is known (with references),
what was tried, what failed and why, and the next step. Plain language; Lean goes in
`ErdosResearch/`.

- `erdos-43-status.md`: #43, resolved; dropped (session 1).
- `erdos-1052.md`: #1052 (unitary perfect numbers), sessions 1–7; paused in session 8.
- `erdos-470.md`: #470 (odd weird numbers), current problem since session 8 (session 9: ω ≤ 3 in Lean;
  session 10: ω ≤ 4 in Lean; session 11: ω = 5 checked in Python with last-prime families,
  general last-prime lemmas in Lean; session 13: faster search and a resumable ω = 6 run; session 31: C/GMP
  port `scripts/odd_weird_family.c`, validated by `sh scripts/validate-owf.sh`, mandatory after any change).
  The ω = 6 checkpoint is stored gzipped as `data/omega6.ck.gz` (the plain `data/omega6.ck` is gitignored):
  `gunzip -kf notes/data/omega6.ck.gz` before a run, `gzip -9 -c notes/data/omega6.ck > notes/data/omega6.ck.gz` after.
  Since session 50 the checkpoint is split: `data/omega6.ck.gz` is frozen (36729 lines) and new lines go to
  `data/omega6-2.ck.gz`; run on `zcat data/omega6.ck.gz data/omega6-2.ck.gz > plain` (details at the top of `erdos-470.md`).
  Sessions 52–57: subset-sum certificates in Lean (`ErdosResearch/SubsetSum*.lean`: chain condition, glue, prime step,
  prime-power step, bitset certificate, exponent-raising step, step lists, greedy gap bound, late raise) as building
  blocks for a Lean family search.
  `data/roottest50.ck.gz` (session 32): resumable checkpoint of `ROOTTEST=50` (region subtree of root 3^50), same format.
- **`omega6-invalidated.md` (2026-11-23): the star-loop parity bug is fixed. Every ω = 6 result before the fix (roots 3^1…3^20,
  the seed checkpoint, ROOTTEST=50) is invalid. The data is kept as `data/*-con-fallo.*`, the seed checkpoint was removed, and the
  workers restart from 3^1 in generation `v2` (`data/omega6-v2*.gz`, in 40000-line parts since session 92; see `omega6-job.md`). The ω = 6 lines below describe generation 1 (buggy).**
- `omega6-job.md`: **since 2026-11-22 the ω = 6 search runs by itself in pgal's StatefulSet `owf` (2 workers), never in a session.**
  A session only runs `sh scripts/owf-queue.sh read` (read-only, from `/lean/state/owf`); never `owf` or `launch-next`.
  The older run instructions are history. `data/omega6-roots.txt` (written by `read`) lists the finished roots.
- `root-loop-3.md` (2026-11-23): why `ROOTTEST=50` stalled at 5^24, the closing exponent of the ω = 6 loop over 3
  (≥ 42, Fermat-prime near-ties), and a **parity bug in the star loop of `family`** (the ω = 6 checkpoint is not a proof).
- `palomar.md`: the Palomar package (Lean v4.35.0, module system, Challenge/Solution, comparator.json,
  formalization.yaml, preflight CI); sessions 14–16.
- `build-times.md`: time per Lean module; what is in the default `lake build` (Palomar chain) and what is in the
  non-default lib `ErdosResearchExtra` (research modules, built explicitly by the CI).
- `mathlib-upstream.md` (session 92): the next work, chosen after card #192. It prepares the repo's general lemmas
  (`Pseudoperfect.of_dvd`, the chain criterion for `Finset.subsetSum`, …) for Mathlib, in `ErdosResearch/Upstream.lean`.
  Alternatives discarded, with the reasons, are listed there. The Mathlib PR waits for Pablo's approval (card #197).
