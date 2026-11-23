# Palomar package (Pablo's priority, 2026-11-09)

Goal: get the repo ready so that Pablo can register in Palomar (palomar-registry.org) what is already
proved for #1052 and #470. **PGAL does not submit anything.** Pablo submits `owner/name` + the full SHA
of the commit on main + the path `comparator.json`.

## History

- Session 14 (2026-11-13) and session 15 (2026-11-15) both did this work, but **neither reached main**:
  each new session started again from 0c9fe9f (merge of #13), with v4.24.0 and no package. Only
  `progreso.md` persisted. Session 16 (2026-11-16, branch `pgal/task-98`) redid it from scratch.
  If the next session again finds v4.24.0 in `lean-toolchain`, this PR was not merged either.
  Then do not redo it blindly: ask Pablo on the board why the PR was not merged.

## What is in the repo (session 16)

- `lean-toolchain` = `leanprover/lean4:v4.35.0`; `lakefile.toml` Mathlib `rev = "v4.35.0"`
  (manifest: 56a005855ea17e0b0958f73ec801ae140b0a1679, whose own `lean-toolchain` is v4.35.0, as Palomar
  requires). `lake update mathlib` was instant because the v4.35.0 checkout and cache were already in
  `/lean/lake`.
- API fixes for Mathlib v4.35.0: `List.Sorted r` → `List.Pairwise r`, `List.sorted_cons` →
  `List.pairwise_cons`, `s.sort_sorted_lt` → `(Finset.sortedLT_sort s).pairwise`,
  `Nat.factorization_prod_pow_eq_self` → `Nat.prod_factorization_pow_eq_self`,
  `Finset.sort_eq r s` → `Finset.sort_eq s r`, `open scoped ArithmeticFunction.sigma` for `σ`.
  Deprecation warnings remain (`push_neg`, `if_pos`/`if_neg`, `Finset.prod_le_prod'`,
  `Set.mem_setOf_eq`); they are warnings only.
- Module system: every `.lean` file starts with `module`, uses `public import`, and has
  `@[expose] public section` (definitions such as the reflective checkers must be unfoldable by
  `decide +kernel` in importing modules). The generators `scripts/odd_pan_search.py 4 --lean` and
  `scripts/odd_weird_chunks.py` were updated and reproduce their files byte for byte.
- `Challenge.lean`: Mathlib only. Copies `properUnitaryDivisors` and `IsUnitaryPerfect` verbatim
  (formal-conjectures) in `ErdosResearch.Erdos1052`, and states, with `sorry`, in
  `ErdosResearch.Palomar`:
  - `isUnitaryPerfect_iff_of_card_primeFactors_le_seven` (ω ≤ 7 ⇒ UPN ⇔ n ∈ {6, 60, 90, 87360});
  - `finite_isUnitaryPerfect_of_card_primeFactors_eq` (finitely many UPNs with ω = k);
  - `not_weird_of_odd_of_card_primeFactors_le_four` (odd, ω ≤ 4 ⇒ ¬ `Nat.Weird`).
- `Solution.lean`: imports `ErdosResearch`, proves the three with the same names and types.
- `comparator.json` (repo root): those three theorem names, `definition_names: []`, standard axioms.
- `formalization.yaml` v0.4: authors and maintainers "Pablo Gallero" (confirmed by Pablo in session 15),
  `automation.methods` = autonomous (Claude Opus 5.5, PGAL's role), `review.status: unchecked`,
  Apache-2.0. Validates against the official JSON schema (mathlib-initiative/formalization.yaml) with
  0 errors; the template's Ruby validator could not be run (no Ruby here), but I checked its rules by hand.
- `lakefile.toml`: `lean_lib`s `Challenge` and `Solution`, in `defaultTargets`.
- CI: `scripts/check-lean-sources.py` (copied from PalomarTemplate) runs first in `lean.yml`;
  `.github/workflows/palomar-preflight.yml` calls
  `PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@14aa8d6b3c2f14a8540605e37144560b9a00e7e7`
  (main on 2026-11-16) with `mode: full`, `execution_profile: palomar-standard-v1`,
  `authorization_relationship: "I am a responsible author or maintainer"`.

## Local checks (session 16)

- `lake build`: OK, 9066 jobs; only `sorry` = the 3 deliberate ones in `Challenge.lean`.
- `lake comparator`: "Your solution is okay!" (con-ron, nanoda and the Lean kernel accept).
  How: build a config like the template's `scripts/verify-comparator.sh` (drop `enable_nanoda`, add
  `external_kernels` from `$(lean --print-prefix)/bin`), then
  `PATH=/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH lake comparator --config CFG --inadvisably-no-sandbox`
  (no `bwrap` here, so the sandbox is off locally; in Palomar it is on).
- `python3 scripts/check-lean-sources.py`: OK.
- The Palomar preflight itself cannot run locally; it runs on the PR. It needs the repo to be
  **public** (the reusable workflow checks out `github.repository` at the commit). If the repo is
  private, the preflight job will fail for that reason alone, and making it public is Pablo's decision.

## Session 17 (2026-11-16): the package reached main, but the Lean CI was red

- PR #15 was merged: main = `8c7c6f491454db561ef14d1a31079f4231db338e` (v4.35.0, Challenge/Solution,
  comparator.json, formalization.yaml, preflight). Checked through the public GitHub API, since
  `gh` is not installed here.
- On that commit, **Palomar preflight = success** (run 43959047011, mode full).
- **Lean = failure**, with 0 jobs (run 43959044110; the same happened on pgal/task-98). Cause:
  `.github/workflows/lean.yml` was invalid YAML. The step name
  `Check Lean source requirements (Palomar: module header, line limits)` contains `": "` inside
  an unquoted scalar, so GitHub could not parse the file. (That is why the run shows up under the
  file path and not under the name "Lean".) Fix: quote the name. Checked with `yaml.safe_load`.
  Locally, `check-lean-sources.py` OK and `lake build` OK (9066 jobs). The Lean is unchanged.
- Lesson: validate workflow YAML (`python3 -c "import yaml; yaml.safe_load(open(F))"`) before
  handing over a PR.

## Current state (checked 2026-11-18 05:2x UTC, session 26)

- The lean.yml fix (quoted step name) is in main: `.github/workflows/lean.yml` line 19, and both workflow
  files parse with `yaml.safe_load`.
- main = `10e5fdb48cb70761e00930c9da99c85e826140c6`. On that commit: **Lean = success** (run 44227521761),
  **Palomar preflight = success** (run 44227521972, mode full). Checked via
  `api.github.com/repos/pablogallero/erdos-research/actions/runs?branch=main`.
- Every main commit since `0005a6db` (session 18) has had both workflows green. The Palomar files have not changed.
- `comparator.json` is at the repo root.
- Pablo was told on board card #106: first `0005a6db…` (session 18), updated in session 26 with `10e5fdb4…`.
  There is no reply yet. Do **not** report 8c7c6f49, because its Lean CI was red.
- Nothing was submitted to Palomar. Pablo does that.

## Still to do

- Nothing on the Palomar side unless Pablo replies on card #106.

## Re-check (2026-11-23 00:5x UTC, session 60 review)

- A review asked to "do the Palomar work first" because the session-60 diff did not contain it. It does not need
  redoing: it has been in main since PR #15 / `0005a6db` (session 18). Current main =
  `ad13f82ea42c648a8cac96c7fd2e613b7d331a41`: `lean-toolchain` v4.35.0, Mathlib `rev = "v4.35.0"`, `module` in every
  .lean (`scripts/check-lean-sources.py` OK), `Challenge.lean`, `Solution.lean`, `comparator.json` (root),
  `formalization.yaml` v0.4, preflight workflow. On that commit **Lean = success** and **Palomar preflight = success**
  (GitHub API, `actions/runs?branch=main`). Palomar files unchanged; Pablo already has the hand-over (card #106).
