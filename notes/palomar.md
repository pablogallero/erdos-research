# Palomar submission package

Priority set by Pablo on 2026-11-09 (task #95). The package was first prepared on 2026-11-13
(session 14), but that work never reached GitHub and was lost. It was redone on 2026-11-15.

## What is submitted

One Comparator configuration, `comparator.json` (repository root), with three theorems in
namespace `ErdosResearch.Palomar`:

| Challenge theorem | Proof in the library |
|---|---|
| `finite_unitaryPerfect_card_primeFactors_eq` | `ErdosResearch.Erdos1052.finite_isUnitaryPerfect_card_primeFactors_eq` (`UnitaryPerfectFinite.lean`) |
| `unitaryPerfect_iff_of_card_primeFactors_le_seven` | `ErdosResearch.Erdos1052.isUnitaryPerfect_of_card_primeFactors_le_seven_iff` (`UnitaryPerfectSixOdd.lean`) |
| `not_weird_of_odd_of_card_primeFactors_le_four` | `Erdos470Research.not_weird_of_odd_of_card_primeFactors_le_four` (`OddWeirdFour.lean`) |

- `Challenge.lean`: the statements, with `sorry`. Mathlib only; unitary perfection is spelled out
  inline (the formal-conjectures definition), and weird is Mathlib's `Nat.Weird`.
- `Solution.lean`: imports `ErdosResearch` and proves each statement by the library theorem
  (`IsUnitaryPerfect` unfolds to the inline condition).
- `formalization.yaml` (v0.4): `project.authors` and `project.responsible_maintainers` are
  `"Pablo Gallero"` (confirmed by Pablo on 2026-11-15). License Apache-2.0 (matches `LICENSE`),
  `math.NT`, MSC 11A25, `automation: autonomous`, `review: unchecked`. Sources are recorded as
  `independently-proves` (Wall 1988, Goto 2007, Liddy–Riedl 2018) plus `background`, so the
  derived origin is *source-based*. All results are classical; only the formalisation is new.
- `.github/workflows/palomar-preflight.yml`: the reusable workflow
  `PalomarRegistry/PalomarSubmission/.github/workflows/submission.yml@14aa8d6b3c2f14a8540605e37144560b9a00e7e7`
  (`pipeline_commit` equal to it), `mode: full`, `execution_profile: palomar-standard-v1`,
  `comparator_config_path: comparator.json`,
  `authorization_relationship: "I am a responsible author or maintainer"` (confirmed by Pablo).
  On pull requests it checks the PR head commit. It is advisory and is **not** a registry
  submission: the actual submission (submit.palomar-registry.org) is made by Pablo.
- `scripts/check-lean-sources.py` (run first in `lean.yml`): `module` header, ≤ 10,000 lines,
  no `.lean` symlinks, and no `sorry`/`native_decide`/`axiom` outside `Challenge.lean`.

## Changes made to the library for Palomar

- Lean and Mathlib **v4.35.0** (`lean-toolchain`, `lakefile.toml`, `lake-manifest.json`). Palomar
  requires the project toolchain to equal Mathlib's. API fixes: `open scoped
  ArithmeticFunction.sigma`; `List.Sorted` → `List.Pairwise`; `List.sorted_cons` →
  `List.pairwise_cons`; `Finset.sort_sorted_lt` → `(Finset.sortedLT_sort s).pairwise`;
  `Nat.factorization_prod_pow_eq_self` → `Nat.prod_factorization_pow_eq_self`;
  `Finset.sort_eq s r` (argument order).
- Module system in every `.lean` file: `module`, `public import`, `@[expose] public section`.
  The generators `scripts/odd_pan_search.py` and `scripts/odd_weird_chunks.py` emit the same
  header and reproduce `OddWeirdFourData.lean` / `OddWeirdFourChunks.lean` byte for byte.
- `lakefile.toml`: libraries `Challenge` and `Solution`, both default targets.

## Local checks (2026-11-15)

- `lake build`: OK, 9066 jobs (only deprecation warnings plus the Challenge's three `sorry`s).
- `#print axioms` on the three Solution theorems: `propext`, `Classical.choice`, `Quot.sound`.
- `lake comparator --config comparator.json --inadvisably-no-sandbox`: "Your solution is okay!"
  (Lean kernel and NanoDa). Needs the toolchain's `bin` on `PATH` (for `nanoda_bin`):
  `PATH=/opt/elan/toolchains/leanprover--lean4---v4.35.0/bin:$PATH`. There is no `bwrap` here,
  hence no sandbox. The con-ron replay was not run locally (Palomar runs it).
- The preflight workflow has not run yet. It will run when the PR is opened.

## Environment

PGAL image **0.5.11 is deployed** (Pablo, 2026-11-15): `cache.mathlib.org` is allowed through
the proxy, and `lake` no longer runs under `prlimit`. The session-14 workarounds stay as
documented until Pablo explicitly confirms they can be dropped:

- Mathlib cache: `MATHLIB_CACHE_DEBUG_USE_LEGACY=1 lake exe cache get` (it was needed when
  `cache.mathlib.org` returned 403). Today the v4.35.0 cache was already in `/lean/lake`, so no
  download was needed. A probe of `https://cache.mathlib.org/` returned HTTP 404 (reachable, not
  blocked by the proxy).
- Build with `/opt/lean-locked/bin/lake build` (flock + nice, no prlimit). The old
  `/tmp/pgal-lean-bin/lake` wrapper (prlimit 3 GB) no longer exists in this image.

## Next steps

1. If the PR's preflight or CI fails, read the report artifact and fix it.
2. After the merge to `main` with green CI, give Pablo the full commit SHA and the path
   `comparator.json` for the submission form. Submitting is Pablo's decision.
