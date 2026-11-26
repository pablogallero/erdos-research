# Next work (session 92, 2026-11-25): Mathlib upstream of the generic lemmas

## Decision and why

The task from Pablo (2026-11-25) says to choose the next work myself (card #192, now closed) and to
prefer a reasonable probability of success over a lottery.

- **Chosen: upstream to Mathlib the general lemmas this repo needed.** They are small, Mathlib lacks them,
  and other people will use them. Success is likely (the Lean is already done; review is the only risk),
  the cost is low, and the payoff is real but modest: a useful contribution and some reputation.
  The ω = 6 search for #470 keeps running in the background (v2 workers). It is the only potentially *new*
  result in this repo, and it needs no session time beyond `read`.
- **Discarded for now:** the 4 candidates in `docs/candidatos-siguiente-problema.md` (#64, #993, #128,
  #939 r = 4). Each has P(success) ≤ 1–2 %, so they are lotteries, and all of them are crowded with AI teams.
  Also discarded: the Lean replay of ω = 6 (session 88: ≥ 500 kernel-h per root, infeasible). Non-mathematical
  projects (Galician resources, accessibility, open data) are not feasible from here yet: there is no general
  web search, and only GitHub, arXiv, OpenAlex, Semantic Scholar, zbMATH and Stack Exchange are reachable.
  None of them has a concrete, checkable target that beats this option on probability. I would revisit them
  if Pablo gives a data source.
- Change plan if Mathlib rejects the approach, or if ω = 6 v2 closes (then the paper note comes first).

## Literature / existing work (checked 2026-11-25)

- Mathlib `master`, `Mathlib/NumberTheory/FactorisationProperties.lean` (raw.githubusercontent.com, 243 lines):
  it has `Abundant.of_dvd`, `Abundant.mul_left` and `Perfect.pseudoperfect`. It has **no** `Pseudoperfect.of_dvd`,
  `Pseudoperfect.not_deficient`, `Deficient.not_weird`, `Perfect.not_weird`, or `Weird.not_pseudoperfect_of_dvd`.
- Mathlib `master`, `Mathlib/Combinatorics/Additive/SubsetSum.lean`: it has the definition and cardinality bounds,
  but **no** interval / chain criterion.
- GitHub issue search on `leanprover-community/mathlib4` (terms: Pseudoperfect, subsetSum, abundant): there is no
  open PR on these lemmas. The closest are merged #34109 (infinite abundant) and #40562 (positivity lemmas).

## What is done

`ErdosResearch/Upstream.lean` (in `ErdosResearchExtra`; module ≈ 15 s; no sorry/native_decide; axioms
propext/Classical.choice/Quot.sound; `lake build ErdosResearchExtra` OK, 9095 jobs; check-lean-sources OK):

| lemma | target file in Mathlib |
|---|---|
| `Pseudoperfect.of_dvd`, `Pseudoperfect.mul_left` (same signature shape as `Abundant.of_dvd` / `mul_left`) | FactorisationProperties |
| `Pseudoperfect.not_deficient`, `Deficient.not_weird`, `Perfect.not_weird`, `Weird.not_pseudoperfect_of_dvd` | FactorisationProperties |
| `mem_subsetSum_of_chain` (Stewart 1954 / Brown 1961 chain criterion, finset form with no sorting) | Combinatorics/Additive/SubsetSum |
| `pseudoperfect_of_chain` | FactorisationProperties (it imports SubsetSum? check before the PR) |

## What is NOT done

- It has not been compiled against Mathlib `master`, only against v4.35.0 (the repo's pin). Names may
  differ (for example, `if_neg` is already deprecated in favour of `ite_eq_right` in v4.35).
- No Mathlib PR has been opened: that publishes under Pablo's account and needs his approval (board card).
  Pablo also decides who appears as the author and how the PR mentions the AI assistance.
- Docstrings and references (Stewart 1954, Zbl 0056.27004; Brown 1961) have to be put in Mathlib's
  `references.bib` format.

## Next steps

1. Once Pablo approves: a fork of mathlib4 at master, move the lemmas into the target files, then `lake build`
   plus the Mathlib linters (`lake exe lint-style`), and open the PR as a draft.
2. Optional, same PR series: `ErdosResearch/SubsetSumGlue.lean` (`glue`, subset sums of a union /
   scaled set) as general `Finset.subsetSum` API, after checking it against master.

## Session 93 (2026-11-25, 23:00 UTC): patch against Mathlib master ready (nothing published)

- Mathlib master = `348837d3aa976624060d7c35c183fff587c5a24a` (2026-11-25 19:52), toolchain `v4.37.0-rc1`.
  The two target files on master differ from the repo's v4.35.0 copies **only** in docs and `@[oeis …]`
  attributes, so definitions and every API name used (`mem_subsetSum_iff`, `subsetSum_mono`,
  `induction_on_max`, `Perfect.pseudoperfect`, `weird_seventy`) are the same.
- **`notes/mathlib-upstream.patch`** (unified diff against those two master files, `git apply -p1` in a
  mathlib4 checkout; sha256 8d47171e…d978): `Finset.mem_subsetSum_of_chain` at the end of
  `Combinatorics/Additive/SubsetSum.lean`; in `NumberTheory/FactorisationProperties.lean` (after
  `Abundant.mul_left`, plus a private `import Mathlib.Combinatorics.Additive.SubsetSum`):
  `Pseudoperfect.pos`, `.of_dvd`, `.mul_left`, `.not_deficient`, `Deficient.not_pseudoperfect`,
  `Deficient.not_weird`, `Perfect.not_weird`, `Weird.not_pseudoperfect_of_dvd`, `pseudoperfect_of_chain`.
  Lines ≤ 100 characters, `↦`, Mathlib naming.
- Checked: the patched master `SubsetSum.lean` compiles as is with `lake env lean` against Mathlib v4.35.0
  (rc 0); the patched `FactorisationProperties.lean` compiles (rc 0) with the `@[oeis]` lines removed and the
  chain lemma inlined *before* the public section (to mimic the private import; the v4.35 olean of SubsetSum
  lacks the new lemma). Standalone sanity file (12 pseudoperfect by the chain criterion) also rc 0.
- **Not checked:** compilation with the master toolchain. `elan toolchain install leanprover/lean4:v4.37.0-rc1`
  fails: `/opt/elan` is read-only and, with a writable `ELAN_HOME`, the download gets `CONNECT tunnel failed, 403`
  (the release host is not in the egress). Core lemma names (`filter_insert`, `ite_eq_right`,
  `filter_true_of_mem`, `sum_image`) could have moved between v4.35 and v4.37-rc1. The Mathlib CI of the PR
  (or an egress change) will tell. Also not run: `lake exe lint-style` / `#lint`.
- `ErdosResearch/Upstream.lean` is unchanged (the patch adds `Pseudoperfect.pos` and
  `Deficient.not_pseudoperfect`); the patch is the canonical text for the PR.
- Next: if Pablo approves on #197: fork, `git apply -p1 notes/mathlib-upstream.patch`, run Mathlib's CI and
  linters, open as a DRAFT with the authorship/AI note he chooses.

## Session 94 (2026-11-26, 00:00 UTC): second patch, general `Finset.subsetSum` API (nothing published)

- Decision: card #197 is still unanswered, so I took the low-cost item from session 93 instead of starting
  anything new. Mathlib master (re-fetched 00:03 UTC) has only `subsetSum_mono`, `subsetSum_erase_zero` and
  the inclusion `a +ᵥ A.subsetSum ⊆ (insert a A).subsetSum`. The GitHub search for `subsetSum` PRs shows
  only #31689 (the original file, merged), so nothing open overlaps.
- New `ErdosResearch/UpstreamSubsetSum.lean` (ErdosResearchExtra only; namespace `ErdosResearch.Upstream`;
  ≈ 15 s; standard axioms; no sorry/native_decide): `subsetSum_empty`, `subsetSum_singleton` (simp),
  `sum_mem_subsetSum`, **`subsetSum_union`** (disjoint ⇒ `(A ∪ B).subsetSum = A.subsetSum + B.subsetSum`),
  **`subsetSum_insert`** (`a ∉ A` ⇒ `A.subsetSum ∪ (a +ᵥ A.subsetSum)`, the equality version of Mathlib's
  inclusion), **`subsetSum_image`** (additive monoid hom injective on `A`). Any `AddCommMonoid`; these
  generalise `SubsetSumGlue.subsetSums_union` / `subsetSums_image_mul`. Two sanity examples.
- **`notes/mathlib-upstream-2.patch`** (sha256 5f69684c…c5cb): the same lemmas inserted into master's
  `Combinatorics/Additive/SubsetSum.lean` before the ordered section, plus
  `public import Mathlib.Algebra.Group.Pointwise.Finset.Basic` (needed for `Finset` `+`; no import cycle:
  only `Mathlib.lean` imports SubsetSum). Checked: `git apply -p1 --check` on master's file OK; the patched
  master file compiles against v4.35.0 with `lake env lean` (rc 0); lines ≤ 100 chars.
- Not checked: master toolchain v4.37.0-rc1 (same egress 403 as session 93), Mathlib linters, whether
  reviewers want the extra import (alternative: put the lemmas in a new file
  `Combinatorics/Additive/SubsetSum/Pointwise.lean`).
- Next: same as session 93. If Pablo approves #197, the two patches can be one PR or two (independent files).

## Session 98 (2026-11-26): patches still current

- GitHub API: last commits on master's `Combinatorics/Additive/SubsetSum.lean` (29c53517, 2026-10-09) and
  `NumberTheory/FactorisationProperties.lean` (cc12abd2, 2026-11-24) predate the base 348837d3 (2026-11-25),
  so both patches still apply as they are. Search of open mathlib4 PRs: 0 mention `pseudoperfect`; the 3 hits
  for `subsetSum` are unrelated chores. Still waiting for #197.
