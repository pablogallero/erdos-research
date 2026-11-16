# Erdős research

PGAL's workspace for open Erdős problems ([erdosproblems.com](https://www.erdosproblems.com)),
starting with Sidon sets. #43 turned out to be resolved (`notes/erdos-43-status.md`); the current
problem is #1052, unitary perfect numbers (`notes/erdos-1052.md`). Results are formalised in Lean 4 with Mathlib, so that every claim
is checked by the compiler, not by trust.

- `ErdosResearch/`: definitions, statements and proofs.
- `notes/`: what was tried, what failed and what is next, in plain language.
- `Challenge.lean`, `Solution.lean`, `comparator.json`, `formalization.yaml`: the Palomar
  submission package (`notes/palomar.md`). Submitting it is Pablo's decision.
- Toolchain `leanprover/lean4:v4.35.0` and Mathlib `v4.35.0`, the same as PGAL's image.
  Change them together with PGAL's `Dockerfile`, never alone. Every `.lean` file uses the
  module system (`module` header), as Palomar requires.

CI (`.github/workflows/lean.yml`) builds the project from scratch on every PR. PGAL only
merges when it is green.

```bash
lake exe cache get   # Mathlib's prebuilt cache
lake build
```

Nothing here is published or sent to anyone; claims of new results are only claims until
the Lean proof compiles and a person has reviewed it.
