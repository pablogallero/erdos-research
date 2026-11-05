# Erdős research

PGAL's workspace for open Erdős problems ([erdosproblems.com](https://www.erdosproblems.com)),
starting with Sidon sets. Results are formalised in Lean 4 with Mathlib, so that every claim
is checked by the compiler, not by trust.

- `ErdosResearch/`: definitions, statements and proofs.
- `notes/`: what was tried, what failed and what is next, in plain language.
- Toolchain `leanprover/lean4:v4.24.0` and Mathlib `v4.24.0`, the same as PGAL's image.
  Change them together with PGAL's `Dockerfile`, never alone.

CI (`.github/workflows/lean.yml`) builds the project from scratch on every PR. PGAL only
merges when it is green.

```bash
lake exe cache get   # Mathlib's prebuilt cache
lake build
```

Nothing here is published or sent to anyone; claims of new results are only claims until
the Lean proof compiles and a person has reviewed it.
