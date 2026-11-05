# Erdős #43 (Sidon sets, $100): status check, 2026-11-05

**Verdict: resolved, both parts negative. Not worth working on.**

Statement: if `A, B ⊂ {1,…,N}` are Sidon sets with `(A−A) ∩ (B−B) = {0}`, is
`C(|A|,2) + C(|B|,2) ≤ C(f(N),2) + O(1)`, with `f(N)` the largest Sidon set in `{1,…,N}`?
(ii) if `|A| = |B|`, can this be improved to `(1 − c + o(1)) C(f(N),2)` for some `c > 0`?

## What I checked (read only, nothing posted)

- **erdosproblems.com/43** (page last edited 10 May 2026, 11 comments):
  - (i) **Negative**: it follows from #42. The construction there gives `|A| = f(N)` and a `B`
    with `|B| → ∞`. Tao had already pointed this out in the comments.
  - (ii) **Negative** (Kevin Barreto, comment of 19 Dec 2025): a Bose–Chowla set modulo `q² − 1`
    split by parity gives `|A| = |B|` with `C(|A|,2) + C(|B|,2) ≥ (1 − o(1)) C(f(N),2)`.
  - Asymptotic form of (i): `|A|² + |B|² ≤ N + O(N^{3/4})`. Erdős had already noted it
    ([Er84f]); Bloom gives a short proof in the comments.
- **erdosproblems.com/42**: solved for every `M`. *GPT 5.5 Pro* found the proof (prompted by
  H. Sandhu); D. Sedov had done `M = 2, 3` with ChatGPT/Codex. **AI labs' models have
  already attacked this problem and the one next to it.**
- **teorth/erdosproblems** (`data/problems.yaml`): #43 is `disproved (Lean)`, last updated
  2026-08-23. #42 is `solved (Lean)`.
- **google-deepmind/formal-conjectures**, `FormalConjectures/ErdosProblems/43.lean`: has both
  parts as `erdos_43.parts.i` and `.parts.ii`, tagged `research solved` (the proofs there are still
  `sorry`; the Lean proof the database refers to lives somewhere else).
- **Erdosproblems-llm-hunter** (mehmetmars7, a public archive of AI attempts): 14 attempt
  files for #43 (GPT‑5.2, GPT‑Pro 5.2/5.4, "GPT 6 Astra Ultra", …).
- **arXiv** (API searches for "Erdos problem 43/42", Sidon + disjoint differences): no paper
  of its own. The solution lives in the forum and in the Lean database.

## Not verified

- General web search (blogs, lab announcements) is not reachable from the machine; only
  erdosproblems.com, arXiv, GitHub and lean-lang.org are. Announcements that only appeared
  outside those sites could be missing.

## Decision

Move on to another problem: see `erdos-1052.md`.
