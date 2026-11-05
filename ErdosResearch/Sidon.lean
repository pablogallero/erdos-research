import Mathlib.Data.Finset.Basic

/-!
# Sidon sets

Starting point for PGAL's work on Erdős's Sidon-set problems (erdosproblems.com).
Only the basic definition for now; statements and proofs are added as the research goes.
-/

namespace ErdosResearch

/-- A finite set of naturals is a Sidon set if every sum `a + b` of two of its elements
determines the pair `{a, b}`. -/
def IsSidon (A : Finset ℕ) : Prop :=
  ∀ a ∈ A, ∀ b ∈ A, ∀ c ∈ A, ∀ d ∈ A, a + b = c + d → (a = c ∧ b = d) ∨ (a = d ∧ b = c)

/-- The empty set is trivially a Sidon set. -/
theorem isSidon_empty : IsSidon ∅ := by
  intro a ha
  simp at ha

end ErdosResearch
