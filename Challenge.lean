module

public import Mathlib

/-!
# Erdős Problem 264: existence of an irrationality sequence (challenge statement)

A sequence of positive integers `a` keeps an irrational reciprocal sum under every bounded integer
perturbation `b` with `a n + b n ≠ 0` for all `n`. This file states, in Mathlib vocabulary only,
that such a sequence exists. The proof is in `IrrationalitySequences.Main`, which proves a theorem
of the same name and statement.
-/

@[expose] public section

namespace Erdos264

theorem exists_irrationality_sequence :
    ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧
      ∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) →
        0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) →
        Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n)) := by
  sorry

end Erdos264
