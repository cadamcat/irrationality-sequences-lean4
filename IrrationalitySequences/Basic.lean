module

public import Mathlib

/-!
# Irrationality sequences: definitions

A sequence of positive integers `a` is an *irrationality sequence* if `∑ 1 / (a n + b n)` is
irrational for every bounded integer sequence `b` with `a n + b n ≠ 0` for all `n`. The existence
question of Erdős Problem 264 asks whether such a sequence exists.

The definition follows Formal Conjectures' `Erdos264.IsIrrationalitySequence` (Apache-2.0), which
also requires `b n ≠ 0`; the definition here drops that requirement, so it is the stronger property.
-/

@[expose] public section

namespace Erdos264

/-- Bounded integer perturbations of `a`, with nonzero denominators, keep the reciprocal sum
irrational. Zero perturbations are allowed. -/
def IsStrongIrrationalitySequence (a : ℕ → ℕ) : Prop :=
  ∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) →
    0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) →
    Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n))

/-- The target: some sequence of positive integers is an irrationality sequence. -/
def Statement : Prop :=
  ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧ IsStrongIrrationalitySequence a

end Erdos264
