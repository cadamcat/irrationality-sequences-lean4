module

public import IrrationalitySequences

/-!
# Non-vacuity checks

The property `IsStrongIrrationalitySequence` is not satisfied trivially: the constant sequence `1`
fails it, because its reciprocal sum diverges, so its `tsum` is `0`. The witness sequence is
explicit: its first value is `4`, and every value is positive.
-/

@[expose] public section

namespace Erdos264

example : ¬ IsStrongIrrationalitySequence (fun _ ↦ 1) := by
  intro h
  have hb : (0 : ℝ) = ∑' _ : ℕ, (1 : ℝ) / (((1 : ℕ) : ℤ) + (0 : ℤ)) := by
    rw [tsum_eq_zero_of_not_summable]
    simpa using (not_summable_iff_tendsto_nat_atTop_of_nonneg (f := fun _ : ℕ ↦ (1 : ℝ))
      (fun _ ↦ zero_le_one)).2 (by simpa using tendsto_natCast_atTop_atTop)
  have := h (fun _ ↦ 0) (by simp) (by simp) (by simp)
  rw [← hb] at this
  exact this ⟨0, by simp⟩

example : fast 0 = 4 := by
  rw [fast_eq]; simp

example (n : ℕ) : 0 < fast n := fast_pos n

end Erdos264
