module

public import IrrationalitySequences.Basic

/-!
# A product-dominating irrationality sequence

We construct `a n = 4 * (n + 1) * ∏ i < n, (a i + n + 1)`.
For a bounded integer perturbation, every sufficiently late tail is positive
and at most `4 / a n`. The denominator of the rational partial sum through
index `n - 1` is at most the product in this definition.

If the total were a rational `q`, choose `n` beyond the perturbation bound
with `q.den < n + 1`. The tail would then be smaller than the minimum gap
between `q` and that partial sum, a contradiction.
-/

@[expose] public section

namespace Erdos264

open Finset

/-- Each new denominator dominates the product of all earlier denominators,
even after an integer perturbation bounded by the current index. -/
def fast (n : ℕ) : ℕ :=
  4 * (n + 1) * ∏ i : Fin n, (fast i + n + 1)
termination_by n
decreasing_by exact i.isLt

theorem fast_eq (n : ℕ) :
    fast n = 4 * (n + 1) * ∏ i : Fin n, (fast i + n + 1) := by
  rw [fast]

theorem fast_lower (n : ℕ) : 4 * (n + 1) ≤ fast n := by
  rw [fast_eq]
  have h : 1 ≤ ∏ i : Fin n, (fast i + n + 1) :=
    Finset.one_le_prod (fun i _ ↦ by omega)
  nlinarith

theorem fast_pos (n : ℕ) : 0 < fast n := by
  have := fast_lower n
  omega

theorem fast_growth (n : ℕ) : 2 * fast n ≤ fast (n + 1) := by
  have h : fast n + (n + 1) + 1 ≤
      ∏ i : Fin (n + 1), (fast i + (n + 1) + 1) := by
    simpa using Finset.single_le_prod
      (s := Finset.univ) (f := fun i : Fin (n + 1) ↦ fast i + (n + 1) + 1)
      (fun i _ ↦ by omega) (a := ⟨n, by omega⟩) (Finset.mem_univ _)
  rw [fast_eq (n + 1)]
  nlinarith

theorem fast_growth_iter (n k : ℕ) : fast n * 2 ^ k ≤ fast (n + k) := by
  induction k with
  | zero => simp
  | succ k ih =>
    have := fast_growth (n + k)
    rw [pow_succ]
    simpa only [Nat.add_succ] using (by nlinarith : fast n * (2 ^ k * 2) ≤ fast (n + k + 1))

theorem tail_term_bounds (b : ℕ → ℤ) (C n k : ℕ)
    (hb : ∀ i, |(b i : ℝ)| ≤ C) (hn : C ≤ n + 1) :
    0 < (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k)) ∧
    (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k)) ≤
      (2 / (fast n : ℝ)) * (1 / 2 : ℝ) ^ k := by
  have ha : (0 : ℝ) < fast n := by exact_mod_cast fast_pos n
  have hak : (0 : ℝ) < fast (n + k) := by exact_mod_cast fast_pos (n + k)
  have hl : (4 : ℝ) * (n + k + 1) ≤ fast (n + k) := by
    exact_mod_cast fast_lower (n + k)
  have hC : (C : ℝ) ≤ n + 1 := by exact_mod_cast hn
  have hbk : -(C : ℝ) ≤ b (n + k) := (abs_le.mp (hb (n + k))).1
  have hd : 0 < (fast (n + k) : ℝ) + b (n + k) := by nlinarith
  have hg : (fast n : ℝ) * (2 : ℝ) ^ k ≤ fast (n + k) := by
    exact_mod_cast fast_growth_iter n k
  constructor
  · push_cast
    exact one_div_pos.mpr hd
  · push_cast
    calc
      1 / ((fast (n + k) : ℝ) + b (n + k)) ≤ 2 / (fast (n + k) : ℝ) :=
        (div_le_div_iff₀ hd hak).mpr (by nlinarith)
      _ ≤ 2 / ((fast n : ℝ) * (2 : ℝ) ^ k) :=
        div_le_div_of_nonneg_left (by norm_num) (mul_pos ha (by positivity)) hg
      _ = (2 / (fast n : ℝ)) * (1 / 2 : ℝ) ^ k := by
        rw [div_pow, one_pow]
        field_simp

theorem tail_estimate (b : ℕ → ℤ) (C n : ℕ)
    (hb : ∀ i, |(b i : ℝ)| ≤ C) (hn : C ≤ n + 1) :
    Summable (fun k ↦ (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k))) ∧
    0 < ∑' k, (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k)) ∧
    (∑' k, (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k))) ≤
      4 / (fast n : ℝ) := by
  have hgeom : Summable (fun k : ℕ ↦ (2 / (fast n : ℝ)) * (1 / 2 : ℝ) ^ k) :=
    (summable_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)).mul_left _
  have hs := Summable.of_nonneg_of_le
    (fun k ↦ (tail_term_bounds b C n k hb hn).1.le)
    (fun k ↦ (tail_term_bounds b C n k hb hn).2) hgeom
  refine ⟨hs, hs.tsum_pos (fun k ↦ (tail_term_bounds b C n k hb hn).1.le) 0
    (tail_term_bounds b C n 0 hb hn).1, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, (2 / (fast n : ℝ)) * (1 / 2 : ℝ) ^ k :=
      hs.tsum_le_tsum (fun k ↦ (tail_term_bounds b C n k hb hn).2) hgeom
    _ = 4 / (fast n : ℝ) := by
      rw [tsum_mul_left, tsum_geometric_of_abs_lt_one (by norm_num : |(1 / 2 : ℝ)| < 1)]
      norm_num
      ring

theorem rational_gap (q r : ℚ) (h : q ≠ r) :
    1 ≤ |(q : ℝ) - r| * (q.den : ℝ) * (r.den : ℝ) := by
  have hd : (q - r).den ≤ q.den * r.den :=
    Nat.le_of_dvd (Nat.mul_pos q.pos r.pos) (Rat.sub_den_dvd q r)
  have hn : (q - r).num ≠ 0 := by
    exact Rat.num_ne_zero.mpr (sub_ne_zero.mpr h)
  have hab : (1 : ℝ) ≤ |((q - r).num : ℝ)| := by
    exact_mod_cast Int.one_le_abs hn
  have he : |(q : ℝ) - r| * ((q - r).den : ℝ) = |((q - r).num : ℝ)| := by
    rw [← abs_of_pos (show (0 : ℝ) < (q - r).den by exact_mod_cast (q - r).pos),
      ← abs_mul]
    congr 1
    exact_mod_cast Rat.mul_den_eq_num (q - r)
  have hd' : ((q - r).den : ℝ) ≤ (q.den : ℝ) * (r.den : ℝ) := by exact_mod_cast hd
  nlinarith [abs_nonneg ((q : ℝ) - r)]

theorem partial_den_bound (b : ℕ → ℤ) (C n : ℕ)
    (hb : ∀ i, (b i).natAbs ≤ C)
    (hz : ∀ i, (fast i : ℤ) + b i ≠ 0) :
    (∑ i ∈ range n, (1 : ℚ) / ((fast i : ℤ) + b i)).den ≤
      ∏ i ∈ range n, (fast i + C) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [sum_range_succ, prod_range_succ]
    have hd : ((1 : ℚ) / ((fast n : ℤ) + b n)).den ≤ fast n + C := by
      rw [one_div, ← Int.cast_add, Rat.inv_intCast_den, ite_eq_right (hz n)]
      exact (Int.natAbs_add_le _ _).trans (by simpa using Nat.add_le_add_left (hb n) (fast n))
    exact (Nat.le_of_dvd (by positivity) (Rat.add_den_dvd _ _)).trans (Nat.mul_le_mul ih hd)

theorem fast_strong : IsStrongIrrationalitySequence fast := by
  intro b hupper hlower hzero
  obtain ⟨U, hU⟩ := hupper
  obtain ⟨L, hL⟩ := hlower
  obtain ⟨C, hC⟩ := exists_nat_ge (max |(U : ℝ)| |(L : ℝ)|)
  have hb : ∀ i, |(b i : ℝ)| ≤ C := by
    intro i
    have hui : b i ≤ U := hU ⟨i, rfl⟩
    have hli : L ≤ b i := hL ⟨i, rfl⟩
    have hui' : (b i : ℝ) ≤ U := by exact_mod_cast hui
    have hli' : (L : ℝ) ≤ b i := by exact_mod_cast hli
    have hUc : |(U : ℝ)| ≤ C := (le_max_left _ _).trans hC
    have hLc : |(L : ℝ)| ≤ C := (le_max_right _ _).trans hC
    exact abs_le.mpr ⟨by linarith [neg_abs_le (L : ℝ)], by linarith [le_abs_self (U : ℝ)]⟩
  have hbNat : ∀ i, (b i).natAbs ≤ C := by
    intro i
    have hi := hb i
    rw [← Int.cast_abs, ← Int.natCast_natAbs, Int.cast_natCast] at hi
    exact_mod_cast hi
  have hz : ∀ i, (fast i : ℤ) + b i ≠ 0 := by
    intro i hi
    exact hzero ⟨i, hi⟩
  intro hrat
  obtain ⟨q, hq⟩ := hrat
  let n := C + q.den
  have hn : C ≤ n + 1 := by dsimp [n]; omega
  obtain ⟨hs, htpos, htbound⟩ := tail_estimate b C n hb hn
  let r : ℚ := ∑ i ∈ range n, (1 : ℚ) / ((fast i : ℤ) + b i)
  have hsall : Summable (fun i ↦ (1 : ℝ) / ((fast i : ℤ) + b i)) := by
    apply Summable.comp_nat_add (k := n)
    simpa only [Nat.add_comm] using hs
  have hsplit : (r : ℝ) + (∑' k, (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k))) = q := by
    have he := hsall.sum_add_tsum_nat_add n
    rw [← hq] at he
    simpa [r, Rat.cast_sum, Nat.add_comm] using he
  have hne : q ≠ r := by
    intro he
    have he' : (q : ℝ) = r := by exact_mod_cast he
    linarith
  have hr : r.den ≤ ∏ i ∈ range n, (fast i + n + 1) := by
    apply (partial_den_bound b C n hbNat hz).trans
    exact Finset.prod_le_prod (fun i _ ↦ by omega)
  have ha : (0 : ℝ) < fast n := by exact_mod_cast fast_pos n
  have hprod : (4 : ℝ) * (n + 1) * (r.den : ℝ) ≤ fast n := by
    have he := fast_eq n
    rw [Fin.prod_univ_eq_prod_range (fun i ↦ fast i + n + 1) n] at he
    have hh : 4 * (n + 1) * r.den ≤ fast n := by nlinarith
    exact_mod_cast hh
  have hnq : (q.den : ℝ) < n + 1 := by
    exact_mod_cast (show q.den < n + 1 by dsimp [n]; omega)
  have hrd : (0 : ℝ) < r.den := by exact_mod_cast r.pos
  have hqd : (0 : ℝ) < q.den := by exact_mod_cast q.pos
  have hgap := rational_gap q r hne
  have hab : |(q : ℝ) - r| = ∑' k, (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k)) := by
    rw [abs_of_pos (by linarith : 0 < (q : ℝ) - r)]
    linarith
  rw [hab] at hgap
  have htail : (∑' k, (1 : ℝ) / ((fast (n + k) : ℤ) + b (n + k))) * (fast n : ℝ) ≤ 4 :=
    (le_div_iff₀ ha).mp htbound
  have hmul := mul_le_mul_of_nonneg_left hprod htpos.le
  have hlt := mul_lt_mul_of_pos_left hnq (mul_pos htpos hrd)
  nlinarith

theorem statement : Statement := ⟨fast, fast_pos, fast_strong⟩

/-- Erdős Problem 264, existence form, in Mathlib vocabulary: some sequence of positive integers
keeps an irrational reciprocal sum under every bounded integer perturbation with nonzero
denominators. -/
theorem exists_irrationality_sequence :
    ∃ a : ℕ → ℕ, (∀ n, 0 < a n) ∧
      ∀ b : ℕ → ℤ, BddAbove (Set.range b) → BddBelow (Set.range b) →
        0 ∉ Set.range (fun n ↦ (a n : ℤ) + b n) →
        Irrational (∑' n, (1 : ℝ) / ((a n : ℤ) + b n)) :=
  statement

end Erdos264
