/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.LogRectangle
import Li2Lean.P0.ConfigSelfJensen
import Li2Lean.P0.ConfigSelfCombinatorics

open MeasureTheory

namespace Li2Lean.P0.Config.SelfCells

noncomputable section

lemma secondPrimitive_nat (n : ℕ) :
    LogSegment.secondPrimitive (n : ℝ) = latticeH n := by
  simp only [LogSegment.secondPrimitive, latticeH, Real.log_abs]
  ring

lemma secondPrimitive_neg (x : ℝ) :
    LogSegment.secondPrimitive (-x) = LogSegment.secondPrimitive x := by
  simp [LogSegment.secondPrimitive]

lemma unitCellLog_eq (d : ℝ) :
    unitCellLog d = LogSegment.secondPrimitive (d + 1) +
      LogSegment.secondPrimitive (d - 1) - 2 * LogSegment.secondPrimitive d := by
  unfold unitCellLog
  rw [intervalIntegral.integral_comp_add_left
    (fun x : ℝ => ∫ v in (0 : ℝ)..1, Real.log |x - v|) d]
  rw [LogSegment.integral_integral_log_abs_sub]
  simp only [add_zero, sub_zero, add_sub_cancel_right]
  ring

lemma cellError_eq (n : ℕ) :
    cellError n = Real.log ((n + 1 : ℕ) : ℝ) - unitCellLog ((n + 1 : ℕ) : ℝ) := by
  rw [unitCellLog_eq]
  have ha : ((n + 1 : ℕ) : ℝ) + 1 = ((n + 2 : ℕ) : ℝ) := by push_cast; ring
  have hb : ((n + 1 : ℕ) : ℝ) - 1 = (n : ℝ) := by push_cast; ring
  rw [ha, hb]
  simp only [secondPrimitive_nat, cellError]

lemma cellError_nonneg (n : ℕ) : 0 ≤ cellError n := by
  rw [cellError_eq]
  exact sub_nonneg.mpr (unitCellLog_le_log _ (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le n)))

/-- The aggregate off-diagonal cell error for arbitrary finite lattice sites.
The original v10 budget is retained, without a range bound on the sites. -/
theorem cellError_double_sum_le (sites : Finset ℕ) :
    (∑ i ∈ sites, ∑ j ∈ sites,
      if i = j then 0 else cellError (Nat.dist i j - 1)) ≤
    (sites.card : ℝ) * (Real.log (2 * Real.pi) - 3 / 2) := by
  have h := distance_double_sum_le cellError cellErrorBudget cellError_nonneg
    sum_cellError_le sites
  convert h using 1 <;> simp only [cellErrorBudget] <;> ring

/-- Scaling of the continuous second primitive, including its value at zero. -/
lemma secondPrimitive_div (x m : ℝ) (hm : m ≠ 0) :
    m ^ 2 * LogSegment.secondPrimitive (x / m) =
      LogSegment.secondPrimitive x - x ^ 2 / 2 * Real.log m := by
  by_cases hx : x = 0
  · subst x
    simp
  · simp only [LogSegment.secondPrimitive, Real.log_abs, Real.log_div hx hm]
    field_simp
    ring

/-- The lattice distance is the absolute real difference of the sites. -/
lemma nat_dist_cast (i j : ℕ) : (Nat.dist i j : ℝ) = |(i : ℝ) - (j : ℝ)| := by
  rcases le_total i j with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (by exact_mod_cast h)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (by exact_mod_cast h)

lemma unitCellLog_neg (d : ℝ) : unitCellLog (-d) = unitCellLog d := by
  rw [unitCellLog_eq, unitCellLog_eq]
  have h₁ : -d + 1 = -(d - 1) := by ring
  have h₂ : -d - 1 = -(d + 1) := by ring
  rw [h₁, h₂, secondPrimitive_neg, secondPrimitive_neg, secondPrimitive_neg]
  ring

lemma unitCellLog_nat_dist (i j : ℕ) :
    unitCellLog ((i : ℝ) - (j : ℝ)) = unitCellLog (Nat.dist i j : ℝ) := by
  rw [nat_dist_cast]
  by_cases h : 0 ≤ (i : ℝ) - (j : ℝ)
  · rw [abs_of_nonneg h]
  · rw [abs_of_neg (lt_of_not_ge h), unitCellLog_neg]

@[simp] lemma unitCellLog_zero : unitCellLog 0 = -(3 / 2 : ℝ) := by
  rw [unitCellLog_eq]
  norm_num [LogSegment.secondPrimitive]

lemma unitCellLog_nat (n : ℕ) (hn : 0 < n) :
    unitCellLog (n : ℝ) = Real.log (n : ℝ) - cellError (n - 1) := by
  rw [cellError_eq, Nat.sub_add_cancel hn]
  ring

end

end Li2Lean.P0.Config.SelfCells
