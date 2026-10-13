/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Config
import Li2Lean.P0.ConfigSelfKernel

open MeasureTheory

namespace Li2Lean.P0.Config.SelfCells

noncomputable section

/-- The literal logarithmic energy of two selected half-open cells. -/
def cellLogIntegral (m i j : ℕ) : ℝ :=
  ∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
    ∂((volume.restrict (pinnedCell m i)).prod (volume.restrict (pinnedCell m j)))

lemma pinnedCell_endpoints_le (m i : ℕ) :
    (i : ℝ) / (m : ℝ) ≤ ((i + 1 : ℕ) : ℝ) / (m : ℝ) := by
  apply div_le_div_of_nonneg_right
  · exact_mod_cast Nat.le_succ i
  · positivity

lemma integrable_cell_log (m i j : ℕ) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((volume.restrict (pinnedCell m i)).prod (volume.restrict (pinnedCell m j))) :=
  LogSegment.integrable_log_abs_sub_rectangle (pinnedCell_endpoints_le m j)

/-- Exact scale change for the logarithmic cell integral, including the
self-cell and adjacent-cell cases. -/
theorem cellLogIntegral_scaled (m : ℕ) (hm : 0 < m) (i j : ℕ) :
    (m : ℝ) ^ 2 * cellLogIntegral m i j =
      unitCellLog ((i : ℝ) - (j : ℝ)) - Real.log (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  unfold cellLogIntegral pinnedCell
  rw [LogSegment.integral_log_abs_sub_rectangle
    (pinnedCell_endpoints_le m i) (pinnedCell_endpoints_le m j)]
  have h₁ : ((i + 1 : ℕ) : ℝ) / m - (j : ℝ) / m =
      ((i : ℝ) - j + 1) / m := by push_cast; ring
  have h₂ : (i : ℝ) / m - (j : ℝ) / m = ((i : ℝ) - j) / m := by ring
  have h₃ : ((i + 1 : ℕ) : ℝ) / m - ((j + 1 : ℕ) : ℝ) / m =
      ((i : ℝ) - j) / m := by push_cast; ring
  have h₄ : (i : ℝ) / m - ((j + 1 : ℕ) : ℝ) / m =
      ((i : ℝ) - j - 1) / m := by push_cast; ring
  rw [h₁, h₂, h₃, h₄]
  rw [mul_add, mul_sub, mul_sub]
  rw [secondPrimitive_div _ _ hm0, secondPrimitive_div _ _ hm0,
    secondPrimitive_div _ _ hm0]
  rw [unitCellLog_eq]
  ring

/-- Product expansion for the actual finite cell measure. -/
lemma latticeCellMeasure_prod_eq (m : ℕ) (sites : Finset ℕ) :
    (latticeCellMeasure m sites).prod (latticeCellMeasure m sites) =
      ∑ i ∈ sites, ∑ j ∈ sites,
        (volume.restrict (pinnedCell m i)).prod (volume.restrict (pinnedCell m j)) := by
  unfold latticeCellMeasure
  rw [← Measure.sum_coe_finset sites, Measure.prod_sum, Measure.sum_fintype,
    Fintype.sum_prod_type]
  change (∑ i : sites, ∑ j : sites,
    (volume.restrict (pinnedCell m (i : ℕ))).prod
      (volume.restrict (pinnedCell m (j : ℕ)))) = _
  calc
    _ = ∑ i : sites, ∑ j ∈ sites,
        (volume.restrict (pinnedCell m (i : ℕ))).prod
          (volume.restrict (pinnedCell m j)) := by
      apply Finset.sum_congr rfl
      intro i hi
      exact Finset.sum_coe_sort sites
        (fun j : ℕ =>
          (volume.restrict (pinnedCell m (i : ℕ))).prod
            (volume.restrict (pinnedCell m j))
          : ℕ → Measure (ℝ × ℝ))
    _ = _ := Finset.sum_coe_sort sites
      (fun i : ℕ => ∑ j ∈ sites,
        (volume.restrict (pinnedCell m i)).prod
          (volume.restrict (pinnedCell m j)))

lemma integrable_latticeCellMeasure_log (m : ℕ) (sites : Finset ℕ) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((latticeCellMeasure m sites).prod (latticeCellMeasure m sites)) := by
  rw [latticeCellMeasure_prod_eq]
  apply integrable_finsetSum_measure.mpr
  intro i hi
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact integrable_cell_log m i j

/-- The actual Bochner integral, not a formal sum-valued proxy. -/
theorem latticeCellMeasure_log_eq (m : ℕ) (sites : Finset ℕ) :
    (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂((latticeCellMeasure m sites).prod (latticeCellMeasure m sites))) =
      ∑ i ∈ sites, ∑ j ∈ sites, cellLogIntegral m i j := by
  rw [latticeCellMeasure_prod_eq, integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    exact integral_finsetSum_measure (fun j hj => integrable_cell_log m i j)
  · intro i hi
    exact integrable_finsetSum_measure.mpr (fun j hj => integrable_cell_log m i j)

end

end Li2Lean.P0.Config.SelfCells
