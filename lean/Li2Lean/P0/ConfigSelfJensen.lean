/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.LogSegment
import Li2Lean.P0.ConfigSelfStirling

open MeasureTheory

namespace Li2Lean.P0.Config.SelfCells

noncomputable section

/-- The literal unit-cell logarithmic average `J_d` in v10. -/
def unitCellLog (d : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..1, ∫ v in (0 : ℝ)..1, Real.log |d + u - v|

lemma log_cell_le_affine {d u v : ℝ} (hd : 1 ≤ d)
    (hu : u ∈ Set.Ioo (0 : ℝ) 1) (hv : v ∈ Set.Ioo (0 : ℝ) 1) :
    Real.log |d + u - v| ≤ Real.log d + (u - v) / d := by
  have hdpos : 0 < d := by linarith
  have hpos : 0 < d + u - v := by linarith [hu.1, hv.2]
  have h := Real.log_le_sub_one_of_pos (div_pos hpos hdpos)
  rw [Real.log_div hpos.ne' hdpos.ne'] at h
  have heq : (d + u - v) / d - 1 = (u - v) / d := by
    field_simp
    ring
  rw [heq] at h
  simpa only [Real.log_abs] using (by linarith : Real.log (d + u - v) ≤ Real.log d + (u - v) / d)

lemma integral_cell_affine (d u : ℝ) :
    (∫ v in (0 : ℝ)..1, Real.log d + (u - v) / d) =
      Real.log d + (u - 1 / 2) / d := by
  have hc : IntervalIntegrable (fun _ : ℝ => u) volume 0 1 := intervalIntegrable_const
  have hi : IntervalIntegrable (fun v : ℝ => v) volume 0 1 := continuous_id.intervalIntegrable _ _
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hc.sub hi).div_const d),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_sub hc hi, intervalIntegral.integral_const, integral_id]
  norm_num

lemma integral_cell_affine_outer (d : ℝ) :
    (∫ u in (0 : ℝ)..1, Real.log d + (u - 1 / 2) / d) = Real.log d := by
  have hi : IntervalIntegrable (fun u : ℝ => u) volume 0 1 := continuous_id.intervalIntegrable _ _
  have hc : IntervalIntegrable (fun _ : ℝ => (1 / 2 : ℝ)) volume 0 1 := intervalIntegrable_const
  rw [intervalIntegral.integral_add intervalIntegrable_const ((hi.sub hc).div_const d),
    intervalIntegral.integral_const, intervalIntegral.integral_div,
    intervalIntegral.integral_sub hi hc, intervalIntegral.integral_const, integral_id]
  norm_num

/-- Jensen's one-sided comparison includes adjacent cells. The only
singular corner is an endpoint null set, handled by the Ioo comparison
theorem rather than by imposing separation of the selected sites. -/
theorem unitCellLog_le_log (d : ℝ) (hd : 1 ≤ d) : unitCellLog d ≤ Real.log d := by
  have houter : IntervalIntegrable
      (fun u => ∫ v in (0 : ℝ)..1, Real.log |d + u - v|) volume 0 1 :=
    ((LogSegment.continuous_integral_log_abs_sub 0 1).comp
      (continuous_const.add continuous_id)).intervalIntegrable _ _
  have hright : IntervalIntegrable
      (fun u : ℝ => Real.log d + (u - 1 / 2) / d) volume 0 1 :=
    (continuous_const.add ((continuous_id.sub continuous_const).div_const d)).intervalIntegrable _ _
  calc
    unitCellLog d ≤ ∫ u in (0 : ℝ)..1, Real.log d + (u - 1 / 2) / d := by
      apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num) houter hright
      intro u hu
      calc
        (∫ v in (0 : ℝ)..1, Real.log |d + u - v|) ≤
            ∫ v in (0 : ℝ)..1, Real.log d + (u - v) / d := by
          apply intervalIntegral.integral_mono_on_of_le_Ioo (by norm_num)
            (LogSegment.intervalIntegrable_log_abs_sub (d + u) 0 1)
            ((continuous_const.add ((continuous_const.sub continuous_id).div_const d)).intervalIntegrable _ _)
          intro v hv
          exact log_cell_le_affine hd hu hv
        _ = Real.log d + (u - 1 / 2) / d := integral_cell_affine d u
    _ = Real.log d := integral_cell_affine_outer d

end

end Li2Lean.P0.Config.SelfCells
