/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.Tube

namespace Li2Lean

noncomputable section

namespace ContourKit

/-- The P0 circle parametrization agrees with Mathlib's `circleMap`. -/
theorem p0CirclePoint_eq_circleMap (z : ℂ) (r t : ℝ) :
    P0.circlePoint z r t = circleMap z r t := by
  simp [P0.circlePoint, circleMap, mul_comm]

/-- The mean logarithmic distance to a point is the logarithm of the larger
of the circle radius and the center-to-point distance. -/
theorem circleAverage_log_norm_sub_const_eq_log_max (x z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    Real.circleAverage (fun y : ℂ => Real.log ‖y - x‖) z r =
      Real.log (max r ‖z - x‖) := by
  rw [circleAverage_log_norm_sub_const_eq_log_radius_add_posLog
    (a := x) (c := z) (R := r) hr.ne']
  have hdist : 0 ≤ ‖z - x‖ := norm_nonneg _
  have harg : 0 ≤ r⁻¹ * ‖z - x‖ :=
    mul_nonneg (inv_nonneg.mpr hr.le) hdist
  rw [Real.posLog_eq_log_max_one harg]
  have hmax : r * max 1 (r⁻¹ * ‖z - x‖) = max r ‖z - x‖ := by
    rcases le_total ‖z - x‖ r with hd | hd
    · have hquot : r⁻¹ * ‖z - x‖ ≤ 1 := by
        calc
          r⁻¹ * ‖z - x‖ = ‖z - x‖ / r := by rw [div_eq_mul_inv]; ring
          _ ≤ 1 := (div_le_one₀ hr).2 hd
      rw [max_eq_left hquot, max_eq_left hd]
      simp
    · have hquot : 1 ≤ r⁻¹ * ‖z - x‖ := by
        calc
          1 = r * r⁻¹ := by field_simp
          _ ≤ ‖z - x‖ * r⁻¹ := mul_le_mul_of_nonneg_right hd
            (inv_nonneg.mpr hr.le)
          _ = r⁻¹ * ‖z - x‖ := by ring
      rw [max_eq_right hquot, max_eq_right hd]
      calc
        r * (r⁻¹ * ‖z - x‖) = (r * r⁻¹) * ‖z - x‖ := by ring
        _ = ‖z - x‖ := by rw [mul_inv_cancel₀ hr.ne', one_mul]
  calc
    Real.log r + Real.log (max 1 (r⁻¹ * ‖z - x‖)) =
        Real.log (r * max 1 (r⁻¹ * ‖z - x‖)) := by
          rw [Real.log_mul (ne_of_gt hr)]
          · exact ne_of_gt (lt_of_lt_of_le zero_lt_one (le_max_left _ _))
    _ = Real.log (max r ‖z - x‖) := by rw [hmax]

/-- The ordinary interval-integral form of the circle-average identity. -/
theorem intervalAverage_log_norm_sub_const_eq_log_max (x z : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖x - circleMap z r t‖) /
        (2 * Real.pi) = Real.log (max r ‖x - z‖) := by
  have hmean := circleAverage_log_norm_sub_const_eq_log_max x z hr
  have hIntegral :
      (∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖x - circleMap z r t‖) =
        ∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖circleMap z r t - x‖ := by
    apply intervalIntegral.integral_congr
    intro t ht
    change Real.log ‖x - circleMap z r t‖ = Real.log ‖circleMap z r t - x‖
    rw [norm_sub_rev]
  calc
    (∫ t in (0 : ℝ)..(2 * Real.pi), Real.log ‖x - circleMap z r t‖) /
        (2 * Real.pi) =
      Real.circleAverage (fun y : ℂ => Real.log ‖y - x‖) z r := by
        rw [Real.circleAverage_def, smul_eq_mul, div_eq_mul_inv, hIntegral]
        ring
    _ = Real.log (max r ‖z - x‖) := hmean
    _ = Real.log (max r ‖x - z‖) := by rw [norm_sub_rev]

end ContourKit

end

end Li2Lean
