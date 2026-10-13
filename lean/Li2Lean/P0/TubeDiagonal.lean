/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.CircleSmoothing

namespace Li2Lean.P0

noncomputable section

/-- The exact diagonal circle-energy correction in docs/6333 §4 (4.5). -/
theorem circlePairEnergy_self_eq_neg_log_radius (z : ℂ) {r : ℝ}
   (hr : 0 < r) :
   circlePairEnergy z z r = -Real.log r := by
 let twoPi : ℝ := 2 * Real.pi
 have htwoPi : twoPi ≠ 0 := by
   dsimp [twoPi]
   positivity
 have hpoint_norm (v : ℝ) : ‖circlePoint z r v - z‖ = r := by
   rw [circlePoint, add_sub_cancel_left, norm_mul, Complex.norm_real,
     Real.norm_of_nonneg hr.le, Complex.norm_exp_I_mul_ofReal, mul_one]
 have hmean (v : ℝ) :
     (∫ u in (0 : ℝ)..(2 * Real.pi),
       Real.log ‖circlePoint z r v - circlePoint z r u‖) / twoPi =
       Real.log r := by
   have h := ContourKit.intervalAverage_log_norm_sub_const_eq_log_max
     (x := circlePoint z r v) z hr
   rw [hpoint_norm v, max_self] at h
   simpa only [ContourKit.p0CirclePoint_eq_circleMap] using h
 have hinner (u : ℝ) :
     (∫ v in (0 : ℝ)..(2 * Real.pi),
       realLogKernel (circlePoint z r u) (circlePoint z r v)) =
       -twoPi * Real.log r := by
   have hkernel :
       (∫ v in (0 : ℝ)..(2 * Real.pi),
         realLogKernel (circlePoint z r u) (circlePoint z r v)) =
         -(∫ v in (0 : ℝ)..(2 * Real.pi),
           Real.log ‖circlePoint z r u - circlePoint z r v‖) := by
     rw [← intervalIntegral.integral_neg]
     apply intervalIntegral.integral_congr
     intro v hv
     simp [realLogKernel]
   rw [hkernel]
   have hraw := (div_eq_iff htwoPi).mp (hmean u)
   dsimp [twoPi] at hraw ⊢
   rw [hraw]
   ring
 have houter :
     (∫ u in (0 : ℝ)..(2 * Real.pi),
       ∫ v in (0 : ℝ)..(2 * Real.pi),
         realLogKernel (circlePoint z r u) (circlePoint z r v)) =
       -(twoPi ^ 2) * Real.log r := by
   calc
     _ = ∫ u in (0 : ℝ)..(2 * Real.pi), -twoPi * Real.log r := by
       apply intervalIntegral.integral_congr
       intro u hu
       exact hinner u
     _ = (2 * Real.pi) * (-twoPi * Real.log r) := by
       simp [intervalIntegral.integral_const]
       ring
     _ = -(twoPi ^ 2) * Real.log r := by
       dsimp [twoPi]
       ring
 unfold circlePairEnergy
 rw [houter]
 dsimp [twoPi]
 field_simp [show 2 * Real.pi ≠ 0 by positivity]
