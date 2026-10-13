/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorSourceOutside

/-! # Almost-everywhere exterior Green control for the field's real sources -/

open MeasureTheory Complex

namespace Li2Lean.P0

noncomputable section

/-- Both strict source regions obey the exterior one-sweep Green inequality. -/
theorem ellipse_exterior_point_green_off_boundary {z x : ℂ} (hz : ellipseLevel z < 0)
    (hx : ellipseLevel x ≠ 0) (hzx : z ≠ x) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        realLogKernel (joukowski ζ) x) 0 1 ≤
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  rcases lt_or_gt_of_ne hx with hneg | hpos
  · exact ellipse_exterior_point_green hz hneg hzx
  · have h := exterior_poisson_point_green_inside (ellipseExteriorInverse_norm_gt_one hz) hpos
    have heq : Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
          realLogKernel (joukowski ζ) x) 0 1 =
        realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
      simpa only [joukowski_ellipseExteriorInverse, exteriorCorrection, not_lt_of_ge hz.le, ↓reduceIte] using h
    exact heq.le

/-- The real source line meets the ellipse at precisely two parameter values. -/
theorem ellipse_real_source_level_eq_zero_iff (s : ℝ) :
    ellipseLevel ((-s : ℝ) : ℂ) = 0 ↔
      s = semiMajor - center ∨ s = -semiMajor - center := by
  have hA : semiMajor ≠ 0 := by norm_num [semiMajor]
  simp only [ellipseLevel, Complex.ofReal_re, Complex.ofReal_im,
    zero_div, zero_pow (by decide : 2 ≠ 0), sub_zero]
  constructor
  · intro h
    have hf : (((-s - center) / semiMajor) - 1) * (((-s - center) / semiMajor) + 1) = 0 := by
      nlinarith
    rcases mul_eq_zero.mp hf with hp | hm
    · right
      have hd : (-s - center) / semiMajor = 1 := by linarith
      have he := (div_eq_iff hA).mp hd
      linarith
    · left
      have hd : (-s - center) / semiMajor = -1 := by linarith
      have he := (div_eq_iff hA).mp hd
      linarith
  · rintro (rfl | rfl) <;> field_simp [hA] <;> ring

/-- The complete real source line satisfies the exterior Green bound almost everywhere.
The only excluded source parameters are the two ellipse intersections and a possible collision.
This covers the literal `[-1/2,0]` logarithmic source segment of `phi`. -/
theorem ellipse_exterior_real_source_green_ae {z : ℂ} (hz : ellipseLevel z < 0) :
    ∀ᵐ s : ℝ ∂volume,
      Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
          realLogKernel (joukowski ζ) ((-s : ℝ) : ℂ)) 0 1 ≤
        realLogKernel z ((-s : ℝ) : ℂ) + exteriorCorrection ellipseExteriorInverse z := by
  filter_upwards [volume.ae_ne (semiMajor - center), volume.ae_ne (-semiMajor - center),
    volume.ae_ne (-z.re)] with s hs₁ hs₂ hs₃
  apply ellipse_exterior_point_green_off_boundary hz
  · intro h
    rcases (ellipse_real_source_level_eq_zero_iff s).mp h with h | h
    · exact hs₁ h
    · exact hs₂ h
  · intro h
    apply hs₃
    have hr := congrArg Complex.re h
    simp only [Complex.ofReal_re] at hr
    linarith

/-- The favorable sign for the logarithmic part of `-phi`, with no finite source discretization. -/
theorem ellipse_exterior_phi_source_log_ae {z : ℂ} (hz : ellipseLevel z < 0) :
    ∀ᵐ s : ℝ ∂volume,
      Real.log ‖z + (s : ℂ)‖ - exteriorCorrection ellipseExteriorInverse z ≤
        Real.circleAverage
          (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
            Real.log ‖joukowski ζ + (s : ℂ)‖) 0 1 := by
  filter_upwards [ellipse_exterior_real_source_green_ae hz] with s hs
  have h := Real.circleAverage_fun_smul (a := (-1 : ℝ))
    (f := fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
      Real.log ‖joukowski ζ + (s : ℂ)‖) (c := (0 : ℂ)) (R := 1)
  have hn : Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        realLogKernel (joukowski ζ) ((-s : ℝ) : ℂ)) 0 1 =
      -Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
          Real.log ‖joukowski ζ + (s : ℂ)‖) 0 1 := by
    simpa only [realLogKernel, Complex.ofReal_neg, sub_neg_eq_add,
      smul_eq_mul, neg_one_mul, mul_neg] using h
  rw [hn] at hs
  simp only [realLogKernel, Complex.ofReal_neg, sub_neg_eq_add] at hs
  linarith

end
end Li2Lean.P0
