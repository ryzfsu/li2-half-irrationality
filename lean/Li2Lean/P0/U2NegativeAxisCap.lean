/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourCoarse
import Li2Lean.P0.ConfigContourTail

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Interval

namespace Li2Lean.P0.U2GlobalFejer

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourTail
open Li2Lean.P0.ConfigContourCoarse

/-- The real distance from `-t` to the literal ellipse is bounded below by
` t - leftClearance`; this is the negative-axis bridge needed below. -/
theorem negativeAxis_distance_lower {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) (u : ℝ) :
    t - leftClearance ≤ ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := by
  have hclear : 0 < t - leftClearance := by
    norm_num [leftClearance] at *
    linarith
  have hshift : 0 < t + ellipseX u := by
    have hx := ellipseX_lower u
    linarith
  have hsquare : ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ ^ 2 =
      (t + ellipseX u) ^ 2 + ellipseY u ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, neg_zero, ellipseX, ellipseY]
    ring
  have hnorm : 0 ≤ ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := norm_nonneg _
  have hright : t - leftClearance ≤ t + ellipseX u := by
    linarith [ellipseX_lower u]
  nlinarith [sq_nonneg (ellipseY u)]

/-- Distances from the negative axis increase with the axis parameter. -/
theorem negativeAxis_distance_mono {s t : ℝ}
    (hs : (1 / 2 : ℝ) ≤ s) (hst : s ≤ t) (u : ℝ) :
    ‖-(s : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ ≤
      ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := by
  have hss : 0 < s + ellipseX u := by
    have hx := ellipseX_lower u
    norm_num [leftClearance] at *
    linarith
  have htt : 0 < t + ellipseX u := by linarith
  have hsqS : ‖-(s : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ ^ 2 =
      (s + ellipseX u) ^ 2 + ellipseY u ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, neg_zero, ellipseX, ellipseY]
    ring
  have hsqT : ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ ^ 2 =
      (t + ellipseX u) ^ 2 + ellipseY u ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, neg_zero, ellipseX, ellipseY]
    ring
  have hsnon : 0 ≤ ‖-(s : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := norm_nonneg _
  have htnon : 0 ≤ ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := norm_nonneg _
  nlinarith

/-- The contour potential on the negative axis is bounded below by the
pointwise left-vertex logarithm. -/
theorem contourReferencePotential_neg_lower {t : ℝ}
    (ht : (1 / 2 : ℝ) ≤ t) :
    ConfigContourSelfPotential.contourMass * Real.log (t - leftClearance) ≤
      contourReferencePotential (-(t : ℂ)) := by
  have harg : 0 < t - leftClearance := by
    norm_num [leftClearance] at *
    linarith
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hlog := intervalIntegrable_ellipse_log_distance (-(t : ℂ))
  have hactual : IntervalIntegrable
      (fun u : ℝ => contourDensity u *
        Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖)
      volume 0 (2 * Real.pi) :=
    hlog.continuousOn_mul continuous_density.continuousOn
  have hmajor : IntervalIntegrable
      (fun u : ℝ => contourDensity u * Real.log (t - leftClearance))
      volume 0 (2 * Real.pi) :=
    (continuous_density.mul continuous_const).intervalIntegrable _ _
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      contourDensity u * Real.log (t - leftClearance) ≤
        contourDensity u * Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := by
    intro u hu
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log harg (negativeAxis_distance_lower ht u))
      (contourDensity_nonneg u)
  have hint := intervalIntegral.integral_mono_on hpi hmajor hactual hpoint
  have hmass : (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u) =
      (2 * Real.pi) * ConfigContourSelfPotential.contourMass := by
    rw [ConfigFejerMass.integral_contourDensity,
      ConfigFejerMass.contourWeight_sum]
    norm_num [ConfigContourSelfPotential.contourMass]
  unfold contourReferencePotential contourReferenceIntegral
  calc
    ConfigContourSelfPotential.contourMass * Real.log (t - leftClearance) =
        (2 * Real.pi)⁻¹ *
          (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u *
            Real.log (t - leftClearance)) := by
      rw [show (fun u : ℝ => contourDensity u * Real.log (t - leftClearance)) =
          fun u => Real.log (t - leftClearance) * contourDensity u by
            funext u; ring,
        intervalIntegral.integral_const_mul, hmass]
      have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp
    _ ≤ (2 * Real.pi)⁻¹ *
        (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u *
          Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖) :=
      mul_le_mul_of_nonneg_left hint (by positivity)

/-- Monotonicity of the negative-axis contour potential. -/
theorem contourReferencePotential_neg_mono {s t : ℝ}
    (hs : (1 / 2 : ℝ) ≤ s) (hst : s ≤ t) :
    contourReferencePotential (-(s : ℂ)) ≤
      contourReferencePotential (-(t : ℂ)) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hlogS := intervalIntegrable_ellipse_log_distance (-(s : ℂ))
  have hlogT := intervalIntegrable_ellipse_log_distance (-(t : ℂ))
  have hS : IntervalIntegrable
      (fun u : ℝ => contourDensity u *
        Real.log ‖-(s : ℂ) - Li2Lean.p0EllipsePoint 1 u‖)
      volume 0 (2 * Real.pi) :=
    hlogS.continuousOn_mul continuous_density.continuousOn
  have hT : IntervalIntegrable
      (fun u : ℝ => contourDensity u *
        Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖)
      volume 0 (2 * Real.pi) :=
    hlogT.continuousOn_mul continuous_density.continuousOn
  have hpoint : ∀ u ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      contourDensity u * Real.log ‖-(s : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ ≤
        contourDensity u * Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := by
    intro u hu
    have hd := negativeAxis_distance_mono hs hst u
    have hleft : 0 < s - leftClearance := by
      norm_num [leftClearance] at *
      linarith
    have hdspos : 0 < ‖-(s : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ :=
      lt_of_lt_of_le hleft (negativeAxis_distance_lower hs u)
    exact mul_le_mul_of_nonneg_left
      (Real.log_le_log hdspos hd) (contourDensity_nonneg u)
  have hint := intervalIntegral.integral_mono_on hpi hS hT hpoint
  unfold contourReferencePotential contourReferenceIntegral
  exact mul_le_mul_of_nonneg_left hint (by positivity)

end
end Li2Lean.P0.U2GlobalFejer
