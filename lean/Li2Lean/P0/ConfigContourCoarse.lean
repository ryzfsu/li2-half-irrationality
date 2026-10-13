/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourSelfPotential
import Li2Lean.P0.ConfigContourTail
import Mathlib.Analysis.SpecialFunctions.Integrability.Log

open MeasureTheory
open scoped Interval

namespace Li2Lean.P0.ConfigContourCoarse

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourTail

/-- The squared distance to the literal ellipse, written in real coordinates. -/
def ellipseDistanceSq (z : ℂ) (u : ℝ) : ℝ :=
  (z.re - ellipseX u) ^ 2 + (z.im - ellipseY u) ^ 2

theorem analyticOnNhd_ellipseDistanceSq (z : ℂ) (s : Set ℝ) :
    AnalyticOnNhd ℝ (ellipseDistanceSq z) s := by
  unfold ellipseDistanceSq ellipseX ellipseY
  fun_prop

theorem ellipseDistanceSq_eq_norm_sq (z : ℂ) (u : ℝ) :
    ellipseDistanceSq z u = ‖z - Li2Lean.p0EllipsePoint 1 u‖ ^ 2 := by
  rw [Complex.sq_norm]
  simp only [ellipseDistanceSq, Li2Lean.p0EllipsePoint, Nat.cast_one,
    Complex.ofReal_one, one_mul, Complex.normSq_apply, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero, zero_add,
    neg_zero, ellipseX, ellipseY]
  ring

/-- The logarithmic kernel along the actual contour is integrable, including
the diagonal parameter where `Real.log 0 = 0` by convention.  The proof uses
the analytic squared distance, whose logarithmic singularities are integrable. -/
theorem intervalIntegrable_ellipse_log_distance (z : ℂ) :
    IntervalIntegrable
      (fun v : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖)
      volume 0 (2 * Real.pi) := by
  have hm : MeromorphicOn (ellipseDistanceSq z) (Set.uIcc 0 (2 * Real.pi)) :=
    (analyticOnNhd_ellipseDistanceSq z (Set.uIcc 0 (2 * Real.pi))).meromorphicOn
  have hsquare : IntervalIntegrable
      (fun v : ℝ => Real.log (ellipseDistanceSq z v)) volume 0 (2 * Real.pi) :=
    hm.intervalIntegrable_log
  have hfun : (fun v : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖) =
      fun v => (1 / 2 : ℝ) * Real.log (ellipseDistanceSq z v) := by
    funext v
    rw [ellipseDistanceSq_eq_norm_sq]
    rw [Real.log_pow]
    norm_num
    ring
  rw [hfun]
  exact hsquare.const_mul (1 / 2 : ℝ)

/-- A uniform upper estimate for the actual contour potential. -/
theorem contourReferencePotential_le_of_distance_bound
    (z : ℂ) {B : ℝ} (hB : 1 ≤ B)
    (hdist : ∀ v ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      ‖z - Li2Lean.p0EllipsePoint 1 v‖ ≤ B) :
    contourReferencePotential z ≤ ConfigContourSelfPotential.contourMass * Real.log B := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hlog : IntervalIntegrable
      (fun v : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖)
      volume 0 (2 * Real.pi) := intervalIntegrable_ellipse_log_distance z
  have hdensity : ContinuousOn contourDensity
      (Set.uIcc (0 : ℝ) (2 * Real.pi)) := continuous_density.continuousOn
  have hactual : IntervalIntegrable
      (fun v : ℝ => contourDensity v *
        Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖)
      volume 0 (2 * Real.pi) := hlog.continuousOn_mul hdensity
  have hmajor : IntervalIntegrable
      (fun v : ℝ => contourDensity v * Real.log B)
      volume 0 (2 * Real.pi) :=
    (continuous_density.mul continuous_const).intervalIntegrable _ _
  have hpoint : ∀ v ∈ Set.Icc (0 : ℝ) (2 * Real.pi),
      contourDensity v * Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖ ≤
        contourDensity v * Real.log B := by
    intro v hv
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
    by_cases hzero : ‖z - Li2Lean.p0EllipsePoint 1 v‖ = 0
    · simp [hzero]
      exact mul_nonneg (contourDensity_nonneg v) hlogB
    · have hnorm : 0 < ‖z - Li2Lean.p0EllipsePoint 1 v‖ :=
        lt_of_le_of_ne (norm_nonneg _) (Ne.symm hzero)
      exact mul_le_mul_of_nonneg_left
        (Real.log_le_log hnorm (hdist v hv)) (contourDensity_nonneg v)
  have hint := intervalIntegral.integral_mono_on hpi hactual hmajor hpoint
  have hmass : (∫ v in (0 : ℝ)..(2 * Real.pi), contourDensity v) =
      (2 * Real.pi) * ConfigContourSelfPotential.contourMass := by
    rw [ConfigFejerMass.integral_contourDensity,
      ConfigFejerMass.contourWeight_sum]
    norm_num [ConfigContourSelfPotential.contourMass]
  have hmajor_eq :
      (∫ v in (0 : ℝ)..(2 * Real.pi), contourDensity v * Real.log B) =
        Real.log B * ((2 * Real.pi) * ConfigContourSelfPotential.contourMass) := by
    rw [show (fun v : ℝ => contourDensity v * Real.log B) =
        fun v => Real.log B * contourDensity v by funext v; ring,
      intervalIntegral.integral_const_mul, hmass]
  unfold contourReferencePotential contourReferenceIntegral
  calc
    (2 * Real.pi)⁻¹ *
        (∫ v in (0 : ℝ)..(2 * Real.pi), contourDensity v *
          Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖) ≤
      (2 * Real.pi)⁻¹ *
        (∫ v in (0 : ℝ)..(2 * Real.pi), contourDensity v * Real.log B) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = ConfigContourSelfPotential.contourMass * Real.log B := by
      rw [hmajor_eq]
      have hpi_ne : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      field_simp

/-- Any two points on the literal ellipse are less than five units apart. -/
theorem ellipsePoint_distance_le_five (u v : ℝ) :
    ‖Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v‖ ≤ 5 := by
  have hre :
      (Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v).re =
        (12783 / 10000 : ℝ) * (Real.cos u - Real.cos v) := by
    simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one,
      one_mul, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero, zero_add, neg_zero]
    ring
  have him :
      (Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v).im =
        (229 / 200 : ℝ) * (Real.sin u - Real.sin v) := by
    simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one,
      one_mul, Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, mul_zero, sub_zero,
      add_zero, zero_add, neg_zero]
    ring
  have hcu : |Real.cos u| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos u, Real.cos_le_one u⟩
  have hcv : |Real.cos v| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_cos v, Real.cos_le_one v⟩
  have hsu : |Real.sin u| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin u, Real.sin_le_one u⟩
  have hsv : |Real.sin v| ≤ 1 :=
    abs_le.mpr ⟨Real.neg_one_le_sin v, Real.sin_le_one v⟩
  have hcos : |Real.cos u - Real.cos v| ≤ 2 := by
    calc
      |Real.cos u - Real.cos v| ≤ |Real.cos u| + |Real.cos v| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hsin : |Real.sin u - Real.sin v| ≤ 2 := by
    calc
      |Real.sin u - Real.sin v| ≤ |Real.sin u| + |Real.sin v| := abs_sub _ _
      _ ≤ 2 := by linarith
  have hreBound : |(Li2Lean.p0EllipsePoint 1 u -
      Li2Lean.p0EllipsePoint 1 v).re| ≤ (12783 / 10000 : ℝ) * 2 := by
    rw [hre, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 12783 / 10000)]
    exact mul_le_mul_of_nonneg_left hcos (by norm_num)
  have himBound : |(Li2Lean.p0EllipsePoint 1 u -
      Li2Lean.p0EllipsePoint 1 v).im| ≤ (229 / 200 : ℝ) * 2 := by
    rw [him, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 229 / 200)]
    exact mul_le_mul_of_nonneg_left hsin (by norm_num)
  calc
    ‖Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v‖ ≤
        |(Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v).re| +
          |(Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v).im| :=
      Complex.norm_le_abs_re_add_abs_im _
    _ ≤ (12783 / 10000 : ℝ) * 2 + (229 / 200 : ℝ) * 2 :=
      add_le_add hreBound himBound
    _ ≤ 5 := by norm_num

/-- A concrete, unconditional bound for the actual self-potential on the
literal contour.  This is a coarse semantic estimate, not the C-A row bound. -/
theorem contourSelfPotential_le_log_five (u : ℝ) :
    contourSelfPotential u ≤ ConfigContourSelfPotential.contourMass * Real.log 5 := by
  apply contourReferencePotential_le_of_distance_bound
    (Li2Lean.p0EllipsePoint 1 u) (by norm_num)
  intro v hv
  exact ellipsePoint_distance_le_five u v

end

end Li2Lean.P0.ConfigContourCoarse
