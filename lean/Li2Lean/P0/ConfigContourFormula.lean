/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigFejerLog

/-!
# Closed formula for the actual v10 exterior contour potential

This is `nu_out` in `certificates/dual/check_dual.py`.  The theorem evaluates
the original integral against all 64 Fejer weights.  The square root is the
positive real root, and the entire frequency range `t >= 1/2` is included.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigContourFormula

noncomputable section

open ConfigContourReference ConfigContourKernel ConfigFejerMass ConfigFejerLog

def outsideRadius (t : ℝ) : ℝ :=
  (t + 11281 / 10000 +
    Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * contourScale ^ 2 * contourRatio)) / 2

def outsideParameter (t : ℝ) : ℝ := -contourScale / outsideRadius t

theorem outside_discriminant_nonneg {t : ℝ} (ht : 1 / 2 ≤ t) :
    0 ≤ (t + 11281 / 10000) ^ 2 - 4 * contourScale ^ 2 * contourRatio := by
  norm_num [contourScale, contourRatio]
  nlinarith [sq_nonneg (t - 1 / 2)]

theorem outsideRadius_gt_scale {t : ℝ} (ht : 1 / 2 ≤ t) :
    contourScale < outsideRadius t := by
  have hsq := Real.sq_sqrt (outside_discriminant_nonneg ht)
  have hn := Real.sqrt_nonneg
    ((t + 11281 / 10000) ^ 2 - 4 * contourScale ^ 2 * contourRatio)
  unfold outsideRadius
  norm_num only [contourScale, contourRatio] at *
  nlinarith

theorem outsideRadius_pos {t : ℝ} (ht : 1 / 2 ≤ t) :
    0 < outsideRadius t := contourScale_pos.trans (outsideRadius_gt_scale ht)

theorem outsideRadius_quadratic {t : ℝ} (ht : 1 / 2 ≤ t) :
    outsideRadius t ^ 2 - (t + 11281 / 10000) * outsideRadius t +
      contourScale ^ 2 * contourRatio = 0 := by
  have hsq := Real.sq_sqrt (outside_discriminant_nonneg ht)
  unfold outsideRadius
  nlinarith

theorem outsideParameter_norm_lt_one {t : ℝ} (ht : 1 / 2 ≤ t) :
    ‖(outsideParameter t : ℂ)‖ < 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, outsideParameter, abs_div,
    abs_neg, abs_of_pos contourScale_pos, abs_of_pos (outsideRadius_pos ht)]
  exact (div_lt_one (outsideRadius_pos ht)).mpr (outsideRadius_gt_scale ht)

theorem outsideCorrection_norm_lt_one {t : ℝ} (ht : 1 / 2 ≤ t) :
    ‖(contourRatio * outsideParameter t : ℂ)‖ < 1 := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg contourRatio_nonneg]
  have hp := outsideParameter_norm_lt_one ht
  nlinarith [norm_nonneg (outsideParameter t : ℂ), contourRatio_nonneg,
    contourRatio_lt_one]

theorem log_norm_inverse_phase (x u : ℝ) :
    Real.log ‖1 - (x : ℂ) / phase u‖ =
      Real.log ‖1 - (x : ℂ) * phase u‖ := by
  rw [div_eq_mul_inv, Complex.inv_eq_conj (norm_phase u)]
  have h : 1 - (x : ℂ) * (starRingEnd ℂ) (phase u) =
      (starRingEnd ℂ) (1 - (x : ℂ) * phase u) := by simp
  rw [h, Complex.norm_conj]

theorem outside_difference_factorization {t : ℝ} (ht : 1 / 2 ≤ t) (u : ℝ) :
    -(t : ℂ) - Li2Lean.p0EllipsePoint 1 u =
      -(outsideRadius t : ℂ) *
        (1 - (outsideParameter t : ℂ) * phase u) *
        (1 - (contourRatio * outsideParameter t : ℝ) / phase u) := by
  have hr : (outsideRadius t : ℂ) ≠ 0 := by
    exact_mod_cast ne_of_gt (outsideRadius_pos ht)
  have hquad : (outsideRadius t : ℂ) ^ 2 -
      ((t : ℂ) + 11281 / 10000) * (outsideRadius t : ℂ) +
      (contourScale : ℂ) ^ 2 * (contourRatio : ℂ) = 0 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) (outsideRadius_quadratic ht)
    push_cast at h
    exact h
  rw [ellipse_eq_joukowski]
  unfold outsideParameter
  push_cast
  field_simp [phase_ne_zero u, hr]
  linear_combination 10000 * phase u * hquad

theorem log_factor_ne_zero {a : ℂ} (ha : ‖a‖ < 1) (u : ℝ) :
    1 - a * phase u ≠ 0 := by
  intro heq
  have hnorm := congrArg norm (sub_eq_zero.mp heq)
  rw [norm_one, norm_mul, norm_phase, mul_one] at hnorm
  linarith

theorem outside_log_distance {t : ℝ} (ht : 1 / 2 ≤ t) (u : ℝ) :
    Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ =
      Real.log (outsideRadius t) +
        Real.log ‖1 - (outsideParameter t : ℂ) * phase u‖ +
        Real.log ‖1 - (contourRatio * outsideParameter t : ℝ) * phase u‖ := by
  have h1 := norm_ne_zero_iff.mpr (log_factor_ne_zero (outsideParameter_norm_lt_one ht) u)
  have h2 : ‖1 - (contourRatio * outsideParameter t : ℝ) / phase u‖ ≠ 0 := by
    rw [div_eq_mul_inv, Complex.inv_eq_conj (norm_phase u)]
    have heq : 1 - ((contourRatio * outsideParameter t : ℝ) : ℂ) *
        (starRingEnd ℂ) (phase u) =
        (starRingEnd ℂ) (1 - ((contourRatio * outsideParameter t : ℝ) : ℂ) * phase u) := by
      simp
    rw [heq, Complex.norm_conj]
    apply norm_ne_zero_iff.mpr
    simpa only [Complex.ofReal_mul] using
      log_factor_ne_zero (outsideCorrection_norm_lt_one ht) u
  rw [outside_difference_factorization ht, norm_mul, norm_mul, norm_neg,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos (outsideRadius_pos ht),
    Real.log_mul (mul_ne_zero (ne_of_gt (outsideRadius_pos ht)) h1) h2,
    Real.log_mul (ne_of_gt (outsideRadius_pos ht)) h1, log_norm_inverse_phase]

theorem continuous_contourDensity : Continuous contourDensity := by
  unfold contourDensity
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    (continuous_fejer48.comp (continuous_id.sub continuous_const))

/-- Evaluation of the actual contour reference on the entire negative
frequency axis, first in the complex Fejer polynomial form. -/
theorem contourReferencePotential_neg_polynomial (t : ℝ) (ht : 1 / 2 ≤ t) :
    contourReferencePotential (-(t : ℂ)) =
      (267885951940 / 1000000000000 : ℝ) * Real.log (outsideRadius t) -
        contourLogPolynomial (outsideParameter t : ℂ) -
        contourLogPolynomial ((contourRatio * outsideParameter t : ℝ) : ℂ) := by
  have h0 : IntervalIntegrable
      (fun u => contourDensity u * Real.log (outsideRadius t)) volume 0 (2 * Real.pi) :=
    (continuous_contourDensity.mul continuous_const).intervalIntegrable _ _
  have h1 : IntervalIntegrable
      (fun u => contourDensity u * Real.log ‖1 - (outsideParameter t : ℂ) * phase u‖)
      volume 0 (2 * Real.pi) :=
    (continuous_contourDensity.mul
      (continuous_log_norm (outsideParameter_norm_lt_one ht))).intervalIntegrable _ _
  have h2 : IntervalIntegrable
      (fun u => contourDensity u *
        Real.log ‖1 - ((contourRatio * outsideParameter t : ℝ) : ℂ) * phase u‖)
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    apply continuous_contourDensity.mul
    apply continuous_log_norm
    simpa only [Complex.ofReal_mul] using outsideCorrection_norm_lt_one ht
  unfold contourReferencePotential contourReferenceIntegral
  simp_rw [outside_log_distance ht, mul_add]
  rw [intervalIntegral.integral_add (h0.add h1) h2,
    intervalIntegral.integral_add h0 h1, intervalIntegral.integral_mul_const,
    integral_contourDensity, contourWeight_sum,
    integral_contourDensity_log_norm (outsideParameter_norm_lt_one ht),
    integral_contourDensity_log_norm (by
      simpa only [Complex.ofReal_mul] using outsideCorrection_norm_lt_one ht)]
  have hpi : 2 * Real.pi ≠ 0 := ne_of_gt (by positivity)
  field_simp
  ring

/-- The literal `nu_out(t)` formula in the v10 C-A checker.  The `n=0`
summand is zero, so this is precisely the checker sum over `n=1,...,48`.
No numerical or logarithmic-potential identity is a hypothesis. -/
theorem contourReferencePotential_neg (t : ℝ) (ht : 1 / 2 ≤ t) :
    contourReferencePotential (-(t : ℂ)) =
      (267885951940 / 1000000000000 : ℝ) * Real.log (outsideRadius t) -
        ∑ n ∈ Finset.range 49,
          ((1 + contourRatio ^ n) * contourMoment n / (n : ℝ)) *
            outsideParameter t ^ n := by
  rw [contourReferencePotential_neg_polynomial t ht,
    contourLogPolynomial_ofReal, contourLogPolynomial_ofReal, sub_sub,
    ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [mul_pow]
  ring

end

end Li2Lean.P0.ConfigContourFormula
