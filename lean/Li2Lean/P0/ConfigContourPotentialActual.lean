/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourSelfPotentialActual

open MeasureTheory
open Filter
open scoped BigOperators Interval

namespace Li2Lean.P0.ConfigContourPotentialActual

noncomputable section

open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourSelfPotentialActual
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourExternalFourier
open Li2Lean.P0.ConfigContourExternalPOC
open Li2Lean.P0.ConfigContourAbelPOC
open Li2Lean.P0.ConfigFejerMass
open Li2Lean.P0.ConfigFejerLog

private theorem externalKernel_eq_correction (q u v : ℝ) :
    externalLogKernel q u v =
      Real.log ‖1 - (q : ℂ) / (phase u * phase v)‖ := by
  have hz : circleZeta (-(u + v)) = (phase u * phase v)⁻¹ := by
    rw [circleZeta_eq_phase]
    unfold phase
    rw [← Complex.exp_add, ← Complex.exp_neg]
    congr 1
    push_cast
    ring
  unfold externalLogKernel
  rw [hz]
  rfl

private theorem diagonalKernel_eq_phase_difference (u v : ℝ) :
    diagonalLogKernel u v = Real.log ‖phase u - phase v‖ := by
  simp [diagonalLogKernel, circleZeta_eq_phase]

private theorem diagonalKernel_symm (u v : ℝ) :
    diagonalLogKernel u v = diagonalLogKernel v u := by
  rw [diagonalKernel_eq_phase_difference, diagonalKernel_eq_phase_difference]
  rw [norm_sub_rev]

private theorem externalLogKernel_symm (q u v : ℝ) :
    externalLogKernel q u v = externalLogKernel q v u := by
  simp [externalLogKernel, add_comm]

/-- Circle-parameter collisions form a countable set.  On the integration
interval this is the diagonal together with its periodic endpoint copy. -/
private theorem phase_collision_countable (u : ℝ) :
    ({v : ℝ | phase v = phase u}).Countable := by
  have hsub : {v : ℝ | phase v = phase u} ⊆
      (fun n : ℤ => u + (n : ℝ) * (2 * Real.pi)) '' (Set.univ : Set ℤ) := by
    intro v hv
    have hZ : circleZeta v = circleZeta u := by
      rw [circleZeta_eq_phase, circleZeta_eq_phase]
      exact hv
    have hexp : Complex.exp (Complex.I * (v : ℂ)) =
        Complex.exp (Complex.I * (u : ℂ)) := hZ
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him := congrArg Complex.im hn
    have hv' : v = u + (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] using him
    exact ⟨n, by simp, hv'.symm⟩
  have himage :
      ((fun n : ℤ => u + (n : ℝ) * (2 * Real.pi)) ''
        (Set.univ : Set ℤ)).Countable := by
    simpa only [Set.image_univ] using
      Set.countable_range (fun n : ℤ => u + (n : ℝ) * (2 * Real.pi))
  exact himage.mono hsub

private theorem phase_ne_ae (u : ℝ) :
    ∀ᵐ v ∂volume, phase v ≠ phase u := by
  have hc := phase_collision_countable u
  simpa only [ae_iff, Classical.not_not] using hc.measure_zero volume

private theorem externalLogKernel_continuous (q u : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    Continuous (fun v : ℝ => externalLogKernel q u v) := by
  have hcont := ConfigFejerLog.continuous_log_norm (a := (q : ℂ)) hq
  have hEq : (fun v : ℝ => externalLogKernel q u v) =
      fun v => Real.log ‖1 - (q : ℂ) * phase (-(u + v))‖ := by
    funext v
    simp [externalLogKernel, circleZeta_eq_phase]
  rw [hEq]
  exact hcont.comp (continuous_neg.comp (continuous_const.add continuous_id))

/-- The literal contour potential can be integrated after splitting the
Joukowski logarithm off its collision set. -/
theorem contourReferencePotential_joukowski_split (u : ℝ) :
    contourSelfPotential u =
      contourMass * Real.log contourScale +
        (2 * Real.pi)⁻¹ *
          ((∫ v in (0 : ℝ)..(2 * Real.pi),
              contourDensity v * diagonalLogKernel u v) +
            (∫ v in (0 : ℝ)..(2 * Real.pi),
              contourDensity v * externalLogKernel contourRatio u v)) := by
  have hq : ‖(contourRatio : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg]
    exact contourRatio_lt_one
  have hdiag : IntervalIntegrable
      (fun v : ℝ => contourDensity v * diagonalLogKernel u v)
      volume (0 : ℝ) (2 * Real.pi) := by
    have hlog := DiagonalLogClassicalProbe.diagonalLogKernel_intervalIntegrable u
    have hmul := hlog.mul_continuousOn
      ConfigContourExternalPOC.contourDensity_continuous.continuousOn
    have hfun : (fun v : ℝ => contourDensity v * diagonalLogKernel u v) =
        fun v => diagonalLogKernel v u * contourDensity v := by
      funext v
      rw [diagonalKernel_symm]
      ring
    rw [hfun]
    exact hmul
  have hext : IntervalIntegrable
      (fun v : ℝ => contourDensity v * externalLogKernel contourRatio u v)
      volume (0 : ℝ) (2 * Real.pi) := by
    exact ((ConfigContourExternalPOC.contourDensity_continuous.mul
      (externalLogKernel_continuous contourRatio u hq)).intervalIntegrable _ _)
  have hconst : IntervalIntegrable
      (fun v : ℝ => contourDensity v * Real.log contourScale)
      volume (0 : ℝ) (2 * Real.pi) := by
    exact (ConfigContourExternalPOC.contourDensity_continuous.mul
      continuous_const).intervalIntegrable _ _
  have hsplit :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        contourDensity v *
          Real.log ‖Li2Lean.p0EllipsePoint 1 u -
            Li2Lean.p0EllipsePoint 1 v‖) =
      ∫ v in (0 : ℝ)..(2 * Real.pi),
        contourDensity v * Real.log contourScale +
          (contourDensity v * diagonalLogKernel u v +
            contourDensity v * externalLogKernel contourRatio u v) := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [phase_ne_ae u] with v hv
    intro hvI
    have hphase : phase u ≠ phase v := fun h => hv h.symm
    rw [ellipse_log_distance u v hphase,
      diagonalKernel_eq_phase_difference,
      externalKernel_eq_correction]
    ring
  rw [contourSelfPotential_eq_source_integral, hsplit,
    intervalIntegral.integral_add hconst (hdiag.add hext),
    intervalIntegral.integral_add hdiag hext,
    intervalIntegral.integral_mul_const,
    integral_contourDensity, contourMass_eq_source]
  field_simp

/-- Reindex the Abel boundary coefficient at natural index `n` as frequency
`n+1`; the zero-frequency term is zero under Lean's real division convention. -/
private theorem contourLogPolynomial_phase_neg_succ_sum (u : ℝ) :
    contourLogPolynomial (phase (-u)) =
      ∑ n ∈ Finset.range 48,
        contourFourierMoment (n + 1) * (1 / (n + 1 : ℝ)) *
          Real.cos ((n + 1 : ℝ) * u) := by
  rw [contourLogPolynomial_phase_neg]
  let f : ℕ → ℝ := fun n =>
    contourFourierMoment n * (1 / (n : ℝ)) *
      Real.cos ((n : ℝ) * u)
  have h := Finset.sum_range_succ' f 48
  have hzero : f 0 = 0 := by
    simp [f]
  rw [hzero, add_zero] at h
  convert h using 1 <;> simp [f, Nat.cast_add]

/-- Pointwise formula (5.5) for the actual v10 contour potential. -/
theorem contourSelfPotential_eq_fourier (u : ℝ) :
    contourSelfPotential u = contourSelfPotentialFourier u := by
  have hq : ‖(contourRatio : ℂ)‖ < 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg]
    exact contourRatio_lt_one
  have hext :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        contourDensity v * externalLogKernel contourRatio u v) =
      ∑ n ∈ Finset.range 48,
        (-(contourRatio ^ (n + 1) / (n + 1 : ℝ))) *
          (2 * Real.pi * contourFourierMoment (n + 1) *
            Real.cos ((n + 1 : ℝ) * u)) := by
    have hsymfun :
        (fun v : ℝ => contourDensity v *
          externalLogKernel contourRatio u v) =
        (fun v => contourDensity v *
          externalLogKernel contourRatio v u) := by
      funext v
      rw [externalLogKernel_symm contourRatio u v]
    rw [hsymfun]
    exact externalLogKernel_integral_eq_finite_moment contourRatio u hq
  have hdiag :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        contourDensity v * diagonalLogKernel u v) =
      -(2 * Real.pi) * contourLogPolynomial (phase (-u)) := by
    calc
      _ = ∫ v in (0 : ℝ)..(2 * Real.pi),
            contourDensity v * diagonalLogKernel v u := by
          congr 1
          funext v
          rw [diagonalKernel_symm]
      _ = _ := contourDensity_diagonalLog_integral u
  rw [contourReferencePotential_joukowski_split,
    hdiag, hext,
    contourLogPolynomial_phase_neg_succ_sum]
  unfold contourSelfPotentialFourier
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  rw [mul_add]
  rw [Finset.mul_sum]
  have hscale (S : ℝ) :
      (2 * Real.pi)⁻¹ * (-(2 * Real.pi) * S) = -S := by
    field_simp
  have hfirst :
      (2 * Real.pi)⁻¹ *
          (∑ i ∈ Finset.range 48,
            -(2 * Real.pi) *
              (contourFourierMoment (i + 1) * (1 / (i + 1 : ℝ)) *
                Real.cos ((i + 1 : ℝ) * u))) =
        -(∑ i ∈ Finset.range 48,
            contourFourierMoment (i + 1) * (1 / (i + 1 : ℝ)) *
              Real.cos ((i + 1 : ℝ) * u)) := by
    rw [← Finset.mul_sum, hscale]
  have hsecond :
      (2 * Real.pi)⁻¹ *
          (∑ n ∈ Finset.range 48,
            -(contourRatio ^ (n + 1) / (n + 1 : ℝ)) *
              (2 * Real.pi * contourFourierMoment (n + 1) *
                Real.cos ((n + 1 : ℝ) * u))) =
        ∑ n ∈ Finset.range 48,
          (2 * Real.pi)⁻¹ *
            (-(contourRatio ^ (n + 1) / (n + 1 : ℝ)) *
              (2 * Real.pi * contourFourierMoment (n + 1) *
                Real.cos ((n + 1 : ℝ) * u))) := by
    rw [Finset.mul_sum]
  rw [hfirst, hsecond, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  have hsum : ∀ n ∈ Finset.range 48,
      -(contourFourierMoment (n + 1) * (1 / (n + 1 : ℝ)) *
          Real.cos ((n + 1 : ℝ) * u)) +
        (2 * Real.pi)⁻¹ *
          (-(contourRatio ^ (n + 1) / (n + 1 : ℝ)) *
            (2 * Real.pi * contourFourierMoment (n + 1) *
              Real.cos ((n + 1 : ℝ) * u))) =
        -((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
          (n + 1 : ℝ) * Real.cos ((n + 1 : ℝ) * u)) := by
    intro n hn
    have hpi : (Real.pi : ℝ) ≠ 0 := ne_of_gt Real.pi_pos
    field_simp [hpi]
    ring
  rw [Finset.sum_congr rfl hsum]
  rw [Finset.sum_neg_distrib]
  ring

/-- The exact Fourier obligation for the literal contour is now witnessed by
the actual potential theorem, with no auxiliary certificate premise. -/
theorem contourSelfPotentialFourierObligation_holds :
    ContourSelfPotentialFourierObligation := by
  intro u
  exact contourSelfPotential_eq_fourier u

end

end Li2Lean.P0.ConfigContourPotentialActual

#print axioms Li2Lean.P0.ConfigContourPotentialActual.contourReferencePotential_joukowski_split
#print axioms Li2Lean.P0.ConfigContourPotentialActual.contourSelfPotential_eq_fourier
#print axioms Li2Lean.P0.ConfigContourPotentialActual.contourSelfPotentialFourierObligation_holds
