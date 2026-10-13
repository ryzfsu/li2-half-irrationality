/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourAbelPOC
import Li2Lean.P0.ConfigContourExternalFourierFejer
import Li2Lean.P0.ConfigContourKernel
import Li2Lean.P0.ConfigFejerLog
import Li2Lean.DiagonalLogClassicalProbe

open MeasureTheory
open scoped BigOperators Interval
open Filter

namespace Li2Lean.P0.ConfigContourSelfPotentialActual

noncomputable section

open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
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
    rw [← Complex.exp_add]
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  unfold externalLogKernel
  rw [hz]
  rfl

private theorem diagonalKernel_eq_phase_difference (u v : ℝ) :
    diagonalLogKernel u v = Real.log ‖phase u - phase v‖ := by
  simp [diagonalLogKernel, circleZeta_eq_phase]

private theorem contourLogPolynomial_continuous (v : ℝ) :
    Continuous (fun r : ℝ =>
      contourLogPolynomial ((r : ℂ) * phase (-v))) := by
  unfold contourLogPolynomial fejerLogPolynomial
  fun_prop

/-- The literal Appendix A contour polynomial on the unit circle is exactly
the cosine series of the actual degree-48 Fejer moments.  The `range 49`
includes frequency zero, whose coefficient vanishes by the real convention
`1 / 0 = 0`; all nonzero frequencies are precisely 1 through 48 as in
v10 (5.5). -/
theorem contourLogPolynomial_phase_neg (u : ℝ) :
    contourLogPolynomial (phase (-u)) =
      ∑ n ∈ Finset.range 49,
        contourFourierMoment n * ((1 : ℝ) / (n : ℝ)) *
          Real.cos ((n : ℝ) * u) := by
  have harg (j : Fin 64) :
      phase (-u) * phase (contourAngle j) =
        (1 : ℂ) * phase (contourAngle j - u) := by
    unfold phase
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  unfold contourLogPolynomial
  have hterm (j : Fin 64) :
      (fejerLogPolynomial (phase (-u) * phase (contourAngle j))).re =
        ∑ n ∈ Finset.range 49,
          (1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
            Real.cos ((n : ℝ) * (contourAngle j - u)) := by
    rw [harg]
    simpa [Complex.ofReal_one] using
      (fejerLogPolynomial_ofReal_re (1 : ℝ) (contourAngle j - u))
  simp_rw [hterm]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Finset.mem_range] at hn
  have hangle (j : Fin 64) :
      (n : ℝ) * (contourAngle j - u) =
        (n : ℝ) * contourAngle j - (n : ℝ) * u := by ring
  simp_rw [hangle, Real.cos_sub]
  by_cases hn48 : n ≤ 48
  · have hsin0 :
        (∑ j : Fin 64, contourWeight j *
          Real.sin ((n : ℝ) * contourAngle j)) = 0 := by
      simpa [contourSineFourierMoment] using
        contourSineFourierMoment_eq_zero n
    have hcos :
        (∑ j : Fin 64, contourWeight j *
          ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
            (Real.cos ((n : ℝ) * contourAngle j) *
              Real.cos ((n : ℝ) * u)))) =
          ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
            Real.cos ((n : ℝ) * u) *
              (∑ j : Fin 64, contourWeight j *
                Real.cos ((n : ℝ) * contourAngle j)) := by
      calc
        _ = ∑ j : Fin 64,
            ((((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
              Real.cos ((n : ℝ) * u)) *
              (contourWeight j * Real.cos ((n : ℝ) * contourAngle j))) := by
          apply Finset.sum_congr rfl
          intro j hj
          ring
        _ = _ := by rw [Finset.mul_sum]
    have hsine :
        (∑ j : Fin 64, contourWeight j *
          ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
            (Real.sin ((n : ℝ) * contourAngle j) *
              Real.sin ((n : ℝ) * u)))) = 0 := by
      calc
        _ = ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
              Real.sin ((n : ℝ) * u) *
              (∑ j : Fin 64, contourWeight j *
                Real.sin ((n : ℝ) * contourAngle j)) := by
          calc
            _ = ∑ j : Fin 64,
                (((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
                  Real.sin ((n : ℝ) * u)) *
                  (contourWeight j *
                    Real.sin ((n : ℝ) * contourAngle j)) := by
              apply Finset.sum_congr rfl
              intro j hj
              ring
            _ = _ := by rw [Finset.mul_sum]
        _ = 0 := by rw [hsin0]; ring
    calc
      _ = (∑ j : Fin 64, contourWeight j *
            ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
              (Real.cos ((n : ℝ) * contourAngle j) *
                Real.cos ((n : ℝ) * u)))) +
          ∑ j : Fin 64, contourWeight j *
            ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ)) *
              (Real.sin ((n : ℝ) * contourAngle j) *
                Real.sin ((n : ℝ) * u))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = ((1 - (n : ℝ) / 49) * ((1 : ℝ) ^ n / (n : ℝ))) *
            Real.cos ((n : ℝ) * u) *
              (∑ j : Fin 64, contourWeight j *
                Real.cos ((n : ℝ) * contourAngle j)) := by
        rw [hcos, hsine]
        ring
      _ = contourFourierMoment n * ((1 : ℝ) / (n : ℝ)) *
            Real.cos ((n : ℝ) * u) := by
        unfold contourFourierMoment K48Coeff
        simp only [if_pos hn48, one_pow]
        ring
  · omega


/-- The logarithmic unit-circle kernel is integrable against the literal
Fejer density, and its integral is the Abel limit of the finite polynomial.
This treats the diagonal singularity by the established Abel/DCT argument. -/
theorem contourDensity_diagonalLog_integral (v : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * diagonalLogKernel u v) =
      -(2 * Real.pi) * contourLogPolynomial (phase (-v)) := by
  have hg : Continuous contourDensity := contourDensity_continuous
  have hlim := diagonalAbel_weighted_limit contourDensity hg v
  have heq : (fun r : ℝ =>
      ∫ u in (0 : ℝ)..(2 * Real.pi),
        diagonalAbelKernel r u v * contourDensity u) =ᶠ[
          nhdsWithin (1 : ℝ) (Set.Iio 1)] (fun r : ℝ =>
      -(2 * Real.pi) * contourLogPolynomial ((r : ℂ) * phase (-v))) := by
    filter_upwards [show ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
        0 ≤ r ∧ r < 1 by
      filter_upwards [self_mem_nhdsWithin,
        mem_nhdsWithin_of_mem_nhds
          (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hpos
      exact ⟨le_of_lt hpos, hr⟩] with r ⟨hr0, hr1⟩
    have hrnorm : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    simpa [mul_comm] using contourDensity_diagonalAbel_integral hrnorm v
  have hlim' := hlim.congr' heq
  have hp := contourLogPolynomial_continuous v
  have hpt : Tendsto (fun r : ℝ =>
      -(2 * Real.pi) * contourLogPolynomial ((r : ℂ) * phase (-v)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (-(2 * Real.pi) * contourLogPolynomial (phase (-v)))) := by
    have ht : Tendsto (fun r : ℝ => contourLogPolynomial ((r : ℂ) * phase (-v)))
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (contourLogPolynomial (phase (-v)))) := by
      convert (hp.continuousAt : ContinuousAt
        (fun r : ℝ => contourLogPolynomial ((r : ℂ) * phase (-v))) (1 : ℝ)).tendsto.mono_left
          (nhdsWithin_le_nhds :
            nhdsWithin (1 : ℝ) (Set.Iio 1) ≤ nhds (1 : ℝ)) using 1 <;> simp
    simpa using (tendsto_const_nhds.mul ht)
  have huniq := tendsto_nhds_unique hlim' hpt
  simpa [mul_comm, diagonalKernel_eq_phase_difference] using huniq

end

end Li2Lean.P0.ConfigContourSelfPotentialActual

#print axioms Li2Lean.P0.ConfigContourSelfPotentialActual.contourLogPolynomial_phase_neg
#print axioms Li2Lean.P0.ConfigContourSelfPotentialActual.contourDensity_diagonalLog_integral
