/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourPotentialActual
import Li2Lean.P0.ConfigContourCoarse
import Li2Lean.P0.ConfigContourMeasure
import Li2Lean.P0.ConfigContourProduct
import Li2Lean.P0.ContourProductIntegrability
import Li2Lean.P0.DualL6Variations

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Interval

namespace Li2Lean.P0.U2GlobalFejer

noncomputable section

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourPotentialActual
open Li2Lean.P0.ConfigContourMeasure
open Li2Lean.P0.ConfigContourCoarse
open Li2Lean.P0.ConfigContourProduct
open Li2Lean.P0.ConfigContourProductIntegrability
open Li2Lean.P0.L6Variations

/-- The literal Fejer contour mass times a coarse Fourier lower-bound cost. -/
def contourPotentialLowerCost : ℝ :=
  contourMass * |Real.log contourScale| + 96 * contourMass

private theorem contourFourierMoment_abs_le (n : ℕ) :
    |contourFourierMoment n| ≤ contourMass := by
  unfold contourFourierMoment K48Coeff
  by_cases hn : n ≤ 48
  · simp only [if_pos hn]
    have hcoef0 : 0 ≤ 1 - (n : ℝ) / 49 := by
      have hn' : (n : ℝ) ≤ 49 := by exact_mod_cast (Nat.le_succ_of_le hn)
      linarith
    have hcoef1 : 1 - (n : ℝ) / 49 ≤ 1 := by
      have hn0 : 0 ≤ (n : ℝ) := by positivity
      linarith
    have hsum :
        |∑ j : Fin 64, contourWeight j * Real.cos ((n : ℝ) * contourAngle j)| ≤
          contourMass := by
      calc
        |∑ j : Fin 64, contourWeight j * Real.cos ((n : ℝ) * contourAngle j)| ≤
            ∑ j : Fin 64, |contourWeight j * Real.cos ((n : ℝ) * contourAngle j)| :=
          Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin 64, contourWeight j := by
          apply Finset.sum_le_sum
          intro j hj
          rw [abs_mul, abs_of_nonneg (contourWeight_nonneg j)]
          exact mul_le_of_le_one_right (contourWeight_nonneg j)
            (Real.abs_cos_le_one _)
        _ = contourMass := contourMass_eq_source.symm
    rw [abs_mul]
    have hc : 0 ≤ 1 - (n : ℝ) / 49 := hcoef0
    have hc' : |1 - (n : ℝ) / 49| = 1 - (n : ℝ) / 49 := abs_of_nonneg hc
    rw [hc']
    calc
      (1 - (n : ℝ) / 49) *
          |∑ j : Fin 64, contourWeight j * Real.cos ((n : ℝ) * contourAngle j)| ≤
          1 * contourMass := by
            exact mul_le_mul hcoef1 hsum (by positivity) (by positivity)
      _ = contourMass := by ring
  · simp only [if_neg hn, abs_zero]
    norm_num [contourMass]

private theorem contourPotentialFourier_lower (u : ℝ) :
    -contourPotentialLowerCost ≤ contourSelfPotentialFourier u := by
  unfold contourSelfPotentialFourier contourPotentialLowerCost
  have hmass : 0 ≤ contourMass := by norm_num [contourMass]
  have hscale : -(contourMass * |Real.log contourScale|) ≤
      contourMass * Real.log contourScale := by
    have h := neg_abs_le (Real.log contourScale)
    nlinarith
  have hterm : ∀ n ∈ Finset.range 48,
      |((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
          (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u)| ≤ 2 * contourMass := by
    intro n hn
    have hnpos : 0 < (n + 1 : ℝ) := by positivity
    have hq0 : 0 ≤ contourRatio ^ (n + 1) :=
      pow_nonneg contourRatio_nonneg _
    have hq1 : contourRatio ^ (n + 1) ≤ 1 := by
      exact pow_le_one₀ contourRatio_nonneg (by norm_num [contourRatio])
    have hm := contourFourierMoment_abs_le (n + 1)
    have hcos : |Real.cos ((n + 1 : ℝ) * u)| ≤ 1 := Real.abs_cos_le_one _
    have hfac : 0 ≤ (1 + contourRatio ^ (n + 1)) /
        (n + 1 : ℝ) := by positivity
    have hfac2 : (1 + contourRatio ^ (n + 1)) /
        (n + 1 : ℝ) ≤ 2 := by
      have hden : (1 : ℝ) ≤ (n + 1 : ℝ) := by norm_num
      have hnum : 1 + contourRatio ^ (n + 1) ≤ 2 := by linarith
      apply (div_le_iff₀ hnpos).2
      nlinarith [hnum]
    have habs :
        |((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
          (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u)| ≤ 2 * contourMass := by
      rw [abs_mul, abs_div, abs_mul,
        abs_of_nonneg (by positivity : 0 ≤ 1 + contourRatio ^ (n + 1)),
        abs_of_pos (by positivity : 0 < (n + 1 : ℝ))]
      have hnum : (1 + contourRatio ^ (n + 1)) *
          |contourFourierMoment (n + 1)| ≤ 2 * contourMass := by
        exact le_trans (mul_le_mul_of_nonneg_left hm (by linarith))
          (by nlinarith [hmass])
      have hden : 0 < (n + 1 : ℝ) := by positivity
      calc
        ((1 + contourRatio ^ (n + 1)) * |contourFourierMoment (n + 1)| /
            (n + 1 : ℝ)) * |Real.cos ((n + 1 : ℝ) * u)| ≤
            ((1 + contourRatio ^ (n + 1)) * |contourFourierMoment (n + 1)| /
              (n + 1 : ℝ)) * 1 := by
                exact mul_le_mul_of_nonneg_left hcos (by positivity)
        _ ≤ 2 * contourMass := by
          rw [mul_one]
          apply (div_le_iff₀ hden).2
          nlinarith [hnum]
    exact habs
  have hsum :
      ∑ n ∈ Finset.range 48,
          ((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
            (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u) ≤
        ∑ n ∈ Finset.range 48, 2 * contourMass := by
    apply Finset.sum_le_sum
    intro n hn
    exact le_trans (le_abs_self _) (hterm n hn)
  have hcount : (∑ _n ∈ Finset.range 48, (2 * contourMass : ℝ)) =
      96 * contourMass := by norm_num; ring
  rw [hcount] at hsum
  nlinarith [hscale, hsum]

/-- The signed logarithmic potential on the literal contour has a uniform
coarse lower bound obtained from the finite degree-48 Fejer polynomial. -/
theorem contourReferencePotential_lower_on_ellipse (u : ℝ) :
    -contourPotentialLowerCost ≤
      contourReferencePotential (Li2Lean.p0EllipsePoint 1 u) := by
  simpa [contourSelfPotential] using
    (contourPotentialFourier_lower u).trans_eq
      (ConfigContourPotentialActual.contourSelfPotential_eq_fourier u).symm

end
end Li2Lean.P0.U2GlobalFejer

namespace Li2Lean.P0.U2GlobalFejer

open Li2Lean.P0.L6Variations

private lemma posLog_inv_le_log_sub {r B : ℝ} (hB : 1 ≤ B)
    (hr : 0 ≤ r) (hrB : r ≤ B) :
    Real.posLog r⁻¹ ≤ Real.log B - Real.log r := by
  by_cases hr0 : r = 0
  · subst r
    simp only [inv_zero, Real.log_zero, Real.posLog]
    simpa [Real.posLog] using (Real.log_nonneg hB)
  · have hrpos : 0 < r := lt_of_le_of_ne hr (Ne.symm hr0)
    have hlogB : 0 ≤ Real.log B := Real.log_nonneg hB
    have hlogr : Real.log r ≤ Real.log B := Real.log_le_log hrpos hrB
    change max 0 (Real.log r⁻¹) ≤ Real.log B - Real.log r
    rw [Real.log_inv]
    by_cases hlog : 0 ≤ Real.log r
    · rw [max_eq_left (by linarith)]
      linarith
    · rw [max_eq_right (by linarith)]
      linarith

private theorem lintegral_l6PosKernel_le_of_log_bound
    (ν : Measure ℂ) [IsFiniteMeasure ν] (z : ℂ)
    {B : ℝ} (hB : 1 ≤ B)
    (hAtom : ν {z} = 0)
    (hInt : Integrable (fun w : ℂ => Real.log ‖z - w‖) ν)
    (hDist : ∀ᵐ w ∂ν, ‖z - w‖ ≤ B) :
    (∫⁻ w, l6PosKernel z w ∂ν) ≤
      ENNReal.ofReal (∫ w, Real.log B - Real.log ‖z - w‖ ∂ν) := by
  have hmeas : Measurable (fun w : ℂ => Real.log ‖z - w‖) := by
    exact Real.measurable_log.comp (by fun_prop)
  have hG : Integrable (fun w : ℂ => Real.log B - Real.log ‖z - w‖) ν := by
    exact (integrable_const (Real.log B)).sub hInt
  have hGnonneg : ∀ᵐ w ∂ν, 0 ≤ Real.log B - Real.log ‖z - w‖ := by
    filter_upwards [hDist] with w hw
    by_cases hz : ‖z - w‖ = 0
    · simp [hz, Real.log_nonneg hB]
    · have hr : 0 < ‖z - w‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm hz)
      exact sub_nonneg.mpr (Real.log_le_log hr hw)
  have hFmeas : Measurable (fun w : ℂ =>
      Real.posLog ‖z - w‖⁻¹) := by
    exact measurable_posLog.comp (by fun_prop)
  have hF : Integrable (fun w : ℂ => Real.posLog ‖z - w‖⁻¹) ν := by
    refine hG.mono' hFmeas.aestronglyMeasurable ?_
    filter_upwards [hDist, hGnonneg] with w hw hgw
    have hnonneg : 0 ≤ Real.posLog ‖z - w‖⁻¹ := Real.posLog_nonneg
    have hpoint := posLog_inv_le_log_sub hB (norm_nonneg (z - w)) hw
    rw [Real.norm_of_nonneg hnonneg]
    exact hpoint
  have hne : ∀ᵐ w ∂ν, w ≠ z := by
    rw [ae_iff]
    have hset : {w : ℂ | ¬w ≠ z} = {z} := by
      ext w
      simp
    rw [hset]
    exact hAtom
  have hkernel :
      (fun w : ℂ => l6PosKernel z w) =ᵐ[ν]
        (fun w : ℂ => ENNReal.ofReal (Real.posLog ‖z - w‖⁻¹)) := by
    filter_upwards [hne] with w hw
    have hzw : z ≠ w := Ne.symm hw
    simp [l6PosKernel, hzw]
  rw [lintegral_congr_ae hkernel]
  have hFnonneg : 0 ≤ᵐ[ν] (fun w : ℂ => Real.posLog ‖z - w‖⁻¹) :=
    Filter.Eventually.of_forall (fun _ => Real.posLog_nonneg)
  have hlin := ofReal_integral_eq_lintegral_ofReal hF hFnonneg
  rw [← hlin]
  apply ENNReal.ofReal_le_ofReal
  have hpoint_ae : ∀ᵐ w ∂ν,
      Real.posLog ‖z - w‖⁻¹ ≤ Real.log B - Real.log ‖z - w‖ := by
    filter_upwards [hDist] with w hw
    exact posLog_inv_le_log_sub hB (norm_nonneg (z - w)) hw
  exact integral_mono_ae hF hG hpoint_ae

end Li2Lean.P0.U2GlobalFejer

namespace Li2Lean.P0.U2GlobalFejer

open Li2Lean.P0.L6Variations
open Li2Lean.P0.ConfigContourReference

private theorem contourReference_log_integrable (z : ℂ) :
    Integrable (fun w : ℂ => Real.log ‖z - w‖)
      ConfigContourMeasure.contourReferenceMeasure := by
  have hf : Measurable (fun w : ℂ => Real.log ‖z - w‖) := by
    exact Real.measurable_log.comp (by fun_prop)
  rw [ConfigContourMeasure.contourReferenceMeasure]
  apply (integrable_map_measure hf.aestronglyMeasurable
    ConfigContourMeasure.continuous_ellipse.aemeasurable).2
  let m : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (contourDensity u)
  have hfmeas : Measurable f := by
    exact ENNReal.measurable_ofReal.comp
      ConfigContourMeasure.continuous_contourDensity.measurable
  have hftop : ∀ᵐ u ∂m, f u < ⊤ := by
    filter_upwards [] with u
    exact ENNReal.ofReal_lt_top
  rw [ConfigContourMeasure.contourParamMeasure]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply (integrable_withDensity_iff_integrable_smul' hfmeas hftop).2
  have hbase : Integrable
      (fun u : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 u‖) m := by
    dsimp [m]
    exact ConfigContourProductIntegrability.contour_inner_log_integrable z
  have hdens : ∀ᵐ u ∂m, ‖contourDensity u‖ ≤
      49 * ConfigContourSelfPotential.contourMass := by
    filter_upwards [] with u
    have hnon : 0 ≤ contourDensity u := contourDensity_nonneg u
    have hle := ConfigContourProductIntegrability.contourDensity_le_49_mass u
    rw [Real.norm_of_nonneg hnon]
    exact hle
  have hmul := hbase.mul_bdd
    ConfigContourMeasure.continuous_contourDensity.aestronglyMeasurable hdens
  have htoReal : ∀ u : ℝ, (f u).toReal = contourDensity u := by
    intro u
    dsimp [f]
    exact ENNReal.toReal_ofReal (contourDensity_nonneg u)
  simpa [Function.comp_apply, smul_eq_mul, htoReal, mul_comm] using hmul

private theorem contourReference_log_bound_ae (u : ℝ) :
    ∀ᵐ w ∂ConfigContourMeasure.contourReferenceMeasure,
      ‖Li2Lean.p0EllipsePoint 1 u - w‖ ≤ 5 := by
  have hset : MeasurableSet {w : ℂ |
      ‖Li2Lean.p0EllipsePoint 1 u - w‖ ≤ (5 : ℝ)} := by
    exact (isClosed_le
      (continuous_norm.comp (continuous_const.sub continuous_id))
      continuous_const).measurableSet
  rw [ConfigContourMeasure.contourReferenceMeasure,
    ae_map_iff ConfigContourMeasure.continuous_ellipse.aemeasurable hset]
  filter_upwards [] with v
  exact ConfigContourCoarse.ellipsePoint_distance_le_five u v

/-- Positive part of the literal Fejer contour potential is uniformly bounded
on every point of the literal ellipse.  The RHS is an explicit finite ENNReal
constant assembled from the 64-cell Fejer mass and the chord bound. -/
theorem contourReference_l6PosKernel_bound_on_ellipse (u : ℝ) :
    (∫⁻ w, l6PosKernel (Li2Lean.p0EllipsePoint 1 u) w ∂
      ConfigContourMeasure.contourReferenceMeasure) ≤
      ENNReal.ofReal (ConfigContourSelfPotential.contourMass * Real.log 5 +
        contourPotentialLowerCost) := by
  have hmain := lintegral_l6PosKernel_le_of_log_bound
    ConfigContourMeasure.contourReferenceMeasure
    (Li2Lean.p0EllipsePoint 1 u) (B := (5 : ℝ)) (by norm_num)
    (ConfigContourMeasure.contourReferenceMeasure_singleton _)
    (contourReference_log_integrable _)
    (contourReference_log_bound_ae u)
  have hpot := contourReferencePotential_lower_on_ellipse u
  have hmass : ConfigContourSelfPotential.contourMass =
      ConfigContourMeasure.contourReferenceMeasure.real Set.univ := by
    change ConfigContourSelfPotential.contourMass =
      (ConfigContourMeasure.contourReferenceMeasure Set.univ).toReal
    rw [ConfigContourMeasure.contourReferenceMeasure_univ]
    norm_num [ConfigContourSelfPotential.contourMass]
  have hpot_eq :
      (∫ w, Real.log (5 : ℝ) -
        Real.log ‖Li2Lean.p0EllipsePoint 1 u - w‖ ∂
        ConfigContourMeasure.contourReferenceMeasure) =
      ConfigContourSelfPotential.contourMass * Real.log 5 -
        contourReferencePotential (Li2Lean.p0EllipsePoint 1 u) := by
    rw [integral_sub (integrable_const _) (contourReference_log_integrable _)]
    rw [integral_const]
    simp only [smul_eq_mul]
    rw [hmass]
    simp only [ConfigContourMeasure.contourReferencePotential_eq_integral]
  rw [hpot_eq] at hmain
  have hcost_nonneg : 0 ≤ contourPotentialLowerCost := by
    unfold contourPotentialLowerCost
    have hm : 0 ≤ ConfigContourSelfPotential.contourMass := by
      norm_num [ConfigContourSelfPotential.contourMass]
    positivity
  have hmass_nonneg : 0 ≤ ConfigContourSelfPotential.contourMass := by
    norm_num [ConfigContourSelfPotential.contourMass]
  have hlog5 : 0 ≤ Real.log (5 : ℝ) := Real.log_nonneg (by norm_num)
  apply le_trans hmain
  apply ENNReal.ofReal_le_ofReal
  linarith

end Li2Lean.P0.U2GlobalFejer

namespace Li2Lean.P0.U2GlobalFejer

open Li2Lean.P0.L6Variations

/-- The same explicit cap stated on the whole literal support `Gamma`. -/
theorem contourReference_l6PosKernel_bound_on_Gamma {z : ℂ}
    (hz : z ∈ Gamma) :
    (∫⁻ w, l6PosKernel z w ∂ConfigContourMeasure.contourReferenceMeasure) ≤
      ENNReal.ofReal (ConfigContourSelfPotential.contourMass * Real.log 5 +
        contourPotentialLowerCost) := by
  obtain ⟨u, rfl⟩ := hz
  have hp : Li2Lean.p0EllipsePoint 1 u = Li2Lean.P0.gammaPoint u := by
    simpa [Li2Lean.P0.ellipsePoint] using
      (Li2Lean.P0.ellipsePoint_one_eq_gammaPoint u)
  rw [← hp]
  exact contourReference_l6PosKernel_bound_on_ellipse u

end Li2Lean.P0.U2GlobalFejer
