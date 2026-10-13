/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourMeasure
import Li2Lean.P0.ConfigContourSelfPotential
import Li2Lean.P0.ConfigContourCoarse
import Li2Lean.P0.ConfigContourProduct
import Li2Lean.P0.DualL6Variations

open MeasureTheory Set Filter
open scoped ENNReal BigOperators Interval
namespace Li2Lean.P0.ConfigContourProductIntegrability
noncomputable section
open Li2Lean.P0.ConfigContourReference Li2Lean.P0.ConfigContourMeasure
open Li2Lean.P0.ConfigContourSelfPotential Li2Lean.P0.ConfigContourProduct
open Li2Lean.P0.ConfigContourCoarse
open Li2Lean.P0.L6Variations

theorem contour_inner_log_integrable (z : ℂ) :
    Integrable (fun v : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖)
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hIcc : Integrable (fun v : ℝ => Real.log ‖z - Li2Lean.p0EllipsePoint 1 v‖)
      (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))) :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le (by positivity)).mp
      (intervalIntegrable_ellipse_log_distance z)
  apply hIcc.mono_measure
  exact Measure.restrict_mono_set volume (by
    intro v hv
    exact ⟨le_of_lt hv.1, hv.2⟩)

theorem fejer48_le_49 (u : ℝ) : fejer48 u ≤ 49 := by
  unfold fejer48
  have hsum : ‖∑ r ∈ Finset.range 49,
      Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)‖ ≤ (49 : ℝ) := by
    calc
      ‖∑ r ∈ Finset.range 49,
          Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)‖ ≤
          ∑ r ∈ Finset.range 49, ‖Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)‖ := by
            apply norm_sum_le
      _ = 49 := by simp [Complex.norm_exp]
  have hnon : 0 ≤ ‖∑ r ∈ Finset.range 49,
      Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)‖ := norm_nonneg _
  nlinarith [hsum]

theorem contourDensity_le_49_mass (u : ℝ) : contourDensity u ≤ 49 * contourMass := by
  unfold contourDensity
  have hsum : (∑ j : Fin 64, contourWeight j * fejer48 (u - contourAngle j)) ≤
      ∑ j : Fin 64, contourWeight j * 49 := by
    apply Finset.sum_le_sum
    intro j hj
    exact mul_le_mul_of_nonneg_left (fejer48_le_49 _) (contourWeight_nonneg j)
  calc
    contourDensity u = ∑ j : Fin 64, contourWeight j * fejer48 (u - contourAngle j) := rfl
    _ ≤ ∑ j : Fin 64, contourWeight j * 49 := hsum
    _ = 49 * contourMass := by
      rw [← Finset.sum_mul, contourMass_eq_source]
      ring

private theorem contourLogDistanceKernel_ioc_integrable :
    Integrable contourLogDistanceKernel
      ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).prod
        (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi)))) := by
  rw [Measure.prod_restrict]
  apply contourLogDistanceKernel_integrable.mono_measure
  apply Measure.restrict_mono_set
  intro p hp
  exact ⟨⟨le_of_lt hp.1.1, hp.1.2⟩, ⟨le_of_lt hp.2.1, hp.2.2⟩⟩

theorem density_param_kernel_integrable : Integrable contourLogDistanceKernel
    ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).withDensity
      (fun u => ENNReal.ofReal (contourDensity u)) |>.prod
    ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).withDensity
      (fun u => ENNReal.ofReal (contourDensity u)))) := by
  let m : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let f : ℝ → ℝ≥0∞ := fun u => ENNReal.ofReal (contourDensity u)
  have hf : Measurable f := ENNReal.measurable_ofReal.comp continuous_contourDensity.measurable
  have hbase : Integrable contourLogDistanceKernel (m.prod m) := by
    dsimp [m]
    exact contourLogDistanceKernel_ioc_integrable
  rw [show (m.withDensity f).prod (m.withDensity f) =
      (m.prod m).withDensity (fun p : ℝ × ℝ => f p.1 * f p.2) from prod_withDensity hf hf]
  have hfd : Measurable (fun p : ℝ × ℝ => f p.1 * f p.2) :=
    (hf.comp measurable_fst).mul (hf.comp measurable_snd)
  have hbound : ∀ u : ℝ, f u ≤ ENNReal.ofReal (49 * contourMass) := by
    intro u
    exact ENNReal.ofReal_le_ofReal (contourDensity_le_49_mass u)
  have hflt : ∀ᵐ p ∂(m.prod m), f p.1 * f p.2 < ⊤ := by
    filter_upwards [] with p
    calc
      f p.1 * f p.2 ≤ ENNReal.ofReal (49 * contourMass) * ENNReal.ofReal (49 * contourMass) :=
        mul_le_mul (hbound p.1) (hbound p.2) (by positivity) (by positivity)
      _ < ⊤ := by exact ENNReal.mul_lt_top (by finiteness) (by finiteness)
  rw [integrable_withDensity_iff hfd hflt]
  let g : ℝ × ℝ → ℝ := fun p => (f p.1 * f p.2).toReal
  have hg : Measurable g := ENNReal.measurable_toReal.comp hfd
  have hg_bound : ∀ᵐ p ∂(m.prod m), ‖g p‖ ≤ (49 * contourMass) ^ 2 := by
    filter_upwards [] with p
    have h1 : 0 ≤ contourDensity p.1 := contourDensity_nonneg _
    have h2 : 0 ≤ contourDensity p.2 := contourDensity_nonneg _
    have hb1 := contourDensity_le_49_mass p.1
    have hb2 := contourDensity_le_49_mass p.2
    dsimp [g, f]
    rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal h1, ENNReal.toReal_ofReal h2]
    rw [abs_of_nonneg (mul_nonneg h1 h2)]
    nlinarith
  have hw := hbase.mul_bdd hg.aestronglyMeasurable hg_bound
  simpa [g, Pi.mul_apply, Function.comp_apply] using hw

theorem contourParam_kernel_integrable :
    Integrable contourLogDistanceKernel (contourParamMeasure.prod contourParamMeasure) := by
  letI : IsFiniteMeasure contourParamMeasure := ⟨by
    rw [contourParamMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  apply density_param_kernel_integrable.mono_measure
  apply Measure.prod_mono
  · unfold contourParamMeasure
    apply (Measure.le_iff').2
    intro s
    rw [Measure.smul_apply]
    change ENNReal.ofReal (2 * Real.pi)⁻¹ * _ ≤ _
    apply mul_le_of_le_one_left
    · exact bot_le
    simpa using (ENNReal.ofReal_le_ofReal ((inv_le_one₀ (show 0 < (2 * Real.pi : ℝ) by positivity)).2 (by nlinarith [Real.pi_gt_three])))
  · unfold contourParamMeasure
    apply (Measure.le_iff').2
    intro s
    rw [Measure.smul_apply]
    change ENNReal.ofReal (2 * Real.pi)⁻¹ * _ ≤ _
    apply mul_le_of_le_one_left
    · exact bot_le
    simpa using (ENNReal.ofReal_le_ofReal ((inv_le_one₀ (show 0 < (2 * Real.pi : ℝ) by positivity)).2 (by nlinarith [Real.pi_gt_three])))


theorem contourReferenceMeasure_prod_integrable :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (contourReferenceMeasure.prod contourReferenceMeasure) := by
  letI : IsFiniteMeasure contourParamMeasure := ⟨by
    rw [contourParamMeasure_univ]
    exact ENNReal.ofReal_lt_top⟩
  change Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((contourParamMeasure.map (Li2Lean.p0EllipsePoint 1)).prod
        (contourParamMeasure.map (Li2Lean.p0EllipsePoint 1)))
  rw [Measure.map_prod_map contourParamMeasure contourParamMeasure
      continuous_ellipse.measurable continuous_ellipse.measurable]
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    exact (Real.measurable_log.comp (by fun_prop : Measurable (fun p : ℂ × ℂ => ‖p.1 - p.2‖))).neg
  apply (integrable_map_measure
    hmeas.aestronglyMeasurable
    (continuous_ellipse.measurable.prodMap continuous_ellipse.measurable).aemeasurable).2
  have hneg := contourParam_kernel_integrable.neg
  refine hneg.congr (Filter.Eventually.of_forall (fun p => ?_))
  simp [li2LogKernel, contourLogDistanceKernel]
end
end Li2Lean.P0.ConfigContourProductIntegrability
