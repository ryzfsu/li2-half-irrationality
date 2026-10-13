/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorRealSources
import Li2Lean.P0.TubeInteriorSweep

/-! # Actual exterior Poisson measures on the v10 ellipse -/

open MeasureTheory Complex

namespace Li2Lean.P0

noncomputable section

/-- Normalized angular Poisson density for the unit circle. -/
def exteriorPoissonAngleDensity (p : ℂ) (θ : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * poissonKernel 0 p (circleMap 0 1 θ)

/-- Explicit exterior Poisson law on the literal ellipse, defined for every disk parameter. -/
def ellipsePoissonMeasure (p : ℂ) : Measure ℂ :=
  Measure.map gammaPoint
    ((volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))).withDensity
      (fun θ => ENNReal.ofReal (exteriorPoissonAngleDensity p θ)))

/-- Joint measurability of the angular density without branch choices or regularity premises. -/
theorem measurable_exteriorPoissonAngleDensity :
    Measurable (fun q : ℂ × ℝ => exteriorPoissonAngleDensity q.1 q.2) := by
  unfold exteriorPoissonAngleDensity poissonKernel
  fun_prop

/-- The explicit ellipse Poisson measures form a measurable kernel. -/
theorem measurable_ellipsePoissonMeasure : Measurable ellipsePoissonMeasure := by
  unfold ellipsePoissonMeasure
  apply (Measure.measurable_map gammaPoint TubeInterior.continuous_gammaPoint.measurable).comp
  apply measurable_withDensity
  exact measurable_exteriorPoissonAngleDensity.ennreal_ofReal

/-- Positivity of the actual angular density for every genuine disk parameter. -/
theorem exteriorPoissonAngleDensity_nonneg {p : ℂ} (hp : ‖p‖ < 1) (θ : ℝ) :
    0 ≤ exteriorPoissonAngleDensity p θ := by
  apply mul_nonneg (by positivity : 0 ≤ (2 * Real.pi)⁻¹)
  apply poissonKernel_unit_nonneg hp
  simp

/-- Angular density integrability is proved before any mass normalization. -/
theorem integrable_exteriorPoissonAngleDensity {p : ℂ} (hp : ‖p‖ < 1) :
    Integrable (exteriorPoissonAngleDensity p)
      (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) := by
  have hi := (poissonKernel_unit_continuous hp).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  change IntervalIntegrable (fun θ => poissonKernel 0 p (circleMap 0 1 θ)) volume 0 (2 * Real.pi) at hi
  apply (intervalIntegrable_iff_integrableOn_Ioc_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mp
  exact hi.const_mul (2 * Real.pi)⁻¹

/-- The normalizing factor is exactly `1/(2*pi)`. -/
theorem integral_exteriorPoissonAngleDensity {p : ℂ} (hp : ‖p‖ < 1) :
    ∫ θ in Set.Ioc (0 : ℝ) (2 * Real.pi), exteriorPoissonAngleDensity p θ = 1 := by
  have h := poissonKernel_unit_mass hp
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)] at h
  simpa only [exteriorPoissonAngleDensity, integral_const_mul, smul_eq_mul] using h

/-- The literal ellipse Poisson measure has total mass one. -/
theorem ellipsePoissonMeasure_univ {p : ℂ} (hp : ‖p‖ < 1) :
    ellipsePoissonMeasure p Set.univ = 1 := by
  rw [ellipsePoissonMeasure, Measure.map_apply TubeInterior.continuous_gammaPoint.measurable MeasurableSet.univ,
    Set.preimage_univ, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    ← ofReal_integral_eq_lintegral_ofReal (integrable_exteriorPoissonAngleDensity hp)
      (Filter.Eventually.of_forall (exteriorPoissonAngleDensity_nonneg hp)),
    integral_exteriorPoissonAngleDensity hp]
  norm_num

/-- Every member of the explicit family is supported on the unchanged contour. -/
theorem ellipsePoissonMeasure_boundary_support (p : ℂ) :
    ellipsePoissonMeasure p Gammaᶜ = 0 := by
  rw [ellipsePoissonMeasure, Measure.map_apply TubeInterior.continuous_gammaPoint.measurable
    TubeInterior.measurable_Gamma.compl]
  have he : gammaPoint ⁻¹' Gammaᶜ = ∅ := by
    ext θ
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact Set.mem_range_self θ
  rw [he, measure_empty]

/-- The map used by angular integration is the actual Joukowski boundary map. -/
theorem joukowski_circleMap_eq_gammaPoint (θ : ℝ) :
    joukowski (circleMap 0 1 θ) = gammaPoint θ := by
  simpa only [circleMap, Complex.ofReal_one, one_mul, mul_one, zero_add, mul_comm] using
    joukowski_unit_circle_eq_gammaPoint θ

/-- Exact conversion from the constructed probability measure to the proven Poisson average. -/
theorem integral_ellipsePoissonMeasure {p : ℂ} (hp : ‖p‖ < 1)
    (f : ℂ → ℝ) (hf : Measurable f) :
    ∫ y, f y ∂ellipsePoissonMeasure p =
      Real.circleAverage (fun ζ => poissonKernel 0 p ζ * f (joukowski ζ)) 0 1 := by
  have hd : Measurable (fun θ => ENNReal.ofReal (exteriorPoissonAngleDensity p θ)) :=
    (measurable_exteriorPoissonAngleDensity.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [ellipsePoissonMeasure, integral_map_of_stronglyMeasurable
    TubeInterior.continuous_gammaPoint.measurable hf.stronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hd (Filter.Eventually.of_forall (fun θ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (exteriorPoissonAngleDensity_nonneg hp _), smul_eq_mul]
  rw [Real.circleAverage_def, intervalIntegral.integral_of_le (by positivity : (0 : ℝ) ≤ 2 * Real.pi)]
  simp only [smul_eq_mul, joukowski_circleMap_eq_gammaPoint, exteriorPoissonAngleDensity, mul_assoc,
    integral_const_mul]

/-- Exterior part of the literal harmonic-measure family, using the constructed inverse. -/
def exteriorSweep (z : ℂ) : Measure ℂ :=
  ellipsePoissonMeasure (exteriorPoissonParameter (ellipseExteriorInverse z))

/-- Measurability makes exterior sweeping available for arbitrary admissible measures. -/
theorem measurable_exteriorSweep : Measurable exteriorSweep := by
  unfold exteriorSweep exteriorPoissonParameter
  apply measurable_ellipsePoissonMeasure.comp
  exact (Complex.continuous_conj.measurable.comp measurable_ellipseExteriorInverse).inv

/-- Probability normalization holds at every strict exterior ellipse point. -/
theorem exteriorSweep_univ {z : ℂ} (hz : ellipseLevel z < 0) : exteriorSweep z Set.univ = 1 := by
  apply ellipsePoissonMeasure_univ
  simpa using exteriorPoissonParameter_mem_ball (ellipseExteriorInverse_norm_gt_one hz)

/-- Boundary support does not impose a density cap or exclude atomic source measures. -/
theorem exteriorSweep_boundary_support (z : ℂ) : exteriorSweep z Gammaᶜ = 0 :=
  ellipsePoissonMeasure_boundary_support _

/-- The genuine exterior measure obeys the same-source Green bound off boundary source points. -/
theorem exteriorSweep_point_green {z x : ℂ} (hz : ellipseLevel z < 0)
    (hx : ellipseLevel x ≠ 0) (hzx : z ≠ x) :
    (∫ y, realLogKernel y x ∂exteriorSweep z) ≤
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  have hp : ‖exteriorPoissonParameter (ellipseExteriorInverse z)‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball (ellipseExteriorInverse_norm_gt_one hz)
  rw [exteriorSweep, integral_ellipsePoissonMeasure hp _ (by unfold realLogKernel; fun_prop)]
  exact ellipse_exterior_point_green_off_boundary hz hx hzx

/-- Weighted circle integrability transports to the actual ellipse measure. -/
theorem integrable_ellipsePoissonMeasure_of_circle {p : ℂ} (hp : ‖p‖ < 1)
    (f : ℂ → ℝ) (hf : Measurable f)
    (hi : CircleIntegrable (fun ζ => poissonKernel 0 p ζ * f (joukowski ζ)) 0 1) :
    Integrable f (ellipsePoissonMeasure p) := by
  have hd : Measurable (fun θ => ENNReal.ofReal (exteriorPoissonAngleDensity p θ)) :=
    (measurable_exteriorPoissonAngleDensity.comp (measurable_const.prodMk measurable_id)).ennreal_ofReal
  rw [ellipsePoissonMeasure]
  apply (integrable_map_measure hf.aestronglyMeasurable
    TubeInterior.continuous_gammaPoint.measurable.aemeasurable).2
  apply (integrable_withDensity_iff_integrable_smul' hd
    (Filter.Eventually.of_forall (fun θ => ENNReal.ofReal_lt_top))).2
  change IntervalIntegrable
    (fun θ => poissonKernel 0 p (circleMap 0 1 θ) * f (joukowski (circleMap 0 1 θ)))
    volume 0 (2 * Real.pi) at hi
  have hi' := (intervalIntegrable_iff_integrableOn_Ioc_of_le
    (by positivity : (0 : ℝ) ≤ 2 * Real.pi)).mp hi
  have hmul := hi'.const_mul (2 * Real.pi)⁻¹
  simp only [Function.comp_def]
  simp_rw [ENNReal.toReal_ofReal (exteriorPoissonAngleDensity_nonneg hp _)]
  simpa only [smul_eq_mul, exteriorPoissonAngleDensity, mul_assoc, joukowski_circleMap_eq_gammaPoint] using hmul

/-- All point logarithms, including boundary singularities, are integrable for the exterior law. -/
theorem exteriorSweep_integrable_logKernel {z : ℂ} (hz : ellipseLevel z < 0) (x : ℂ) :
    Integrable (fun y => realLogKernel y x) (exteriorSweep z) := by
  have hp : ‖exteriorPoissonParameter (ellipseExteriorInverse z)‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball (ellipseExteriorInverse_norm_gt_one hz)
  apply integrable_ellipsePoissonMeasure_of_circle hp _ (by unfold realLogKernel; fun_prop)
  have hi := (exterior_poisson_source_circleIntegrable hp x).neg
  change CircleIntegrable (fun ζ =>
    -(poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
      Real.log ‖joukowski ζ - x‖)) 0 1 at hi
  simpa only [realLogKernel, mul_neg] using hi

/-- Sweeping an arbitrary positive measure carried by the exterior preserves its total mass. -/
theorem swept_exterior_mass (ν : Measure ℂ) (hν : ∀ᵐ z ∂ν, ellipseLevel z < 0) :
    sweptMeasure ν exteriorSweep Set.univ = ν Set.univ := by
  rw [sweptMeasure, Measure.bind_apply MeasurableSet.univ measurable_exteriorSweep.aemeasurable]
  have h : (fun z => exteriorSweep z Set.univ) =ᵐ[ν] (fun _ => (1 : ENNReal)) :=
    hν.mono (fun _ hz => exteriorSweep_univ hz)
  rw [lintegral_congr_ae h]
  simp

/-- Sweeping any original measure retains support on Gamma, without a cap or atom restriction. -/
theorem swept_exterior_boundary_support (ν : Measure ℂ) :
    sweptMeasure ν exteriorSweep Gammaᶜ = 0 := by
  rw [sweptMeasure, Measure.bind_apply TubeInterior.measurable_Gamma.compl
    measurable_exteriorSweep.aemeasurable]
  simp only [exteriorSweep_boundary_support, lintegral_zero]

/-- The actual exterior measure has the precise positive-source Green identity. -/
theorem exteriorSweep_positive_source (z x : ℂ) (hz : ellipseLevel z < 0)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (∫ y, realLogKernel y x ∂exteriorSweep z) =
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  have hp : ‖exteriorPoissonParameter (ellipseExteriorInverse z)‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball (ellipseExteriorInverse_norm_gt_one hz)
  rw [exteriorSweep, integral_ellipsePoissonMeasure hp _ (by unfold realLogKernel; fun_prop)]
  exact ellipse_exterior_point_green_positive_source hz hx hxim

/-- Full reflected-frequency-half-line application, now for the actual sweep measure. -/
theorem exteriorSweep_frequency_source {δ : ℝ} {z x : ℂ}
    (hδ : δ ≤ tubeRadiusMax) (hzt : z ∈ tube δ) (hz : ellipseLevel z < 0)
    (hx : x.re ≤ -(1 : ℝ) / 2) :
    (∫ y, realLogKernel y x ∂exteriorSweep z) ≤
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z :=
  exteriorSweep_point_green hz (reflected_frequency_source_level_neg x hx).ne
    (tube_ne_reflected_frequency_source hδ hzt hx)

/-- The actual exterior measure has the favorable logarithmic sign for `-phi` almost everywhere. -/
theorem exteriorSweep_phi_source_log_ae {z : ℂ} (hz : ellipseLevel z < 0) :
    ∀ᵐ s : ℝ ∂volume,
      Real.log ‖z + (s : ℂ)‖ - exteriorCorrection ellipseExteriorInverse z ≤
        ∫ y, Real.log ‖y + (s : ℂ)‖ ∂exteriorSweep z := by
  have hp : ‖exteriorPoissonParameter (ellipseExteriorInverse z)‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball (ellipseExteriorInverse_norm_gt_one hz)
  filter_upwards [ellipse_exterior_phi_source_log_ae hz] with s hs
  rw [exteriorSweep, integral_ellipsePoissonMeasure hp _ (by fun_prop)]
  exact hs

end
end Li2Lean.P0
