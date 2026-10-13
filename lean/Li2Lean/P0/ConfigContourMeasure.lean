/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigFejerMass

/-!
# The v10 contour reference as a `Measure ℂ`

`ConfigContourReference.contourReferenceIntegral` is a functional on
`ℂ → ℝ`.  Here the same object is realized as the pushforward under the
literal ellipse parameterization of the parameter measure
`(2*pi)⁻¹ * contourDensity(u) du` on `(0, 2*pi]`.  The density is the
unchanged 64-term Fejer mixture of v10 (5.4).  The functional and the
measure agree on every a.e.-strongly-measurable integrand, the measure has
the Appendix A mass, and it has no atoms (the parameterization is injective
on one full turn).
-/

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0.ConfigContourMeasure

noncomputable section

open ConfigContourReference

theorem continuous_fejer48 : Continuous fejer48 := by
  unfold fejer48
  fun_prop

theorem continuous_contourDensity : Continuous contourDensity := by
  unfold contourDensity
  exact continuous_finsetSum _ fun j _ =>
    continuous_const.mul (continuous_fejer48.comp (continuous_id.sub continuous_const))

theorem continuous_ellipse : Continuous (Li2Lean.p0EllipsePoint 1) := by
  unfold Li2Lean.p0EllipsePoint
  fun_prop

/-- The parameter measure `(2*pi)⁻¹ * contourDensity(u) du` on one turn. -/
def contourParamMeasure : Measure ℝ :=
  ENNReal.ofReal (2 * Real.pi)⁻¹ •
    (volume.restrict (Ioc 0 (2 * Real.pi))).withDensity
      (fun u => ENNReal.ofReal (contourDensity u))

/-- The v10 contour reference measure `nu_0` on `ℂ`. -/
def contourReferenceMeasure : Measure ℂ :=
  contourParamMeasure.map (Li2Lean.p0EllipsePoint 1)

theorem measurable_densityENN :
    Measurable (fun u => ENNReal.ofReal (contourDensity u)) :=
  ENNReal.measurable_ofReal.comp continuous_contourDensity.measurable

theorem integral_contourParamMeasure (g : ℝ → ℝ) :
    ∫ u, g u ∂contourParamMeasure =
      (2 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u * g u := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  rw [contourParamMeasure, integral_smul_measure,
    integral_withDensity_eq_integral_toReal_smul measurable_densityENN
      (Eventually.of_forall fun _ => ENNReal.ofReal_lt_top),
    intervalIntegral.integral_of_le h2pi,
    ENNReal.toReal_ofReal (inv_nonneg.mpr h2pi)]
  simp only [smul_eq_mul, ENNReal.toReal_ofReal (contourDensity_nonneg _)]

/-- The functional of v10 (5.4) is integration against the measure. -/
theorem contourReferenceIntegral_eq_integral {f : ℂ → ℝ}
    (hf : AEStronglyMeasurable f contourReferenceMeasure) :
    contourReferenceIntegral f = ∫ z, f z ∂contourReferenceMeasure := by
  rw [contourReferenceMeasure, integral_map continuous_ellipse.aemeasurable hf,
    integral_contourParamMeasure]
  rfl

/-- The logarithmic potential of v10 (5.4) is the potential of the measure. -/
theorem contourReferencePotential_eq_integral (z : ℂ) :
    contourReferencePotential z =
      ∫ w, Real.log ‖z - w‖ ∂contourReferenceMeasure := by
  apply contourReferenceIntegral_eq_integral
  exact (Real.measurable_log.comp
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable).aestronglyMeasurable

theorem contourParamMeasure_univ :
    contourParamMeasure univ =
      ENNReal.ofReal (contourReferenceIntegral (fun _ => 1)) := by
  have h2pi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hInt : IntegrableOn contourDensity (Ioc 0 (2 * Real.pi)) :=
    continuous_contourDensity.integrableOn_Ioc
  have hlin := ofReal_integral_eq_lintegral_ofReal hInt
    (Eventually.of_forall fun u => contourDensity_nonneg u)
  rw [contourParamMeasure, Measure.smul_apply, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ, ← hlin, smul_eq_mul, ← ENNReal.ofReal_mul (inv_nonneg.mpr h2pi)]
  congr 1
  unfold contourReferenceIntegral
  rw [intervalIntegral.integral_of_le h2pi]
  simp only [mul_one]

/-- The Appendix A mass of `nu_0`, in the `du/(2*pi)` normalization. -/
theorem contourReferenceMeasure_univ :
    contourReferenceMeasure univ =
      ENNReal.ofReal (267885951940 / 1000000000000 : ℝ) := by
  rw [contourReferenceMeasure, Measure.map_apply continuous_ellipse.measurable
    MeasurableSet.univ, preimage_univ, contourParamMeasure_univ,
    ConfigFejerMass.contourReferenceIntegral_one]

instance : IsFiniteMeasure contourReferenceMeasure :=
  ⟨by rw [contourReferenceMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem ellipse_eq_iff_cos_sin {u v : ℝ}
    (h : Li2Lean.p0EllipsePoint 1 u = Li2Lean.p0EllipsePoint 1 v) :
    Real.cos u = Real.cos v ∧ Real.sin u = Real.sin v := by
  have hre := congrArg Complex.re h
  have him := congrArg Complex.im h
  simp [Li2Lean.p0EllipsePoint, Complex.cos_ofReal_re, Complex.sin_ofReal_re] at hre him
  constructor
  · linarith
  · linarith

/-- The literal ellipse parameterization is injective on one full turn. -/
theorem ellipse_injOn : InjOn (Li2Lean.p0EllipsePoint 1) (Ioc 0 (2 * Real.pi)) := by
  intro u hu v hv h
  obtain ⟨hc, hs⟩ := ellipse_eq_iff_cos_sin h
  have hexp : Complex.exp ((u : ℂ) * Complex.I) = Complex.exp ((v : ℂ) * Complex.I) := by
    rw [Complex.exp_mul_I, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_cos,
      ← Complex.ofReal_sin, ← Complex.ofReal_sin, hc, hs]
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have hreal : u = v + n * (2 * Real.pi) := by
    have := congrArg Complex.im hn
    simpa using this
  have hpi : 0 < Real.pi := Real.pi_pos
  have hlt : (n : ℝ) * (2 * Real.pi) < 2 * Real.pi := by
    linarith [hu.1, hu.2, hv.1, hv.2]
  have hgt : -(2 * Real.pi) < (n : ℝ) * (2 * Real.pi) := by
    linarith [hu.1, hu.2, hv.1, hv.2]
  have hn1 : (n : ℝ) < 1 := by nlinarith
  have hn2 : -1 < (n : ℝ) := by nlinarith
  have hn0 : n = 0 := by
    have h1 : n < 1 := by exact_mod_cast hn1
    have h2 : -1 < n := by exact_mod_cast hn2
    omega
  simp [hn0] at hreal
  exact hreal

/-- `nu_0` has no atoms: the Fejer density is absolutely continuous in the
parameter, and every fiber of the ellipse map on one turn has at most one
point. -/
theorem contourReferenceMeasure_singleton (z : ℂ) : contourReferenceMeasure {z} = 0 := by
  have hmeas : MeasurableSet (Li2Lean.p0EllipsePoint 1 ⁻¹' {z}) :=
    continuous_ellipse.measurable (measurableSet_singleton z)
  rw [contourReferenceMeasure, Measure.map_apply continuous_ellipse.measurable
    (measurableSet_singleton z), contourParamMeasure, Measure.smul_apply,
    withDensity_apply _ hmeas, Measure.restrict_restrict hmeas]
  have hsub : (Li2Lean.p0EllipsePoint 1 ⁻¹' {z} ∩ Ioc 0 (2 * Real.pi)).Subsingleton := by
    intro u hu v hv
    exact ellipse_injOn hu.2 hv.2 (by rw [hu.1, hv.1])
  rw [setLIntegral_measure_zero _ _ (hsub.measure_zero volume), smul_zero]

end

end Li2Lean.P0.ConfigContourMeasure
