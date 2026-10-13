/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInterior
import Mathlib.Probability.Distributions.Cauchy

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- Width of the logarithmic strip covering the actual v10 preimage annulus. -/
def annulusWidth : ℝ := -Real.log annulusRatio

theorem annulusWidth_pos : 0 < annulusWidth := by
  exact neg_pos.mpr (Real.log_neg annulusRatio_pos annulusRatio_lt_one)

/-- The selected annular root has logarithmic depth in `(0, annulusWidth)`. -/
def preimageDepth (z : ℂ) : ℝ := -Real.log ‖interiorPreimage z‖

theorem preimageDepth_pos {z : ℂ} (hz : z ∈ ellipseInterior) :
    0 < preimageDepth z := by
  have h := interiorPreimage_mem_annulus hz
  exact neg_pos.mpr (Real.log_neg (annulusRatio_pos.trans h.1) h.2)

theorem preimageDepth_lt_width {z : ℂ} (hz : z ∈ ellipseInterior) :
    preimageDepth z < annulusWidth := by
  have h := interiorPreimage_mem_annulus hz
  exact neg_lt_neg (Real.log_lt_log annulusRatio_pos h.1)

/-- Angular coordinate in the upper-half-plane exponential of the strip. -/
def stripAngle (z : ℂ) : ℝ := Real.pi * preimageDepth z / annulusWidth

/-- Location of the Cauchy law obtained by exponentiating the strip. -/
def stripLocation (z : ℂ) : ℝ :=
  Real.exp (Real.pi * (interiorPreimage z).arg / annulusWidth) *
    Real.cos (stripAngle z)

/-- Scale of the Cauchy law. On the original interior this is strictly positive,
so `toNNReal` does not change the upper-half-plane imaginary coordinate. -/
def stripScale (z : ℂ) : ℝ≥0 :=
  Real.toNNReal (Real.exp (Real.pi * (interiorPreimage z).arg / annulusWidth) *
    Real.sin (stripAngle z))

theorem stripAngle_pos {z : ℂ} (hz : z ∈ ellipseInterior) :
    0 < stripAngle z := by
  exact div_pos (mul_pos Real.pi_pos (preimageDepth_pos hz)) annulusWidth_pos

theorem stripAngle_lt_pi {z : ℂ} (hz : z ∈ ellipseInterior) :
    stripAngle z < Real.pi := by
  unfold stripAngle
  exact (div_lt_iff₀ annulusWidth_pos).mpr
    (mul_lt_mul_of_pos_left (preimageDepth_lt_width hz) Real.pi_pos)

theorem stripScale_pos {z : ℂ} (hz : z ∈ ellipseInterior) :
    0 < stripScale z := by
  apply Real.toNNReal_pos.mpr
  exact mul_pos (Real.exp_pos _)
    (Real.sin_pos_of_pos_of_lt_pi (stripAngle_pos hz) (stripAngle_lt_pi hz))

/-- The fixed boundary map for the upper-half-plane real axis. Positive real
points reach the outer annulus boundary; negative real points reach the inner
boundary, whose ellipse parametrization has the opposite orientation. -/
def stripBoundaryPoint (t : ℝ) : ℂ :=
  if 0 ≤ t then gammaPoint (annulusWidth / Real.pi * Real.log |t|)
  else gammaPoint (-(annulusWidth / Real.pi * Real.log |t|))

theorem continuous_gammaPoint : Continuous gammaPoint := by
  unfold gammaPoint
  fun_prop

theorem measurable_Gamma : MeasurableSet Gamma := by
  obtain ⟨K, hK, hcover⟩ := isSigmaCompact_range continuous_gammaPoint
  rw [Gamma, ← hcover]
  exact MeasurableSet.iUnion fun n => (hK n).isClosed.measurableSet

theorem measurable_stripBoundaryPoint : Measurable stripBoundaryPoint := by
  unfold stripBoundaryPoint
  apply Measurable.ite measurableSet_Ici
  · exact continuous_gammaPoint.measurable.comp
      ((measurable_id.abs.log).const_mul _)
  · exact continuous_gammaPoint.measurable.comp
      (((measurable_id.abs.log).const_mul _).neg)

theorem stripBoundaryPoint_mem_Gamma (t : ℝ) : stripBoundaryPoint t ∈ Gamma := by
  unfold stripBoundaryPoint
  split_ifs <;> exact Set.mem_range_self _

/-- Joint measurability of the actual Cauchy measure, including zero scale.
The nonzero-scale density and the degenerate Dirac branch are both explicit. -/
theorem measurable_cauchyMeasure_parameters :
    Measurable (fun p : ℝ × ℝ≥0 => cauchyMeasure p.1 p.2) := by
  unfold cauchyMeasure
  apply Measurable.ite (measurableSet_eq_fun measurable_snd measurable_const)
  · exact Measure.measurable_dirac.comp measurable_fst
  · apply measurable_withDensity
    unfold Function.uncurry cauchyPDF cauchyPDFReal
    fun_prop

theorem measurable_preimageDepth : Measurable preimageDepth := by
  exact measurable_interiorPreimage.norm.log.neg

theorem measurable_stripAngle : Measurable stripAngle := by
  exact (measurable_preimageDepth.const_mul _).div_const _

theorem measurable_stripLocation : Measurable stripLocation := by
  exact (((measurable_interiorPreimage.carg.const_mul _).div_const _).exp).mul
    measurable_stripAngle.cos

theorem measurable_stripScale : Measurable stripScale := by
  unfold stripScale
  exact ((((measurable_interiorPreimage.carg.const_mul _).div_const _).exp).mul
    measurable_stripAngle.sin).real_toNNReal

/-- Concrete candidate for interior harmonic measure of the v10 ellipse:
map the upper-half-plane Cauchy law through the two boundary components of
the covering strip. This definition by itself asserts no Green identity. -/
def interiorSweep (z : ℂ) : Measure ℂ :=
  Measure.map stripBoundaryPoint (cauchyMeasure (stripLocation z) (stripScale z))

/-- The actual explicitly defined sweep has total mass one. -/
instance interiorSweep_isProbability (z : ℂ) : IsProbabilityMeasure (interiorSweep z) := by
  unfold interiorSweep
  infer_instance

theorem interiorSweep_mass (z : ℂ) : interiorSweep z Set.univ = 1 := by
  exact measure_univ

/-- The explicit family is a measurable measure kernel, so it may be bound
against every original admissible finite contour measure. -/
theorem measurable_interiorSweep : Measurable interiorSweep := by
  exact (Measure.measurable_map stripBoundaryPoint measurable_stripBoundaryPoint).comp
    (measurable_cauchyMeasure_parameters.comp
      (measurable_stripLocation.prodMk measurable_stripScale))

/-- The exact contour support law for the explicit candidate, with no density
cap and no point exclusions imposed on the original source measure. -/
theorem interiorSweep_boundary_support (z : ℂ) : interiorSweep z Gammaᶜ = 0 := by
  rw [interiorSweep, Measure.map_apply measurable_stripBoundaryPoint measurable_Gamma.compl]
  have hempty : stripBoundaryPoint ⁻¹' Gammaᶜ = ∅ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false, iff_false, not_not]
    exact stripBoundaryPoint_mem_Gamma t
  rw [hempty, measure_empty]

/-- Binding the explicit interior family preserves every original finite
contour mass; the statement actually holds for arbitrary positive measures. -/
theorem swept_interior_mass (ν : Measure ℂ) :
    sweptMeasure ν interiorSweep Set.univ = ν Set.univ := by
  rw [sweptMeasure, Measure.bind_apply MeasurableSet.univ
    measurable_interiorSweep.aemeasurable]
  simp only [interiorSweep_mass, lintegral_const, one_mul]

/-- The bound family is supported on the unchanged contour for every source
measure, independently of smoothness, cap, or atomicity assumptions. -/
theorem swept_interior_boundary_support (ν : Measure ℂ) :
    sweptMeasure ν interiorSweep Gammaᶜ = 0 := by
  rw [sweptMeasure, Measure.bind_apply measurable_Gamma.compl
    measurable_interiorSweep.aemeasurable]
  simp only [interiorSweep_boundary_support, lintegral_zero]

end
end Li2Lean.P0.TubeInterior
