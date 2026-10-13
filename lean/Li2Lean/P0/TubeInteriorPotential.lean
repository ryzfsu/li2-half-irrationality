/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorSweep
import Li2Lean.P0.TubeSweepFubini

open MeasureTheory

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- The literal ellipse is the Joukowski image of the compact unit circle. -/
theorem Gamma_eq_range_joukowski_circle :
    Gamma = Set.range (fun w : Circle => joukowski (w : ℂ)) := by
  ext z
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨Circle.exp u, ?_⟩
    simpa only [Circle.coe_exp, mul_comm] using joukowski_unit_circle_eq_gammaPoint u
  · rintro ⟨w, rfl⟩
    refine ⟨(w : ℂ).arg, ?_⟩
    have hw : Complex.exp (Complex.I * ((w : ℂ).arg : ℂ)) = (w : ℂ) := by
      simpa only [Circle.norm_coe, Complex.ofReal_one, one_mul, mul_one, mul_comm] using
        Complex.norm_mul_exp_arg_mul_I (w : ℂ)
    rw [← joukowski_unit_circle_eq_gammaPoint, hw]

/-- Compactness of the actual contour, used for finite source potentials. -/
theorem isCompact_Gamma : IsCompact Gamma := by
  rw [Gamma_eq_range_joukowski_circle]
  apply isCompact_range
  unfold joukowski
  have hcoe : Continuous (fun w : Circle => (w : ℂ)) := continuous_subtype_val
  exact (continuous_const.add (continuous_const.mul hcoe)).add
    (continuous_const.mul (hcoe.inv₀ (fun w => Circle.coe_ne_zero w)))

/-- A point of the original open ellipse interior is never on its contour. -/
theorem interior_not_mem_Gamma {x : ℂ} (hx : x ∈ ellipseInterior) : x ∉ Gamma := by
  rintro ⟨u, rfl⟩
  change 0 < ellipseLevel (gammaPoint u) at hx
  rw [ellipseLevel_gammaPoint] at hx
  exact lt_irrefl _ hx

/-- The finite logarithmic source kernel is continuous on the exact contour
whenever its point source is not on that contour. -/
theorem continuousOn_realLogKernel_boundary {x : ℂ} (hx : x ∉ Gamma) :
    ContinuousOn (fun y => realLogKernel y x) Gamma := by
  unfold realLogKernel
  apply ContinuousOn.neg
  apply ContinuousOn.log
  · exact (continuous_norm.comp (continuous_id.sub continuous_const)).continuousOn
  · intro y hy
    apply norm_ne_zero_iff.mpr
    exact sub_ne_zero.mpr (by intro h; exact hx (h ▸ hy))

/-- Any finite measure supported on the original ellipse integrates every
nonboundary point-source logarithm. No density bound is assumed. -/
theorem integrable_realLogKernel_of_boundary_support (μ : Measure ℂ)
    [IsFiniteMeasure μ] (hμ : μ Gammaᶜ = 0) {x : ℂ} (hx : x ∉ Gamma) :
    Integrable (fun y => realLogKernel y x) μ := by
  have hOn : IntegrableOn (fun y => realLogKernel y x) Gamma μ :=
    (continuousOn_realLogKernel_boundary hx).integrableOn_compact isCompact_Gamma
  have hrestrict : μ.restrict Gamma = μ :=
    Measure.restrict_eq_self_of_ae_mem (by change μ Gammaᶜ = 0; exact hμ)
  simpa only [IntegrableOn, hrestrict] using hOn

/-- The concrete Cauchy sweep has integrable point-source potentials at all
original interior targets, including focal points. -/
theorem integrable_realLogKernel_interiorSweep (z : ℂ) {x : ℂ}
    (hx : x ∈ ellipseInterior) :
    Integrable (fun y => realLogKernel y x) (interiorSweep z) := by
  exact integrable_realLogKernel_of_boundary_support (interiorSweep z)
    (interiorSweep_boundary_support z) (interior_not_mem_Gamma hx)

/-- Binding against every original finite source measure keeps interior
point-source potentials integrable. This is not the singular self-energy
comparison, whose Green and boundary-logarithm steps remain separate. -/
theorem integrable_realLogKernel_swept_interior (ν : Measure ℂ)
    [IsFiniteMeasure ν] {x : ℂ} (hx : x ∈ ellipseInterior) :
    Integrable (fun y => realLogKernel y x) (sweptMeasure ν interiorSweep) := by
  letI : IsFiniteMeasure (sweptMeasure ν interiorSweep) :=
    ⟨by rw [swept_interior_mass]; exact measure_lt_top ν Set.univ⟩
  exact integrable_realLogKernel_of_boundary_support (sweptMeasure ν interiorSweep)
    (swept_interior_boundary_support ν) (interior_not_mem_Gamma hx)

/-- Topological support form required by the original admissible measure class. -/
theorem interiorSweep_support_subset (z : ℂ) : (interiorSweep z).support ⊆ Gamma := by
  apply Measure.support_subset_of_isClosed isCompact_Gamma.isClosed
  change interiorSweep z Gammaᶜ = 0
  exact interiorSweep_boundary_support z

/-- Topological support is retained for every bound positive measure, with
no cap or finite-energy restriction added to the measure quantifier. -/
theorem swept_interior_support_subset (ν : Measure ℂ) :
    (sweptMeasure ν interiorSweep).support ⊆ Gamma := by
  apply Measure.support_subset_of_isClosed isCompact_Gamma.isClosed
  change sweptMeasure ν interiorSweep Gammaᶜ = 0
  exact swept_interior_boundary_support ν

/-- The point-source potential of the bound measure is the integral of the
actual pointwise Cauchy-sweep potentials, for every original finite source
measure. The needed signed integrability has been proved, not assumed. -/
theorem integral_realLogKernel_swept_interior (ν : Measure ℂ)
    [IsFiniteMeasure ν] {x : ℂ} (hx : x ∈ ellipseInterior) :
    (∫ y, realLogKernel y x ∂sweptMeasure ν interiorSweep) =
      ∫ z, (∫ y, realLogKernel y x ∂interiorSweep z) ∂ν := by
  exact integral_sweptMeasure ν interiorSweep (fun y => realLogKernel y x)
    measurable_interiorSweep.aemeasurable (integrable_realLogKernel_swept_interior ν hx)

end
end Li2Lean.P0.TubeInterior
