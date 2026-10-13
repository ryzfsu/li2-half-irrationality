/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Reference
import Li2Lean.P0.ReferenceEtaEnergy
import Li2Lean.P0.ReferenceMass
import Li2Lean.P0.ReferenceFirstMoment
import Li2Lean.P0.ReferenceFrequencyField
import Li2Lean.P0.DensityCaps
import Li2Lean.P0.FrequencyKernelReference
import Li2Lean.P0.ContourFieldFinite

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Li2Lean.P0
noncomputable section
open ConfigSegment ConfigContourMeasure ReferencePackaging

/-- The literal companion mass is the sum of the two exact reference masses. -/
theorem reference_companion_mass_actual :
    p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
      ConfigContourMeasure.contourReferenceMeasure Set.univ = 1 := by
  unfold p0CompanionMeasure
  rw [Measure.add_apply]
  have hmap : (Measure.map Complex.ofReal ConfigSegment.pinnedReferenceMeasure) Set.univ =
      ConfigSegment.pinnedReferenceMeasure Set.univ := by
    rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ]
    simp
  rw [hmap, ReferencePackaging.pinnedReferenceMeasure_univ,
    ConfigContourMeasure.contourReferenceMeasure_univ]
  norm_num [← ENNReal.ofReal_add]

/-- The actual reference companion field is integrable on its literal compact support. -/
theorem reference_companion_field_integrable_actual :
    Integrable (fun z : ℂ => p0CompanionField z)
      (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure) := by
  letI : IsFiniteMeasure ConfigSegment.pinnedReferenceMeasure := by
    constructor
    rw [ReferencePackaging.pinnedReferenceMeasure_univ]
    exact ENNReal.ofReal_lt_top
  letI : IsFiniteMeasure ConfigContourMeasure.contourReferenceMeasure := inferInstance
  letI : IsFiniteMeasure
      (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure) := by
    constructor
    rw [reference_companion_mass_actual]
    norm_num
  apply EnergyLowerBound.integrable_companionField_of_ae_norm_le
  change ∀ᵐ z : ℂ ∂(Measure.map Complex.ofReal ConfigSegment.pinnedReferenceMeasure +
      ConfigContourMeasure.contourReferenceMeasure), ‖z‖ ≤ 4
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff Complex.measurable_ofReal.aemeasurable
      (isClosed_le continuous_norm continuous_const).measurableSet]
    have hk : ∀ᵐ x : ℝ ∂ConfigSegment.pinnedReferenceMeasure,
        x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) :=
      (Measure.absolutelyContinuous_of_le
        ReferencePackaging.pinnedReferenceMeasure_le_volume_restrict).ae_le
        (ae_restrict_mem measurableSet_Icc)
    filter_upwards [hk] with x hx
    simp only [Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  · filter_upwards [Measure.support_mem_ae
      (μ := ConfigContourMeasure.contourReferenceMeasure)] with z hz
    have hzG : z ∈ Gamma := ReferencePackaging.nu0_supported hz
    exact TubeVariance.norm_le_four_of_mem_Gamma hzG

end
end Li2Lean.P0
