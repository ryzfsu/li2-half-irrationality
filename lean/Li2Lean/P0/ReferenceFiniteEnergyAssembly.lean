/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Reference
import Li2Lean.P0.ReferenceActualSupport
import Li2Lean.P0.ReferenceAtomless
import Li2Lean.P0.ReferenceMass
import Li2Lean.P0.ReferenceFirstMoment
import Li2Lean.P0.ReferenceFrequencyField
import Li2Lean.P0.ReferenceEtaEnergy
import Li2Lean.P0.ReferenceCrossEnergy
import Li2Lean.P0.DensityCaps
import Li2Lean.P0.FrequencyKernelReference
import Li2Lean.P0.ContourFieldFinite
import Li2Lean.P0.ContourProductIntegrability
import Li2Lean.P0.ReferenceEtaMuMixed

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Li2Lean.P0
noncomputable section
open ConfigSegment ConfigContourMeasure ReferencePackaging

/-- Assemble the literal finite-energy reference once the two remaining
product-kernel integrability leaves are supplied explicitly.  The measure
inequalities, masses, atomlessness, field, first moment, and μ×μ kernel are
all discharged by concrete lemmas; no finite-energy certificate field is
accepted as input. -/
theorem p0ReferenceFiniteEnergyData_of_product_integrability
    (hEtaSelf : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      ((p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure).prod
       (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure)))
    (hEtaMu : Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
      ((p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure).prod
       ConfigSegment.frequencyReferenceMeasure)) :
    P0ReferenceFiniteEnergyData := by
  have hκ : ConfigSegment.pinnedReferenceMeasure ≤
      volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) :=
    ReferencePackaging.pinnedReferenceMeasure_le_volume_restrict
  have hμ : ConfigSegment.frequencyReferenceMeasure ≤
      volume.restrict (Set.Ici (1 / 2 : ℝ)) :=
    ReferencePackaging.frequencyReferenceMeasure_le_volume_restrict
  have hν : Measure.support ConfigContourMeasure.contourReferenceMeasure ⊆ Gamma := by
    simpa [ReferencePackaging.nu0, ConfigContourMeasure.contourReferenceMeasure] using
      ReferencePackaging.nu0_supported
  have hmass : p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
      ConfigContourMeasure.contourReferenceMeasure Set.univ = 1 :=
    reference_companion_mass_actual
  have hμmass : ConfigSegment.frequencyReferenceMeasure Set.univ = 1 :=
    ReferencePackaging.frequencyReferenceMeasure_univ
  have hηfield : Integrable (fun z : ℂ => p0CompanionField z)
      (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure) :=
    reference_companion_field_integrable_actual
  have hμid : Integrable (fun t : ℝ => t)
      ConfigSegment.frequencyReferenceMeasure :=
    ReferencePackaging.frequencyReferenceMeasure_integrable_id
  have hμfield : Integrable (fun t : ℝ => p0RegularizedFrequencyField t)
      ConfigSegment.frequencyReferenceMeasure :=
    ReferencePackaging.frequencyReferenceMeasure_integrable_regularizedField
  have hηatom : ∀ z : ℂ,
      (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure) {z} = 0 := by
    intro z
    exact ReferencePackaging.eta0_singleton_literal z
  have hμkernel : Integrable
      (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      (ConfigSegment.frequencyReferenceMeasure.prod
        ConfigSegment.frequencyReferenceMeasure) :=
    p0RegularizedFrequencyKernel_frequencyReference_integrable
  exact {
    kappa_le_density := hκ
    nu_supported := hν
    companion_mass := hmass
    mu_le_density := hμ
    frequency_mass := hμmass
    finite_energy := by
      refine ⟨hμid, hηfield, hμfield, ?_, hηatom, hμkernel, ?_⟩
      · exact hEtaSelf
      · exact hEtaMu }

end
end Li2Lean.P0

namespace Li2Lean.P0
noncomputable section
open ConfigSegment ConfigContourMeasure ReferencePackaging

/-- The η×η leaf reduces to the three proved C-A pieces plus the explicit
ν×ν contour product leaf. -/
theorem reference_eta_self_integrable_of_nu_self
    (hNuSelf : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      (ConfigContourMeasure.contourReferenceMeasure.prod
       ConfigContourMeasure.contourReferenceMeasure)) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      ((p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure).prod
       (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure)) := by
  have hkk := ReferencePackaging.integrable_li2LogKernel_kappa0_prod
  have hkn := ReferencePackaging.integrable_li2LogKernel_kappa0_nu0
  have hnk := ReferencePackaging.integrable_li2LogKernel_nu0_kappa0
  have hexpand := ReferencePackaging.eta0_prod_expand
  rw [show p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
      ConfigContourMeasure.contourReferenceMeasure =
      ReferencePackaging.eta0 by rfl]
  rw [hexpand]
  exact (((hkk.add_measure hkn).add_measure hnk).add_measure hNuSelf)

end
end Li2Lean.P0

namespace Li2Lean.P0
noncomputable section
open ConfigSegment ConfigContourMeasure ReferencePackaging

/-- The ν×ν leaf is discharged by the canonical contour product theorem; only
the mixed η×μ leaf remains explicit. -/
theorem p0ReferenceFiniteEnergyData_of_mixed_integrability
    (hEtaMu : Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
      ((p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
        ConfigContourMeasure.contourReferenceMeasure).prod
       ConfigSegment.frequencyReferenceMeasure)) :
    P0ReferenceFiniteEnergyData := by
  apply p0ReferenceFiniteEnergyData_of_product_integrability
  · exact reference_eta_self_integrable_of_nu_self
      ConfigContourProductIntegrability.contourReferenceMeasure_prod_integrable
  · exact hEtaMu

end
end Li2Lean.P0

namespace Li2Lean.P0
noncomputable section
open ConfigSegment ConfigContourMeasure ReferencePackaging

/-- The literal reference finite-energy witness: the eta self and eta-mu
product leaves are both discharged by concrete integrability theorems. -/
theorem p0ReferenceFiniteEnergyData_literal :
    P0ReferenceFiniteEnergyData := by
  exact p0ReferenceFiniteEnergyData_of_mixed_integrability
    ReferencePackaging.integrable_p0RegularizedMixedKernel_eta0_mu0


end
end Li2Lean.P0
