/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferencePackaging
import Li2Lean.P0.TubeInteriorPotential

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.ReferencePackaging

noncomputable section
open ConfigSegment ConfigContourMeasure

/-- The Fejér contour is carried on the literal ellipse: this is a support
statement obtained from the map itself, with no surrogate contour. -/
theorem nu0_supported : Measure.support nu0 ⊆ Gamma := by
  apply Measure.support_subset_of_isClosed TubeInterior.isCompact_Gamma.isClosed
  have hzero : nu0 Gammaᶜ = 0 := by
    rw [nu0, contourReferenceMeasure, Measure.map_apply continuous_ellipse.measurable
      TubeInterior.isCompact_Gamma.isClosed.measurableSet.compl]
    have hpre : (Li2Lean.p0EllipsePoint 1 ⁻¹' Gammaᶜ) = (∅ : Set ℝ) := by
      ext u
      simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_range]
      constructor
      · intro h
        exact (h ⟨u, (ellipsePoint_one_eq_gammaPoint u).symm⟩).elim
      · intro h
        exact h.elim
    rw [hpre]
    simp
  exact hzero

end
end Li2Lean.P0.ReferencePackaging

namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment

/-- The stored Appendix-A arrays obey the unit-density cap cell by cell. -/
theorem pinned_units_cap (j : ℕ) (hj : j < 32) :
    32 * ConfigData.pinnedMassUnits.getD j 0 ≤
      ConfigData.referenceDenominator := by
  have hj' : j ≤ 31 := by omega
  interval_cases j <;> decide +kernel

theorem frequency_units_cap (j : ℕ) (hj : j < 160) :
    32 * ConfigData.frequencyMassUnits.getD j 0 ≤
      ConfigData.referenceDenominator := by
  have hj' : j ≤ 159 := by omega
  interval_cases j <;> decide +kernel

theorem pinned_density_cap (j : ℕ) (hj : j < 32) :
    referenceDensity ConfigData.pinnedMassUnits j ≤ 1 := by
  unfold referenceDensity
  have h := pinned_units_cap j hj
  apply (div_le_iff₀ (by norm_num [ConfigData.referenceDenominator])).2
  exact_mod_cast h

theorem frequency_density_cap (j : ℕ) (hj : j < 160) :
    referenceDensity ConfigData.frequencyMassUnits j ≤ 1 := by
  unfold referenceDensity
  have h := frequency_units_cap j hj
  apply (div_le_iff₀ (by norm_num [ConfigData.referenceDenominator])).2
  exact_mod_cast h

end
end Li2Lean.P0.ReferencePackaging

namespace Li2Lean.P0.ReferencePackaging
noncomputable section

/-- The remaining exact mass closure is recorded as explicit obligations for
 the reference triple; no certificate field hides these equalities. -/
def exactMassClosureObligations : Prop :=
  kappa0 Set.univ = ENNReal.ofReal (732114048060 / 1000000000000 : ℝ) ∧
  mu0 Set.univ = 1 ∧ eta0 Set.univ = 1

end
end Li2Lean.P0.ReferencePackaging
