/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceClosure
import Li2Lean.P0.ConfigRealTail
open MeasureTheory Set
open scoped ENNReal
namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment ConfigRealTail Li2Lean.LogSegment
 theorem continuous_B0_literal : Continuous Config.B0 := by
  have h1 : Continuous (fun t : ℝ => primitive (t + 5 / 4)) :=
    continuous_primitive.comp (continuous_id.add continuous_const)
  have h2 : Continuous (fun t : ℝ => primitive (t + 1 / 4)) :=
    continuous_primitive.comp (continuous_id.add continuous_const)
  have h3 : Continuous (fun t : ℝ => primitive (t + 2)) :=
    continuous_primitive.comp (continuous_id.add continuous_const)
  have h4 : Continuous (fun t : ℝ => primitive t) := continuous_primitive.comp continuous_id
  have heq : Config.B0 = fun t : ℝ =>
      primitive (t + 5 / 4) - primitive (t + 1 / 4) +
        (primitive (t + 2) - primitive t) := by
    funext t
    exact B0_eq_endpoints t
  rw [heq]
  exact (h1.sub h2).add (h3.sub h4)
 theorem continuous_psi_literal : Continuous Config.psi := by
  have h1 : Continuous (fun t : ℝ => t * Real.log t) := Real.continuous_mul_log
  have h2 : Continuous (fun t : ℝ => (t - 1 / 2) * Real.log (t - 1 / 2)) :=
    Real.continuous_mul_log.comp (continuous_id.sub continuous_const)
  have h3 : Continuous (fun t : ℝ => t * ell) := continuous_id.mul continuous_const
  unfold Config.psi
  exact ((h1.sub h2).sub continuous_const).sub h3
 theorem frequencyReferenceMeasure_integrable_regularizedField :
    Integrable (fun t : ℝ => p0RegularizedFrequencyField t)
      ConfigSegment.frequencyReferenceMeasure := by
  unfold ConfigSegment.frequencyReferenceMeasure ConfigSegment.referenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  have hcc : IntegrableOn (fun t : ℝ => p0RegularizedFrequencyField t)
      (Set.Icc (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)) := by
    have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t))
        (Set.Icc (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)) := by
      apply ContinuousOn.log
      · fun_prop
      · intro t ht
        have hleft : (1 / 2 : ℝ) ≤ t := by
          have := ht.1
          simp only [referenceCellLeft] at this
          have hj0 : (0 : ℝ) ≤ (j : ℝ) := by positivity
          linarith
        intro hzero
        linarith
    have hfield : ContinuousOn (fun t : ℝ => p0RegularizedFrequencyField t)
        (Set.Icc (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)) := by
      unfold p0RegularizedFrequencyField
      exact ((continuous_B0_literal.continuousOn.sub continuous_psi_literal.continuousOn).sub
        (hlog.const_mul 3))
    exact hfield.integrableOn_Icc
  have hco := hcc.mono_set Ico_subset_Icc_self
  exact hco.smul_measure ENNReal.ofReal_ne_top
end
end Li2Lean.P0.ReferencePackaging
