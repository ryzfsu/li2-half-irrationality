/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceClosure
open MeasureTheory Set
open scoped ENNReal
namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment
 theorem frequencyReferenceMeasure_integrable_id :
    Integrable (fun t : ℝ => t) frequencyReferenceMeasure := by
  unfold frequencyReferenceMeasure referenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  have hcc : IntegrableOn (fun t : ℝ => t)
      (Set.Icc (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)) :=
    continuousOn_id.integrableOn_Icc
  have hco : IntegrableOn (fun t : ℝ => t)
      (Set.Ico (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)) :=
    hcc.mono_set Ico_subset_Icc_self
  exact hco.smul_measure ENNReal.ofReal_ne_top
end
end Li2Lean.P0.ReferencePackaging
