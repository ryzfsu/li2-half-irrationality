/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceClosure
import Li2Lean.P0.ConfigPinnedTail
import Li2Lean.P0.ConfigRealTail
open MeasureTheory Set
open scoped ENNReal
namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment
 theorem pinnedReferenceMeasure_univ :
    pinnedReferenceMeasure Set.univ =
      ENNReal.ofReal (732114048060 / 1000000000000 : ℝ) := by
  unfold pinnedReferenceMeasure referenceMeasure
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ico,
    referenceCellRight, referenceCellLeft, smul_eq_mul]
  have hwidth : ∀ i : ℕ, (1 / 4 + ((i + 1 : ℕ) : ℝ) / 32 - (1 / 4 + (i : ℝ) / 32)) = ((i : ℝ) + 1) / 32 - (i : ℝ) / 32 := by
    intro i; push_cast; ring
  simp_rw [hwidth]
  have hs : (∑ j ∈ Finset.range 32,
      ENNReal.ofReal (referenceDensity ConfigData.pinnedMassUnits j) *
        ENNReal.ofReal (((j : ℝ) + 1) / 32 - (j : ℝ) / 32)) =
      ∑ j ∈ Finset.range 32,
        ENNReal.ofReal (referenceDensity ConfigData.pinnedMassUnits j *
          (((j : ℝ) + 1) / 32 - (j : ℝ) / 32)) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [ENNReal.ofReal_mul (referenceDensity_nonneg _ _)]
  rw [hs]
  have hterms : (∑ j ∈ Finset.range 32,
      ENNReal.ofReal (referenceDensity ConfigData.pinnedMassUnits j *
        (((j : ℝ) + 1) / 32 - (j : ℝ) / 32))) =
      ∑ j ∈ Finset.range 32,
        ENNReal.ofReal (referenceDensity ConfigData.pinnedMassUnits j * (1 / 32 : ℝ)) := by
    apply Finset.sum_congr rfl; intro j hj
    apply congrArg ENNReal.ofReal
    ring
  rw [hterms, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.sum_mul]
    rw [ConfigPinnedTail.pinnedReferenceDensity_sum]
    norm_num [ConfigPinnedTail.pinnedMass]
  · intro j hj
    exact mul_nonneg (referenceDensity_nonneg _ _) (by norm_num)
 theorem frequencyReferenceMeasure_univ :
    frequencyReferenceMeasure Set.univ = 1 := by
  unfold frequencyReferenceMeasure referenceMeasure
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.restrict_apply_univ, Real.volume_Ico,
    referenceCellRight, referenceCellLeft, smul_eq_mul]
  have hwidth : ∀ i : ℕ, (1 / 2 + ((i + 1 : ℕ) : ℝ) / 32 - (1 / 2 + (i : ℝ) / 32)) = ((i : ℝ) + 1) / 32 - (i : ℝ) / 32 := by
    intro i; push_cast; ring
  simp_rw [hwidth]
  have hs : (∑ j ∈ Finset.range 160,
      ENNReal.ofReal (referenceDensity ConfigData.frequencyMassUnits j) *
        ENNReal.ofReal (((j : ℝ) + 1) / 32 - (j : ℝ) / 32)) =
      ∑ j ∈ Finset.range 160,
        ENNReal.ofReal (referenceDensity ConfigData.frequencyMassUnits j *
          (((j : ℝ) + 1) / 32 - (j : ℝ) / 32)) := by
    apply Finset.sum_congr rfl; intro j hj
    rw [ENNReal.ofReal_mul (referenceDensity_nonneg _ _)]
  rw [hs]
  have hterms : (∑ j ∈ Finset.range 160,
      ENNReal.ofReal (referenceDensity ConfigData.frequencyMassUnits j *
        (((j : ℝ) + 1) / 32 - (j : ℝ) / 32))) =
      ∑ j ∈ Finset.range 160,
        ENNReal.ofReal (referenceDensity ConfigData.frequencyMassUnits j * (1 / 32 : ℝ)) := by
    apply Finset.sum_congr rfl; intro j hj
    apply congrArg ENNReal.ofReal
    ring
  rw [hterms, ← ENNReal.ofReal_sum_of_nonneg]
  · rw [← Finset.sum_mul]
    rw [ConfigRealTail.frequencyReferenceDensity_sum]
    norm_num
  · intro j hj
    exact mul_nonneg (referenceDensity_nonneg _ _) (by norm_num)
end
end Li2Lean.P0.ReferencePackaging
