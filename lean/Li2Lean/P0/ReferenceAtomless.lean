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
open ConfigSegment ConfigContourMeasure
 theorem referenceMeasure_singleton (start : ℝ) (count : ℕ) (units : List ℕ) (x : ℝ) :
    referenceMeasure start count units {x} = 0 := by
  unfold referenceMeasure
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply, Measure.restrict_apply (measurableSet_singleton x)]
  simp only [smul_eq_mul]
  apply mul_eq_zero_of_right
  apply measure_mono_null inter_subset_left Real.volume_singleton
 theorem pinnedReferenceMeasure_singleton (x : ℝ) :
    pinnedReferenceMeasure {x} = 0 := by
  exact referenceMeasure_singleton _ _ _ _
 theorem eta0_singleton (z : ℂ) :
    (p0CompanionMeasure ConfigSegment.pinnedReferenceMeasure
      ConfigContourMeasure.contourReferenceMeasure) {z} = 0 := by
  rw [p0CompanionMeasure, Measure.add_apply]
  have hν := ConfigContourMeasure.contourReferenceMeasure_singleton z
  have hκ : Measure.map Complex.ofReal ConfigSegment.pinnedReferenceMeasure {z} = 0 := by
    rw [Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton z)]
    by_cases hz : z.im = 0
    · have hzre : z = Complex.ofReal z.re := by
        apply Complex.ext <;> simp [hz]
      have hpre : Complex.ofReal ⁻¹' {z} = {z.re} := by
        ext x
        constructor
        · intro hx
          change Complex.ofReal x = z at hx
          have hr := congrArg Complex.re hx
          simpa using hr
        · intro hx
          change Complex.ofReal x = z
          rw [hzre]
          congr 1
      rw [hpre, pinnedReferenceMeasure_singleton]
    · have hempty : Complex.ofReal ⁻¹' {z} = (∅ : Set ℝ) := by
        ext x
        constructor
        · intro hx
          change Complex.ofReal x = z at hx
          have hi := congrArg Complex.im hx
          exact (hz hi.symm).elim
        · intro hx
          exact hx.elim
      rw [hempty, measure_empty]
  rw [hκ, hν, zero_add]
end
end Li2Lean.P0.ReferencePackaging
