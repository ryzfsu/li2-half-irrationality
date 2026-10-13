/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferencePinnedSemantics
import Li2Lean.P0.ActualReferencePinnedCorrection
import Li2Lean.P0.ConfigLogEnclosures

open MeasureTheory
namespace Li2Lean.P0.ActualReferencePinnedBound
open ActualReferencePinnedData ActualReferencePinnedSemantics
open ActualReferenceQLogFormula ConfigContourSelfPotential ConfigContourKernel

/-- A deliberately coarse bound retaining the unchanged actual pinned and contour masses. -/
theorem pinnedContourFinite_enclosure :
    (774 / 10000 : ℝ) ≤ pinnedContourFinite ∧
      pinnedContourFinite ≤ (7741 / 100000 : ℝ) := by
  have heq : (∑ n ∈ Finset.range 48, contourFourierMoment (n+1) *
      ((pinnedPowerIntegralQ (n+1) : ℝ) / (n+1 : ℝ))) =
      ∑ n ∈ Finset.range 48,
        ((powerIntTable.getD (n+1) 0 : ℚ) : ℝ) / (n+1 : ℝ) *
          contourFourierMoment (n+1) := by
    apply Finset.sum_congr rfl
    intro n hn
    rw [← powerIntTable_eq_pinnedPowerIntegralQ (n+1) (by
      have := Finset.mem_range.mp hn
      omega)]
    ring
  rw [pinnedContourFinite_eq_sum48, heq]
  have hS := correction_enclosure
  have hlog := ConfigLogEnclosures.log_referenceScale_enclosure_v10
  change (191983067064 / 1000000000000 : ℝ) ≤ Real.log contourScale ∧
    Real.log contourScale ≤ (191983067065 / 1000000000000 : ℝ) at hlog
  dsimp [ConfigPinnedTail.pinnedMass, contourMass]
  constructor <;> nlinarith [hlog.1, hlog.2, hS.1, hS.2]

/-- The same bound for the genuine contour potential integrated against the actual pinned measure. -/
theorem pinnedContour_enclosure :
    (774 / 10000 : ℝ) ≤
      (∫ x, ConfigContourReference.contourReferencePotential (x : ℂ)
        ∂ConfigSegment.pinnedReferenceMeasure) ∧
    (∫ x, ConfigContourReference.contourReferencePotential (x : ℂ)
        ∂ConfigSegment.pinnedReferenceMeasure) ≤ (7741 / 100000 : ℝ) := by
  rw [pinned_contour_eq_finite]
  exact pinnedContourFinite_enclosure

end Li2Lean.P0.ActualReferencePinnedBound
#print axioms Li2Lean.P0.ActualReferencePinnedBound.pinnedContour_enclosure
