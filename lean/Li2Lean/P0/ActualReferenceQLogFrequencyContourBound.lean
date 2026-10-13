/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceQLogOutsideCertificate
import Li2Lean.P0.ActualReferenceQLogOutsideBridge

open MeasureTheory
namespace Li2Lean.P0.ActualReferenceQLogOutsideCheck
open ConfigSegment ConfigContourReference ActualReferenceQLogOutsideBridge

/-- A certified lower bound for the literal contour-frequency mixed energy. -/
theorem frequencyContour_lower :
    (350421/1000000 : ℝ) ≤
      ∫ t, contourReferencePotential (-(t : ℂ)) ∂frequencyReferenceMeasure := by
  rw [integral_contourReferencePotential_neg_frequency_eq_checker]
  have h := frequencyContourEndpoint_lower
  unfold frequencyContourEndpoint densityQ edgeQ at h
  unfold referenceDensity referenceCellRight referenceCellLeft
  norm_num only [ConfigData.referenceDenominator, Nat.cast_add, Nat.cast_one] at *
  push_cast at h
  exact h

end Li2Lean.P0.ActualReferenceQLogOutsideCheck
#print axioms Li2Lean.P0.ActualReferenceQLogOutsideCheck.frequencyContour_lower
