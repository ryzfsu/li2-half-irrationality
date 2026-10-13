/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceQLogClosed
import Li2Lean.P0.ActualReferenceQLogEnclosure
import Li2Lean.P0.ActualReferencePinnedBound
import Li2Lean.P0.ActualReferenceQLogFrequencyContourBound
import Li2Lean.P0.ConfigRectangleBounds

/-!
# Unconditional lower bound for the literal reference qLog

Every component below is an integral against the fixed Appendix A reference
measures. The logarithmic rectangle certificates, exact pinned polynomial,
Fourier self-energy, and exterior endpoint primitive are all kernel checked.
The pinned-contour interaction has multiplicity two in the actual qLog.
-/

namespace Li2Lean.P0.ActualReferenceQLogBound

open ConfigReferenceSymmetry ConfigQLogDecomposition
open ActualReferenceQLogClosed ActualReferenceQLogCross
open ActualReferenceQLogEnclosure

/-- The literal Appendix A reference logarithmic energy clears the required
rational threshold, with no numerical or analytic premise. -/
theorem actualReference_qLog_lower :
    (-11 / 25 : ℝ) < ConfigReferenceSymmetry.actualReference.qLog := by
  rw [ActualReferenceQLogClosed.actualReference_qLog_eq_six_terms]
  apply qLog_margin_of_component_bounds
  · exact ConfigRectangleBounds.pinnedSelfEnergy_bounds.1
  · exact ConfigRectangleBounds.frequencySelfEnergy_bounds.1
  · exact ConfigRectangleBounds.pinnedFrequencyCross_bounds.1
  · have h := ActualReferencePinnedBound.pinnedContour_enclosure.1
    change (774 / 10000 : ℝ) ≤ ActualReferenceQLogCross.pinnedContour at h
    linarith
  · have h := contourSelfEnergyFourier_enclosure.1
    linarith
  · have h := ActualReferenceQLogOutsideCheck.frequencyContour_lower
    change (350421 / 1000000 : ℝ) ≤ ActualReferenceQLogCross.frequencyContour at h
    linarith

end Li2Lean.P0.ActualReferenceQLogBound

#print axioms Li2Lean.P0.ActualReferenceQLogBound.actualReference_qLog_lower
