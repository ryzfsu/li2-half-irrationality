/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceQLogFormula
import Li2Lean.P0.ActualReferenceQLogCross
import Li2Lean.P0.ActualReferenceQLogOutside

/-!
# A finite closed expression for the actual reference logarithmic energy

All six terms refer to the literal Appendix A arrays. The real interactions
use the second logarithmic primitive, the pinned interaction uses an exact
rational polynomial integral, the self-interaction uses the proved Fourier
identity, and the frequency interaction uses elementary endpoint primitives.
No free energy field or numerical premise is introduced.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ActualReferenceQLogClosed

noncomputable section

open ConfigSegment ConfigReferenceSymmetry ConfigContourReference
open ConfigQLogSegments ConfigQLogDecomposition
open ActualReferenceQLogFormula ConfigContourSelfPotential

def pinnedSelfFinite : ℝ :=
  ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 32,
    referenceDensity ConfigData.pinnedMassUnits i *
      referenceDensity ConfigData.pinnedMassUnits j *
      rectangleLogValue
        (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
        (referenceCellLeft (1 / 4) j) (referenceCellRight (1 / 4) j)

def frequencySelfFinite : ℝ :=
  ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160,
    referenceDensity ConfigData.frequencyMassUnits i *
      referenceDensity ConfigData.frequencyMassUnits j *
      rectangleLogValue
        (referenceCellLeft (1 / 2) i) (referenceCellRight (1 / 2) i)
        (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)

def pinnedFrequencyFinite : ℝ :=
  ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 160,
    referenceDensity ConfigData.pinnedMassUnits i *
      referenceDensity ConfigData.frequencyMassUnits j *
      rectangleLogAddValue
        (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
        (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j)

def frequencyContourFinite : ℝ :=
  ∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j *
    (ActualReferenceQLogOutside.outsideContourPrimitive (referenceCellRight (1 / 2) j) -
      ActualReferenceQLogOutside.outsideContourPrimitive (referenceCellLeft (1 / 2) j))

/-- The exact expression consumed by a rational interval enclosure. -/
def actualReferenceQLogFinite : ℝ :=
  pinnedSelfFinite + frequencySelfFinite + pinnedFrequencyFinite +
    2 * pinnedContourFinite + contourSelfEnergyFourier + frequencyContourFinite

/-- The source-locked six-term identity using the proven contour self-energy. -/
theorem actualReference_qLog_eq_six_terms :
    actualReference.qLog =
      pinnedSelfEnergy + frequencySelfEnergy + pinnedFrequencyCross +
        2 * ActualReferenceQLogCross.pinnedContour + contourSelfEnergyFourier +
          ActualReferenceQLogCross.frequencyContour := by
  rw [ActualReferenceQLogCross.actualReference_qLog_eq_six_terms]
  rw [show ActualReferenceQLogCross.contourSelf = contourSelfEnergyFourier from
    contour_self_energy_eq_fourier]
  rfl

/-- Unconditional closed finite formula for the literal `actualReference.qLog`. -/
theorem actualReference_qLog_eq_finite :
    actualReference.qLog = actualReferenceQLogFinite := by
  rw [actualReference_qLog_eq_six_terms]
  have hr := real_segment_terms_eq_rectangle_sums
  rw [hr.1, hr.2.1, hr.2.2]
  rw [show ActualReferenceQLogCross.pinnedContour = pinnedContourFinite from
      pinned_contour_eq_finite,
    show ActualReferenceQLogCross.frequencyContour = frequencyContourFinite from
      ActualReferenceQLogOutside.integral_contourReferencePotential_neg_frequency]
  rfl

end

end Li2Lean.P0.ActualReferenceQLogClosed

#print axioms Li2Lean.P0.ActualReferenceQLogClosed.actualReference_qLog_eq_six_terms
#print axioms Li2Lean.P0.ActualReferenceQLogClosed.actualReference_qLog_eq_finite
