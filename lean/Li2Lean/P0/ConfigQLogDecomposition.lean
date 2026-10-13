/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigQLogSegments

open MeasureTheory

namespace Li2Lean.P0.ConfigQLogDecomposition

noncomputable section

open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigQLogSegments

/-! The real-segment interactions reduce to finite rectangle sums. -/

def pinnedSelfEnergy : ℝ :=
  ∫ x, pinnedReferencePotential x ∂pinnedReferenceMeasure

def frequencySelfEnergy : ℝ :=
  ∫ x, frequencyReferencePotential x ∂frequencyReferenceMeasure

def pinnedFrequencyCross : ℝ :=
  ∫ x, reflectedFrequencyPotential (x : ℂ) ∂pinnedReferenceMeasure

def pinnedEtaField : ℝ :=
  ∫ x, etaReferencePotential (x : ℂ) ∂pinnedReferenceMeasure

def contourEtaField : ℝ :=
  contourReferenceIntegral etaReferencePotential

def contourFrequencyCross : ℝ :=
  contourReferenceIntegral reflectedFrequencyPotential

/-- Exact decomposition of the literal reference energy into the two
eta-potential integrals, the frequency self-energy, and the two
eta--frequency interactions. Contour terms remain as the actual contour
integrals. -/
theorem actualReference_qLog_eq_five_terms :
    actualReference.qLog =
      pinnedEtaField + contourEtaField + frequencySelfEnergy +
        pinnedFrequencyCross + contourFrequencyCross := by
  unfold actualReference qEtaEta qMuMu qEtaMu etaReferenceIntegral
    pinnedEtaField contourEtaField frequencySelfEnergy pinnedFrequencyCross
    contourFrequencyCross
  abel

/-- The three purely real-segment energies are exactly the finite rectangle
sums for the pinned and frequency references and their reflected interaction.
-/
theorem real_segment_terms_eq_rectangle_sums :
    pinnedSelfEnergy =
        ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 32,
          referenceDensity ConfigData.pinnedMassUnits i *
            referenceDensity ConfigData.pinnedMassUnits j *
            rectangleLogValue
              (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
              (referenceCellLeft (1 / 4) j) (referenceCellRight (1 / 4) j) ∧
    frequencySelfEnergy =
        ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160,
          referenceDensity ConfigData.frequencyMassUnits i *
            referenceDensity ConfigData.frequencyMassUnits j *
            rectangleLogValue
              (referenceCellLeft (1 / 2) i) (referenceCellRight (1 / 2) i)
              (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j) ∧
    pinnedFrequencyCross =
        ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 160,
          referenceDensity ConfigData.pinnedMassUnits i *
            referenceDensity ConfigData.frequencyMassUnits j *
            rectangleLogAddValue
              (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
              (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j) := by
  refine ⟨?_, ?_, ?_⟩
  · exact pinnedSelfEnergy_eq_rectangleSum
  · exact frequencySelfEnergy_eq_rectangleSum
  · exact pinnedReflectedFrequencyEnergy_eq_rectangleSum

end

end Li2Lean.P0.ConfigQLogDecomposition

#print axioms Li2Lean.P0.ConfigQLogDecomposition.actualReference_qLog_eq_five_terms
#print axioms Li2Lean.P0.ConfigQLogDecomposition.real_segment_terms_eq_rectangle_sums
