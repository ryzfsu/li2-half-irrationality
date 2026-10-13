/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferencePinnedData
import Li2Lean.P0.CA.Contour.FourierConst
namespace Li2Lean.P0.ActualReferencePinnedData
open Li2Lean.P0.CA.Contour Li2Lean.P0.CA.Contour.QI
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000
def correctionI : QI := sumIdx 48 (fun n =>
  rnd (smul (powerIntTable.getD (n+1) 0 / (n+1 : ℚ)) (momI (n+1))))

theorem correctionI_check : QI.sub_le correctionI
    ⟨-39755 / 1000000, -39754 / 1000000⟩ = true := by decide +kernel

/-- Soundness of the finite correction interval, before the polynomial-integral bridge. -/
theorem correctionI_mem : correctionI.mem
    (∑ n ∈ Finset.range 48,
      ((powerIntTable.getD (n+1) 0 : ℚ) : ℝ) / (n+1 : ℝ) *
        ConfigContourSelfPotential.contourFourierMoment (n+1)) := by
  unfold correctionI
  apply mem_sumIdx
  intro n hn
  have h := mem_rnd (mem_smul (powerIntTable.getD (n+1) 0 / (n+1 : ℚ))
    (momI_mem (k := n+1) (by omega)))
  push_cast at h
  constructor <;> linarith [h.1, h.2]

theorem correction_enclosure :
    (-39755 / 1000000 : ℝ) ≤
      (∑ n ∈ Finset.range 48,
        ((powerIntTable.getD (n+1) 0 : ℚ) : ℝ) / (n+1 : ℝ) *
          ConfigContourSelfPotential.contourFourierMoment (n+1)) ∧
    (∑ n ∈ Finset.range 48,
        ((powerIntTable.getD (n+1) 0 : ℚ) : ℝ) / (n+1 : ℝ) *
          ConfigContourSelfPotential.contourFourierMoment (n+1)) ≤
      (-39754 / 1000000 : ℝ) := by
  have h := QI.mem_of_sub_le correctionI_check correctionI_mem
  norm_num only [QI.mem, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at h
  constructor <;> linarith [h.1, h.2]

end Li2Lean.P0.ActualReferencePinnedData
#print axioms Li2Lean.P0.ActualReferencePinnedData.pTable_recurrence
#print axioms Li2Lean.P0.ActualReferencePinnedData.momentTable_eq
#print axioms Li2Lean.P0.ActualReferencePinnedData.powerIntTable_eq
#print axioms Li2Lean.P0.ActualReferencePinnedData.correctionI_check

#print axioms Li2Lean.P0.ActualReferencePinnedData.correction_enclosure
