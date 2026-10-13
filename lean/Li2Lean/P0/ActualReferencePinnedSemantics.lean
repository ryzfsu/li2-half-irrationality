/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PinnedListBasic
import Li2Lean.P0.ActualReferencePinnedData
import Li2Lean.P0.ActualReferenceQLogFormula

open MeasureTheory
open scoped BigOperators
namespace Li2Lean.P0.ActualReferencePinnedSemantics
noncomputable section
set_option maxHeartbeats 4000000
open PinnedListBasic ActualReferencePinnedData ActualReferenceQLogFormula
open ConfigSegment ConfigContourReference

theorem evalL_addL (x : ℝ) (p q : List ℚ) :
    evalL x (addL p q) = evalL x p + evalL x q := by
  induction p generalizing q with
  | nil => simp [addL, evalL]
  | cons a p ih =>
    cases q with
    | nil => simp [addL, evalL]
    | cons b q => simp [addL, evalL, ih]; ring

theorem evalL_nextL (x : ℝ) (p q : List ℚ) :
    evalL x (nextL p q) =
      ((x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ)) * evalL x q -
      (1333 / 24233 : ℝ) * evalL x p := by
  simp only [nextL, evalL_addL, evalL, evalL_map]
  push_cast
  ring

theorem evalL_pTable (n : ℕ) (hn : n < 49) (x : ℝ) :
    evalL x (pTable.getD n []) = Polynomial.aeval x (pairPolyQ n) := by
  induction n using Nat.twoStepInduction with
  | zero => rw [pTable_zero]; simp [evalL, pairPolyQ]
  | one =>
    rw [pTable_one]
    simp [evalL, pairPolyQ, pairTraceQ]
    ring
  | more n h0 h1 =>
    rw [← pTable_recurrence n (by omega), evalL_nextL,
      h0 (by omega), h1 (by omega)]
    simp only [pairPolyQ, map_sub, map_mul, Polynomial.aeval_C, aeval_pairTraceQ]
    norm_num

theorem integral_monomial (k : ℕ) :
    (∫ x : ℝ, x ^ k ∂pinnedReferenceMeasure) = (monomialMomentQ k : ℝ) := by
  change (∫ x : ℝ, x ^ k ∂referenceMeasure (1 / 4) 32 ConfigData.pinnedMassUnits) = _
  rw [integral_reference_of_continuous (f := fun x : ℝ => x ^ k) (continuous_id.pow k)]
  simp_rw [integral_pow]
  unfold monomialMomentQ ConfigSegment.referenceDensity ConfigSegment.referenceCellLeft
    ConfigSegment.referenceCellRight
  push_cast
  simp [ConfigData.referenceDenominator, mul_div_assoc]

theorem integral_evalL (p : List ℚ) :
    (∫ x : ℝ, evalL x p ∂pinnedReferenceMeasure) =
      ∑ k ∈ Finset.range p.length, (p.getD k 0 : ℝ) * (monomialMomentQ k : ℝ) := by
  simp_rw [evalL_sum]
  rw [integral_finsetSum]
  · simp_rw [integral_const_mul, integral_monomial]
  · intro k hk
    exact integrable_reference_of_continuous (continuous_const.mul (continuous_id.pow k))
      (1 / 4) 32 ConfigData.pinnedMassUnits

theorem powerIntTable_eq_pinnedPowerIntegralQ (n : ℕ) (hn : n < 49) :
    powerIntTable.getD n 0 = pinnedPowerIntegralQ n := by
  rw [powerIntTable_eq n hn]
  have hm : integrateTable (pTable.getD n []) =
      ∑ k ∈ Finset.range (pTable.getD n []).length,
        (pTable.getD n []).getD k 0 * monomialMomentQ k := by
    unfold integrateTable
    apply Finset.sum_congr rfl
    intro k hk
    rw [momentTable_eq k (lt_of_lt_of_le (Finset.mem_range.mp hk) (pTable_length n hn))]
  rw [hm]
  apply Rat.cast_injective (α := ℝ)
  push_cast
  rw [← integral_evalL]
  simp_rw [evalL_pTable n hn]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat, pinnedReferenceMeasure,
    pinnedPowerIntegralQ] using
    integral_reference_aeval_eq (pairPolyQ n) (1 / 4) 32 ConfigData.pinnedMassUnits

end
end Li2Lean.P0.ActualReferencePinnedSemantics
#print axioms Li2Lean.P0.ActualReferencePinnedSemantics.powerIntTable_eq_pinnedPowerIntegralQ
