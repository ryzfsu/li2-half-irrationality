/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.RowInputs
import Li2Lean.P0.ConfigSlackSemanticIdentity
import Li2Lean.P0.ConfigContourTail
import Li2Lean.P0.ConfigTail

/-!
# The frequency tail beyond `81/10`

The actual `Wmu` is differentiable on `(11/2, ∞)`, its derivative is at least
the v10 (5.8) envelope `tailSlopeV10`, hence at least
`28975217729/991618303000 > 0` on `[81/10, ∞)`, and `Wmu` is monotone there.
Every step is proved from the actual reference: the real fields
(`realTailWithPinned_deriv_ge`), the Fejer contour slope
(`contourReferencePotential_neg_deriv_le`) and the exact masses
`pinnedMass + contourMass = 1`.
-/

open Set

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.P0.ConfigSegment Li2Lean.P0.ConfigRealTail Li2Lean.P0.ConfigPinnedTail
  Li2Lean.P0.ConfigContourTail Li2Lean.P0.ConfigContourReference

noncomputable section

/-- The contour part of `Wmu`, as a function of the frequency variable. -/
def contourNeg (t : ℝ) : ℝ := contourReferencePotential (-(t : ℂ))

theorem frequencyFunction_eq_tail :
    frequencyFunction = fun t => realTailWithPinned t - contourNeg t := by
  funext t
  rw [frequencyFunction,
    ConfigSlackSemanticIdentity.actualWmu_eq_reference_integrals]
  simp only [realTailWithPinned, realTailPart, contourNeg]

theorem realTailWithPinned_hasDerivAt {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    DifferentiableAt ℝ realTailWithPinned t := by
  have ht0 : 0 ≤ t := by linarith
  have ht1 : (1 / 2 : ℝ) < t := by linarith
  have hreal := (((B0_hasDerivAt (by linarith : 0 < t)).sub (psi_hasDerivAt ht1)).sub
    ((frequencyReferencePotential_hasDerivAt ht).const_mul 2))
  have hp := pinnedReferenceNegative_hasDerivAt ht0
  exact (hreal.sub hp).differentiableAt

theorem contourNeg_differentiableAt {t : ℝ} (ht : leftClearance < t) :
    DifferentiableAt ℝ contourNeg t :=
  (hasDerivAt_contourReferencePotential_neg ht).differentiableAt

theorem frequencyFunction_differentiableAt {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    DifferentiableAt ℝ frequencyFunction t := by
  have hc : leftClearance < t := by unfold leftClearance; linarith
  rw [frequencyFunction_eq_tail]
  exact (realTailWithPinned_hasDerivAt ht).sub (contourNeg_differentiableAt hc)

/-- The derivative of the actual `Wmu` dominates the v10 (5.8) envelope. -/
theorem frequencyFunction_deriv_ge_envelope {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    ConfigTail.tailSlopeV10 t ≤ deriv frequencyFunction t := by
  have hc : leftClearance < t := by unfold leftClearance; linarith
  have hsplit : deriv frequencyFunction t =
      deriv realTailWithPinned t - deriv contourNeg t := by
    rw [frequencyFunction_eq_tail]
    exact ((realTailWithPinned_hasDerivAt ht).hasDerivAt.sub
      (contourNeg_differentiableAt hc).hasDerivAt).deriv
  rw [hsplit]
  have hr := realTailWithPinned_deriv_ge ht
  have hcn : deriv contourNeg t ≤ contourMass / (t - leftClearance) :=
    contourReferencePotential_neg_deriv_le hc
  have hd : 0 < t - leftClearance := by linarith
  have hq : 0 < t + 1 / 4 := by linarith
  have hpm : pinnedMass / (t + 1 / 4) ≤ pinnedMass / (t - leftClearance) := by
    apply div_le_div_of_nonneg_left (by norm_num [pinnedMass]) hd
    unfold leftClearance
    linarith
  have hmass : pinnedMass / (t - leftClearance) + contourMass / (t - leftClearance) =
      1 / (t - (751 / 5000)) := by
    unfold pinnedMass contourMass leftClearance
    rw [← add_div]
    norm_num
  unfold ConfigTail.tailSlopeV10 ConfigTail.tailSlopeRationalV10
  have hneg : (-1 : ℝ) / (2 * (t - 1 / 2)) = -(1 / (2 * (t - 1 / 2))) := neg_div _ _
  rw [hneg]
  linarith

/-- The derivative of the actual `Wmu` is at least the v10 tail floor. -/
theorem frequencyFunction_deriv_ge_floor {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    ConfigTail.tailSlopeFloorV10 ≤ deriv frequencyFunction t :=
  ConfigTail.derivative_lower_of_v10_envelope ht
    (frequencyFunction_deriv_ge_envelope (by linarith))

/-- The actual `Wmu` is monotone on `[81/10, ∞)`. -/
theorem frequencyFunction_monotoneOn :
    MonotoneOn frequencyFunction (Ici (81 / 10 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici _)
  · intro t ht
    exact (frequencyFunction_differentiableAt
      (by have := (mem_Ici.mp ht); linarith)).continuousAt.continuousWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    exact (frequencyFunction_differentiableAt
      (by have := (mem_Ioi.mp ht); linarith)).differentiableWithinAt
  · intro t ht
    rw [interior_Ici] at ht
    have h := frequencyFunction_deriv_ge_floor (le_of_lt (mem_Ioi.mp ht))
    have hpos : (0 : ℝ) ≤ ConfigTail.tailSlopeFloorV10 := by
      unfold ConfigTail.tailSlopeFloorV10
      norm_num
    linarith

theorem frequencyFunction_tail_ge {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    frequencyFunction (81 / 10) ≤ frequencyFunction t :=
  frequencyFunction_monotoneOn (mem_Ici.mpr le_rfl) (mem_Ici.mpr ht) ht

end

end Li2Lean.P0.CA.Receipt
