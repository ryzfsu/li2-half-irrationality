/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Receipt
import Li2Lean.P0.Tube.Gap.Ledger
import Li2Lean.P0.ContourEnergyLowerBound
import Li2Lean.P0.DualL6Reference

/-!
# Actual C-A receipt to the actual tube infimum

This is the producer interface for the completed row receipt.  The receipt is
the proposition `CAReceiptSlackActual`; it carries the row and analytic proof
obligations, but no free real alpha value.  The conclusions below refer to the
literal `P0.alphaGamma = sInf (Set.range p0ExtendedEnergy)` and the literal
`p0TubeAlpha`.
-/

namespace Li2Lean.P0.CA.Wire

open Li2Lean.P0
open Li2Lean.P0.CA.Receipt
open Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.L6Admissible
open Li2Lean.P0.TubeGap

noncomputable section

/-- A finite-energy literal reference makes the actual contour infimum finite
above.  The lower bound is the independently proved `-200` bound, and the
reference itself supplies a finite member of the energy range. -/
theorem alphaGamma_lt_top_of_reference_finite
    (h : P0ReferenceFiniteEnergyData) : P0.alphaGamma < ⊤ := by
  have hle : P0.alphaGamma ≤ P0.p0ExtendedEnergy (p0ReferenceMeasures h) := by
    unfold P0.alphaGamma
    exact csInf_le EnergyLowerBound.p0ExtendedEnergy_bddBelow
      (Set.mem_range_self (p0ReferenceMeasures h))
  rw [P0.p0ExtendedEnergy_eq_value_of_finite (p0ReferenceMeasures h)
    (p0ReferenceMeasures_finite_energy h)] at hle
  exact lt_of_le_of_lt hle (WithTop.coe_lt_top _)

/-- Compose an actual C-A receipt with the actual tube transfer. -/
theorem actual_receipt_alphaGamma_and_tube_lower
    (R : CAReceiptSlackActual)
    (h : P0ReferenceFiniteEnergyData)
    {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ tubeRadiusMax) :
    BddBelow (Set.range P0.p0ExtendedEnergy) ∧
    ((-200 : ℝ) : WithTop ℝ) ≤ P0.alphaGamma ∧
    ((397 / 200 : ℝ) : WithTop ℝ) < P0.alphaGamma ∧
    P0.alphaGamma < ⊤ ∧
    ((397 / 200 - 300 * δ : ℝ) : WithTop ℝ) ≤ P0.p0TubeAlpha δ := by
  have hCA : ((397 / 200 : ℝ) : WithTop ℝ) < P0.alphaGamma := by
    have hR := R.alpha_bound
    have heq : (((P0.caSlackAlphaTarget : ℚ) : ℝ) : WithTop ℝ) =
        ((397 / 200 : ℝ) : WithTop ℝ) := by
      norm_num [P0.caSlackAlphaTarget]
    rw [heq] at hR
    exact hR
  have hTube := p0TubeAlpha_ge_actual hδ hδmax hCA.le
  refine ⟨EnergyLowerBound.p0ExtendedEnergy_bddBelow,
    EnergyLowerBound.alphaGamma_ge, hCA,
    alphaGamma_lt_top_of_reference_finite h, ?_⟩
  convert hTube using 1 <;> norm_num

end

end Li2Lean.P0.CA.Wire
