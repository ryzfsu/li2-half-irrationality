/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceCASlackAdapter
import Li2Lean.P0.ActualReferenceQLogBound
import Li2Lean.P0.CA.Wire.RowInputs
import Li2Lean.P0.CA.Wire.AlphaTubeActualMinimal

/-!
# Premise-free `397/200 < alphaGamma` and the actual tube lower bound

All inputs of the actual C-A slack receipt are theorems:

* rows: `CA.Wire.caRowInputs` (2511 contour, 8192 pinned, 16384 frequency
  rows, kernel checked);
* reference-energy enclosure: `ActualReferenceQLogBound.actualReference_qLog_lower`
  (`-11/25 < actualReference.qLog`);
* L6 linearization: `p0ReferenceFiniteEnergyData_literal` and
  `p0L6CrossEnergy_actual_reference` (used inside `caAnalyticInputs_of_qLog`).

The conclusions are about the literal `P0.alphaGamma`
(`sInf (Set.range p0ExtendedEnergy)`) and the literal `P0.p0TubeAlpha`.
No hypothesis of any theorem below restates its conclusion; the theorems in
this file take no premise except the tube radius range.
-/

namespace Li2Lean.P0.AlphaUnconditional

open Li2Lean.P0
open Li2Lean.P0.CA.Receipt
open Li2Lean.P0.TubeGap

noncomputable section

/-- The completed actual C-A slack receipt, with no premise. -/
theorem caReceiptSlackActual_proved : CAReceiptSlackActual :=
  caReceiptSlackActual_of_caRows CA.Wire.caRowInputs
    ActualReferenceQLogBound.actualReference_qLog_lower

/-- Premise-free C-A target: `397/200 < alphaGamma`. -/
theorem alphaGamma_gt_397_200 : ((397 / 200 : ℝ) : WithTop ℝ) < P0.alphaGamma :=
  actualReference_alpha397_lt_of_caRows CA.Wire.caRowInputs
    ActualReferenceQLogBound.actualReference_qLog_lower

/-- Premise-free floor: `199/100 < alphaGamma`. -/
theorem alphaGamma_gt_199_100 : ((199 / 100 : ℝ) : WithTop ℝ) < P0.alphaGamma :=
  actualReference_alphaFloor_lt_of_caReceipt caReceiptSlackActual_proved

/-- Premise-free statement-audit S4 package: the energy range is bounded
below, `-200 ≤ alphaGamma`, `397/200 < alphaGamma < ⊤`, and the literal tube
infimum is at least `397/200 - 300 δ` for every admissible tube radius. -/
theorem alphaGamma_and_tube_lower_unconditional
    {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ tubeRadiusMax) :
    BddBelow (Set.range P0.p0ExtendedEnergy) ∧
    ((-200 : ℝ) : WithTop ℝ) ≤ P0.alphaGamma ∧
    ((397 / 200 : ℝ) : WithTop ℝ) < P0.alphaGamma ∧
    P0.alphaGamma < ⊤ ∧
    ((397 / 200 - 300 * δ : ℝ) : WithTop ℝ) ≤ P0.p0TubeAlpha δ :=
  CA.Wire.actual_receipt_alphaGamma_and_tube_lower caReceiptSlackActual_proved
    p0ReferenceFiniteEnergyData_literal hδ hδmax

/-- `alphaGamma` is a finite real number above `397/200`. -/
theorem alphaGamma_finite_gt_397_200 :
    ∃ a : ℝ, P0.alphaGamma = (a : WithTop ℝ) ∧ 397 / 200 < a := by
  have hR := alphaGamma_and_tube_lower_unconditional (δ := 1 / 64) (by norm_num)
    (by norm_num [tubeRadiusMax])
  obtain ⟨-, -, hlt, htop, -⟩ := hR
  obtain ⟨a, ha⟩ := WithTop.ne_top_iff_exists.mp htop.ne
  refine ⟨a, ha.symm, ?_⟩
  rw [← ha] at hlt
  exact_mod_cast hlt

end

end Li2Lean.P0.AlphaUnconditional
