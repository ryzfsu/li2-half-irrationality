/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Agents.F_L8.Types
import Li2Lean.Kit.MeanValueRemainder

/-
Adapter from the generic mean-value allowance theorem to the existing
ReceiptCell.modelRemainderValid interface. The adapted receipt lowers the
row floor by exactly the allowance; it does not assert the old floor itself.
The analytic midpoint and derivative premises remain explicit.
-/

namespace Li2Lean.F_L8

open ContourKit

/-- A receipt row with its certified value-error allowance spent from the floor. -/
def ReceiptCell.afterAllowance (c : ReceiptCell) (allowance : ℚ) : ReceiptCell :=
  { c with lower := c.lower - allowance }

/-- The Lipschitz row theorem proves the existing zero-remainder model for the
floor after allowance is spent. -/
theorem ReceiptCell.modelRemainderValid_afterAllowance
    (c : ReceiptCell) (allowance slope : ℚ) (hwidth : c.lo ≤ c.hi)
    (hcheck : ContourKit.checkMeanValueAllowance c.lo c.hi allowance slope = true)
    {f : ℝ → ℝ}
    (hcenter : (c.lower : ℝ) ≤
      f (ContourKit.rationalCellCenter c.lo c.hi : ℝ))
    (hdiff : ∀ y ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ), DifferentiableAt ℝ f y)
    (hderiv : ∀ y ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ),
      |deriv f y| ≤ (slope : ℝ)) :
    (c.afterAllowance allowance).modelRemainderValid f hwidth := by
  intro x hx
  have hbound := ContourKit.meanValueAllowance_row_sound
    (lo := c.lo) (hi := c.hi) (lower := c.lower)
    (allowance := allowance) (slope := slope)
    hcheck hcenter hdiff hderiv hx.1 hx.2
  simp only [ReceiptCell.modelRemainderValid,
    ContourKit.TaylorLowerRemainderValid, ReceiptCell.model,
    ReceiptCell.afterAllowance] at hx ⊢
  simp only [horner, Rat.cast_zero, neg_zero, mul_zero, add_zero]
  push_cast
  linarith

end Li2Lean.F_L8

