/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Agents.F_L8.Types
import Mathlib.Data.Rat.Init

/-!
# Generic slack receipt for the narrowed C-A target

This module carries the regenerated C-A row tables without identifying them
with ConfigData. A receipt stores the three row lists, their exact lengths
(2511 contour, 8192 pinned, 16384 frequency), the rational floor -1673/500,
and explicit regional and total allowance accounting. The exact-chain fields
only record rational coverage; analytic modelRemainderValid obligations remain
separate inputs for the eventual CAReceipt.

The target is the paper-preserving narrowed value 397/200. No row data or
potential callback is hard-coded here, so a generated table can be checked and
then instantiated independently.
-/

namespace Li2Lean.P0

open Li2Lean.F_L8

noncomputable section

/-- Narrowed C-A target from the slack regeneration, 397/200. -/
def caSlackAlphaTarget : ℚ := 397 / 200

/-- Common lower floor carried by the regenerated slack table. -/
def caSlackFloor : ℚ := -(1673 : ℚ) / 500

/-- One generated rational row together with its value-error allowance. -/
structure SlackRow where
  cell : ReceiptCell
  allowance : ℚ
  allowance_nonneg : 0 ≤ allowance
  deriving Repr

namespace SlackRow

/-- Forget the allowance and recover the receipt cell used by ExactChain. -/
def toReceiptCell (r : SlackRow) : ReceiptCell := r.cell

end SlackRow

/-- The cells underlying a list of generated rows. -/
def slackCells (rows : List SlackRow) : List ReceiptCell :=
  rows.map SlackRow.toReceiptCell

/-- The total value-error allowance assigned to a row list. -/
def slackAllowanceSum (rows : List SlackRow) : ℚ :=
  (rows.map SlackRow.allowance).sum

theorem slackAllowanceSum_nil : slackAllowanceSum [] = 0 := by
  rfl

theorem slackAllowanceSum_cons (r : SlackRow) (rows : List SlackRow) :
    slackAllowanceSum (r :: rows) = r.allowance + slackAllowanceSum rows := by
  rfl

theorem slackAllowanceSum_nonneg (rows : List SlackRow) :
    0 ≤ slackAllowanceSum rows := by
  induction rows with
  | nil =>
      simp [slackAllowanceSum]
  | cons r rows ih =>
      rw [slackAllowanceSum_cons]
      exact add_nonneg r.allowance_nonneg ih

/-- A generated three-region certificate for the 397/200 slack target.

The table data are deliberately abstract lists. In particular, the exact-chain
fields do not mention ConfigData and can be filled by a regenerated table
after its reflected row checker has been proved sound.
-/
structure CAReceiptSlack where
  contourRows : List SlackRow
  pinnedRows : List SlackRow
  frequencyRows : List SlackRow
  contour_rows_length : contourRows.length = 2511
  pinned_rows_length : pinnedRows.length = 8192
  frequency_rows_length : frequencyRows.length = 16384
  contour_chain : ExactChain (slackCells contourRows) 0 1
  pinned_chain : ExactChain (slackCells pinnedRows) (1 / 4) (5 / 4)
  frequency_chain : ExactChain (slackCells frequencyRows) (1 / 2) (81 / 10)
  floor : ℚ
  floor_eq : floor = caSlackFloor
  contour_floor : ∀ r ∈ contourRows, floor ≤ r.cell.lower
  pinned_floor : ∀ r ∈ pinnedRows, floor ≤ r.cell.lower
  frequency_floor : ∀ r ∈ frequencyRows, floor ≤ r.cell.lower
  contour_allowance_budget : ℚ
  pinned_allowance_budget : ℚ
  frequency_allowance_budget : ℚ
  total_allowance_budget : ℚ
  contour_allowance_budget_nonneg : 0 ≤ contour_allowance_budget
  pinned_allowance_budget_nonneg : 0 ≤ pinned_allowance_budget
  frequency_allowance_budget_nonneg : 0 ≤ frequency_allowance_budget
  total_allowance_budget_nonneg : 0 ≤ total_allowance_budget
  regional_budget_sum_le_total :
    contour_allowance_budget + pinned_allowance_budget +
        frequency_allowance_budget ≤ total_allowance_budget
  contour_allowance_sum_le :
    slackAllowanceSum contourRows ≤ contour_allowance_budget
  pinned_allowance_sum_le :
    slackAllowanceSum pinnedRows ≤ pinned_allowance_budget
  frequency_allowance_sum_le :
    slackAllowanceSum frequencyRows ≤ frequency_allowance_budget
  total_allowance_sum_le :
    slackAllowanceSum contourRows + slackAllowanceSum pinnedRows +
        slackAllowanceSum frequencyRows ≤ total_allowance_budget
  alphaTarget : ℚ
  alphaTarget_eq : alphaTarget = caSlackAlphaTarget

/-- The row count carried by a contour slack receipt. -/
theorem CAReceiptSlack.contour_count (R : CAReceiptSlack) :
    R.contourRows.length = 2511 :=
  R.contour_rows_length

/-- The row count carried by a pinned slack receipt. -/
theorem CAReceiptSlack.pinned_count (R : CAReceiptSlack) :
    R.pinnedRows.length = 8192 :=
  R.pinned_rows_length

/-- The row count carried by a frequency slack receipt. -/
theorem CAReceiptSlack.frequency_count (R : CAReceiptSlack) :
    R.frequencyRows.length = 16384 :=
  R.frequency_rows_length

/-- The exact narrowed target encoded by a slack receipt. -/
theorem CAReceiptSlack.target_eq (R : CAReceiptSlack) :
    R.alphaTarget = (397 / 200 : ℚ) := by
  rw [R.alphaTarget_eq]
  rfl

/-- The exact common floor encoded by a slack receipt. -/
theorem CAReceiptSlack.floor_value (R : CAReceiptSlack) :
    R.floor = (-(1673 : ℚ) / 500) := by
  exact R.floor_eq

/-- Every allowance sum is nonnegative independently of the table values. -/
theorem CAReceiptSlack.allowance_sums_nonneg (R : CAReceiptSlack) :
    0 ≤ slackAllowanceSum R.contourRows ∧
      0 ≤ slackAllowanceSum R.pinnedRows ∧
      0 ≤ slackAllowanceSum R.frequencyRows :=
  ⟨slackAllowanceSum_nonneg _, slackAllowanceSum_nonneg _,
    slackAllowanceSum_nonneg _⟩

/-- The regional allowance budgets add up to at most the total budget. -/
theorem CAReceiptSlack.regional_budget_le_total (R : CAReceiptSlack) :
    R.contour_allowance_budget + R.pinned_allowance_budget +
        R.frequency_allowance_budget ≤ R.total_allowance_budget :=
  R.regional_budget_sum_le_total

end

end Li2Lean.P0
