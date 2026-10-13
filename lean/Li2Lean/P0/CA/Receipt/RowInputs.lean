/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Data
import Li2Lean.P0.CA.Receipt.Penalty
import Li2Lean.P0.ConfigReferenceSymmetry

/-!
# The three regional row inputs of the C-A 397/200 receipt

These are the only analytic row hypotheses of the receipt. Each says that
every row of the generated slack table (`Data.contourRows`,
`Data.pinnedRows`, `Data.frequencyRows`) satisfies the ORIGINAL constant-model
remainder obligation `ReceiptCell.modelRemainderValid` for the ACTUAL first
variation at `ConfigReferenceSymmetry.actualReference`:

* contour: `u ↦ Weta actualReference (p0EllipsePoint 1 (π u))` on `[0,1]`;
* pinned: `x ↦ Weta actualReference x` on `[1/4,5/4]`;
* frequency: `Wmu actualReference` on `[1/2,81/10]`.

The functions and the `RowsValid` predicate have exactly the shape of the
`CAReceipt` fields `contour_cell_bounds`, `pinned_cell_bounds`,
`frequency_cell_bounds`. Region agents may prove the statement shard by shard
and combine with `rowsValid_append`.
-/

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.F_L8
open Li2Lean.P0.ConfigReferenceSymmetry

noncomputable section

/-- The actual contour first variation, in the receipt parameter `u/π`. -/
def contourFunction (u : ℝ) : ℝ :=
  Config.Weta actualReference (Li2Lean.p0EllipsePoint 1 (Real.pi * u))

/-- The actual pinned first variation on the real segment. -/
def pinnedFunction (x : ℝ) : ℝ :=
  Config.Weta actualReference (x : ℂ)

/-- The actual frequency first variation. -/
def frequencyFunction (t : ℝ) : ℝ :=
  Config.Wmu actualReference t

/-- Every row of `cells` satisfies its original constant-model obligation. -/
def RowsValid (f : ℝ → ℝ) (cells : List ReceiptCell) : Prop :=
  ∀ c ∈ cells, ∀ hwidth : c.lo ≤ c.hi, c.modelRemainderValid f hwidth

theorem rowsValid_append {f : ℝ → ℝ} {xs ys : List ReceiptCell} :
    RowsValid f (xs ++ ys) ↔ RowsValid f xs ∧ RowsValid f ys := by
  constructor
  · intro h
    exact ⟨fun c hc => h c (List.mem_append_left _ hc),
      fun c hc => h c (List.mem_append_right _ hc)⟩
  · rintro ⟨hx, hy⟩ c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hx c hc
    · exact hy c hc

/-- Row input (C): all 2511 contour rows, for the actual `Weta` on `Γ`. -/
def ContourRowInput : Prop := RowsValid contourFunction Data.contourRows

/-- Row input (P): all 8192 pinned rows, for the actual `Weta` on the segment. -/
def PinnedRowInput : Prop := RowsValid pinnedFunction Data.pinnedRows

/-- Row input (F): all 16384 frequency rows, for the actual `Wmu`. -/
def FrequencyRowInput : Prop := RowsValid frequencyFunction Data.frequencyRows

/-- The three regional inputs together. -/
structure CARowInputs : Prop where
  contour : ContourRowInput
  pinned : PinnedRowInput
  frequency : FrequencyRowInput

end

end Li2Lean.P0.CA.Receipt
