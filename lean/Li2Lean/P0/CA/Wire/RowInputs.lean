/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Wire.ContourEq
import Li2Lean.P0.CA.Wire.PinnedEq
import Li2Lean.P0.CA.Wire.FrequencyEq
import Li2Lean.P0.CA.Contour.All
import Li2Lean.P0.CA.Pinned.All
import Li2Lean.P0.CA.Receipt.RowInputs

/-!
# The three C-A row inputs, proved

`CARowInputs` of the receipt (`Receipt/RowInputs.lean`) from the proved region
theorems, through the kernel-checked data identities of this directory:

* contour: `Contour.contourSlackRows_modelRemainderValid` (2511 rows);
* pinned: `Pinned.pinnedCells_actualWeta` (8192 rows);
* frequency: `Frequency.frequencyRows_modelRemainderValid` (16384 rows).

Every bound is the ORIGINAL row lower; the functions are the literal
`Weta`/`Wmu` at `ConfigReferenceSymmetry.actualReference`.
-/

namespace Li2Lean.P0.CA.Wire

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt

theorem contourRowInput : ContourRowInput := by
  intro c hc hw
  rw [contourRows_eq] at hc
  obtain ⟨d, hd, rfl⟩ := List.mem_map.mp hc
  have hr : (⟨d.cell, 1 / 2000, by norm_num⟩ : P0.SlackRow) ∈ Contour.contourSlackRows := by
    unfold Contour.contourSlackRows
    exact List.mem_map.mpr ⟨d, hd, rfl⟩
  exact Contour.contourSlackRows_modelRemainderValid _ hr hw

theorem pinnedRowInput : PinnedRowInput := by
  intro c hc hw
  rw [pinnedRows_eq] at hc
  exact Pinned.pinnedCells_actualWeta c hc hw

theorem frequencyRowInput : FrequencyRowInput := by
  intro c hc hw
  rw [frequencyRows_eq] at hc
  exact Frequency.frequencyRows_modelRemainderValid c hc hw

/-- All three regional row inputs of the C-A 397/200 receipt. -/
theorem caRowInputs : CARowInputs :=
  ⟨contourRowInput, pinnedRowInput, frequencyRowInput⟩

end Li2Lean.P0.CA.Wire
