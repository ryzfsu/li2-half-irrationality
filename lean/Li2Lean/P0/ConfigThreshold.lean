/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigData

namespace Li2Lean.P0.ConfigThreshold

open Li2Lean.F_L8

/-- Finite rational check that every contour row clears the C-A floor. -/
def contourThresholdCheck : List ReceiptCell → Bool
  | [] => true
  | c :: rest => decide ((-669 / 200 : ℚ) ≤ c.lower) &&
      contourThresholdCheck rest

theorem contourThresholdCheck_append (xs ys : List ReceiptCell) :
    contourThresholdCheck (xs ++ ys) =
      (contourThresholdCheck xs && contourThresholdCheck ys) := by
  induction xs with
  | nil => simp [contourThresholdCheck]
  | cons c xs ih =>
      simp [contourThresholdCheck, ih, Bool.and_assoc]

theorem contourThresholdCheck_sound {cells : List ReceiptCell}
    (h : contourThresholdCheck cells = true) :
    ∀ c ∈ cells, (-669 / 200 : ℚ) ≤ c.lower := by
  induction cells with
  | nil =>
      intro c hc
      simp at hc
  | cons head tail ih =>
      simp only [contourThresholdCheck, Bool.and_eq_true] at h
      intro c hc
      rcases List.mem_cons.mp hc with hhead | htail
      · subst c
        exact of_decide_eq_true h.1
      · exact ih h.2 c htail

theorem contourCellsChunk000_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk000 = true := by
  decide +kernel

theorem contourCellsChunk001_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk001 = true := by
  decide +kernel

theorem contourCellsChunk002_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk002 = true := by
  decide +kernel

theorem contourCellsChunk003_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk003 = true := by
  decide +kernel

theorem contourCellsChunk004_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk004 = true := by
  decide +kernel

theorem contourCellsChunk005_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk005 = true := by
  decide +kernel

theorem contourCellsChunk006_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk006 = true := by
  decide +kernel

theorem contourCellsChunk007_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk007 = true := by
  decide +kernel

theorem contourCellsChunk008_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk008 = true := by
  decide +kernel

theorem contourCellsChunk009_threshold_check :
    contourThresholdCheck ConfigData.contourCellsChunk009 = true := by
  decide +kernel

theorem contourCells_threshold_check :
    contourThresholdCheck ConfigData.contourCells = true := by
  rw [ConfigData.contourCells]
  rw [contourThresholdCheck_append, contourThresholdCheck_append,
    contourThresholdCheck_append, contourThresholdCheck_append,
    contourThresholdCheck_append, contourThresholdCheck_append,
    contourThresholdCheck_append, contourThresholdCheck_append,
    contourThresholdCheck_append]
  rw [contourCellsChunk000_threshold_check, contourCellsChunk001_threshold_check,
    contourCellsChunk002_threshold_check, contourCellsChunk003_threshold_check,
    contourCellsChunk004_threshold_check, contourCellsChunk005_threshold_check,
    contourCellsChunk006_threshold_check, contourCellsChunk007_threshold_check,
    contourCellsChunk008_threshold_check, contourCellsChunk009_threshold_check]
  rfl

theorem contourCells_lower_floor {c : ReceiptCell}
    (hc : c ∈ ConfigData.contourCells) :
    (-669 / 200 : ℚ) ≤ c.lower :=
  contourThresholdCheck_sound contourCells_threshold_check c hc

end Li2Lean.P0.ConfigThreshold
