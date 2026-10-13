/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.Rows.Shard000
import Li2Lean.P0.CA.Contour.Rows.Shard001
import Li2Lean.P0.CA.Contour.Rows.Shard002
import Li2Lean.P0.CA.Contour.Rows.Shard003
import Li2Lean.P0.CA.Contour.Rows.Shard004
import Li2Lean.P0.CA.Contour.Rows.Shard005
import Li2Lean.P0.CA.Contour.Rows.Shard006
import Li2Lean.P0.CA.Contour.Rows.Shard007
import Li2Lean.P0.CA.Contour.Rows.Shard008
import Li2Lean.P0.CA.Contour.Rows.Shard009
import Li2Lean.P0.CA.Contour.Rows.Shard010
import Li2Lean.P0.CA.Contour.Rows.Shard011
import Li2Lean.P0.CA.Contour.Rows.Shard012
import Li2Lean.P0.CA.Contour.Rows.Shard013
import Li2Lean.P0.CA.Contour.Rows.Shard014
import Li2Lean.P0.CA.Contour.Rows.CsvCells
import Li2Lean.P0.ConfigSlackReceipt

/-!
# All 2511 slack-table contour rows: `modelRemainderValid` for the actual `Weta`

`csvCells` is the slack table `contour_cells.csv` verbatim (sha256
88c04384dc0bc1b2665a4f0193d1f47a686ca445f4f816032e5adabe5772ef6f).  The
grouped shards are checked by `decide +kernel`; their concatenated cells are
proved equal to `csvCells`.  The final theorem gives, for every row, the
ORIGINAL receipt cell's `modelRemainderValid` for
`u ↦ Weta actualReference (p0EllipsePoint 1 (π u))`; no allowance is spent.
-/

set_option maxRecDepth 100000

namespace Li2Lean.P0.CA.Contour

open Rows Li2Lean.F_L8

def allGroups : List Grp := shard000 ++ shard001 ++ shard002 ++ shard003 ++ shard004 ++ shard005 ++ shard006 ++ shard007 ++ shard008 ++ shard009 ++ shard010 ++ shard011 ++ shard012 ++ shard013 ++ shard014

theorem allGrp_append (a b : List Grp) : allGrp (a ++ b) = (allGrp a && allGrp b) := by
  induction a with
  | nil => simp [allGrp]
  | cons g gs ih => simp [allGrp, ih, Bool.and_assoc]

theorem allGroups_ok : allGrp allGroups = true := by
  simp only [allGroups, allGrp_append, shard000_ok, shard001_ok, shard002_ok, shard003_ok, shard004_ok, shard005_ok, shard006_ok, shard007_ok, shard008_ok, shard009_ok, shard010_ok, shard011_ok, shard012_ok, shard013_ok, shard014_ok, Bool.and_self]

def groupedCells : List Cell := allGroups.flatMap Grp.cells

theorem groupedCells_eq : groupedCells = csvCells := by decide +kernel

theorem csvCells_valid {c : Cell} (hc : c ∈ csvCells) (hw : c.cell.lo ≤ c.cell.hi) :
    c.cell.modelRemainderValid target hw := by
  rw [← groupedCells_eq] at hc
  obtain ⟨g, hg, hcg⟩ := List.mem_flatMap.mp hc
  exact checkGrp_valid (allGrp_mem allGroups_ok hg) hcg hw

/-! ## The slack-receipt rows -/

def contourSlackRows : List SlackRow :=
  csvCells.map (fun c => ⟨c.cell, 1 / 2000, by norm_num⟩)

theorem contourSlackRows_length : contourSlackRows.length = 2511 := by
  simp [contourSlackRows, csvCells_length]

theorem slackCells_contour : slackCells contourSlackRows = csvCells.map Cell.cell := by
  simp [slackCells, contourSlackRows, SlackRow.toReceiptCell, Function.comp_def]

theorem contourSlackRows_chain : ExactChain (slackCells contourSlackRows) 0 1 := by
  rw [slackCells_contour]
  exact ConfigData.exactChainCheck_sound (by decide +kernel)

def floorCheck : List Cell → Bool
  | [] => true
  | c :: cs => decide (caSlackFloor ≤ c.lower) && floorCheck cs

theorem floorCheck_mem {cs : List Cell} (h : floorCheck cs = true) {c : Cell} (hc : c ∈ cs) :
    caSlackFloor ≤ c.lower := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
      simp only [floorCheck, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact of_decide_eq_true h.1
      · exact ih h.2 hc

theorem contourSlackRows_floor : ∀ r ∈ contourSlackRows, caSlackFloor ≤ r.cell.lower := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact floorCheck_mem (cs := csvCells) (by decide +kernel) hc

theorem contourSlackRows_allowance : ∀ r ∈ contourSlackRows, r.allowance = 1 / 2000 := by
  intro r hr
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  rfl

/-- Main result: every one of the 2511 slack-table contour rows satisfies
`modelRemainderValid` for the ACTUAL `Weta` on the contour, with its original
cell lower bound. -/
theorem contourSlackRows_modelRemainderValid :
    ∀ r ∈ contourSlackRows, ∀ hw : r.cell.lo ≤ r.cell.hi,
      r.cell.modelRemainderValid
        (fun u => Config.Weta ConfigReferenceSymmetry.actualReference
          (Li2Lean.p0EllipsePoint 1 (Real.pi * u))) hw := by
  intro r hr hw
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hr
  exact csvCells_valid hc hw

end Li2Lean.P0.CA.Contour
