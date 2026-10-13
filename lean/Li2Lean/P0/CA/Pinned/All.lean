/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Pinned.Shards.Chunk00
import Li2Lean.P0.CA.Pinned.Shards.Chunk01
import Li2Lean.P0.CA.Pinned.Shards.Chunk02
import Li2Lean.P0.CA.Pinned.Shards.Chunk03
import Li2Lean.P0.CA.Pinned.Shards.Chunk04
import Li2Lean.P0.CA.Pinned.Shards.Chunk05
import Li2Lean.P0.CA.Pinned.Shards.Chunk06
import Li2Lean.P0.CA.Pinned.Shards.Chunk07
import Li2Lean.P0.CA.Pinned.Shards.Chunk08
import Li2Lean.P0.CA.Pinned.Shards.Chunk09
import Li2Lean.P0.CA.Pinned.Shards.Chunk10
import Li2Lean.P0.CA.Pinned.Shards.Chunk11
import Li2Lean.P0.CA.Pinned.Shards.Chunk12
import Li2Lean.P0.CA.Pinned.Shards.Chunk13
import Li2Lean.P0.CA.Pinned.Shards.Chunk14
import Li2Lean.P0.CA.Pinned.Shards.Chunk15
import Li2Lean.P0.CA.Pinned.Shards.Chunk16
import Li2Lean.P0.CA.Pinned.Shards.Chunk17
import Li2Lean.P0.CA.Pinned.Shards.Chunk18
import Li2Lean.P0.CA.Pinned.Shards.Chunk19
import Li2Lean.P0.CA.Pinned.Shards.Chunk20
import Li2Lean.P0.CA.Pinned.Shards.Chunk21
import Li2Lean.P0.CA.Pinned.Shards.Chunk22
import Li2Lean.P0.CA.Pinned.Shards.Chunk23
import Li2Lean.P0.CA.Pinned.Shards.Chunk24
import Li2Lean.P0.CA.Pinned.Shards.Chunk25
import Li2Lean.P0.CA.Pinned.Shards.Chunk26
import Li2Lean.P0.CA.Pinned.Shards.Chunk27
import Li2Lean.P0.CA.Pinned.Shards.Chunk28
import Li2Lean.P0.CA.Pinned.Shards.Chunk29
import Li2Lean.P0.CA.Pinned.Shards.Chunk30
import Li2Lean.P0.CA.Pinned.Shards.Chunk31
import Li2Lean.P0.ConfigReferenceSymmetry

/-!
# All 8,192 pinned C-A rows: raw `modelRemainderValid` for the actual `Weta`

`ConfigData.pinnedCells` is the 8,192-row pinned slack table (checked
row-for-row by the repository's pinned-table checker).  Every row is
proved with its ORIGINAL cell lower bound: no allowance is subtracted, so the
1/10000 row allowance remains available exactly once to the receipt.
-/

namespace Li2Lean.P0.CA.Pinned

open Li2Lean.F_L8

theorem pinnedCells_modelRemainderValid :
    ∀ c ∈ Li2Lean.P0.ConfigData.pinnedCells, ∀ hw : c.lo ≤ c.hi,
      c.modelRemainderValid Li2Lean.P0.ConfigContourSelfPotential.pinnedWeta hw := by
  intro c hc hw
  rw [Li2Lean.P0.ConfigData.pinnedCells] at hc
  rcases List.mem_append.mp hc with hc | h31
  swap
  · exact Shards.Chunk31.valid c h31 hw
  rcases List.mem_append.mp hc with hc | h30
  swap
  · exact Shards.Chunk30.valid c h30 hw
  rcases List.mem_append.mp hc with hc | h29
  swap
  · exact Shards.Chunk29.valid c h29 hw
  rcases List.mem_append.mp hc with hc | h28
  swap
  · exact Shards.Chunk28.valid c h28 hw
  rcases List.mem_append.mp hc with hc | h27
  swap
  · exact Shards.Chunk27.valid c h27 hw
  rcases List.mem_append.mp hc with hc | h26
  swap
  · exact Shards.Chunk26.valid c h26 hw
  rcases List.mem_append.mp hc with hc | h25
  swap
  · exact Shards.Chunk25.valid c h25 hw
  rcases List.mem_append.mp hc with hc | h24
  swap
  · exact Shards.Chunk24.valid c h24 hw
  rcases List.mem_append.mp hc with hc | h23
  swap
  · exact Shards.Chunk23.valid c h23 hw
  rcases List.mem_append.mp hc with hc | h22
  swap
  · exact Shards.Chunk22.valid c h22 hw
  rcases List.mem_append.mp hc with hc | h21
  swap
  · exact Shards.Chunk21.valid c h21 hw
  rcases List.mem_append.mp hc with hc | h20
  swap
  · exact Shards.Chunk20.valid c h20 hw
  rcases List.mem_append.mp hc with hc | h19
  swap
  · exact Shards.Chunk19.valid c h19 hw
  rcases List.mem_append.mp hc with hc | h18
  swap
  · exact Shards.Chunk18.valid c h18 hw
  rcases List.mem_append.mp hc with hc | h17
  swap
  · exact Shards.Chunk17.valid c h17 hw
  rcases List.mem_append.mp hc with hc | h16
  swap
  · exact Shards.Chunk16.valid c h16 hw
  rcases List.mem_append.mp hc with hc | h15
  swap
  · exact Shards.Chunk15.valid c h15 hw
  rcases List.mem_append.mp hc with hc | h14
  swap
  · exact Shards.Chunk14.valid c h14 hw
  rcases List.mem_append.mp hc with hc | h13
  swap
  · exact Shards.Chunk13.valid c h13 hw
  rcases List.mem_append.mp hc with hc | h12
  swap
  · exact Shards.Chunk12.valid c h12 hw
  rcases List.mem_append.mp hc with hc | h11
  swap
  · exact Shards.Chunk11.valid c h11 hw
  rcases List.mem_append.mp hc with hc | h10
  swap
  · exact Shards.Chunk10.valid c h10 hw
  rcases List.mem_append.mp hc with hc | h09
  swap
  · exact Shards.Chunk09.valid c h09 hw
  rcases List.mem_append.mp hc with hc | h08
  swap
  · exact Shards.Chunk08.valid c h08 hw
  rcases List.mem_append.mp hc with hc | h07
  swap
  · exact Shards.Chunk07.valid c h07 hw
  rcases List.mem_append.mp hc with hc | h06
  swap
  · exact Shards.Chunk06.valid c h06 hw
  rcases List.mem_append.mp hc with hc | h05
  swap
  · exact Shards.Chunk05.valid c h05 hw
  rcases List.mem_append.mp hc with hc | h04
  swap
  · exact Shards.Chunk04.valid c h04 hw
  rcases List.mem_append.mp hc with hc | h03
  swap
  · exact Shards.Chunk03.valid c h03 hw
  rcases List.mem_append.mp hc with hc | h02
  swap
  · exact Shards.Chunk02.valid c h02 hw
  rcases List.mem_append.mp hc with hc | h01
  swap
  · exact Shards.Chunk01.valid c h01 hw
  exact Shards.Chunk00.valid c hc hw

/-- The same statement for the literal `Config.Weta actualReference` on the real segment. -/
theorem pinnedCells_actualWeta :
    ∀ c ∈ Li2Lean.P0.ConfigData.pinnedCells, ∀ hw : c.lo ≤ c.hi,
      c.modelRemainderValid
        (fun x : ℝ => Li2Lean.P0.Config.Weta
          Li2Lean.P0.ConfigReferenceSymmetry.actualReference (Complex.ofReal x)) hw :=
  pinnedCells_modelRemainderValid

/-- Pointwise form: every real `x` in a pinned row lies above the row's raw lower bound. -/
theorem pinnedCells_lower {c : ReceiptCell} (hc : c ∈ Li2Lean.P0.ConfigData.pinnedCells)
    {x : ℝ} (hxlo : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ Li2Lean.P0.Config.Weta
      Li2Lean.P0.ConfigReferenceSymmetry.actualReference (Complex.ofReal x) := by
  have hw : c.lo ≤ c.hi := by exact_mod_cast hxlo.trans hxhi
  exact ReceiptCell.sound c hw (pinnedCells_modelRemainderValid c hc hw) hxlo hxhi

end Li2Lean.P0.CA.Pinned

#print axioms Li2Lean.P0.CA.Pinned.pinnedCells_modelRemainderValid
#print axioms Li2Lean.P0.CA.Pinned.pinnedCells_actualWeta
#print axioms Li2Lean.P0.CA.Pinned.pinnedCells_lower
#print axioms Li2Lean.P0.CA.Pinned.chunk_valid
#print axioms Li2Lean.P0.CA.Pinned.moment_mem
#print axioms Li2Lean.P0.CA.Pinned.contourPotential_eq_poly
#print axioms Li2Lean.P0.CA.Pinned.pinnedWeta_terms
