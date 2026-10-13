/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.SeedLiteral.SourceEntryShard

namespace Li2Lean.P0.SeedLiteral

set_option maxRecDepth 1000000

/-- The rational P0 matrix specialized at T = 0 and reduced to F_83. -/
noncomputable def actualSeedEntry (r c : Fin 64) : F83 :=
  ((((Li2Lean.p0MatrixQ (2 : ℚ) 32 r c).eval (0 : ℚ)) : ℚ) : F83)

set_option maxHeartbeats 5000000 in
/-- The top block of the actual P0 matrix is its literal C source. -/
theorem actualSeedEntry_top_formula (r c : Fin 64) (hr : r.val < 32) :
    actualSeedEntry r c =
      ((Li2Lean.p0CQ (2 : ℚ) 16 (8 + r.val) c.val : ℚ) : F83) := by
  simp [actualSeedEntry, Li2Lean.p0MatrixQ, hr]

set_option maxHeartbeats 5000000 in
/-- The bottom block of the actual P0 matrix is its literal B source. -/
theorem actualSeedEntry_bottom_formula (r c : Fin 64) (hr : 32 ≤ r.val) :
    actualSeedEntry r c =
      ((Li2Lean.p0BQ (2 : ℚ) 16 (8 + (r.val - 32)) c.val : ℚ) : F83) := by
  simp [actualSeedEntry, Li2Lean.p0MatrixQ, not_lt.mpr hr]

set_option maxHeartbeats 5000000 in
/-- The first 8-by-8 block of the actual rational P0 seed matches sourceEntry. -/
theorem actualSeed_block8_source (i j : Fin 8) :
    actualSeedEntry ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
      sourceEntry i.val j.val := by
  fin_cases i <;> fin_cases j
  all_goals rw [actualSeedEntry_top_formula _ _ (by decide)]
  all_goals apply ZMod.val_injective 83
  all_goals decide +kernel

set_option maxHeartbeats 5000000 in
/-- The first 8-by-8 block of the actual rational P0 seed matches aTable. -/
theorem actualSeed_block8 (i j : Fin 8) :
    actualSeedEntry ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
      ((aTable[i.val]!)[j.val]! : F83) := by
  calc
    actualSeedEntry ⟨i.val, by omega⟩ ⟨j.val, by omega⟩ =
        sourceEntry i.val j.val := actualSeed_block8_source i j
    _ = ((aTable[i.val]!)[j.val]! : F83) := source_block8 i j

#print axioms actualSeedEntry_top_formula
#print axioms actualSeedEntry_bottom_formula
#print axioms actualSeed_block8_source
#print axioms actualSeed_block8

end Li2Lean.P0.SeedLiteral
