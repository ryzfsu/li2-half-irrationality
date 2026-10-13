/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.ActualSourceMatrix

namespace Li2Lean.P0

/-- The v10 source matrix `p0MatrixQ 2 32` at `T = 0`, reduced entrywise to `F83`. -/
noncomputable def actualP0SeedMatrix : Matrix (Fin 64) (Fin 64) (ZMod 83) :=
  Li2Lean.P0.SeedLiteral.actualSeedMatrix

/-- Exact residue-30 determinant of the actual v10 source matrix. -/
theorem actualP0SeedMatrix_det_eq_30 :
    actualP0SeedMatrix.det = (30 : ZMod 83) := by
  exact Li2Lean.P0.SeedLiteral.actualSeedMatrix_det_eq_30

/-- The actual v10 source matrix is nonsingular modulo 83. -/
theorem actualP0SeedMatrix_det_ne_zero : actualP0SeedMatrix.det ≠ 0 := by
  exact Li2Lean.P0.SeedLiteral.actualSeedMatrix_det_ne_zero

#print axioms actualP0SeedMatrix_det_eq_30
#print axioms actualP0SeedMatrix_det_ne_zero

end Li2Lean.P0
