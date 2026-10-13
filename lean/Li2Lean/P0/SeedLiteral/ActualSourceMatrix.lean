/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.Agg
import Li2Lean.P0.SeedLiteral.ActualSourceRow00
import Li2Lean.P0.SeedLiteral.ActualSourceRow01
import Li2Lean.P0.SeedLiteral.ActualSourceRow02
import Li2Lean.P0.SeedLiteral.ActualSourceRow03
import Li2Lean.P0.SeedLiteral.ActualSourceRow04
import Li2Lean.P0.SeedLiteral.ActualSourceRow05
import Li2Lean.P0.SeedLiteral.ActualSourceRow06
import Li2Lean.P0.SeedLiteral.ActualSourceRow07
import Li2Lean.P0.SeedLiteral.ActualSourceRow08
import Li2Lean.P0.SeedLiteral.ActualSourceRow09
import Li2Lean.P0.SeedLiteral.ActualSourceRow10
import Li2Lean.P0.SeedLiteral.ActualSourceRow11
import Li2Lean.P0.SeedLiteral.ActualSourceRow12
import Li2Lean.P0.SeedLiteral.ActualSourceRow13
import Li2Lean.P0.SeedLiteral.ActualSourceRow14
import Li2Lean.P0.SeedLiteral.ActualSourceRow15
import Li2Lean.P0.SeedLiteral.ActualSourceRow16
import Li2Lean.P0.SeedLiteral.ActualSourceRow17
import Li2Lean.P0.SeedLiteral.ActualSourceRow18
import Li2Lean.P0.SeedLiteral.ActualSourceRow19
import Li2Lean.P0.SeedLiteral.ActualSourceRow20
import Li2Lean.P0.SeedLiteral.ActualSourceRow21
import Li2Lean.P0.SeedLiteral.ActualSourceRow22
import Li2Lean.P0.SeedLiteral.ActualSourceRow23
import Li2Lean.P0.SeedLiteral.ActualSourceRow24
import Li2Lean.P0.SeedLiteral.ActualSourceRow25
import Li2Lean.P0.SeedLiteral.ActualSourceRow26
import Li2Lean.P0.SeedLiteral.ActualSourceRow27
import Li2Lean.P0.SeedLiteral.ActualSourceRow28
import Li2Lean.P0.SeedLiteral.ActualSourceRow29
import Li2Lean.P0.SeedLiteral.ActualSourceRow30
import Li2Lean.P0.SeedLiteral.ActualSourceRow31
import Li2Lean.P0.SeedLiteral.ActualSourceRow32
import Li2Lean.P0.SeedLiteral.ActualSourceRow33
import Li2Lean.P0.SeedLiteral.ActualSourceRow34
import Li2Lean.P0.SeedLiteral.ActualSourceRow35
import Li2Lean.P0.SeedLiteral.ActualSourceRow36
import Li2Lean.P0.SeedLiteral.ActualSourceRow37
import Li2Lean.P0.SeedLiteral.ActualSourceRow38
import Li2Lean.P0.SeedLiteral.ActualSourceRow39
import Li2Lean.P0.SeedLiteral.ActualSourceRow40
import Li2Lean.P0.SeedLiteral.ActualSourceRow41
import Li2Lean.P0.SeedLiteral.ActualSourceRow42
import Li2Lean.P0.SeedLiteral.ActualSourceRow43
import Li2Lean.P0.SeedLiteral.ActualSourceRow44
import Li2Lean.P0.SeedLiteral.ActualSourceRow45
import Li2Lean.P0.SeedLiteral.ActualSourceRow46
import Li2Lean.P0.SeedLiteral.ActualSourceRow47
import Li2Lean.P0.SeedLiteral.ActualSourceRow48
import Li2Lean.P0.SeedLiteral.ActualSourceRow49
import Li2Lean.P0.SeedLiteral.ActualSourceRow50
import Li2Lean.P0.SeedLiteral.ActualSourceRow51
import Li2Lean.P0.SeedLiteral.ActualSourceRow52
import Li2Lean.P0.SeedLiteral.ActualSourceRow53
import Li2Lean.P0.SeedLiteral.ActualSourceRow54
import Li2Lean.P0.SeedLiteral.ActualSourceRow55
import Li2Lean.P0.SeedLiteral.ActualSourceRow56
import Li2Lean.P0.SeedLiteral.ActualSourceRow57
import Li2Lean.P0.SeedLiteral.ActualSourceRow58
import Li2Lean.P0.SeedLiteral.ActualSourceRow59
import Li2Lean.P0.SeedLiteral.ActualSourceRow60
import Li2Lean.P0.SeedLiteral.ActualSourceRow61
import Li2Lean.P0.SeedLiteral.ActualSourceRow62
import Li2Lean.P0.SeedLiteral.ActualSourceRow63

namespace Li2Lean.P0.SeedLiteral

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

/-- The actual v10 P0 matrix at `a = 2`, `m = 32`, and `T = 0`, reduced to `F83`. -/
noncomputable def actualSeedMatrix : Mat64 := fun r c => actualSeedEntry r c

/-- The seed matrix is defined from the actual `p0MatrixQ 2 32` specialization at zero. -/
theorem actualSeedMatrix_eq_p0MatrixQ :
    actualSeedMatrix = fun r c =>
      ((((Li2Lean.p0MatrixQ (2 : ℚ) 32 r c).eval (0 : ℚ) : ℚ) : F83)) := rfl

/-- Every entry of the actual rational source matrix reduces to the frozen literal table. -/
theorem actualSeedMatrix_eq_aMat : actualSeedMatrix = aMat := by
  ext r c
  fin_cases r <;> simp [actualSeedMatrix, aMat]

/-- The full actual 64-by-64 v10 seed has determinant exactly 30 modulo 83. -/
theorem actualSeedMatrix_det_eq_30 : actualSeedMatrix.det = (30 : F83) := by
  rw [actualSeedMatrix_eq_aMat]
  exact p0_G32_zero_mod83

/-- In particular, the reduced actual seed matrix is nonsingular. -/
theorem actualSeedMatrix_det_ne_zero : actualSeedMatrix.det ≠ 0 := by
  rw [actualSeedMatrix_det_eq_30]
  decide

#print axioms actualSeedMatrix_eq_p0MatrixQ
#print axioms actualSeedMatrix_eq_aMat
#print axioms actualSeedMatrix_det_eq_30
#print axioms actualSeedMatrix_det_ne_zero

end Li2Lean.P0.SeedLiteral
