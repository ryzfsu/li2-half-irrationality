/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.Agg
import Li2Lean.P0.SeedLiteral.ActualP0SeedCertificate

namespace Li2Lean.P0

/-- The frozen 64-by-64 P0 seed has determinant 30 in `ZMod 83`. -/
theorem p0SeedLiteral_det_eq_30 :
    Matrix.det SeedLiteral.aMat = (30 : ZMod 83) :=
  SeedLiteral.p0_G32_zero_mod83

/-- The frozen seed is reproduced by its explicit unit-lower/upper factors. -/
theorem p0SeedLiteral_lu :
    SeedLiteral.aMat = SeedLiteral.lMat * SeedLiteral.uMat :=
  SeedLiteral.p0_seed_lu

/-- The actual `p0MatrixQ 2 32` source seed has determinant 30 modulo 83. -/
theorem p0ActualSeed_det_eq_30 :
    actualP0SeedMatrix.det = (30 : ZMod 83) :=
  actualP0SeedMatrix_det_eq_30

#print axioms p0SeedLiteral_det_eq_30
#print axioms p0SeedLiteral_lu
#print axioms p0ActualSeed_det_eq_30

end Li2Lean.P0
