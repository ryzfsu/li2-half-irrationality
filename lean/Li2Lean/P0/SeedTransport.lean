/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SourceSeedFinitePlace

namespace Li2Lean.P0.ControlledResidue

open Li2Lean
open Li2Lean.P0

/-- The actual `m = 32`, `T = 0` source value has denominator coprime to 83.
This is the rational-matrix determinant denominator certificate transported
through the paper's exact source-polynomial identity. -/
theorem p0A2SourceEval_den_coprime {F : P0Family} (hbase : F.a = 2) :
    Nat.Coprime (p0SourceEvalQ F 32 0).den 83 := by
  rw [p0A2_sourceSeedQ_det_value hbase]
  exact sourceSeedQ_det_den_coprime_test

/-- Package the literal `p0SourceEvalQ F 32 0` as a reduced rational at 83.
The denominator proof comes from the literal rational source matrix. -/
noncomputable def p0A2SourceEvalReduced (F : P0Family) (hbase : F.a = 2) :
    ContourKit.ReducedRational 83 :=
  reducedOf (p0SourceEvalQ F 32 0) (p0A2SourceEval_den_coprime hbase)

theorem p0A2SourceEvalReduced_value (F : P0Family) (hbase : F.a = 2) :
    (p0A2SourceEvalReduced F hbase).value = p0SourceEvalQ F 32 0 := rfl

/-- The finite-place residue of the actual source-polynomial seed is exactly
30, by the rational determinant identity and the literal 64-by-64 matrix
certificate. -/
theorem p0A2SourceEvalReduced_residue_eq_30
    (F : P0Family) (hbase : F.a = 2) :
    (p0A2SourceEvalReduced F hbase).residue = (30 : F83) := by
  have hvalue : (p0A2SourceEvalReduced F hbase).value = sourceSeedReduced.value := by
    calc
      (p0A2SourceEvalReduced F hbase).value = p0SourceEvalQ F 32 0 := rfl
      _ = Matrix.det sourceSeedQ := p0A2_sourceSeedQ_det_value hbase
      _ = sourceSeedReduced.value := sourceSeedReduced_value.symm
  exact (reducedRational_residue_eq_of_value_eq hvalue).trans
    sourceSeedReduced_residue_eq_30

/-- Any tower seed with the paper's exact rational value has the residue 30
of the constructed source seed. -/
theorem p0A2TowerSeed_residue_eq_30
    {F : P0Family} {tower : P0FrobeniusTowerCertificate F 32 83}
    (hbase : F.a = 2) :
    tower.seed.residue = (30 : F83) := by
  have hvalue : tower.seed.value = sourceSeedReduced.value := by
    calc
      tower.seed.value = p0SourceEvalQ F 32 0 := tower.seed_value
      _ = Matrix.det sourceSeedQ := p0A2_sourceSeedQ_det_value hbase
      _ = sourceSeedReduced.value := sourceSeedReduced_value.symm
  exact (reducedRational_residue_eq_of_value_eq hvalue).trans
    sourceSeedReduced_residue_eq_30

#print axioms p0A2SourceEval_den_coprime
#print axioms p0A2SourceEvalReduced_residue_eq_30
#print axioms p0A2TowerSeed_residue_eq_30

end Li2Lean.P0.ControlledResidue
