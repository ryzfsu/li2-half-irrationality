/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SourceSeedDenominator
import Li2Lean.P0.RationalDeterminantCast
import Li2Lean.P0.ResidueCast

namespace Li2Lean.P0.ControlledResidue

open Li2Lean
open Li2Lean.P0

theorem sourceSeedQ_det_cast_eq_actual_generic :
    ((Matrix.det sourceSeedQ : ℚ) : F83) =
      Matrix.det p0A2ActualSeedMatrix := by
  apply Li2Lean.cast_det_of_entries_83 sourceSeedQ p0A2ActualSeedMatrix
  · exact sourceSeedQ_den_coprime_test
  · intro r c
    exact (p0A2ActualSeedMatrix_entry_source r c).symm

def sourceSeedReduced : ContourKit.ReducedRational 83 :=
  reducedOf (Matrix.det sourceSeedQ) sourceSeedQ_det_den_coprime_test

theorem sourceSeedReduced_value :
    sourceSeedReduced.value = Matrix.det sourceSeedQ := by
  rfl

theorem sourceSeedReduced_residue :
    sourceSeedReduced.residue = Matrix.det p0A2ActualSeedMatrix := by
  change (reducedOf (Matrix.det sourceSeedQ) sourceSeedQ_det_den_coprime_test).residue = _
  rw [reducedOf_residue]
  rw [residueOf_eq_ratCast]
  exact sourceSeedQ_det_cast_eq_actual_generic

theorem sourceSeedReduced_residue_eq_30 :
    sourceSeedReduced.residue = (30 : F83) := by
  rw [sourceSeedReduced_residue, p0A2ActualSeedMatrix_det_eq_30]

/-- The explicit finite-place certificate for the rational source determinant.
Its value field is the rational determinant identity, while its residue field
is the determinant cast bridge above. -/
def sourceSeedFinitePlaceCertificate :
    P0A2SeedDeterminantFinitePlaceCertificate :=
  { source_determinant := sourceSeedReduced
    source_determinant_value := sourceSeedReduced_value
    source_determinant_residue := sourceSeedReduced_residue }

theorem sourceSeedFinitePlaceCertificate_residue_eq_30 :
    sourceSeedFinitePlaceCertificate.source_determinant.residue = (30 : F83) := by
  change sourceSeedReduced.residue = (30 : F83)
  exact sourceSeedReduced_residue_eq_30

end Li2Lean.P0.ControlledResidue
