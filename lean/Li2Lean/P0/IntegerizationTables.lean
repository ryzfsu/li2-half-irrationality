/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.IntegerizationTables.Audit

namespace Li2Lean.P0

/-- Audited finite certificate package for the P0 integerization tables. -/
theorem integerizationTableCertificateBundle :
    (IntegerizationTables.lowPieces.length = 756 ∧
      IntegerizationTables.affineChain (1 / 128) (1 / 2)
        IntegerizationTables.lowPieces = true ∧
      IntegerizationTables.lowPieces.foldl
        (fun acc f => acc + f.integral) 0 =
        IntegerizationTables.p0LowIntegralClaim) ∧
    (IntegerizationTables.p0HighCertificates.length = 11 ∧
      IntegerizationTables.p0HighIntervalChain (1 / 2) (5 / 2)
        IntegerizationTables.p0HighCertificates = true ∧
      IntegerizationTables.p0HighIntegralFromData =
        IntegerizationTables.p0HighIntegralClaim) ∧
    (∀ C : IntegerizationTables.PotentialCertificate,
      C ∈ IntegerizationTables.p0HighCertificates → C.valid) ∧
    IntegerizationTables.p0HighConstraintCount = 1942 ∧
    IntegerizationTables.p0BasicIntegerizerRateClaim < 1979 / 1000 := by
  refine ⟨IntegerizationTables.p0LowFiniteProfile_checked,
    IntegerizationTables.p0HighFiniteTable_checked, ?_,
    IntegerizationTables.p0HighConstraintCount_eq_1942,
    IntegerizationTables.p0BasicIntegerizerRate_lt_1979_over_1000⟩
  intro C hC
  exact IntegerizationTables.p0HighPotentialTable_sound C hC

#print axioms integerizationTableCertificateBundle

end Li2Lean.P0
