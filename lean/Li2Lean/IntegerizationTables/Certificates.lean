/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Tactic.NormNum
import Li2Lean.IntegerizationTables.Data
import Li2Lean.IntegerizationTables.Reflection

set_option maxRecDepth 1000000

namespace Li2Lean
namespace IntegerizationTables

/-- The finite low-prime certificate is checked by rational normalization. -/
theorem p0LowFiniteProfile_checked :
    lowPieces.length = 756 ∧
      affineChain (1 / 128) (1 / 2) lowPieces = true ∧
      lowPieces.foldl (fun acc f => acc + f.integral) 0 = p0LowIntegralClaim := by
  norm_num [lowPieces, affineChain, AffinePiece.integral, p0LowIntegralClaim,
    List.foldl]

set_option maxHeartbeats 10000000 in
theorem p0HighPotentialTable_checked :
    ∀ C ∈ p0HighCertificates, C.checks = true := by
  simp (config := { maxSteps := 10000000 }) [p0HighCertificates,
    PotentialCertificate.checks, PotentialCertificate.shapeChecks,
    PotentialCertificate.pairChecks, PotentialCertificate.widthsCheck,
    PotentialCertificate.objectiveCheck, PotentialCertificate.widthsPartition,
    PotentialCertificate.potentialPairsValid, PotentialCertificate.objectiveValid,
    PotentialCertificate.objectiveIntercept, PotentialCertificate.objectiveSlope,
    PotentialCertificate.sameCellPairCount, listNatSum, listRatSum, getRow, getCol,
    getInt, getGroup, rowPot, colPot, baseEntryBound, sameCellEntryBound,
    boolInt, tauDigit, List.all, List.range, List.range.loop, List.foldl, List.map]
  norm_num

theorem p0HighPotentialTable_sound (C : PotentialCertificate)
    (hC : C ∈ p0HighCertificates) : C.valid :=
  checker_sound C (p0HighPotentialTable_checked C hC)

def p0HighIntervalChain : ℚ → ℚ → List PotentialCertificate → Bool
  | lo, hi, [] => decide (lo = hi)
  | lo, hi, C :: rest =>
      decide (C.lo = lo ∧ C.lo < C.hi) && p0HighIntervalChain C.hi hi rest

def p0HighIntegralFromData : ℚ :=
  (p0HighCertificates.map PotentialCertificate.claimedIntegral).foldl (· + ·) 0

theorem p0HighFiniteTable_checked :
    p0HighCertificates.length = 11 ∧
      p0HighIntervalChain (1 / 2) (5 / 2) p0HighCertificates = true ∧
      p0HighIntegralFromData = p0HighIntegralClaim := by
  norm_num [p0HighCertificates, p0HighIntervalChain, p0HighIntegralFromData,
    p0HighIntegralClaim, List.foldl, List.map, List.range, List.range.loop]

def p0HighConstraintCount : ℕ :=
  listNatSum (p0HighCertificates.map fun C =>
    C.rows.length * C.cols.length + C.sameCellPairCount)

theorem p0HighConstraintCount_eq_1942 : p0HighConstraintCount = 1942 := by
  decide

theorem p0BasicIntegerizerRate_lt_1979_over_1000 :
    p0BasicIntegerizerRateClaim < 1979 / 1000 := by
  norm_num [p0BasicIntegerizerRateClaim, p0LowIntegralClaim,
    p0SmallPrimeTailClaim, p0HighIntegralClaim, p0LogTwoLower,
    Finset.sum_range_succ]

end IntegerizationTables
end Li2Lean

#print axioms Li2Lean.IntegerizationTables.p0LowFiniteProfile_checked
#print axioms Li2Lean.IntegerizationTables.p0HighPotentialTable_checked
#print axioms Li2Lean.IntegerizationTables.p0HighFiniteTable_checked
#print axioms Li2Lean.IntegerizationTables.p0HighConstraintCount_eq_1942
#print axioms Li2Lean.IntegerizationTables.p0BasicIntegerizerRate_lt_1979_over_1000
