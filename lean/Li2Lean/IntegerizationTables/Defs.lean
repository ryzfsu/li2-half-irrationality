/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic

namespace Li2Lean
namespace IntegerizationTables

structure AffinePiece where
  lo : ℚ
  hi : ℚ
  intercept : ℚ
  slope : ℚ
  deriving DecidableEq, Repr, Inhabited

def AffinePiece.integral (f : AffinePiece) : ℚ :=
  f.intercept * (f.hi - f.lo) +
    f.slope * (f.hi ^ 2 - f.lo ^ 2) / 2

def affineChain : ℚ → ℚ → List AffinePiece → Bool
  | lo, hi, [] => decide (lo = hi)
  | lo, hi, f :: rest =>
      decide (f.lo = lo ∧ f.lo < f.hi) && affineChain f.hi hi rest

def listRatSum (xs : List ℚ) : ℚ := xs.foldl (· + ·) 0
def listNatSum (xs : List ℕ) : ℕ := xs.foldl (· + ·) 0

def p0LowIntegralClaim : ℚ :=
  (1448276314740194964855260100800462127260298031042796749529725627370010396734895633658285333350450905704443029571002838710237 : ℚ) /
  1404098881580803157259376918521625735839461675553873436297217652662216162782957043593966060046854826150978176673015236224000

def p0SmallPrimeTailClaim : ℚ := 129 / 8192
def p0HighIntegralClaim : ℚ := 287 / 192

inductive MatrixBlock where
  | C
  | B
  deriving DecidableEq, Repr, Inhabited

structure RowType where
  cell : ℕ
  digit : ℕ
  block : MatrixBlock
  carry : Bool
  deriving DecidableEq, Repr, Inhabited

structure ColType where
  cell : ℕ
  digit : ℕ
  carry : Bool
  deriving DecidableEq, Repr, Inhabited

structure CellGroup where
  widthIntercept : ℚ
  widthSlope : ℚ
  deriving DecidableEq, Repr, Inhabited

structure PotentialCertificate where
  lo : ℚ
  hi : ℚ
  groups : List CellGroup
  rows : List RowType
  cols : List ColType
  rowPotentials : List ℤ
  colPotentials : List ℤ
  declaredBasePairs : ℕ
  claimedLineIntercept : ℚ
  claimedLineSlope : ℚ
  claimedIntegral : ℚ
  deriving DecidableEq, Repr, Inhabited

def boolInt (b : Bool) : ℤ := if b then 1 else 0

def tauDigit (carry : Bool) (digit : ℕ) : ℤ :=
  if 0 < digit then boolInt carry - 1 else 0

def baseEntryBound (r : RowType) (c : ColType) : ℤ :=
  match r.block with
  | .C => - min (boolInt r.carry) (boolInt c.carry)
  | .B => - min (tauDigit r.carry r.digit) (tauDigit c.carry c.digit)

def sameCellEntryBound (r : RowType) (c : ColType) : ℤ :=
  if r.digit ≠ c.digit then baseEntryBound r c + 1
  else
    match r.block with
    | .C => 0
    | .B => if 0 < r.digit then 2 - boolInt r.carry else 0

def getInt (xs : List ℤ) (i : ℕ) : ℤ := xs.getD i 0
def getRow (xs : List RowType) (i : ℕ) : RowType := xs.getD i default
def getCol (xs : List ColType) (i : ℕ) : ColType := xs.getD i default
def getGroup (xs : List CellGroup) (i : ℕ) : CellGroup := xs.getD i default

def rowPot (C : PotentialCertificate) (i : ℕ) : ℤ := getInt C.rowPotentials i
def colPot (C : PotentialCertificate) (j : ℕ) : ℤ := getInt C.colPotentials j

def PotentialCertificate.sameCellPairCount (C : PotentialCertificate) : ℕ :=
  ∑ i : Fin C.rows.length, ∑ j : Fin C.cols.length,
    if (getRow C.rows i.val).cell = (getCol C.cols j.val).cell then 1 else 0

def PotentialCertificate.tableShape (C : PotentialCertificate) : Prop :=
  C.lo < C.hi ∧
  C.rowPotentials.length = C.rows.length ∧
  C.colPotentials.length = C.cols.length ∧
  (∀ i : Fin C.rows.length, (getRow C.rows i.val).cell < C.groups.length) ∧
  (∀ j : Fin C.cols.length, (getCol C.cols j.val).cell < C.groups.length) ∧
  C.declaredBasePairs = C.rows.length * C.cols.length

def PotentialCertificate.widthsPartition (C : PotentialCertificate) : Prop :=
  listRatSum (C.groups.map CellGroup.widthIntercept) = 0 ∧
    listRatSum (C.groups.map CellGroup.widthSlope) = 1

def PotentialCertificate.potentialPairsValid (C : PotentialCertificate) : Prop :=
  ∀ i : Fin C.rows.length, ∀ j : Fin C.cols.length,
    let r := getRow C.rows i.val
    let c := getCol C.cols j.val
    let p := rowPot C i.val + colPot C j.val
    baseEntryBound r c ≤ p ∧
      (r.cell = c.cell → sameCellEntryBound r c ≤ p)

def PotentialCertificate.objectiveIntercept (C : PotentialCertificate) : ℚ :=
  listRatSum ((List.range C.rows.length).map fun i =>
    (rowPot C i : ℚ) * (getGroup C.groups (getRow C.rows i).cell).widthIntercept) +
  listRatSum ((List.range C.cols.length).map fun j =>
    (colPot C j : ℚ) * (getGroup C.groups (getCol C.cols j).cell).widthIntercept)

def PotentialCertificate.objectiveSlope (C : PotentialCertificate) : ℚ :=
  listRatSum ((List.range C.rows.length).map fun i =>
    (rowPot C i : ℚ) * (getGroup C.groups (getRow C.rows i).cell).widthSlope) +
  listRatSum ((List.range C.cols.length).map fun j =>
    (colPot C j : ℚ) * (getGroup C.groups (getCol C.cols j).cell).widthSlope)

def PotentialCertificate.objectiveValid (C : PotentialCertificate) : Prop :=
  C.objectiveIntercept = C.claimedLineIntercept ∧
  C.objectiveSlope = C.claimedLineSlope ∧
  C.claimedIntegral =
    C.claimedLineIntercept * (C.hi - C.lo) +
      C.claimedLineSlope * (C.hi ^ 2 - C.lo ^ 2) / 2

def PotentialCertificate.valid (C : PotentialCertificate) : Prop :=
  C.tableShape ∧ C.widthsPartition ∧ C.potentialPairsValid ∧ C.objectiveValid

def PotentialCertificate.shapeChecks (C : PotentialCertificate) : Bool :=
  decide (C.lo < C.hi ∧ C.rowPotentials.length = C.rows.length ∧
    C.colPotentials.length = C.cols.length ∧
    C.declaredBasePairs = C.rows.length * C.cols.length) &&
  (List.range C.rows.length).all (fun i => decide ((getRow C.rows i).cell < C.groups.length)) &&
  (List.range C.cols.length).all (fun j => decide ((getCol C.cols j).cell < C.groups.length))

def PotentialCertificate.pairChecks (C : PotentialCertificate) : Bool :=
  (List.range C.rows.length).all fun i =>
    (List.range C.cols.length).all fun j =>
      let r := getRow C.rows i
      let c := getCol C.cols j
      let p := rowPot C i + colPot C j
      decide (baseEntryBound r c ≤ p) &&
        (if r.cell = c.cell then decide (sameCellEntryBound r c ≤ p) else true)

def PotentialCertificate.widthsCheck (C : PotentialCertificate) : Bool :=
  decide (listRatSum (C.groups.map CellGroup.widthIntercept) = 0 ∧
    listRatSum (C.groups.map CellGroup.widthSlope) = 1)

def PotentialCertificate.objectiveCheck (C : PotentialCertificate) : Bool :=
  decide (C.objectiveIntercept = C.claimedLineIntercept ∧
    C.objectiveSlope = C.claimedLineSlope ∧
    C.claimedIntegral = C.claimedLineIntercept * (C.hi - C.lo) +
      C.claimedLineSlope * (C.hi ^ 2 - C.lo ^ 2) / 2)

def PotentialCertificate.checks (C : PotentialCertificate) : Bool :=
  C.shapeChecks && C.pairChecks && C.widthsCheck && C.objectiveCheck
def p0LogTwoLower : ℚ :=
  ∑ k ∈ Finset.range 30,
    2 * (1 / 3 : ℚ) ^ (2 * k + 1) / (2 * k + 1 : ℚ)

def p0BasicIntegerizerRateClaim : ℚ :=
  p0LowIntegralClaim + p0SmallPrimeTailClaim + p0HighIntegralClaim -
    (13 / 16 : ℚ) * p0LogTwoLower

end IntegerizationTables
end Li2Lean
