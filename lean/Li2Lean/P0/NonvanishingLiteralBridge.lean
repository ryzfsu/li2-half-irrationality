/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.NonvanishingTower
import Li2Lean.P0.NonvanishingSeedLiteral
import Li2Lean.P0.SeedLiteral.ActualSourceBlock8
import Li2Lean.P0.SeedLiteral.ActualP0SeedCertificate
import Li2Lean.P0.ControlledResidue

namespace Li2Lean

noncomputable section

open Li2Lean.P0

/-!
This file records the exact boundary between the literal 64 x 64 seed and
the tower certificate. The actual source matrix determinant is proved by
`actualP0SeedMatrix_det_eq_30`. The remaining explicit field is the transfer
from the tower's `ReducedRational` seed to this finite-place determinant.
-/

/-- A `ReducedRational` value determines its residue once the denominator is
certified invertible at the finite place. -/
theorem reducedRational_residue_eq_of_value_eq
    {p : ℕ} [Fact (Nat.Prime p)]
    {x y : ContourKit.ReducedRational p}
    (hvalue : x.value = y.value) : x.residue = y.residue := by
  have hxdenQ : (x.denominator : ℚ) ≠ 0 := by
    exact_mod_cast x.denominator_ne_zero
  have hydenQ : (y.denominator : ℚ) ≠ 0 := by
    exact_mod_cast y.denominator_ne_zero
  have hquot : (x.numerator : ℚ) / (x.denominator : ℚ) =
      (y.numerator : ℚ) / (y.denominator : ℚ) := by
    calc
      (x.numerator : ℚ) / (x.denominator : ℚ) = x.value := x.value_eq.symm
      _ = y.value := hvalue
      _ = (y.numerator : ℚ) / (y.denominator : ℚ) := y.value_eq
  have hcrossQ : (x.numerator : ℚ) * (y.denominator : ℚ) =
      (y.numerator : ℚ) * (x.denominator : ℚ) := by
    have h := hquot
    field_simp [hxdenQ, hydenQ] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hcrossZ : x.numerator * y.denominator =
      y.numerator * x.denominator := by
    exact_mod_cast hcrossQ
  have hcross : (x.numerator : ZMod p) * (y.denominator : ZMod p) =
      (y.numerator : ZMod p) * (x.denominator : ZMod p) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod p)) hcrossZ
  rw [x.residue_eq, y.residue_eq]
  field_simp [x.denominator_residue_ne_zero, y.denominator_residue_ne_zero]
  simpa [mul_comm] using hcross

/-- The actual m=32, T=0 source matrix reduced at the finite place. -/
def p0A2ActualSeedMatrix : Matrix (Fin 64) (Fin 64) P0.ControlledResidue.F83 :=
  fun r c => P0.SeedLiteral.actualSeedEntry r c

/-- The source entry is the rational sourceSeedQ entry followed by its
finite-place cast. This is an equality of definitions, not a determinant
or nonvanishing assertion. -/
theorem p0A2ActualSeedMatrix_entry_source (r c : Fin 64) :
    p0A2ActualSeedMatrix r c =
      ((P0.ControlledResidue.sourceSeedQ r c : ℚ) :
        P0.ControlledResidue.F83) := by
  change P0.SeedLiteral.actualSeedEntry r c = _
  rw [P0.SeedLiteral.actualSeedEntry]
  rw [P0.ControlledResidue.sourceSeedQ_eq_p0MatrixQ_eval_zero]

/-- The first 8 x 8 block of the actual seed agrees with the literal table. -/
theorem p0A2ActualSeedMatrix_block8 (i j : Fin 8) :
    p0A2ActualSeedMatrix
        (⟨i.val, by omega⟩ : Fin 64)
        (⟨j.val, by omega⟩ : Fin 64) =
      P0.SeedLiteral.aMat
        (⟨i.val, by omega⟩ : Fin 64)
        (⟨j.val, by omega⟩ : Fin 64) := by
  exact P0.SeedLiteral.actualSeed_block8 i j

/-- The rational seed value is the determinant of the rational source matrix. -/
theorem p0A2_sourceSeedQ_det_value {F : P0Family} (hbase : F.a = 2) :
    p0SourceEvalQ F 32 0 = Matrix.det P0.ControlledResidue.sourceSeedQ := by
  calc
    p0SourceEvalQ F 32 0 = (p0CanonicalPolynomial F.a 32).eval 0 := rfl
    _ = (p0CanonicalPolynomial 2 32).eval 0 := by rw [hbase]
    _ = Matrix.det P0.ControlledResidue.sourceSeedQ :=
      P0.ControlledResidue.sourceSeedQ_det_eq_p0Canonical_eval_zero.symm

/-- The finite-place representative of the rational source determinant.
The first field supplies its 83-integral representation; the second field
is the remaining determinant-level residue transport to the actual source
matrix. -/
structure P0A2SeedDeterminantFinitePlaceCertificate where
  source_determinant : ContourKit.ReducedRational 83
  source_determinant_value : source_determinant.value =
    Matrix.det P0.ControlledResidue.sourceSeedQ
  source_determinant_residue : source_determinant.residue =
    Matrix.det p0A2ActualSeedMatrix

theorem p0A2ActualSeedMatrix_eq_residueHom_map :
    P0.ControlledResidue.residueHom.mapMatrix
        P0.ControlledResidue.sourceSeedGood = p0A2ActualSeedMatrix := by
  ext r c
  change ((P0.ControlledResidue.sourceSeedGood r c : ℚ) :
      P0.ControlledResidue.F83) = p0A2ActualSeedMatrix r c
  rw [p0A2ActualSeedMatrix_entry_source]
  rfl

theorem p0A2_sourceSeedGood_det_residue :
    P0.ControlledResidue.residueHom
        (Matrix.det P0.ControlledResidue.sourceSeedGood) =
      Matrix.det p0A2ActualSeedMatrix := by
  calc
    P0.ControlledResidue.residueHom
        (Matrix.det P0.ControlledResidue.sourceSeedGood) =
        (P0.ControlledResidue.residueHom.mapMatrix
          P0.ControlledResidue.sourceSeedGood).det :=
      RingHom.map_det P0.ControlledResidue.residueHom
        P0.ControlledResidue.sourceSeedGood
    _ = Matrix.det p0A2ActualSeedMatrix := by
      rw [p0A2ActualSeedMatrix_eq_residueHom_map]

def p0A2SourceDeterminant : ContourKit.ReducedRational 83 :=
  P0.ControlledResidue.reducedOf
    (Matrix.det P0.ControlledResidue.sourceSeedQ)
    (by
      exact P0.ControlledResidue.sourceSeedQ_det_mem)

theorem p0A2SourceDeterminant_value :
    p0A2SourceDeterminant.value = Matrix.det P0.ControlledResidue.sourceSeedQ := rfl

theorem p0A2SourceDeterminant_residue :
    p0A2SourceDeterminant.residue = Matrix.det p0A2ActualSeedMatrix := by
  let hcop : Nat.Coprime (Matrix.det P0.ControlledResidue.sourceSeedQ).den 83 := by
    exact P0.ControlledResidue.sourceSeedQ_det_mem
  change P0.ControlledResidue.residueOf
      (Matrix.det P0.ControlledResidue.sourceSeedQ) hcop =
    Matrix.det p0A2ActualSeedMatrix
  rw [P0.ControlledResidue.residueOf_eq_cast]
  have hdet := P0.ControlledResidue.sourceSeedGood_det_coe
  have hmap := p0A2_sourceSeedGood_det_residue
  calc
    ((Matrix.det P0.ControlledResidue.sourceSeedQ : ℚ) :
        P0.ControlledResidue.F83) =
        P0.ControlledResidue.residueHom
          (Matrix.det P0.ControlledResidue.sourceSeedGood) := by
      rw [show (Matrix.det P0.ControlledResidue.sourceSeedQ : ℚ) =
          ((Matrix.det P0.ControlledResidue.sourceSeedGood :
            P0.ControlledResidue.Good83) : ℚ) by
        exact hdet.symm]
      rfl
    _ = Matrix.det p0A2ActualSeedMatrix := hmap

def p0A2SeedDeterminantFinitePlaceCertificate :
    P0A2SeedDeterminantFinitePlaceCertificate :=
  { source_determinant := p0A2SourceDeterminant
    source_determinant_value := p0A2SourceDeterminant_value
    source_determinant_residue := p0A2SourceDeterminant_residue }

theorem P0A2SeedDeterminantFinitePlaceCertificate.seed_argument
    {F : P0Family} (hbase : F.a = 2)
    (hcert : P0A2SeedDeterminantFinitePlaceCertificate) :
    ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      ∃ s : ContourKit.ReducedRational 83,
        s.value = p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r) ∧
        s.residue = hcert.source_determinant.residue := by
  apply p0A2_seed_argument_of_seed_value hbase hcert.source_determinant
  calc
    hcert.source_determinant.value =
        Matrix.det P0.ControlledResidue.sourceSeedQ :=
      hcert.source_determinant_value
    _ = p0SourceEvalQ F 32 0 :=
      (p0A2_sourceSeedQ_det_value hbase).symm

/-- A finite-place determinant representative transfers its residue to the
tower seed because both represent the same rational source determinant. -/
theorem P0A2SeedDeterminantFinitePlaceCertificate.seed_residue_eq_actual_det
    {F : P0Family} {tower : P0FrobeniusTowerCertificate F 32 83}
    (hbase : F.a = 2)
    (hcert : P0A2SeedDeterminantFinitePlaceCertificate) :
    tower.seed.residue = Matrix.det p0A2ActualSeedMatrix := by
  letI : Fact (Nat.Prime 83) := ⟨by norm_num⟩
  have hvalue : tower.seed.value = hcert.source_determinant.value := by
    calc
      tower.seed.value = p0SourceEvalQ F 32 0 := tower.seed_value
      _ = Matrix.det P0.ControlledResidue.sourceSeedQ :=
        p0A2_sourceSeedQ_det_value hbase
      _ = hcert.source_determinant.value :=
        hcert.source_determinant_value.symm
  exact (reducedRational_residue_eq_of_value_eq hvalue).trans
    hcert.source_determinant_residue

/-- The actual rational source matrix has determinant 30 after reduction. -/
theorem p0A2ActualSeedMatrix_det_eq_30 :
    Matrix.det p0A2ActualSeedMatrix = (30 : P0.ControlledResidue.F83) := by
  change Li2Lean.P0.actualP0SeedMatrix.det = _
  exact Li2Lean.P0.actualP0SeedMatrix_det_eq_30

/-- The explicit bridge to the tower's `seed_residue_eq_30` field. The
residue interpretation remains a finite-place transfer obligation. -/
theorem P0A2SeedDeterminantFinitePlaceCertificate.seed_residue_eq_30
    {F : P0Family} {tower : P0FrobeniusTowerCertificate F 32 83}
    (hbase : F.a = 2)
    (hcert : P0A2SeedDeterminantFinitePlaceCertificate) :
    tower.seed.residue = (30 : P0.ControlledResidue.F83) := by
  rw [P0A2SeedDeterminantFinitePlaceCertificate.seed_residue_eq_actual_det
      hbase hcert,
    p0A2ActualSeedMatrix_det_eq_30]

/-- Wrap an existing tower once the a=2 base identity and the finite-place
source determinant link are available. -/
def P0A2SeedDeterminantFinitePlaceCertificate.to_frobenius_certificate
    {F : P0Family} {tower : P0FrobeniusTowerCertificate F 32 83}
    (hbase : F.a = 2)
    (hcert : P0A2SeedDeterminantFinitePlaceCertificate) :
    P0A2FrobeniusTowerCertificate F :=
  { base_is_two := hbase
    tower := tower
    seed_residue_eq_30 := P0A2SeedDeterminantFinitePlaceCertificate.seed_residue_eq_30
      hbase hcert }

end

end Li2Lean
