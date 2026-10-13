/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Nonvanishing
import Li2Lean.P0.Integerization

/-!
# Block determinant algebra for the P0 Frobenius pencil

This file isolates the finite matrix step in `eq:nv-pencil` of
`output/li2-half-paper-v10/sec-nonvanishing.tex`.  The entry-wise Lucas
reduction is deliberately not hidden here: once the reduced tower matrix is
known to be a residue-indexed block diagonal matrix, its determinant and the
block scalar are proved by ordinary matrix algebra.

The final theorem is stated for an arbitrary commutative ring and therefore
does not introduce a certificate field or an additional nonvanishing
hypothesis.  The specialization to the P0 residue field uses
`n = 2 * M` and `c = 2`.
-/

namespace Li2Lean.P0

noncomputable section

open Matrix

variable {R : Type*} [CommRing R]
variable {n M : ℕ}

/-- The residue-block matrix used in `eq:nv-pencil`, docs/6333 §9: a seed
matrix is repeated once per residue class and scaled by the Frobenius scalar
for that residue. -/
def residueBlockMatrix (S : Matrix (Fin n) (Fin n) R) (c : R) (q : ℕ) :
    Matrix (Fin (n * q)) (Fin (n * q)) R :=
  Matrix.reindex finProdFinEquiv finProdFinEquiv
    (Matrix.blockDiagonal (fun v : Fin q => (c ^ v.val) • S))

/-- Determinant of the residue-block matrix from docs/6333 §9, before
simplifying the finite sum of residue indices. -/
theorem det_residueBlockMatrix (S : Matrix (Fin n) (Fin n) R) (c : R) (q : ℕ) :
    (residueBlockMatrix S c q).det =
      (∏ v : Fin q, (c ^ v.val) ^ n) * S.det ^ q := by
  rw [residueBlockMatrix, Matrix.det_reindex_self,
    Matrix.det_blockDiagonal]
  simp only [Matrix.det_smul, Fintype.card_fin]
  rw [Finset.prod_mul_distrib]
  simp [Finset.prod_const]

/-- The finite residue sum in the scalar from docs/6333 §9 is
`q * (q - 1) / 2`. -/
theorem sum_fin_val_mul (q : ℕ) :
    (∑ v : Fin q, v.val) = q * (q - 1) / 2 := by
  calc
    (∑ v : Fin q, v.val) = ∑ i ∈ Finset.range q, i := by
      exact Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q
    _ = q * (q - 1) / 2 := Finset.sum_range_id q

/-- Exact determinant algebra for the residue-indexed Frobenius tower in
docs/6333 §9. -/
theorem det_residueBlockMatrix_eq (S : Matrix (Fin n) (Fin n) R)
    (c : R) (q : ℕ) :
    (residueBlockMatrix S c q).det =
      c ^ (n * (q * (q - 1) / 2)) * S.det ^ q := by
  rw [det_residueBlockMatrix]
  calc
    (∏ v : Fin q, (c ^ v.val) ^ n) * S.det ^ q =
        (∏ v : Fin q, c ^ (v.val * n)) * S.det ^ q := by
          congr 1
          apply Finset.prod_congr rfl
          intro v hv
          rw [pow_mul]
    _ = c ^ (∑ v : Fin q, v.val * n) * S.det ^ q := by
          rw [Finset.prod_pow_eq_pow_sum]
    _ = c ^ (n * (q * (q - 1) / 2)) * S.det ^ q := by
          have hs : (∑ v : Fin q, v.val * n) =
              (∑ v : Fin q, v.val) * n := by
            calc
              (∑ v : Fin q, v.val * n) =
                  ∑ i ∈ Finset.range q, i * n :=
                    Fin.sum_univ_eq_sum_range (fun i : ℕ => i * n) q
              _ = (∑ i ∈ Finset.range q, i) * n := by
                    rw [← Finset.sum_mul]
              _ = (∑ v : Fin q, v.val) * n := by
                    exact congrArg (fun x : ℕ => x * n)
                      (Fin.sum_univ_eq_sum_range (fun i : ℕ => i) q).symm
          rw [hs, sum_fin_val_mul]
          rw [Nat.mul_comm]

/-- The P0 specialization of the scalar in docs/6333 §9 is
`c ^ (M * q * (q - 1))`. -/
theorem det_p0ResidueBlockMatrix_eq (S : Matrix (Fin (2 * M)) (Fin (2 * M)) R)
    (c : R) (q : ℕ) :
    (residueBlockMatrix S c q).det =
      c ^ (M * q * (q - 1)) * S.det ^ q := by
  rw [det_residueBlockMatrix_eq]
  congr 2
  have hEven : Even (q * (q - 1)) := by
    by_cases hq : q = 0
    · simp [hq]
    · have h := Nat.even_mul_succ_self (q - 1)
      have hsucc : (q - 1) + 1 = q := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hq)
      rw [hsucc, Nat.mul_comm] at h
      exact h
  have hhalf : q * (q - 1) / 2 * 2 = q * (q - 1) :=
    Nat.div_mul_cancel hEven.two_dvd
  calc
    2 * M * (q * (q - 1) / 2) = M * (q * (q - 1) / 2 * 2) := by ring
    _ = M * (q * (q - 1)) := by rw [hhalf]
    _ = M * q * (q - 1) := by ring

abbrev P0F83 := ZMod 83

local instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

/-- The Frobenius scalar accumulated by all residue blocks is a unit at the
paper prime `83`, for `q = 83^k`; see docs/6333 §9. -/
theorem p0_tower_scalar_unit (M k : ℕ) :
    (2 : P0F83) ^ (M * 83 ^ k * (83 ^ k - 1)) = 1 := by
  have hmod : 83 ^ k ≡ 1 [MOD 82] := by
    have h83 : 83 ≡ 1 [MOD 82] := by norm_num [Nat.ModEq]
    simpa using h83.pow k
  have hmodNat : 83 ^ k % 82 = 1 := hmod
  have hdiv : 82 ∣ 83 ^ k - 1 := by
    have haux := Nat.mod_add_div (83 ^ k) 82
    rw [hmodNat] at haux
    refine ⟨83 ^ k / 82, ?_⟩
    omega
  obtain ⟨d, hd⟩ := hdiv
  have htwo : (2 : P0F83) ≠ 0 := by decide
  have h82 : (2 : P0F83) ^ 82 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one htwo
  calc
    (2 : P0F83) ^ (M * 83 ^ k * (83 ^ k - 1)) =
        (2 : P0F83) ^ (82 * (M * 83 ^ k * d)) := by
          rw [hd]
          congr 1
          ring
    _ = ((2 : P0F83) ^ 82) ^ (M * 83 ^ k * d) := by rw [pow_mul]
    _ = 1 := by rw [h82]; simp

/-- The exact `83`-tower determinant identity after the residue-block
reindexing from docs/6333 §9. The P0 application still needs the entry-wise
Lucas/Frobenius reduction identifying its concrete tower matrix with
`residueBlockMatrix`. -/
theorem det_p0ResidueBlockMatrix_83 (M k : ℕ)
    (S : Matrix (Fin (2 * M)) (Fin (2 * M)) P0F83) :
    (residueBlockMatrix S 2 (83 ^ k)).det = S.det ^ (83 ^ k) := by
  rw [det_p0ResidueBlockMatrix_eq, p0_tower_scalar_unit]
  simp

/-! ## Exact P0 pencil scaling

The next identity uses the literal rational entries `p0CQ`, `p0BQ`, and
`p0AQ`. It is the polynomial determinant identity in `eq:nv-pencil` before
reduction modulo `p`.
-/

/-- Polynomial substitution `X ↦ X / q²` in the rational P0 determinant,
docs/6333 §9, equation `eq:nv-pencil`. -/
def p0PencilSubstitution (q : ℕ) : Polynomial ℚ :=
  Polynomial.C ((q : ℚ) ^ 2)⁻¹ * Polynomial.X

/-- The exact matrix on the right of the first line of `eq:nv-pencil`,
docs/6333 §§2 and 9. -/
def p0ScaledPencilMatrixQ (a : ℚ) (m q : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) (Polynomial ℚ) := fun r c =>
  let i := m / 4 + (if r.val < m then r.val else r.val - m)
  let j := c.val
  if r.val < m then
    Polynomial.C ((q : ℚ) * p0CQ a (m / 2) i j)
  else
    Polynomial.C ((q : ℚ) ^ 2 * p0BQ a (m / 2) i j) -
      Polynomial.X * Polynomial.C (p0AQ a (m / 2) i j)

/-- Row scalars in the scaled P0 pencil from docs/6333 §9: `q` on the C
block and `q²` on the B block. -/
def p0PencilRowScale (m q : ℕ) : Fin (2 * m) → ℚ := fun r =>
  if r.val < m then (q : ℚ) else (q : ℚ) ^ 2

/-- The product of P0 row scalars in docs/6333 §9 is `q^(3m)`. -/
private theorem p0PencilRowScale_prod (m q : ℕ) :
    (∏ r : Fin (2 * m), p0PencilRowScale m q r) = (q : ℚ) ^ (3 * m) := by
  let f : ℕ → ℚ := fun i => if i < m then (q : ℚ) else (q : ℚ) ^ 2
  have hFin : (∏ r : Fin (2 * m), p0PencilRowScale m q r) =
      ∏ i ∈ Finset.range (2 * m), f i := by
    simpa [p0PencilRowScale, f] using
      (Fin.prod_univ_eq_prod_range f (2 * m))
  rw [hFin]
  have hsplit : 2 * m = m + m := by omega
  rw [hsplit, Finset.prod_range_add]
  have hfirst : (∏ i ∈ Finset.range m, f i) = (q : ℚ) ^ m := by
    calc
      (∏ i ∈ Finset.range m, f i) = ∏ _i ∈ Finset.range m, (q : ℚ) := by
        apply Finset.prod_congr rfl
        intro i hi
        have hi' : i < m := Finset.mem_range.mp hi
        simp [f, hi']
      _ = (q : ℚ) ^ m := by simp [Finset.prod_const]
  have hsecond : (∏ i ∈ Finset.range m, f (m + i)) = ((q : ℚ) ^ 2) ^ m := by
    calc
      (∏ i ∈ Finset.range m, f (m + i)) =
          ∏ _i ∈ Finset.range m, (q : ℚ) ^ 2 := by
        apply Finset.prod_congr rfl
        intro i hi
        have hmi : m ≤ m + i := Nat.le_add_right m i
        simp [f, not_lt_of_ge hmi]
      _ = ((q : ℚ) ^ 2) ^ m := by simp [Finset.prod_const]
  rw [hfirst, hsecond]
  ring

/-- The literal scaled P0 matrix is obtained by substituting `X/q²` and
scaling its two row blocks as in docs/6333 §9, equation `eq:nv-pencil`. -/
private theorem p0_scaled_matrix_eq_rowScale (a : ℚ) (m q : ℕ) (hq : q ≠ 0) :
    p0ScaledPencilMatrixQ a m q = fun r c =>
      Polynomial.C (p0PencilRowScale m q r) *
        Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
          (p0MatrixQ a m r c) := by
  apply Matrix.ext
  intro r c
  by_cases hr : r.val < m
  · simp [p0ScaledPencilMatrixQ, p0PencilRowScale, p0PencilSubstitution,
      p0MatrixQ, hr]
  · have hqQ : (q : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hq
    simp only [p0ScaledPencilMatrixQ, p0PencilRowScale, p0PencilSubstitution,
      p0MatrixQ, if_neg hr]
    change (Polynomial.C ((q : ℚ) ^ 2 *
        p0BQ a (m / 2) (m / 4 + (r.val - m)) c.val) -
        Polynomial.X * Polynomial.C
          (p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val)) =
      Polynomial.C ((q : ℚ) ^ 2) *
        Polynomial.eval₂ Polynomial.C
          (Polynomial.C ((q : ℚ) ^ 2)⁻¹ * Polynomial.X)
          (Polynomial.C (p0BQ a (m / 2) (m / 4 + (r.val - m)) c.val) -
            Polynomial.X * Polynomial.C
              (p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val))
    simp only [Polynomial.eval₂_sub, Polynomial.eval₂_mul,
      Polynomial.eval₂_X, Polynomial.eval₂_C]
    field_simp [Polynomial.C_ne_zero.mpr (pow_ne_zero 2 hqQ)]
    have hqInvPoly' : Polynomial.C ((q : ℚ) ^ 2) *
        Polynomial.C (1 / (q : ℚ) ^ 2) = 1 := by
      rw [← Polynomial.C_mul]
      field_simp [hqQ]
      simp
    rw [Polynomial.C_mul]
    have hcross :
        Polynomial.C ((q : ℚ) ^ 2) *
          (Polynomial.C (1 / (q : ℚ) ^ 2) * Polynomial.X * Polynomial.C
            (p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val)) =
        Polynomial.X * Polynomial.C
            (p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val) := by
      calc
        _ = Polynomial.X * Polynomial.C
              (p0AQ a (m / 2) (m / 4 + (r.val - m)) c.val) *
              (Polynomial.C ((q : ℚ) ^ 2) *
              Polynomial.C (1 / (q : ℚ) ^ 2)) := by ac_rfl
        _ = _ := by rw [hqInvPoly', mul_one]
    rw [mul_sub, hcross]

/-- Exact rational pencil scaling for the literal P0 matrix from docs/6333
§§2 and 9, equation `eq:nv-pencil`; this is the determinant equality before
the separate modular-reduction step. -/
theorem p0_scaled_pencil_det (a : ℤ) (m q : ℕ) (hm : 4 ∣ m) (hq : q ≠ 0) :
    Matrix.det (p0ScaledPencilMatrixQ a m q) =
      Polynomial.C ((q : ℚ) ^ (3 * m)) *
        Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
          (p0CanonicalPolynomial a m) := by
  rw [p0_scaled_matrix_eq_rowScale (a : ℚ) m q hq]
  have hrow := Li2Lean.P0.Integerization.det_row_scale
    (fun r c =>
      Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
        (p0MatrixQ (a : ℚ) m r c))
    (fun r => Polynomial.C (p0PencilRowScale m q r))
  rw [hrow]
  have hscale : (∏ r : Fin (2 * m),
      Polynomial.C (p0PencilRowScale m q r)) =
        Polynomial.C ((q : ℚ) ^ (3 * m)) := by
    calc
      (∏ r : Fin (2 * m), Polynomial.C (p0PencilRowScale m q r)) =
          Polynomial.C (∏ r : Fin (2 * m), p0PencilRowScale m q r) := by simp
      _ = Polynomial.C ((q : ℚ) ^ (3 * m)) := by rw [p0PencilRowScale_prod]
  rw [hscale]
  have hMatrix : p0CanonicalPolynomial a m = Matrix.det (p0MatrixQ (a : ℚ) m) := by
    simp [p0CanonicalPolynomial, hm]
  rw [hMatrix]
  have hdet := RingHom.map_det
    (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q))
    (p0MatrixQ (a : ℚ) m)
  have hdet' : Matrix.det (fun r c =>
      Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
        (p0MatrixQ (a : ℚ) m r c)) =
      Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
        (Matrix.det (p0MatrixQ (a : ℚ) m)) := by
    exact hdet.symm
  rw [hdet']

end

end Li2Lean.P0
