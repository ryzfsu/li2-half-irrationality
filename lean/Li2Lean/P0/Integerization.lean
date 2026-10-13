/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.LayerInterfaces

namespace Li2Lean.P0.Integerization

noncomputable section

/--
For the baseline denominator clearing in docs/6333 §8.1, (8.2), multiplying
each top row by `d` and each bottom row by `d^2` makes the determinant scale
by the product of those row factors. This lemma isolates the determinant
packaging from the still substantive proof that the literal P0 entries have
the required denominators.

The corresponding baseline in docs/6333 §8.1, (8.1)--(8.2), is
`d_U^(3m) (a-1)^(gm) G_m(a,T) ∈ Z[a,T]`. The sharper pole ledger recorded
in docs/6404 §2 is a separate arithmetic obligation; this row-scaling
package alone does not establish that sharper rate.
-/
theorem det_row_scale {R : Type} [CommRing R] {n : ℕ}
    (A : Matrix (Fin n) (Fin n) R) (s : Fin n → R) :
    Matrix.det (fun i j => s i * A i j) =
      (∏ i : Fin n, s i) * Matrix.det A := by
  have hdiag : Matrix.diagonal s * A = fun i j => s i * A i j := by
    ext i j
    simp [Matrix.mul_apply, Matrix.diagonal]
  rw [← hdiag, Matrix.det_mul]
  simp [Matrix.det_diagonal]

/--
A rowwise integral model for a rational polynomial matrix. Each `s i` is
the exact scalar used on row `i`; the P0 baseline uses `d_U` on the C-block
and `d_U^2 (a-1)^g` on the B-block (docs/6333 §8.1, (8.2)).
-/
def IntegerizedRows {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Polynomial ℚ))
    (s : Fin n → ℚ) : Prop :=
  ∃ A : Matrix (Fin n) (Fin n) (Polynomial ℤ),
    ∀ i j, Polynomial.map (Int.castRingHom ℚ) (A i j) =
      Polynomial.C (s i) * M i j

theorem map_det_int_poly_to_rat {n : ℕ}
    (A : Matrix (Fin n) (Fin n) (Polynomial ℤ)) :
    Polynomial.map (Int.castRingHom ℚ) (Matrix.det A) =
      Matrix.det (fun i j => Polynomial.map (Int.castRingHom ℚ) (A i j)) := by
  calc
    Polynomial.map (Int.castRingHom ℚ) (Matrix.det A) =
        (A.map (Polynomial.map (Int.castRingHom ℚ))).det :=
          RingHom.map_det (Polynomial.mapRingHom (Int.castRingHom ℚ)) A
    _ = Matrix.det (fun i j => Polynomial.map (Int.castRingHom ℚ) (A i j)) := by
          rfl

/--
If the scaled rows of a rational polynomial matrix are integral, its
determinant has an integer polynomial representative with the exact product
of row scalars. The theorem is generic packaging; the P0 rowwise
denominator-clearance obligation from docs/6333 §8.1, (8.2), and the sharper
rate in docs/6404 §2 remain open from the formulas in `Li2Lean.LayerInterfaces`.
-/
theorem det_integerized_of_rows {n : ℕ}
    (M : Matrix (Fin n) (Fin n) (Polynomial ℚ))
    (s : Fin n → ℚ) (hrows : IntegerizedRows M s) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (∏ i : Fin n, s i) * Matrix.det M := by
  rcases hrows with ⟨A, hA⟩
  refine ⟨Matrix.det A, ?_⟩
  calc
    Polynomial.map (Int.castRingHom ℚ) (Matrix.det A) =
        Matrix.det (fun i j => Polynomial.map (Int.castRingHom ℚ) (A i j)) :=
          map_det_int_poly_to_rat A
    _ = Matrix.det (fun i j => Polynomial.C (s i) * M i j) := by
          apply congrArg Matrix.det
          funext i j
          exact hA i j
    _ = (∏ i : Fin n, Polynomial.C (s i)) * Matrix.det M := det_row_scale M (fun i => Polynomial.C (s i))
    _ = Polynomial.C (∏ i : Fin n, s i) * Matrix.det M := by simp

/--
The literal rational P0 matrix from docs/6333 §§1--2, already fixed in the
S0.5 interface. This name pins the matrix used by the
integerization lemmas to that construction.
-/
noncomputable def p0RationalDeterminant (a : ℚ) (m : ℕ) : Polynomial ℚ :=
  Matrix.det (Li2Lean.p0MatrixQ a m)

/--
The explicit row factors for the source matrix in `LayerInterfaces.p0MatrixQ`.
Here `d` is the rational image of `d_U`, and `g=m/2`; for indices in the
lower block the additional `(a-1)^g` factor clears the baseline pole order
from docs/6333 §8.1. Establishing that every scaled entry is in `Z[T]` is
deliberately not bundled into this definition.
-/
def p0RowScale (a : ℚ) (m d : ℕ) : Fin (2 * m) → ℚ := fun r =>
  if r.val < m then (d : ℚ) else (d : ℚ) ^ 2 * (a - 1) ^ (m / 2)

/--
Specialization of the generic determinant package to the fixed literal P0
matrix. The premise is the still-open rowwise denominator-clearance proof;
this theorem does not close the full rowwise denominator-clearance result.
-/
theorem p0_determinant_integerized_of_rows {a : ℚ} {m d : ℕ}
    (hrows : IntegerizedRows (Li2Lean.p0MatrixQ a m) (p0RowScale a m d)) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (∏ r : Fin (2 * m), p0RowScale a m d r) *
          p0RationalDeterminant a m := by
  exact det_integerized_of_rows (Li2Lean.p0MatrixQ a m) (p0RowScale a m d) hrows

end

end Li2Lean.P0.Integerization
