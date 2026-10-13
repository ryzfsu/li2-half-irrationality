/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationProofs

namespace Li2Lean.IntegerizationScalarSpecialization

/-- Evaluating a polynomial divisibility by `X^n` preserves the evaluated
factor `a^n`. -/
theorem eval_dvd_eval_of_X_pow {R : Type*} [CommSemiring R]
    (P : Polynomial R) (a : R) (n : ℕ)
    (h : Polynomial.X ^ n ∣ P) : a ^ n ∣ P.eval a := by
  rcases h with ⟨Q, hQ⟩
  refine ⟨Q.eval a, ?_⟩
  rw [hQ, Polynomial.eval_mul, Polynomial.eval_pow,
    Polynomial.eval_X]

/-- Scalar feature divisibility specializes from the formal base variable
to the actual `a = 2` integer polynomial. -/
theorem scalar_two_pow_dvd_eval
    (P : Polynomial (Polynomial ℤ)) (n : ℕ)
    (h : (Polynomial.X : Polynomial (Polynomial ℤ)) ^ n ∣ P) :
    Polynomial.C ((2 : ℤ) ^ n) ∣
      P.eval (Polynomial.C (2 : ℤ)) := by
  have h' := eval_dvd_eval_of_X_pow P (Polynomial.C (2 : ℤ)) n h
  simpa only [Polynomial.C_pow] using h'

/-- Rational-coefficient formal divisibility descends to the literal integer
polynomial and then specializes to the scalar factor `2^n`. -/
theorem scalar_two_pow_dvd_of_rat_map
    (P : Polynomial (Polynomial ℤ)) (n : ℕ)
    (h : (Polynomial.X : Polynomial (Polynomial ℚ)) ^ n ∣
      Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) P) :
    Polynomial.C ((2 : ℤ) ^ n) ∣
      P.eval (Polynomial.C (2 : ℤ)) := by
  exact scalar_two_pow_dvd_eval P n
    (Li2Lean.P0.Integerization.int_bivariate_x_pow_dvd_of_rat_map h)

/-- A square matrix that factors through a strictly smaller finite dimension
has zero determinant. This is the rank-one-feature linear algebra step used
when the available feature vectors are fewer than the matrix dimension. -/
theorem det_mul_eq_zero_of_middle_dimension_lt {K : Type*} [Field K]
    {n r : ℕ} (A : Matrix (Fin n) (Fin r) K)
    (B : Matrix (Fin r) (Fin n) K) (hr : r < n) :
    (A * B).det = 0 := by
  apply Matrix.det_eq_zero_of_not_linearIndependent_rows
  intro hli
  have hArank : A.rank ≤ r := Matrix.rank_le_width A
  have hrank : (A * B).rank ≤ r :=
    (Matrix.rank_mul_le_left A B).trans hArank
  have hfull : (A * B).rank = n := by
    simpa using hli.rank_matrix
  omega

/-- A sum of fewer than `n` outer products has zero determinant. -/
theorem det_sum_rank_one_eq_zero {K : Type*} [Field K]
    {n r : ℕ} (u v : Fin r → Fin n → K) (hr : r < n) :
    (Matrix.of fun i j => ∑ k : Fin r, u k i * v k j).det = 0 := by
  let A : Matrix (Fin n) (Fin r) K := fun i k => u k i
  let B : Matrix (Fin r) (Fin n) K := fun k j => v k j
  have hM : (Matrix.of fun i j => ∑ k : Fin r, u k i * v k j) = A * B := by
    ext i j
    change (∑ k : Fin r, u k i * v k j) =
      ∑ k : Fin r, A i k * B k j
    simp [A, B]
  rw [hM]
  exact det_mul_eq_zero_of_middle_dimension_lt A B hr

#print axioms eval_dvd_eval_of_X_pow
#print axioms scalar_two_pow_dvd_eval
#print axioms scalar_two_pow_dvd_of_rat_map
#print axioms det_mul_eq_zero_of_middle_dimension_lt
#print axioms det_sum_rank_one_eq_zero

end Li2Lean.IntegerizationScalarSpecialization
