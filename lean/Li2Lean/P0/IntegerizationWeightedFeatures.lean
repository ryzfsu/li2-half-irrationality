/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Algebra.Polynomial.Basic

namespace Li2Lean.P0.Integerization

open Finset

/-- Finite column-multilinear expansion of a sum of rank-one features. -/
theorem det_sum_rank_one_expansion
    {R n κ : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    [Fintype κ] (u v : κ → n → R) :
    Matrix.det (Matrix.of fun i j => ∑ k, u k i * v k j) =
      ∑ p : n → κ, (Matrix.det (Matrix.of fun i j => u (p j) i)) * ∏ j, v (p j) j := by
  classical
  simp only [Matrix.det_apply', Matrix.of_apply, prod_univ_sum, mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro p hp
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Finset.prod_mul_distrib]
  ring

/-- Repeating a feature repeats a column in its selected left-vector matrix. -/
theorem det_selected_features_eq_zero
    {R n κ : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (u : κ → n → R) (p : n → κ) (hp : ¬Function.Injective p) :
    Matrix.det (Matrix.of fun i j => u (p j) i) = 0 := by
  classical
  obtain ⟨i, j, hij, hne⟩ := Function.not_injective_iff.mp hp
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp only [Matrix.of_apply, hij])

/-- Weighted rank-one determinant bound. Only injective feature selections
need satisfy the weight bound; repeated-feature terms vanish. -/
theorem pow_dvd_det_weighted_rank_one
    {R n κ : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    [Fintype κ] (a : R) (u v : κ → n → R) (w : κ → ℕ) (N : ℕ)
    (hweight : ∀ p : n → κ, Function.Injective p → N ≤ ∑ j, w (p j)) :
    a ^ N ∣ Matrix.det
      (Matrix.of fun i j => ∑ k, u k i * (a ^ w k * v k j)) := by
  classical
  rw [det_sum_rank_one_expansion]
  apply Finset.dvd_sum
  intro p hp
  by_cases hinj : Function.Injective p
  · rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (hweight p hinj)) _) _
  · rw [det_selected_features_eq_zero u p hinj, zero_mul]
    exact dvd_zero _

/-- Weighted rank-one determinant bound. Only injective feature selections
need satisfy the weight bound; repeated-feature terms vanish. -/
theorem X_pow_dvd_det_weighted_rank_one
    {R n κ : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    [Fintype κ] (u v : κ → n → Polynomial R) (w : κ → ℕ) (N : ℕ)
    (hweight : ∀ p : n → κ, Function.Injective p → N ≤ ∑ j, w (p j)) :
    Polynomial.X ^ N ∣ Matrix.det
      (Matrix.of fun i j => ∑ k, u k i * (Polynomial.X ^ w k * v k j)) := by
  classical
  rw [det_sum_rank_one_expansion]
  apply Finset.dvd_sum
  intro p hp
  by_cases hinj : Function.Injective p
  · rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
    exact dvd_mul_of_dvd_right
      (dvd_mul_of_dvd_left (pow_dvd_pow _ (hweight p hinj)) _) _
  · rw [det_selected_features_eq_zero u p hinj, zero_mul]
    exact dvd_zero _

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.det_sum_rank_one_expansion
#print axioms Li2Lean.P0.Integerization.det_selected_features_eq_zero
#print axioms Li2Lean.P0.Integerization.X_pow_dvd_det_weighted_rank_one

#print axioms Li2Lean.P0.Integerization.pow_dvd_det_weighted_rank_one

