/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.P0.CauchyDeterminant

open Polynomial

theorem eval_matrix_eq_vandermonde_mul_coeff {n : ℕ} (v : Fin n → ℂ)
    (p : Fin n → Polynomial ℂ) (hdeg : ∀ j, (p j).natDegree < n) :
    Matrix.of (fun i j => (p j).eval (v i)) =
      Matrix.vandermonde v * Matrix.of (fun (i j : Fin n) => (p j).coeff i) := by
  ext i j
  simp_rw [Matrix.mul_apply, Matrix.vandermonde_apply, Matrix.of_apply,
    Polynomial.eval, Polynomial.eval₂_eq_sum]
  have hsupp : (p j).support ⊆ Finset.range n := supp_subset_range (hdeg j)
  rw [Polynomial.sum_eq_of_subset _ (fun k => zero_mul ((v i) ^ k)) hsupp,
    ← Fin.sum_univ_eq_sum_range]
  congr 1
  ext k
  simp only [RingHom.id_apply]
  rw [mul_comm]


noncomputable section

def omittedLinearProduct {n : ℕ} (y : Fin n → ℂ) (j : Fin n) : Polynomial ℂ :=
  ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (Polynomial.X + Polynomial.C (y k))

lemma omittedLinearProduct_eval {n : ℕ} (y : Fin n → ℂ) (j : Fin n) (z : ℂ) :
    (omittedLinearProduct y j).eval z =
      ∏ k ∈ (Finset.univ : Finset (Fin n)).erase j, (z + y k) := by
  simp [omittedLinearProduct, Polynomial.eval_prod, Polynomial.eval_add]

lemma omittedLinearProduct_natDegree_lt {n : ℕ} (y : Fin n → ℂ) (j : Fin n) :
    (omittedLinearProduct y j).natDegree < n := by
  calc
    (omittedLinearProduct y j).natDegree ≤
        ∑ k ∈ (Finset.univ : Finset (Fin n)).erase j,
          (Polynomial.X + Polynomial.C (y k)).natDegree := by
            simp only [omittedLinearProduct]
            exact Polynomial.natDegree_prod_le _ _
    _ = ((Finset.univ : Finset (Fin n)).erase j).card := by
      simp
    _ = n - 1 := by simp
    _ < n := by
      have hn : 0 < n := j.isLt |> Nat.zero_lt_of_lt
      omega

lemma lowerPairProduct {n : ℕ} (y : Fin n → ℂ) :
    (∏ i : Fin n, ∏ j ∈ Finset.Iio i, (y j - y i)) =
      ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i - y j) := by
  have hIio (i : Fin n) :
      (Finset.univ : Finset (Fin n)).filter (fun j => j < i) = Finset.Iio i := by
    ext j
    simp [Finset.mem_Iio]
  have hIoi (i : Fin n) :
      (Finset.univ : Finset (Fin n)).filter (fun j => i < j) = Finset.Ioi i := by
    ext j
    simp [Finset.mem_Ioi]
  calc
    (∏ i : Fin n, ∏ j ∈ Finset.Iio i, (y j - y i)) =
        ∏ i : Fin n, ∏ j : Fin n, if j < i then (y j - y i) else 1 := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [← hIio i, Finset.prod_filter]
    _ = ∏ i : Fin n, ∏ j : Fin n, if i < j then (y i - y j) else 1 := by
          rw [Finset.prod_comm]
    _ = ∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i - y j) := by
          apply Finset.prod_congr rfl
          intro i hi
          rw [← hIoi i, Finset.prod_filter]

lemma omittedPairProduct_eq_vandermonde_mul {n : ℕ} (y : Fin n → ℂ) :
    (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (y j - y i)) =
      (Matrix.vandermonde (fun i => -y i)).det *
        (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) := by
  have hsplit (i : Fin n) :
      (Finset.univ : Finset (Fin n)).erase i = Finset.Iio i ∪ Finset.Ioi i := by
    ext j
    simp only [Finset.mem_erase, Finset.mem_univ, Finset.mem_union,
      Finset.mem_Iio, Finset.mem_Ioi]
    constructor
    · intro h
      exact lt_or_gt_of_ne h.1
    · intro h
      rcases h with h | h
      · exact ⟨ne_of_lt h, trivial⟩
      · exact ⟨ne_of_gt h, trivial⟩
  have hdisj (i : Fin n) : Disjoint (Finset.Iio i) (Finset.Ioi i) := by
    rw [Finset.disjoint_left]
    intro j hj₁ hj₂
    simp only [Finset.mem_Iio] at hj₁
    simp only [Finset.mem_Ioi] at hj₂
    omega
  calc
    (∏ i : Fin n, ∏ j ∈ (Finset.univ : Finset (Fin n)).erase i, (y j - y i)) =
        ∏ i : Fin n,
          ((∏ j ∈ Finset.Iio i, (y j - y i)) *
            ∏ j ∈ Finset.Ioi i, (y j - y i)) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [hsplit i, Finset.prod_union (hdisj i)]
    _ = (∏ i : Fin n, ∏ j ∈ Finset.Iio i, (y j - y i)) *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) := by
            rw [← Finset.prod_mul_distrib]
    _ = (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y i - y j)) *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) := by
            rw [lowerPairProduct]
    _ = (Matrix.vandermonde (fun i => -y i)).det *
          (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) := by
            congr 1
            rw [Matrix.det_vandermonde]
            apply Finset.prod_congr rfl
            intro i hi
            apply Finset.prod_congr rfl
            intro j hj
            ring

lemma omittedLinearProduct_coeff_det {n : ℕ} (y : Fin n → ℂ)
    (hy : Function.Injective y) :
    (Matrix.of (fun (i j : Fin n) =>
      (omittedLinearProduct y j).coeff i)).det =
        (Matrix.vandermonde y).det := by
  classical
  let v : Fin n → ℂ := fun i => -y i
  have hEval :
      (Matrix.of (fun (i j : Fin n) =>
        (omittedLinearProduct y j).eval (v i))).det =
          ∏ i : Fin n, ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i,
            (y k - y i) := by
    have hmatrix : Matrix.of (fun (i j : Fin n) =>
        (omittedLinearProduct y j).eval (v i)) =
        Matrix.diagonal (fun i =>
          ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y k - y i)) := by
      ext i j
      change (omittedLinearProduct y j).eval (v i) =
        (if i = j then
          ∏ k ∈ (Finset.univ : Finset (Fin n)).erase i, (y k - y i)
        else 0)
      by_cases hij : i = j
      · subst j
        rw [omittedLinearProduct_eval]
        simp only [v]
        apply Finset.prod_congr rfl
        intro k hk
        ring
      · rw [omittedLinearProduct_eval]
        simp only [v, ite_eq_right hij]
        apply Finset.prod_eq_zero
        · exact Finset.mem_erase.mpr ⟨hij, Finset.mem_univ _⟩
        · simp
    rw [hmatrix, Matrix.det_diagonal]
  have hfactor := eval_matrix_eq_vandermonde_mul_coeff v
    (fun j => omittedLinearProduct y j)
    (fun j => omittedLinearProduct_natDegree_lt y j)
  rw [hfactor, Matrix.det_mul] at hEval
  rw [omittedPairProduct_eq_vandermonde_mul] at hEval
  have hpair :
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (y j - y i)) =
        (Matrix.vandermonde y).det := (Matrix.det_vandermonde y).symm
  rw [hpair] at hEval
  have hv : (Matrix.vandermonde v).det ≠ 0 := by
    apply Matrix.det_vandermonde_ne_zero_iff.mpr
    intro i j hij
    apply hy
    simpa [v] using congrArg Neg.neg hij
  exact mul_left_cancel₀ hv hEval

lemma vandermonde_append_product {d m : ℕ} (x : Fin d → ℂ) (r : Fin m → ℂ) :
    (∏ i : Fin (d + m), ∏ j ∈ Finset.Ioi i,
      (Fin.append x r j - Fin.append x r i)) =
      (∏ i : Fin d, ∏ j ∈ Finset.Ioi i, (x j - x i)) *
        (∏ i : Fin m, ∏ j ∈ Finset.Ioi i, (r j - r i)) *
        (∏ i : Fin d, ∏ j : Fin m, (r j - x i)) := by
  classical
  have hcond {n : ℕ} (v : Fin n → ℂ) :
      (∏ i : Fin n, ∏ j ∈ Finset.Ioi i, (v j - v i)) =
        ∏ i : Fin n, ∏ j : Fin n, if i < j then v j - v i else 1 := by
    apply Finset.prod_congr rfl
    intro i hi
    have hIoi : Finset.Ioi i =
        (Finset.univ : Finset (Fin n)).filter (fun j => i < j) := by
      ext j
      simp
    rw [hIoi, Finset.prod_filter]
  rw [hcond, Fin.prod_univ_add]
  simp_rw [Fin.prod_univ_add]
  have hcc (i j : Fin d) :
      Fin.castAdd m i < Fin.castAdd m j ↔ i < j := by
    simp only [Fin.lt_def, Fin.val_castAdd]
  have hcn (i : Fin d) (j : Fin m) :
      Fin.castAdd m i < Fin.natAdd d j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hnc (i : Fin m) (j : Fin d) :
      ¬ Fin.natAdd d i < Fin.castAdd m j := by
    simp only [Fin.lt_def, Fin.val_castAdd, Fin.val_natAdd]
    omega
  have hnn (i j : Fin m) :
      Fin.natAdd d i < Fin.natAdd d j ↔ i < j := by
    exact Fin.natAdd_lt_natAdd_iff d
  simp only [Fin.append_left, Fin.append_right, hcc, hcn, hnc, hnn,
    if_true, if_false, Finset.prod_const_one, one_mul, mul_one]
  rw [Finset.prod_mul_distrib, ← hcond x, ← hcond r]
  ring

theorem cauchy_det_eq_vandermonde_mul_inv_denominator {n : ℕ}
    (x y : Fin n → ℂ) (hy : Function.Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0) :
    (Matrix.of (fun (i j : Fin n) => (x i + y j)⁻¹)).det =
      (Matrix.vandermonde x).det * (Matrix.vandermonde y).det *
        (∏ i : Fin n, ∏ j : Fin n, (x i + y j))⁻¹ := by
  classical
  let p : Fin n → Polynomial ℂ := omittedLinearProduct y
  let D : Fin n → ℂ := fun i => ∏ j : Fin n, (x i + y j)
  let C : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => (x i + y j)⁻¹)
  let E : Matrix (Fin n) (Fin n) ℂ :=
    Matrix.of (fun i j => (p j).eval (x i))
  have hrow : E = Matrix.of (fun i j => D i * C i j) := by
    ext i j
    change (p j).eval (x i) = D i * C i j
    change (omittedLinearProduct y j).eval (x i) = D i * C i j
    rw [omittedLinearProduct_eval]
    dsimp [D, C]
    rw [← Finset.prod_erase_mul (Finset.univ : Finset (Fin n))
      (fun k => x i + y k) (Finset.mem_univ j)]
    field_simp [hxy i j]
  have hEvalDet : E.det =
      (Matrix.vandermonde x).det * (Matrix.vandermonde y).det := by
    change (Matrix.of (fun i j =>
      (omittedLinearProduct y j).eval (x i))).det = _
    have hfactor := eval_matrix_eq_vandermonde_mul_coeff x
      (fun j => omittedLinearProduct y j)
      (fun j => omittedLinearProduct_natDegree_lt y j)
    rw [hfactor, Matrix.det_mul,
      omittedLinearProduct_coeff_det y hy]
  have hrowDiag : E = Matrix.diagonal D * C := by
    ext i j
    simp [hrow, D, C, Matrix.mul_apply, Matrix.diagonal]
  have hrowDet : E.det = (∏ i : Fin n, D i) * C.det := by
    rw [hrowDiag, Matrix.det_mul, Matrix.det_diagonal]
  have hdet : (∏ i : Fin n, D i) * C.det =
      (Matrix.vandermonde x).det * (Matrix.vandermonde y).det :=
    hrowDet.symm.trans hEvalDet
  have hden : (∏ i : Fin n, D i) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hxy i j
  apply mul_left_cancel₀ hden
  calc
    (∏ i : Fin n, D i) * C.det =
        (Matrix.vandermonde x).det * (Matrix.vandermonde y).det := hdet
    _ = (∏ i : Fin n, D i) *
          ((Matrix.vandermonde x).det * (Matrix.vandermonde y).det *
            (∏ i : Fin n, D i)⁻¹) := by
          field_simp [hden]

theorem cauchy_det_mul_denominator_eq_vandermonde {n : ℕ}
    (x y : Fin n → ℂ) (hy : Function.Injective y)
    (hxy : ∀ i j, x i + y j ≠ 0) :
    (Matrix.of (fun (i j : Fin n) => (x i + y j)⁻¹)).det *
        (∏ i : Fin n, ∏ j : Fin n, (x i + y j)) =
      (Matrix.vandermonde x).det * (Matrix.vandermonde y).det := by
  have hden : (∏ i : Fin n, ∏ j : Fin n, (x i + y j)) ≠ 0 := by
    apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    apply Finset.prod_ne_zero_iff.mpr
    intro j hj
    exact hxy i j
  rw [cauchy_det_eq_vandermonde_mul_inv_denominator x y hy hxy]
  field_simp [hden]


end

end Li2Lean.P0.CauchyDeterminant
