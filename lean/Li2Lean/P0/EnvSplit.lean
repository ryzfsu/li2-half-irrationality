/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvDet

/-!
# Row-by-row splitting and block (Laplace) reduction

* `det_split_rows`: if the `inr` rows are sums `P i + Q i`, the determinant is the sum over
  subsets `t` of the determinants with rows `P i` (`i ∈ t`) and `Q i` (`i ∉ t`)
  (paper v13 `p0-analytic.tex` l. 80: "splitting the diagonal term row by row").
* `norm_det_of_block`: if, after reindexing rows by `eR` and columns by `eC`, the rows
  `inr b` vanish on the columns `inl` and are diagonal on the columns `inr`, then
  `‖det N‖ = ‖det (upper-left block)‖ · ∏ ‖λ b‖`.
-/

open Finset

namespace Li2Lean.P0.Env

noncomputable section

variable {κ ι : Type*} [Fintype κ] [DecidableEq κ] [Fintype ι] [DecidableEq ι]

theorem det_sum_rows_gen (M : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) :
    M.det = ∑ τ : Equiv.Perm (κ ⊕ ι), sgnC τ *
      ((∏ k, M (Sum.inl k) (τ (Sum.inl k))) * ∏ i, M (Sum.inr i) (τ (Sum.inr i))) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro τ _
  rw [Fintype.prod_sum_type]
  simp [Matrix.transpose_apply, sgnC]

/-- Rows `inr i` replaced by `P i` for `i ∈ t` and by `Q i` otherwise. -/
def splitMat (M : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) (P Q : ι → (κ ⊕ ι) → ℂ) (t : Finset ι) :
    Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ :=
  Matrix.of fun r c => Sum.elim (fun k => M (Sum.inl k) c)
    (fun i => if i ∈ t then P i c else Q i c) r

theorem det_split_rows (M : Matrix (κ ⊕ ι) (κ ⊕ ι) ℂ) (P Q : ι → (κ ⊕ ι) → ℂ)
    (h : ∀ i c, M (Sum.inr i) c = P i c + Q i c) :
    M.det = ∑ t : Finset ι, (splitMat M P Q t).det := by
  rw [det_sum_rows_gen M]
  simp_rw [det_sum_rows_gen (splitMat M P Q _)]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [h]
  rw [Finset.prod_add, ← Finset.powerset_univ, Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t _
  simp only [splitMat, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr]
  rw [Finset.prod_ite]
  have h1 : (univ : Finset ι).filter (fun i => i ∈ t) = t := by ext; simp
  have h2 : (univ : Finset ι).filter (fun i => i ∉ t) = univ \ t := by ext; simp
  rw [h1, h2]

/-- Block (Laplace) reduction for pinned rows. -/
theorem norm_det_of_block {ρ α β : Type*} [Fintype ρ] [DecidableEq ρ] [Fintype α]
    [DecidableEq α] [Fintype β] [DecidableEq β]
    (N : Matrix ρ ρ ℂ) (eR eC : α ⊕ β ≃ ρ) (lam : β → ℂ)
    (hzero : ∀ b a, N (eR (Sum.inr b)) (eC (Sum.inl a)) = 0)
    (hdiag : ∀ b b', N (eR (Sum.inr b)) (eC (Sum.inr b')) = if b = b' then lam b else 0) :
    ‖N.det‖ = ‖(Matrix.of fun a a' => N (eR (Sum.inl a)) (eC (Sum.inl a'))).det‖ *
      ∏ b, ‖lam b‖ := by
  rw [← norm_det_submatrix_equiv N eR eC]
  have hblk : N.submatrix eR eC = Matrix.fromBlocks
      (Matrix.of fun a a' => N (eR (Sum.inl a)) (eC (Sum.inl a')))
      (Matrix.of fun a b => N (eR (Sum.inl a)) (eC (Sum.inr b))) 0
      (Matrix.diagonal lam) := by
    ext r c
    rcases r with a | b <;> rcases c with a' | b'
    · simp
    · simp
    · simp [hzero]
    · simp [hdiag, Matrix.diagonal_apply]
  rw [hblk, Matrix.det_fromBlocks_zero₂₁, Matrix.det_diagonal, norm_mul, norm_prod]

end

end Li2Lean.P0.Env
