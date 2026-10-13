/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvMatrix

/-!
# Cauchy-Binet in the frequencies for the truncated P0 determinant

After reindexing rows and columns by `eρ` (`inl k` = lower row `m + k`, `inr i` = upper row
`i`), the lower rows of `truncMatrix m H` are finite sums
`Σ_{t ∈ (g,H]} a_k(t) K(t, ·)`, `a_k(t) = (-1)^{g+1} w_t K(i_k, t)`.  The symmetrized
Cauchy-Binet identity `discrete_andreief` and the counting bound give

  `‖det‖ ≤ Σ_{R increasing, R ⊂ (g,H]} (∏ w_R) ‖det K_{I_m,R}‖ ‖det [K_{R,J_m}; C]‖`

(paper v13 `p0-analytic.tex` ll. 61-71 and l. 629, before the contour expansion).
-/

open Finset

namespace Li2Lean.P0.Env

noncomputable section

/-- Row/column reindexing: `inl k ↦ m + k` (lower block), `inr i ↦ i` (upper block). -/
def eρ (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  (Equiv.sumComm _ _).trans (finSumFinEquiv.trans (finCongr (two_mul m).symm))

theorem eρ_inl (m : ℕ) (k : Fin m) : (eρ m (Sum.inl k)).val = m + k.val := by
  simp [eρ, Nat.add_comm]

theorem eρ_inr (m : ℕ) (i : Fin m) : (eρ m (Sum.inr i)).val = i.val := by
  simp [eρ]

/-- The paper column label `j ∈ J_m` of a reindexed column. -/
def colLab (m : ℕ) (c : Fin m ⊕ Fin m) : ℕ := (eρ m c).val

theorem colLab_lt (m : ℕ) (c : Fin m ⊕ Fin m) : colLab m c < 2 * m := (eρ m c).isLt

theorem colLab_injective (m : ℕ) : Function.Injective (colLab m) := by
  intro a b h
  exact (eρ m).injective (Fin.ext h)

/-- Frequency coefficient `a_k(t) = (-1)^{g+1} w_t K(i_k, t)`. -/
def freqCoef (m : ℕ) (k : Fin m) (t : ℕ) : ℂ :=
  ((((-1 : ℝ) ^ (m / 2 + 1)) * frequencyWeightReal (m / 2) t : ℝ) : ℂ) *
    cauchyKernel (m / 4 + k.val) t

/-- Frequency row vector `K(t, j)`. -/
def freqVec (m : ℕ) (t : ℕ) (c : Fin m ⊕ Fin m) : ℂ := cauchyKernel t (colLab m c)

/-- Upper (source) row `C_{i,j}` with label `i = m/4 + i`. -/
def topRow (m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) : ℂ :=
  ((p0CQ 2 (m / 2) (m / 4 + i.val) (colLab m c) : ℚ) : ℂ)

/-- The matrix `[K_{R,J}; C]` for a frequency tuple `R`. -/
def Ymat (m : ℕ) (R : Fin m → ℕ) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) ℂ :=
  Matrix.of fun r c => Sum.elim (fun l => freqVec m (R l) c) (fun i => topRow m i c) r

theorem trunc_reindex_inl (m H : ℕ) (k : Fin m) (c : Fin m ⊕ Fin m) :
    (truncMatrix m H).submatrix (eρ m) (eρ m) (Sum.inl k) c =
      ∑ t ∈ Ioc (m / 2) H, freqCoef m k t * freqVec m t c := by
  have hk : ¬ (eρ m (Sum.inl k)).val < m := by rw [eρ_inl]; omega
  have hlab : lab m (eρ m (Sum.inl k)) = m / 4 + k.val := by
    rw [lab, eρ_inl, if_neg (by omega)]; omega
  simp only [Matrix.submatrix_apply, truncMatrix, if_neg hk, hlab]
  have hfilter : (range (H + 1)).filter (fun t => m / 2 < t) = Ioc (m / 2) H := by
    ext t; simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_Ioc]; omega
  rw [← Finset.sum_filter, hfilter]
  push_cast
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro t ht
  simp only [freqCoef, freqVec, cauchyKernel, colLab]
  push_cast
  have h1 : ((m / 4 : ℕ) : ℂ) + (k.val : ℂ) + (t : ℂ) ≠ 0 := by
    have : (0 : ℝ) < ((m / 4 : ℕ) : ℝ) + (k.val : ℝ) + (t : ℝ) := by
      have : 0 < t := by simp at ht; omega
      positivity
    exact_mod_cast this.ne'
  have h2 : (t : ℂ) + (((eρ m c).val : ℕ) : ℂ) ≠ 0 := by
    have : (0 : ℝ) < (t : ℝ) + (((eρ m c).val : ℕ) : ℝ) := by
      have : 0 < t := by simp at ht; omega
      positivity
    exact_mod_cast this.ne'
  have h1' : ((m / 4 : ℕ) : ℂ) + (k.val : ℂ) + (t : ℂ) = (((m / 4 + k.val : ℕ) : ℂ) + (t : ℂ)) := by
    push_cast; ring
  rw [show (((eρ m c).val : ℕ) : ℂ) + (t : ℂ) = (t : ℂ) + (((eρ m c).val : ℕ) : ℂ) by ring]
  field_simp

theorem trunc_reindex_inr (m H : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) :
    (truncMatrix m H).submatrix (eρ m) (eρ m) (Sum.inr i) c = topRow m i c := by
  have hi : (eρ m (Sum.inr i)).val < m := by rw [eρ_inr]; exact i.isLt
  have hlab : lab m (eρ m (Sum.inr i)) = m / 4 + i.val := by
    rw [lab, eρ_inr, if_pos i.isLt]
  simp only [Matrix.submatrix_apply, truncMatrix, if_pos hi, hlab, topRow, colLab]

theorem rowRepl_trunc (m H : ℕ) (R : Fin m → ℕ) :
    rowRepl ((truncMatrix m H).submatrix (eρ m) (eρ m)) (fun l => freqVec m (R l)) =
      Ymat m R := by
  ext r c
  rcases r with l | i
  · simp [rowRepl, Ymat]
  · simp only [rowRepl, Ymat, Matrix.of_apply, Sum.elim_inr]
    exact trunc_reindex_inr m H i c

/-- The frequency coefficient matrix `(a_k(R l))`. -/
def freqA (m : ℕ) (R : Fin m → ℕ) : Matrix (Fin m) (Fin m) ℂ :=
  Matrix.of fun k l => freqCoef m k (R l)

theorem norm_det_freqA (m : ℕ) (R : Fin m → ℕ) :
    ‖(freqA m R).det‖ = (∏ l, frequencyWeightReal (m / 2) (R l)) *
      ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) (fun j => ((R j : ℕ) : ℂ))‖ := by
  have h : freqA m R = Matrix.of fun k l =>
      ((((-1 : ℝ) ^ (m / 2 + 1)) * frequencyWeightReal (m / 2) (R l) : ℝ) : ℂ) *
        (Matrix.of fun i j => (((rowIndex m i : ℕ) : ℂ) + ((R j : ℕ) : ℂ))⁻¹ :
          Matrix (Fin m) (Fin m) ℂ) k l := by
    ext k l
    simp [freqA, freqCoef, cauchyKernel, rowIndex]
  rw [h, Matrix.det_mul_row, norm_mul]
  congr 1
  rw [norm_prod]
  apply Finset.prod_congr rfl
  intro l _
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_pow, abs_neg, abs_one, one_pow,
    one_mul, abs_of_nonneg]
  unfold frequencyWeightReal
  positivity

theorem norm_det_freqA_comp (m : ℕ) (R : Fin m → ℕ) (π : Equiv.Perm (Fin m)) :
    ‖(freqA m (R ∘ π)).det‖ = ‖(freqA m R).det‖ := by
  have : freqA m (R ∘ π) = (freqA m R).submatrix id π := by
    ext k l; simp [freqA]
  rw [this, Matrix.det_permute', norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign π) with h | h <;> simp [h]

theorem norm_det_Ymat_comp (m : ℕ) (R : Fin m → ℕ) (π : Equiv.Perm (Fin m)) :
    ‖(Ymat m (R ∘ π)).det‖ = ‖(Ymat m R).det‖ := by
  have : Ymat m (R ∘ π) =
      (Ymat m R).submatrix (Equiv.sumCongr π (Equiv.refl (Fin m))) id := by
    ext r c; rcases r with l | i <;> simp [Ymat]
  rw [this, Matrix.det_permute, norm_mul]
  rcases Int.units_eq_one_or (Equiv.Perm.sign (Equiv.sumCongr π (Equiv.refl (Fin m)))) with
    h | h <;> simp [h]

theorem det_freqA_eq_zero_of_not_injective (m : ℕ) (R : Fin m → ℕ)
    (h : ¬ Function.Injective R) : (freqA m R).det = 0 := by
  obtain ⟨l, l', hR, hne⟩ : ∃ l l', R l = R l' ∧ l ≠ l' := by
    by_contra hc
    apply h
    intro l l' e
    by_contra hne
    exact hc ⟨l, l', e, hne⟩
  exact Matrix.det_zero_of_column_eq hne (fun k => by simp [freqA, hR])

/-- Frequency Cauchy-Binet bound for the truncated determinant. -/
theorem norm_det_trunc_le (m H : ℕ) :
    ‖(truncMatrix m H).det‖ ≤
      ∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
        (∏ l, frequencyWeightReal (m / 2) (r.val l)) *
          ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
              (fun j => ((r.val j : ℕ) : ℂ))‖ * ‖(Ymat m r.val).det‖ := by
  classical
  have hdet : ((truncMatrix m H).submatrix (eρ m) (eρ m)).det = (truncMatrix m H).det :=
    Matrix.det_submatrix_equiv_self _ _
  have hDA := discrete_andreief (Ioc (m / 2) H) ((truncMatrix m H).submatrix (eρ m) (eρ m))
    (freqCoef m) (fun t c => freqVec m t c) (trunc_reindex_inl m H)
  simp only [rowRepl_trunc] at hDA
  set X' := (truncMatrix m H).submatrix (eρ m) (eρ m)
  set G : (Fin m → ℕ) → ℝ := fun f => ‖(freqA m f).det‖ * ‖(Ymat m f).det‖
  have hcount := sum_piFinset_le_factorial_mul_cutoff (m / 2) H m G
    (fun f => by positivity)
    (fun f π => by simp only [G, norm_det_freqA_comp, norm_det_Ymat_comp])
    (fun f hf => by simp only [G, det_freqA_eq_zero_of_not_injective m f hf, norm_zero,
      zero_mul])
  have hfac : (0 : ℝ) < (m.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos m
  have hmain : (m.factorial : ℝ) * ‖X'.det‖ ≤
      (m.factorial : ℝ) * ∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H, G r.val := by
    have h1 : (m.factorial : ℝ) * ‖X'.det‖ = ‖(m.factorial : ℂ) * X'.det‖ := by
      rw [norm_mul, Complex.norm_natCast]
    rw [h1, ← hDA]
    refine (norm_sum_le _ _).trans ?_
    refine le_trans ?_ hcount
    apply Finset.sum_le_sum
    intro f _
    rw [norm_mul]
    rfl
  have hle := le_of_mul_le_mul_left hmain hfac
  rw [hdet] at hle
  refine hle.trans (le_of_eq ?_)
  apply Finset.sum_congr rfl
  intro r _
  show ‖(freqA m r.val).det‖ * ‖(Ymat m r.val).det‖ = _
  rw [norm_det_freqA]

end

end Li2Lean.P0.Env
