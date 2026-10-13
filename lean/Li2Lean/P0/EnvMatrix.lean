/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvBank
import Li2Lean.P0.EnvDet

/-!
# From `G_m(β)` to frequency-truncated complex determinants

`GmBeta m` is the determinant of the complex `2m × 2m` matrix `[C; B - βA]` (evaluation of
the literal rational pencil `p0MatrixQ 2 m` at `T = β`).  Subtracting `log 2` times the
upper block from the lower block (a unipotent row operation) gives `[C; B - βA - log 2 · C]`,
whose lower block is, by the base-2 source bank `bank_hasSum`, the frequency moment
`(-1)^{g+1} Σ_{r>g} w_r/((i+r)(j+r))`.  Truncating the frequency sum at `H` gives matrices
`truncMatrix m H` whose determinants converge to `GmBeta m`; any uniform bound on them bounds
`‖GmBeta m‖` (paper v13 `p0-analytic.tex` ll. 61-93, "the absolute frequency sum converges, and
increasing finite truncations converge").
-/

open Finset Filter Topology

namespace Li2Lean.P0.Env

noncomputable section

/-- Paper row label `i ∈ I_m` of the matrix row `r` (both blocks use `I_m`). -/
def lab (m : ℕ) (r : Fin (2 * m)) : ℕ :=
  m / 4 + (if r.val < m then r.val else r.val - m)

/-- The complex P0 pencil matrix evaluated at `T = β`. -/
def Xbeta (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r c =>
  if r.val < m then ((p0CQ 2 (m / 2) (lab m r) c.val : ℚ) : ℂ)
  else ((p0BQ 2 (m / 2) (lab m r) c.val : ℚ) : ℂ) -
    ((li2InvValue 2 : ℝ) : ℂ) * ((p0AQ 2 (m / 2) (lab m r) c.val : ℚ) : ℂ)

theorem GmBeta_eq_det (m : ℕ) (h4 : 4 ∣ m) : GmBeta m = (Xbeta m).det := by
  unfold GmBeta p0CanonicalPolynomial
  rw [if_pos h4]
  let f := Polynomial.eval₂RingHom (algebraMap ℚ ℂ) ((li2InvValue (2 : ℤ) : ℝ) : ℂ)
  change f (Matrix.det (p0MatrixQ ((2 : ℤ) : ℚ) m)) = _
  rw [RingHom.map_det]
  congr 1
  ext r c
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, p0MatrixQ, Xbeta, lab, f]
  have h2 : ((2 : ℤ) : ℚ) = 2 := by norm_num
  rw [h2]
  split_ifs with hr
  · simp
  · simp [Polynomial.eval₂_sub, Polynomial.eval₂_mul, Polynomial.eval₂_X, Polynomial.eval₂_C]
    ring

/-- The lower block after the row operation, `B - βA - log 2 · C`. -/
def Xinf (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r c =>
  if r.val < m then ((p0CQ 2 (m / 2) (lab m r) c.val : ℚ) : ℂ)
  else ((((p0BQ 2 (m / 2) (lab m r) c.val : ℚ) : ℝ) -
    li2InvValue 2 * ((p0AQ 2 (m / 2) (lab m r) c.val : ℚ) : ℝ) -
    Real.log 2 * ((p0CQ 2 (m / 2) (lab m r) c.val : ℚ) : ℝ) : ℝ) : ℂ)

/-- The unipotent row operation `row_{m+k} += log 2 · row_k`. -/
def rowOp (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r s =>
  (if r = s then 1 else 0) + (if m ≤ r.val ∧ s.val = r.val - m then ((Real.log 2 : ℝ) : ℂ) else 0)

theorem rowOp_det (m : ℕ) (hm : 0 < m) : (rowOp m).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · apply Finset.prod_eq_one
    intro r _
    simp only [rowOp, if_true]
    rw [if_neg (by omega)]
    ring
  · intro r s hrs
    simp only [OrderDual.toDual_lt_toDual] at hrs
    simp only [rowOp]
    rw [if_neg (ne_of_lt hrs), if_neg]
    · ring
    · intro h
      have : s.val < r.val := by omega
      exact absurd hrs (not_lt.mpr (le_of_lt (Fin.lt_def.mpr this)))

theorem Xbeta_eq_rowOp_mul (m : ℕ) : Xbeta m = rowOp m * Xinf m := by
  ext r c
  simp only [Matrix.mul_apply, rowOp, add_mul, Finset.sum_add_distrib, ite_mul, one_mul,
    zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true]
  by_cases hr : r.val < m
  · have hz : (∑ x : Fin (2 * m), (if m ≤ r.val ∧ x.val = r.val - m then
        ((Real.log 2 : ℝ) : ℂ) * Xinf m x c else 0)) = 0 := by
      apply Finset.sum_eq_zero; intro x _; rw [if_neg (by omega)]
    rw [hz, add_zero]
    simp [Xbeta, Xinf, hr]
  · let r0 : Fin (2 * m) := ⟨r.val - m, by omega⟩
    have hsum : (∑ x : Fin (2 * m), (if m ≤ r.val ∧ x.val = r.val - m then
        ((Real.log 2 : ℝ) : ℂ) * Xinf m x c else 0)) = ((Real.log 2 : ℝ) : ℂ) * Xinf m r0 c := by
      rw [Finset.sum_eq_single r0]
      · rw [if_pos ⟨by omega, rfl⟩]
      · intro x _ hx
        rw [if_neg]
        intro h
        exact hx (Fin.ext (by simp [r0]; omega))
      · intro h; exact absurd (Finset.mem_univ r0) h
    rw [hsum]
    have hr0 : r0.val < m := by simp [r0]; omega
    have hlab : lab m r0 = lab m r := by
      simp only [lab, r0, if_pos hr0, if_neg hr]
    simp only [Xbeta, Xinf, if_neg hr, if_pos hr0, hlab]
    push_cast
    ring

theorem det_Xbeta_eq_det_Xinf (m : ℕ) (hm : 0 < m) : (Xbeta m).det = (Xinf m).det := by
  rw [Xbeta_eq_rowOp_mul, Matrix.det_mul, rowOp_det m hm, one_mul]

/-- Frequency-truncated version of `Xinf`, lower block
`(-1)^{g+1} Σ_{r ≤ H, r > g} w_r/((i+r)(j+r))`. -/
def truncMatrix (m H : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) ℂ := fun r c =>
  if r.val < m then ((p0CQ 2 (m / 2) (lab m r) c.val : ℚ) : ℂ)
  else ((((-1 : ℝ) ^ (m / 2 + 1)) * ∑ t ∈ range (H + 1),
    (if m / 2 < t then frequencyWeightReal (m / 2) t /
      (((lab m r : ℝ) + t) * ((c.val : ℝ) + t)) else 0) : ℝ) : ℂ)

theorem tendsto_truncMatrix (m : ℕ) :
    Tendsto (fun H => truncMatrix m H) atTop (𝓝 (Xinf m)) := by
  refine tendsto_pi_nhds.mpr fun r => tendsto_pi_nhds.mpr fun c => ?_
  by_cases hr : r.val < m
  · simp only [truncMatrix, Xinf, if_pos hr]
    exact tendsto_const_nhds
  · simp only [truncMatrix, Xinf, if_neg hr]
    apply (Complex.continuous_ofReal.tendsto _).comp
    have hb := (bank_hasSum (m / 2) (lab m r) c.val).tendsto_sum_nat
    have hb' := (hb.comp (tendsto_add_atTop_nat 1)).const_mul ((-1 : ℝ) ^ (m / 2 + 1))
    have hs : ((-1 : ℝ) ^ (m / 2 + 1)) * ((-1 : ℝ) ^ (m / 2 + 1)) = 1 := by
      rw [← pow_add, ← two_mul, pow_mul]; norm_num
    rw [← mul_assoc, hs, one_mul] at hb'
    exact hb'

/-- Any uniform bound on the truncated determinants bounds `‖G_m(β)‖`. -/
theorem norm_GmBeta_le_of_trunc (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (C : ℝ)
    (hb : ∀ H, ‖(truncMatrix m H).det‖ ≤ C) : ‖GmBeta m‖ ≤ C := by
  rw [GmBeta_eq_det m h4, det_Xbeta_eq_det_Xinf m hm]
  have ht : Tendsto (fun H => ‖(truncMatrix m H).det‖) atTop (𝓝 ‖(Xinf m).det‖) :=
    ((continuous_id.matrix_det.tendsto (Xinf m)).comp (tendsto_truncMatrix m)).norm
  exact le_of_tendsto' ht hb

end

end Li2Lean.P0.Env
