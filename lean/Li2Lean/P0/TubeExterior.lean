/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube

/-!
# Exterior estimates for the literal v10 ellipse

This file proves the elementary exterior geometry used in `sec-tube.tex`.
All constants and geometric objects are those of `P0.Tube`.
-/

open MeasureTheory
open scoped ComplexConjugate

namespace Li2Lean.P0

noncomputable section

/-- The lower semiaxis is strictly positive. -/
theorem semiMinor_pos : 0 < semiMinor := by norm_num [semiMinor]

/-- The Joukowski coefficients are positive real numbers. -/
theorem ellipseC_norm : ‖ellipseC‖ = (semiMajor + semiMinor) / 2 := by
  norm_num [ellipseC, semiMajor, semiMinor]

theorem ellipseD_norm : ‖ellipseD‖ = (semiMajor - semiMinor) / 2 := by
  norm_num [ellipseD, semiMajor, semiMinor]

/-- The exact difference of coefficient norms is the lower semiaxis B. -/
theorem ellipseC_norm_sub_ellipseD_norm : ‖ellipseC‖ - ‖ellipseD‖ = semiMinor := by
  rw [ellipseC_norm, ellipseD_norm]
  ring

/-- The tail factor in the Joukowski factorization is uniformly at least B. -/
theorem joukowski_tail_norm_lower {w v : ℂ} (hw : 1 ≤ ‖w‖) (hv : 1 ≤ ‖v‖) :
    semiMinor ≤ ‖ellipseC - ellipseD * (w * v)⁻¹‖ := by
  have hp : 1 ≤ ‖w * v‖ := by
    rw [norm_mul]
    nlinarith [norm_nonneg w, norm_nonneg v]
  have hi : ‖(w * v)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact inv_le_one_of_one_le₀ hp
  have htail : ‖ellipseD * (w * v)⁻¹‖ ≤ ‖ellipseD‖ := by
    rw [norm_mul]
    exact mul_le_of_le_one_right (norm_nonneg _) hi
  have hrev := norm_sub_norm_le ellipseC (ellipseD * (w * v)⁻¹)
  rw [← ellipseC_norm_sub_ellipseD_norm]
  linarith

/-- The v10 Joukowski map expands exterior distances by at least B. -/
theorem joukowski_exterior_distance {w v : ℂ} (hw : 1 ≤ ‖w‖) (hv : 1 ≤ ‖v‖) :
    semiMinor * ‖w - v‖ ≤ ‖joukowski w - joukowski v‖ := by
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hv0 : v ≠ 0 := by intro h; norm_num [h] at hv
  rw [joukowski_factorization w v hw0 hv0, norm_mul]
  simpa [mul_comm] using mul_le_mul_of_nonneg_left (joukowski_tail_norm_lower hw hv)
    (norm_nonneg (w - v))

/-- Eq. `tube-e`, geometric step: distance to Gamma controls the exterior radius. -/
theorem joukowski_exterior_infDist_lower {w : ℂ} (hw : 1 ≤ ‖w‖) :
    semiMinor * (‖w‖ - 1) ≤ Metric.infDist (joukowski w) Gamma := by
  apply (Metric.le_infDist (Set.range_nonempty gammaPoint)).2
  rintro z ⟨u, rfl⟩
  let v := Complex.exp (Complex.I * (u : ℂ))
  have hv : ‖v‖ = 1 := by simp [v, Complex.norm_exp]
  have hdist := joukowski_exterior_distance hw (le_of_eq hv.symm)
  have hrev : ‖w‖ - 1 ≤ ‖w - v‖ := by simpa [hv] using norm_sub_norm_le w v
  calc
    semiMinor * (‖w‖ - 1) ≤ semiMinor * ‖w - v‖ :=
      mul_le_mul_of_nonneg_left hrev semiMinor_pos.le
    _ ≤ ‖joukowski w - joukowski v‖ := hdist
    _ = dist (joukowski w) (gammaPoint u) := by
      rw [dist_eq_norm, joukowski_unit_circle_eq_gammaPoint]

/-- Eq. `tube-e` for every exterior preimage in the literal closed tube. -/
theorem joukowski_log_bound_of_mem_tube {δ : ℝ} {w : ℂ}
    (hw : 1 ≤ ‖w‖) (hz : joukowski w ∈ tube δ) :
    0 ≤ Real.log ‖w‖ ∧ Real.log ‖w‖ ≤ δ / semiMinor := by
  refine ⟨Real.log_nonneg hw, ?_⟩
  have hd : semiMinor * (‖w‖ - 1) ≤ δ :=
    (joukowski_exterior_infDist_lower hw).trans hz
  have hr : ‖w‖ - 1 ≤ δ / semiMinor :=
    (le_div_iff₀ semiMinor_pos).2 (by simpa [mul_comm] using hd)
  exact (Real.log_le_sub_one_of_pos (lt_of_lt_of_le zero_lt_one hw)).trans hr

/-- The inverse-law input alone discharges the distance field of the tube interface. -/
theorem exterior_distance_lower_bound_of_inverse (W : ℂ → ℂ)
    (hW : ∀ z, ellipseLevel z ≤ 0 → 1 ≤ ‖W z‖ ∧ joukowski (W z) = z)
    (z : ℂ) (hz : ellipseLevel z ≤ 0) :
    semiMinor * (‖W z‖ - 1) ≤ Metric.infDist z Gamma := by
  simpa [(hW z hz).2] using joukowski_exterior_infDist_lower (hW z hz).1

/-- The exact correction bound, including interior and boundary points. -/
theorem exteriorCorrection_bound_of_inverse (W : ℂ → ℂ)
    (hW : ∀ z, ellipseLevel z ≤ 0 → 1 ≤ ‖W z‖ ∧ joukowski (W z) = z)
    {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : z ∈ tube δ) :
    0 ≤ exteriorCorrection W z ∧ exteriorCorrection W z ≤ δ / semiMinor := by
  by_cases hi : 0 < ellipseLevel z
  · simp only [exteriorCorrection, hi, ↓reduceIte]
    exact ⟨le_rfl, div_nonneg hδ semiMinor_pos.le⟩
  · have hWz := hW z (le_of_not_gt hi)
    have ht : joukowski (W z) ∈ tube δ := by simpa [hWz.2] using hz
    simpa [exteriorCorrection, hi] using joukowski_log_bound_of_mem_tube hWz.1 ht

/-- The mean coordinate stated in `sec-tube.tex` for exterior harmonic measure. -/
def exteriorMeanCoordinate (w : ℂ) : ℂ :=
  (center : ℂ) + ellipseC * (conj w)⁻¹ + ellipseD * w⁻¹

/-- Exact algebraic cancellation in the mean-coordinate displacement. -/
theorem exteriorMeanCoordinate_sub (w : ℂ) :
    joukowski w - exteriorMeanCoordinate w = ellipseC * (w - (conj w)⁻¹) := by
  simp only [joukowski, exteriorMeanCoordinate]
  ring

/-- The reciprocal-conjugate displacement has the exact radial norm. -/
theorem norm_sub_conj_inv {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖w - (conj w)⁻¹‖ = ‖w‖ - ‖w‖⁻¹ := by
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hr : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
  have hi : (conj w)⁻¹ = w / (‖w‖ ^ 2 : ℝ) := by
    apply (eq_div_iff (by exact_mod_cast (pow_ne_zero 2 (ne_of_gt hr)))).2
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_eq_conj_mul_self]
    field_simp [hw0]
  have hf : w - (conj w)⁻¹ = ((1 - (‖w‖ ^ 2)⁻¹ : ℝ) : ℂ) * w := by
    rw [hi]
    push_cast
    field_simp
  have hsq : 1 ≤ ‖w‖ ^ 2 := by nlinarith
  have hnonneg : 0 ≤ 1 - (‖w‖ ^ 2)⁻¹ := by
    linarith [inv_le_one_of_one_le₀ hsq]
  rw [hf, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hnonneg]
  field_simp

/-- Literal exterior coordinate displacement bound in `sec-tube.tex`. -/
theorem exteriorMeanCoordinate_distance {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ‖joukowski w - exteriorMeanCoordinate w‖ ≤
      (semiMajor + semiMinor) * (‖w‖ - 1) := by
  rw [exteriorMeanCoordinate_sub, norm_mul, ellipseC_norm, norm_sub_conj_inv hw]
  have hr : 0 < ‖w‖ := lt_of_lt_of_le zero_lt_one hw
  have hrad : ‖w‖ - ‖w‖⁻¹ ≤ 2 * (‖w‖ - 1) := by
    have he : ‖w‖ * ‖w‖⁻¹ = 1 := mul_inv_cancel₀ (ne_of_gt hr)
    nlinarith [sq_nonneg (‖w‖ - 1)]
  have hc : 0 ≤ (semiMajor + semiMinor) / 2 := by norm_num [semiMajor, semiMinor]
  nlinarith [mul_nonneg hc (sub_nonneg.mpr hrad)]

/-- The coordinate change has the exact tube-scale cost used in the exterior field. -/
theorem exteriorMeanCoordinate_distance_of_mem_tube {δ : ℝ} {w : ℂ}
    (hw : 1 ≤ ‖w‖) (hz : joukowski w ∈ tube δ) :
    ‖joukowski w - exteriorMeanCoordinate w‖ ≤
      (semiMajor + semiMinor) * δ / semiMinor := by
  have hr : ‖w‖ - 1 ≤ δ / semiMinor :=
    (le_div_iff₀ semiMinor_pos).2 (by
      simpa [mul_comm] using (joukowski_exterior_infDist_lower hw).trans hz)
  have hc : 0 ≤ semiMajor + semiMinor := by norm_num [semiMajor, semiMinor]
  calc
    ‖joukowski w - exteriorMeanCoordinate w‖ ≤
        (semiMajor + semiMinor) * (‖w‖ - 1) := exteriorMeanCoordinate_distance hw
    _ ≤ (semiMajor + semiMinor) * (δ / semiMinor) :=
      mul_le_mul_of_nonneg_left hr hc
    _ = _ := by ring

/-- The exact disk Green-function sign identity from `sec-tube.tex`. -/
theorem exterior_green_norm_sq_identity (a b : ℂ) :
    ‖a * conj b - 1‖ ^ 2 - ‖a - b‖ ^ 2 =
      (‖a‖ ^ 2 - 1) * (‖b‖ ^ 2 - 1) := by
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply,
    Complex.sub_re, Complex.sub_im, Complex.mul_re, Complex.mul_im,
    Complex.conj_re, Complex.conj_im, Complex.one_re, Complex.one_im]
  ring

/-- The exterior disk Green function is nonnegative off the diagonal. -/
theorem exterior_disk_green_nonneg {a b : ℂ} (ha : 1 ≤ ‖a‖) (hb : 1 ≤ ‖b‖)
    (hab : a ≠ b) :
    0 ≤ Real.log ‖(a * conj b - 1) / (a - b)‖ := by
  have hprod : 0 ≤ (‖a‖ ^ 2 - 1) * (‖b‖ ^ 2 - 1) := by
    apply mul_nonneg <;> nlinarith
  have hnorm : ‖a - b‖ ≤ ‖a * conj b - 1‖ := by
    nlinarith [exterior_green_norm_sq_identity a b, norm_nonneg (a - b),
      norm_nonneg (a * conj b - 1)]
  apply Real.log_nonneg
  rw [norm_div]
  exact (one_le_div (norm_pos_iff.mpr (sub_ne_zero.mpr hab))).2 hnorm

/-- The exterior field coefficient keeps the literal v10 constants and its margin. -/
theorem exterior_field_coefficient_lt_three :
    (1 : ℝ) / 2 + (semiMajor + semiMinor) * Real.log 2 < 3 := by
  have hlog : Real.log 2 ≤ 1 := by
    convert Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2) using 1 <;> norm_num
  have hc : 0 ≤ semiMajor + semiMinor := by norm_num [semiMajor, semiMinor]
  have hm := mul_le_mul_of_nonneg_left hlog hc
  norm_num [semiMajor, semiMinor] at hm ⊢
  linarith

end
end Li2Lean.P0
