/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube
import Mathlib.Analysis.RCLike.Sqrt
import Mathlib.MeasureTheory.Function.SpecialFunctions.Basic

open MeasureTheory

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- The exact annulus ratio for the v10 ellipse, `sec-tube.tex`. -/
def annulusRatio : ℝ := (semiMajor - semiMinor) / (semiMajor + semiMinor)

/-- Real Joukowski coefficients for the literal v10 ellipse. -/
def coeffC : ℝ := (semiMajor + semiMinor) / 2

def coeffD : ℝ := (semiMajor - semiMinor) / 2

theorem coeffC_pos : 0 < coeffC := by norm_num [coeffC, semiMajor, semiMinor]

theorem coeffD_pos : 0 < coeffD := by norm_num [coeffD, semiMajor, semiMinor]

theorem annulusRatio_pos : 0 < annulusRatio := by
  norm_num [annulusRatio, semiMajor, semiMinor]

theorem annulusRatio_lt_one : annulusRatio < 1 := by
  norm_num [annulusRatio, semiMajor, semiMinor]

theorem coeffD_eq_ratio_mul_coeffC : coeffD = annulusRatio * coeffC := by
  norm_num [coeffD, annulusRatio, coeffC, semiMajor, semiMinor]

/-- The polynomial identity that places every interior Joukowski preimage
in the annulus `d/c < |w| < 1`; the ellipse and coefficients are the literal
v10 objects. It is valid for every nonzero preimage, including focal points. -/
theorem ellipseLevel_joukowski_factorization (w : ℂ) (hw : w ≠ 0) :
    Complex.normSq w ^ 2 * ellipseLevel (joukowski w) =
      (1 - Complex.normSq w) * (coeffC ^ 2 * Complex.normSq w - coeffD ^ 2) *
        (w.re ^ 2 / semiMajor ^ 2 + w.im ^ 2 / semiMinor ^ 2) := by
  have hn : Complex.normSq w ≠ 0 := by simpa using hw
  simp only [ellipseLevel, joukowski, ellipseC, ellipseD, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.mul_re,
    Complex.mul_im, Complex.inv_re, Complex.inv_im, zero_mul,
    sub_zero, zero_add, add_zero]
  dsimp [coeffC, coeffD, semiMajor, semiMinor]
  field_simp [hn]
  simp only [Complex.normSq_apply]
  ring

/-- The positive factor in the exact ellipse/annulus identity. -/
theorem ellipse_weight_pos {w : ℂ} (hw : w ≠ 0) :
    0 < w.re ^ 2 / semiMajor ^ 2 + w.im ^ 2 / semiMinor ^ 2 := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hA : 0 < semiMajor ^ 2 := by norm_num [semiMajor]
  have hB : 0 < semiMinor ^ 2 := by norm_num [semiMinor]
  have hre : 0 ≤ w.re ^ 2 := sq_nonneg _
  have him : 0 ≤ w.im ^ 2 := sq_nonneg _
  have hsum : 0 < w.re ^ 2 + w.im ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using hn
  rcases lt_or_eq_of_le hre with hr | hr
  · exact add_pos_of_pos_of_nonneg (div_pos hr hA) (div_nonneg him hB.le)
  · have hi : 0 < w.im ^ 2 := by linarith
    exact add_pos_of_nonneg_of_pos (div_nonneg hre hA.le) (div_pos hi hB)

/-- The exact Joukowski preimage annulus for the v10 ellipse. -/
theorem joukowski_mem_interior_iff (w : ℂ) (hw : w ≠ 0) :
    joukowski w ∈ ellipseInterior ↔ annulusRatio < ‖w‖ ∧ ‖w‖ < 1 := by
  have hn : 0 < Complex.normSq w := Complex.normSq_pos.mpr hw
  have hweight := ellipse_weight_pos hw
  have hfact := ellipseLevel_joukowski_factorization w hw
  have hsign : 0 < ellipseLevel (joukowski w) ↔
      0 < (1 - Complex.normSq w) *
        (coeffC ^ 2 * Complex.normSq w - coeffD ^ 2) := by
    rw [← mul_pos_iff_of_pos_left (sq_pos_of_pos hn), hfact,
      mul_pos_iff_of_pos_right hweight]
  change 0 < ellipseLevel (joukowski w) ↔ _
  rw [hsign, Complex.normSq_eq_norm_sq, coeffD_eq_ratio_mul_coeffC]
  have hc : 0 < coeffC ^ 2 := sq_pos_of_pos coeffC_pos
  have hr : 0 ≤ ‖w‖ := norm_nonneg _
  have hρ : 0 < annulusRatio := annulusRatio_pos
  have hρ1 : annulusRatio < 1 := annulusRatio_lt_one
  have hρsq : annulusRatio ^ 2 < 1 := by nlinarith
  have htail : coeffC ^ 2 * ‖w‖ ^ 2 - (annulusRatio * coeffC) ^ 2 =
      coeffC ^ 2 * (‖w‖ ^ 2 - annulusRatio ^ 2) := by ring
  rw [htail]
  constructor
  · intro h
    rcases mul_pos_iff.mp h with h | h
    · have hn1 : ‖w‖ < 1 := by nlinarith [h.1]
      have hnρ : annulusRatio < ‖w‖ := by
        have hd := (mul_pos_iff_of_pos_left hc).mp h.2
        nlinarith
      exact ⟨hnρ, hn1⟩
    · have hd : ‖w‖ ^ 2 - annulusRatio ^ 2 < 0 := by nlinarith [h.2]
      nlinarith [h.1]
  · rintro ⟨hlo, hhi⟩
    have hleft : 0 < 1 - ‖w‖ ^ 2 := by nlinarith
    have hright : 0 < ‖w‖ ^ 2 - annulusRatio ^ 2 := by nlinarith
    exact mul_pos hleft (mul_pos hc hright)

/-- A global measurable choice of a root of the v10 Joukowski quadratic.
The principal square root may jump on its slit; only measurability is used. -/
def interiorPreimage (z : ℂ) : ℂ :=
  ((z - (center : ℂ)) +
    Complex.sqrt ((z - (center : ℂ)) ^ 2 - 4 * ellipseC * ellipseD)) /
      (2 * ellipseC)

/-- Complex principal square root is Borel measurable, including its slit. -/
theorem measurable_complex_sqrt : Measurable Complex.sqrt := by
  have h : Complex.sqrt = fun z : ℂ =>
      (Real.sqrt ((‖z‖ + z.re) / 2) : ℂ) +
        (if 0 ≤ z.im then (1 : ℂ) else -1) *
          (Real.sqrt ((‖z‖ - z.re) / 2) : ℂ) * Complex.I := by
    funext z
    exact Complex.sqrt_eq_real_add_ite
  rw [h]
  have hi : Measurable (fun z : ℂ => if 0 ≤ z.im then (1 : ℂ) else -1) :=
    Measurable.ite (measurableSet_le measurable_const Complex.measurable_im)
      measurable_const measurable_const
  exact ((measurable_norm.add Complex.measurable_re).div_const 2).sqrt.complex_ofReal.add
    ((hi.mul (((measurable_norm.sub Complex.measurable_re).div_const 2).sqrt.complex_ofReal)).mul_const _)

/-- Measurability needed to push a finite admissible measure into the annulus. -/
theorem measurable_interiorPreimage : Measurable interiorPreimage := by
  unfold interiorPreimage
  exact ((measurable_id.sub measurable_const).add
    (measurable_complex_sqrt.comp
      (((measurable_id.sub measurable_const).pow_const 2).sub measurable_const))).div_const _

/-- The chosen root solves the literal quadratic associated to `joukowski`. -/
theorem interiorPreimage_quadratic (z : ℂ) :
    ellipseC * interiorPreimage z ^ 2 -
      (z - (center : ℂ)) * interiorPreimage z + ellipseD = 0 := by
  have hc : ellipseC ≠ 0 := by
    norm_num [ellipseC, semiMajor, semiMinor]
  have hs : Complex.sqrt ((z - (center : ℂ)) ^ 2 - 4 * ellipseC * ellipseD) ^ 2 =
      (z - (center : ℂ)) ^ 2 - 4 * ellipseC * ellipseD := by
    simpa only [Complex.sqrt] using
      Complex.cpow_ofNat_inv_pow ((z - (center : ℂ)) ^ 2 - 4 * ellipseC * ellipseD) 2
  unfold interiorPreimage
  generalize Complex.sqrt ((z - (center : ℂ)) ^ 2 - 4 * ellipseC * ellipseD) = r at *
  field_simp [hc]
  linear_combination hs

/-- The positive constant coefficient rules out the zero root everywhere. -/
theorem interiorPreimage_ne_zero (z : ℂ) : interiorPreimage z ≠ 0 := by
  intro h
  have hq := interiorPreimage_quadratic z
  rw [h] at hq
  have hd : ellipseD ≠ 0 := by norm_num [ellipseD, semiMajor, semiMinor]
  exact hd (by simpa using hq)

/-- The selected root is a right inverse for the actual v10 Joukowski map. -/
theorem joukowski_interiorPreimage (z : ℂ) : joukowski (interiorPreimage z) = z := by
  have hq := interiorPreimage_quadratic z
  have hw := interiorPreimage_ne_zero z
  unfold joukowski
  field_simp [hw]
  linear_combination hq

/-- Every original interior point has the measurable selected preimage in
the full open annulus. No exclusion of the focal segment is required. -/
theorem interiorPreimage_mem_annulus {z : ℂ} (hz : z ∈ ellipseInterior) :
    annulusRatio < ‖interiorPreimage z‖ ∧ ‖interiorPreimage z‖ < 1 := by
  apply (joukowski_mem_interior_iff _ (interiorPreimage_ne_zero z)).mp
  simpa only [joukowski_interiorPreimage] using hz

end
end Li2Lean.P0.TubeInterior
