/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorPotential
import Mathlib.Analysis.Complex.JensenFormula

open MeasureTheory Filter
open scoped Topology

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- Exponential covering of the exact Joukowski annulus by the upper half-plane. -/
def annulusCover (ζ : ℂ) : ℂ :=
  Complex.exp ((((annulusWidth / Real.pi : ℝ) : ℂ) * Complex.I) * Complex.log ζ)

/-- The bounded analytic covering of the original ellipse interior. -/
def halfPlaneCover (ζ : ℂ) : ℂ := joukowski (annulusCover ζ)

/-- The disk-to-half-plane map centered at `a + i b`; its real boundary
value at angle `t` is `a - b*cot(t/2)`. -/
def diskToHalfPlane (a b : ℝ) (u : ℂ) : ℂ :=
  (a : ℂ) + Complex.I * (b : ℂ) * (1 + u) / (1 - u)

/-- Analytic disk lift of the actual Cauchy sweep. -/
def interiorDiskMap (z u : ℂ) : ℂ :=
  halfPlaneCover (diskToHalfPlane (stripLocation z) (stripScale z : ℝ) u)

theorem arg_pos_of_im_pos {ζ : ℂ} (hζ : 0 < ζ.im) : 0 < ζ.arg := by
  have hnonneg := Complex.arg_nonneg_iff.mpr hζ.le
  have hne : ζ.arg ≠ 0 := by
    intro h
    exact hζ.ne' (Complex.arg_eq_zero_iff.mp h).2
  exact lt_of_le_of_ne hnonneg hne.symm

theorem norm_annulusCover (ζ : ℂ) :
    ‖annulusCover ζ‖ = Real.exp (-(annulusWidth / Real.pi) * ζ.arg) := by
  simp [annulusCover, Complex.norm_exp, Complex.mul_re, Complex.mul_im, Complex.log_im]

theorem annulusCover_ne_zero (ζ : ℂ) : annulusCover ζ ≠ 0 := Complex.exp_ne_zero _

/-- Every upper-half-plane point reaches the full original annulus. -/
theorem annulusCover_mem_annulus {ζ : ℂ} (hζ : 0 < ζ.im) :
    annulusRatio < ‖annulusCover ζ‖ ∧ ‖annulusCover ζ‖ < 1 := by
  have harg := arg_pos_of_im_pos hζ
  have hargπ : ζ.arg < Real.pi := Complex.arg_lt_pi_iff.mpr (Or.inr hζ.ne')
  have hquot : 0 < annulusWidth / Real.pi := div_pos annulusWidth_pos Real.pi_pos
  have hm : annulusWidth / Real.pi * ζ.arg < annulusWidth := by
    have h := mul_lt_mul_of_pos_left hargπ hquot
    simpa only [div_mul_cancel₀ _ Real.pi_ne_zero] using h
  have hρ : Real.exp (-annulusWidth) = annulusRatio := by
    simp only [annulusWidth, neg_neg, Real.exp_log annulusRatio_pos]
  rw [norm_annulusCover]
  constructor
  · rw [← hρ]
    apply Real.exp_lt_exp.mpr
    linarith
  · apply Real.exp_lt_one_iff.mpr
    simpa only [neg_mul] using neg_neg_of_pos (mul_pos hquot harg)

/-- The cover uses the actual defining function, with no deleted focal set. -/
theorem halfPlaneCover_mem_interior {ζ : ℂ} (hζ : 0 < ζ.im) :
    halfPlaneCover ζ ∈ ellipseInterior :=
  (joukowski_mem_interior_iff _ (annulusCover_ne_zero ζ)).mpr
    (annulusCover_mem_annulus hζ)

/-- Exact imaginary-coordinate formula for the centered Cayley map. -/
theorem diskToHalfPlane_im (a b : ℝ) (u : ℂ) :
    (diskToHalfPlane a b u).im = b * (1 - ‖u‖ ^ 2) / ‖1 - u‖ ^ 2 := by
  simp only [diskToHalfPlane, Complex.add_im, Complex.ofReal_im, zero_add,
    Complex.div_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
    Complex.ofReal_re, zero_mul, one_mul, mul_zero, sub_zero, zero_add,
    Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    Complex.sub_re, Complex.sub_im, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring

theorem diskToHalfPlane_im_pos {a b : ℝ} (hb : 0 < b) {u : ℂ} (hu : ‖u‖ < 1) :
    0 < (diskToHalfPlane a b u).im := by
  have hden : 1 - u ≠ 0 := by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    simpa only [hu1, norm_one, lt_self_iff_false] using hu
  rw [diskToHalfPlane_im]
  apply div_pos
  · exact mul_pos hb (by nlinarith [norm_nonneg u])
  · exact sq_pos_of_pos (norm_pos_iff.mpr hden)

theorem interiorDiskMap_mem_interior {z u : ℂ} (hz : z ∈ ellipseInterior)
    (hu : ‖u‖ < 1) : interiorDiskMap z u ∈ ellipseInterior := by
  apply halfPlaneCover_mem_interior
  exact diskToHalfPlane_im_pos (by exact_mod_cast stripScale_pos hz) hu

/-- Analyticity on the entire upper half-plane; no inverse derivative of F is used. -/
theorem analyticAt_halfPlaneCover {ζ : ℂ} (hζ : 0 < ζ.im) :
    AnalyticAt ℂ halfPlaneCover ζ := by
  have hs : ζ ∈ Complex.slitPlane := Or.inr hζ.ne'
  have ha : AnalyticAt ℂ annulusCover ζ := by
    unfold annulusCover
    exact ((analyticAt_const.mul (analyticAt_clog hs))).cexp
  unfold halfPlaneCover joukowski
  exact (analyticAt_const.add (analyticAt_const.mul ha)).add
    (analyticAt_const.mul (ha.inv (annulusCover_ne_zero ζ)))

theorem analyticAt_diskToHalfPlane (a b : ℝ) {u : ℂ} (hu : ‖u‖ < 1) :
    AnalyticAt ℂ (diskToHalfPlane a b) u := by
  have hden : (1 : ℂ) - u ≠ 0 := by
    intro h
    have hu1 : u = 1 := (sub_eq_zero.mp h).symm
    simpa only [hu1, norm_one, lt_self_iff_false] using hu
  unfold diskToHalfPlane
  fun_prop

/-- The same actual Cauchy-sweep lift is analytic at every point of the disk. -/
theorem analyticOnNhd_interiorDiskMap {z : ℂ} (hz : z ∈ ellipseInterior) :
    AnalyticOnNhd ℂ (interiorDiskMap z) (Metric.ball 0 1) := by
  intro u hu
  have hu' : ‖u‖ < 1 := by simpa only [Metric.mem_ball, dist_zero_right] using hu
  exact (analyticAt_halfPlaneCover
    (diskToHalfPlane_im_pos (a := stripLocation z)
      (by exact_mod_cast stripScale_pos hz) hu')).comp
    (analyticAt_diskToHalfPlane _ _ hu')

/-- The upper-half-plane Cauchy parameter is exactly the exponential strip point. -/
theorem stripPoint_eq_exp {z : ℂ} (hz : z ∈ ellipseInterior) :
    (stripLocation z : ℂ) + Complex.I * ((stripScale z : ℝ) : ℂ) =
      Complex.exp (((Real.pi * (interiorPreimage z).arg / annulusWidth : ℝ) : ℂ) +
        Complex.I * (stripAngle z : ℂ)) := by
  have hs : 0 ≤ Real.exp (Real.pi * (interiorPreimage z).arg / annulusWidth) *
      Real.sin (stripAngle z) :=
    (mul_pos (Real.exp_pos _) (Real.sin_pos_of_pos_of_lt_pi
      (stripAngle_pos hz) (stripAngle_lt_pi hz))).le
  rw [Complex.exp_add]
  rw [show Complex.I * (stripAngle z : ℂ) = (stripAngle z : ℂ) * Complex.I by ring,
    Complex.exp_ofReal_mul_I]
  simp only [stripLocation, stripScale, Real.coe_toNNReal _ hs, Complex.ofReal_mul,
    Complex.ofReal_exp]
  ring

/-- The disk lift is centered at the original source point, even on the focal line. -/
theorem interiorDiskMap_zero {z : ℂ} (hz : z ∈ ellipseInterior) :
    interiorDiskMap z 0 = z := by
  have hπ : Real.pi ≠ 0 := Real.pi_ne_zero
  have hL : annulusWidth ≠ 0 := annulusWidth_pos.ne'
  have him :
      ((((Real.pi * (interiorPreimage z).arg / annulusWidth : ℝ) : ℂ) +
        Complex.I * (stripAngle z : ℂ))).im = stripAngle z := by simp
  unfold interiorDiskMap diskToHalfPlane
  simp only [add_zero, sub_zero, div_one, mul_one]
  rw [stripPoint_eq_exp hz]
  unfold halfPlaneCover annulusCover
  rw [Complex.log_exp (by rw [him]; linarith [stripAngle_pos hz, Real.pi_pos])
    (by rw [him]; exact (stripAngle_lt_pi hz).le)]
  have hexponent :
      (((annulusWidth / Real.pi : ℝ) : ℂ) * Complex.I) *
        (((Real.pi * (interiorPreimage z).arg / annulusWidth : ℝ) : ℂ) +
          Complex.I * (stripAngle z : ℂ)) = Complex.log (interiorPreimage z) := by
    unfold stripAngle preimageDepth
    rw [Complex.log]
    push_cast
    field_simp [show (annulusWidth : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hL,
      show (Real.pi : ℂ) ≠ 0 from Complex.ofReal_ne_zero.mpr hπ]
    linear_combination -((Real.log ‖interiorPreimage z‖ : ℝ) : ℂ) * Complex.I_sq
  rw [hexponent, Complex.exp_log (interiorPreimage_ne_zero z), joukowski_interiorPreimage]

/-- The actual ellipse interior is bounded by its major-axis disk. -/
theorem norm_sub_center_lt_semiMajor {z : ℂ} (hz : z ∈ ellipseInterior) :
    ‖z - (center : ℂ)‖ < semiMajor := by
  have hA : 0 < semiMajor := by norm_num [semiMajor]
  have hB : 0 < semiMinor := by norm_num [semiMinor]
  have hAB : semiMinor ^ 2 ≤ semiMajor ^ 2 := by norm_num [semiMinor, semiMajor]
  change 0 < 1 - ((z.re - center) / semiMajor) ^ 2 - (z.im / semiMinor) ^ 2 at hz
  have hdiv : z.im ^ 2 / semiMajor ^ 2 ≤ z.im ^ 2 / semiMinor ^ 2 :=
    div_le_div_of_nonneg_left (sq_nonneg _) (sq_pos_of_pos hB) hAB
  have hs : ((z.re - center) ^ 2 + z.im ^ 2) / semiMajor ^ 2 < 1 := by
    rw [add_div]
    simp only [div_pow] at hz
    linarith
  have hs' := (div_lt_one (sq_pos_of_pos hA)).mp hs
  have hn : ‖z - (center : ℂ)‖ ^ 2 = (z.re - center) ^ 2 + z.im ^ 2 := by
    rw [← Complex.normSq_eq_norm_sq]
    simp [Complex.normSq_apply, pow_two]
  nlinarith [norm_nonneg (z - (center : ℂ))]

/-- Uniform bound supplying the positive-end control in reverse Fatou. -/
theorem interiorDiskMap_norm_sub_le {z u x : ℂ} (hz : z ∈ ellipseInterior)
    (hu : ‖u‖ < 1) : ‖interiorDiskMap z u - x‖ ≤ semiMajor + ‖(center : ℂ) - x‖ := by
  calc
    ‖interiorDiskMap z u - x‖ =
        ‖(interiorDiskMap z u - (center : ℂ)) + ((center : ℂ) - x)‖ := by congr 1; ring
    _ ≤ ‖interiorDiskMap z u - (center : ℂ)‖ + ‖(center : ℂ) - x‖ := norm_add_le _ _
    _ ≤ semiMajor + ‖(center : ℂ) - x‖ :=
      by linarith [norm_sub_center_lt_semiMajor (interiorDiskMap_mem_interior hz hu)]

end
end Li2Lean.P0.TubeInterior
