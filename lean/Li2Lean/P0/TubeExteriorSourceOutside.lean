/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorSource

/-! # Same-side exterior Green inequality for the literal ellipse -/

open MeasureTheory Complex
open scoped ComplexConjugate

namespace Li2Lean.P0

noncomputable section

open TubeInterior

/-- A strict exterior ellipse point has a strict exterior preimage. -/
theorem ellipseExteriorInverse_norm_gt_one {z : ℂ} (hz : ellipseLevel z < 0) :
    1 < ‖ellipseExteriorInverse z‖ := by
  have hge := ellipseExteriorInverse_norm_ge_one hz.le
  refine lt_of_le_of_ne hge ?_
  intro heq
  have hn : ‖ellipseExteriorInverse z‖ = 1 := heq.symm
  have hne : ellipseExteriorInverse z ≠ 0 := by intro h; norm_num [h] at hn
  have h := ellipseLevel_joukowski_factorization (ellipseExteriorInverse z) hne
  rw [joukowski_ellipseExteriorInverse, Complex.normSq_eq_norm_sq, hn] at h
  norm_num at h
  linarith

/-- Reciprocal disk parameter norm identity in the exterior Green function. -/
theorem exterior_poisson_parameter_source_norm {w a : ℂ} (hw : w ≠ 0) :
    ‖exteriorPoissonParameter w - a‖ * ‖w‖ = ‖w * conj a - 1‖ := by
  have hc : conj w ≠ 0 := by simpa using hw
  have heq : -(conj ((exteriorPoissonParameter w - a) * conj w)) = w * conj a - 1 := by
    simp only [exteriorPoissonParameter, map_mul, map_sub, map_inv₀, Complex.conj_conj]
    field_simp [hw]
    ring
  calc
    ‖exteriorPoissonParameter w - a‖ * ‖w‖ =
        ‖(exteriorPoissonParameter w - a) * conj w‖ := by rw [norm_mul, norm_conj]
    _ = ‖-(conj ((exteriorPoissonParameter w - a) * conj w))‖ := by rw [norm_neg, norm_conj]
    _ = _ := by rw [heq]

/-- Scalar logarithmic comparison carrying the exterior disk Green sign. -/
theorem exterior_poisson_root_log_compare {w a : ℂ} (hw : 1 < ‖w‖)
    (ha : 1 < ‖a‖) (hwa : w ≠ a) :
    Real.log ‖w - a‖ ≤ Real.log ‖exteriorPoissonParameter w - a‖ + Real.log ‖w‖ := by
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hpa : exteriorPoissonParameter w ≠ a := by
    have hp : ‖exteriorPoissonParameter w‖ < 1 := by simpa using exteriorPoissonParameter_mem_ball hw
    intro h
    rw [h] at hp
    linarith
  have hprod : 0 ≤ (‖w‖ ^ 2 - 1) * (‖a‖ ^ 2 - 1) := by
    apply mul_nonneg <;> nlinarith
  have hnorm : ‖w - a‖ ≤ ‖w * conj a - 1‖ := by
    nlinarith [exterior_green_norm_sq_identity w a, norm_nonneg (w - a), norm_nonneg (w * conj a - 1)]
  rw [← exterior_poisson_parameter_source_norm hw0] at hnorm
  have hlog := Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hwa)) hnorm
  rwa [Real.log_mul (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpa)) (norm_ne_zero_iff.mpr hw0)] at hlog

/-- Exact exterior-source Poisson mean before applying the disk Green sign. -/
theorem exterior_poisson_log_source_outside {w a : ℂ} (hw : 1 < ‖w‖) (ha : 1 < ‖a‖) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
        Real.log ‖joukowski ζ - joukowski a‖) 0 1 =
      Real.log coeffC + Real.log ‖exteriorPoissonParameter w - a‖ +
        Real.log ‖w - (annulusRatio : ℂ) / a‖ - Real.log ‖w‖ := by
  let b := (annulusRatio : ℂ) / a
  let p := exteriorPoissonParameter w
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  have hb : ‖b‖ < 1 := by
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos annulusRatio_pos]
    exact (div_lt_one (norm_pos_iff.mpr ha0)).2 (annulusRatio_lt_one.trans ha)
  have hp : ‖p‖ < 1 := by simpa [p] using exteriorPoissonParameter_mem_ball hw
  have hPint : CircleIntegrable (poissonKernel 0 p) 0 1 :=
    (poissonKernel_unit_continuous hp).circleIntegrable (by norm_num)
  have hconst : CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log coeffC) 0 1 := by
    have h := hPint.const_smul (a := Real.log coeffC)
    change CircleIntegrable (fun ζ => Real.log coeffC • poissonKernel 0 p ζ) 0 1 at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hinta := poisson_log_circleIntegrable (a := a) hp
  have hintb := poisson_log_circleIntegrable (a := b) hp
  have hsum := hconst.add hinta
  change CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log coeffC +
    poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 at hsum
  have hconstmean : Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log coeffC) 0 1 =
      Real.log coeffC := by
    have h := Real.circleAverage_fun_smul (a := Real.log coeffC)
      (f := poissonKernel 0 p) (c := (0 : ℂ)) (R := 1)
    simpa only [smul_eq_mul, mul_comm, poissonKernel_unit_mass hp, one_mul] using h
  calc
    Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
          Real.log ‖joukowski ζ - joukowski a‖) 0 1 =
        Real.circleAverage (fun ζ =>
          (poissonKernel 0 p ζ * Real.log coeffC + poissonKernel 0 p ζ * Real.log ‖ζ - a‖) +
            poissonKernel 0 p ζ * Real.log ‖ζ - b‖) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hζ
      have hζ0 : ζ ≠ 0 := by intro h; norm_num [h] at hζ'
      have hneq : joukowski ζ ≠ joukowski a := by
        intro h
        have heq := joukowski_injective_exterior hζ'.ge ha.le h
        rw [heq] at hζ'
        linarith
      have h := log_norm_joukowski_sub_twoRoot ζ a hζ0 ha0 hneq
      rw [hζ', Real.log_one, sub_zero] at h
      dsimp only [p, b]
      rw [h]
      ring
    _ = _ := by
      rw [Real.circleAverage_fun_add hsum hintb,
        Real.circleAverage_fun_add hconst hinta, hconstmean,
        poisson_mean_log_norm_sub_outside ha hp, exterior_poisson_log_of_root_inside hb hw]
      dsimp [b, p]
      ring

/-- Eq. `tube-green` for two strict exterior points, with no measure-class restriction. -/
theorem exterior_poisson_point_green_outside {w a : ℂ} (hw : 1 < ‖w‖) (ha : 1 < ‖a‖)
    (hwa : w ≠ a) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
        realLogKernel (joukowski ζ) (joukowski a)) 0 1 ≤
      realLogKernel (joukowski w) (joukowski a) + Real.log ‖w‖ := by
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  have hneq : joukowski w ≠ joukowski a := fun h =>
    hwa (joukowski_injective_exterior hw.le ha.le h)
  have hdecomp := log_norm_joukowski_sub_twoRoot w a hw0 ha0 hneq
  have hcompare := exterior_poisson_root_log_compare hw ha hwa
  have h := Real.circleAverage_fun_smul (a := (-1 : ℝ))
    (f := fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
      Real.log ‖joukowski ζ - joukowski a‖) (c := (0 : ℂ)) (R := 1)
  have hmean : Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
        realLogKernel (joukowski ζ) (joukowski a)) 0 1 =
      -(Real.log coeffC + Real.log ‖exteriorPoissonParameter w - a‖ +
        Real.log ‖w - (annulusRatio : ℂ) / a‖ - Real.log ‖w‖) := by
    calc
      _ = - Real.circleAverage
          (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
            Real.log ‖joukowski ζ - joukowski a‖) 0 1 := by
        simpa only [realLogKernel, smul_eq_mul, neg_one_mul, mul_neg] using h
      _ = _ := by rw [exterior_poisson_log_source_outside hw ha]
  rw [hmean, realLogKernel, hdecomp]
  linarith

/-- The same-side Green bound uses the actual chosen inverse at both ellipse points. -/
theorem ellipse_exterior_point_green {z x : ℂ} (hz : ellipseLevel z < 0)
    (hx : ellipseLevel x < 0) (hzx : z ≠ x) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        realLogKernel (joukowski ζ) x) 0 1 ≤
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  have hw := ellipseExteriorInverse_norm_gt_one hz
  have ha := ellipseExteriorInverse_norm_gt_one hx
  have hwa : ellipseExteriorInverse z ≠ ellipseExteriorInverse x := by
    intro h
    exact hzx (by rw [← joukowski_ellipseExteriorInverse z, h, joukowski_ellipseExteriorInverse])
  have h := exterior_poisson_point_green_outside hw ha hwa
  simpa only [joukowski_ellipseExteriorInverse, exteriorCorrection, not_lt_of_ge hz.le, ↓reduceIte] using h

/-- Every reflected frequency source lies strictly outside the literal ellipse. -/
theorem reflected_frequency_source_level_neg (x : ℂ) (hx : x.re ≤ -(1 : ℝ) / 2) :
    ellipseLevel x < 0 := by
  have hA : 0 < semiMajor := by norm_num [semiMajor]
  have hleft : x.re - center < -semiMajor := by
    norm_num [center, semiMajor] at *
    linarith
  have hquot : (x.re - center) / semiMajor < -1 := by
    apply (div_lt_iff₀ hA).2
    linarith
  dsimp [ellipseLevel]
  nlinarith [sq_nonneg (x.im / semiMinor)]

/-- Horizontal separation from the leftmost point of the original contour. -/
theorem ellipse_infDist_lower_by_real_part (x : ℂ) :
    center - semiMajor - x.re ≤ Metric.infDist x Gamma := by
  apply (Metric.le_infDist (Set.range_nonempty gammaPoint)).2
  rintro z ⟨u, rfl⟩
  have hreal : center - semiMajor ≤ (gammaPoint u).re := by
    simp only [gammaPoint, Complex.add_re, Complex.ofReal_re,
      Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im,
      zero_mul, one_mul, sub_zero, add_zero]
    have hA : 0 ≤ semiMajor := by norm_num [semiMajor]
    nlinarith [mul_nonneg hA (show 0 ≤ Real.cos u + 1 by linarith [Real.neg_one_le_cos u])]
  have hnorm := Complex.re_le_norm (gammaPoint u - x)
  simp only [Complex.sub_re] at hnorm
  rw [dist_eq_norm, norm_sub_rev]
  linarith

/-- The permitted tube is disjoint from the complete reflected frequency half-line. -/
theorem tube_ne_reflected_frequency_source {δ : ℝ} {z x : ℂ}
    (hδ : δ ≤ tubeRadiusMax) (hz : z ∈ tube δ) (hx : x.re ≤ -(1 : ℝ) / 2) : z ≠ x := by
  intro h
  subst z
  have hdist := (ellipse_infDist_lower_by_real_part x).trans hz
  have hgap : tubeRadiusMax < center - semiMajor + (1 : ℝ) / 2 := by
    norm_num [tubeRadiusMax, center, semiMajor]
  linarith

/-- Actual frequency-source application of the exterior point Green bound on the full half-line. -/
theorem ellipse_exterior_point_green_frequency {δ : ℝ} {z x : ℂ}
    (hδ : δ ≤ tubeRadiusMax) (hzt : z ∈ tube δ) (hz : ellipseLevel z < 0)
    (hx : x.re ≤ -(1 : ℝ) / 2) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        realLogKernel (joukowski ζ) x) 0 1 ≤
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z :=
  ellipse_exterior_point_green hz (reflected_frequency_source_level_neg x hx)
    (tube_ne_reflected_frequency_source hδ hzt hx)

/-- Actual positive-source application with the constructed ellipse inverse. -/
theorem ellipse_exterior_point_green_positive_source {z x : ℂ}
    (hz : ellipseLevel z < 0) (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        realLogKernel (joukowski ζ) x) 0 1 =
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  have h := exterior_poisson_point_green_positive_source (ellipseExteriorInverse_norm_gt_one hz) hx hxim
  simpa only [joukowski_ellipseExteriorInverse, exteriorCorrection, not_lt_of_ge hz.le, ↓reduceIte] using h

end
end Li2Lean.P0
