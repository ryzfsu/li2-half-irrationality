/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorPoisson
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

/-! # Explicit Poisson logarithms for the exterior ellipse sweep -/

open MeasureTheory Complex
open scoped ComplexConjugate

namespace Li2Lean.P0

noncomputable section

/-- The reflected logarithm has no branch crossing on the closed unit disk. -/
theorem one_sub_conj_mul_mem_slitPlane {a ζ : ℂ} (ha : ‖a‖ < 1) (hζ : ‖ζ‖ ≤ 1) :
    1 - conj a * ζ ∈ Complex.slitPlane := by
  have hn : ‖conj a * ζ‖ < 1 := by
    rw [norm_mul, norm_conj]
    exact (mul_le_of_le_one_right (norm_nonneg a) hζ).trans_lt ha
  have hre := Complex.re_le_norm (conj a * ζ)
  left
  simp only [Complex.sub_re, Complex.one_re]
  linarith

/-- Unit-circle reflection identity for the logarithmic kernel. -/
theorem norm_one_sub_conj_mul_on_unit {a ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖1 - conj a * ζ‖ = ‖ζ - a‖ := by
  have hprod : ζ * conj ζ = 1 := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    norm_num
  calc
    ‖1 - conj a * ζ‖ = ‖ζ * conj (ζ - a)‖ := by
      congr 1
      rw [map_sub, mul_sub, hprod]
      ring
    _ = ‖ζ - a‖ := by rw [norm_mul, norm_conj, hζ, one_mul]

/-- Logarithmic Poisson formula with an interior pole, expressed without a complex branch. -/
theorem poisson_mean_log_norm_sub {a p : ℂ} (ha : ‖a‖ < 1) (hp : ‖p‖ < 1) :
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖1 - conj a * p‖ := by
  let f : ℂ → ℂ := fun ζ => Complex.log (1 - conj a * ζ)
  have hd : DifferentiableOn ℂ f (Metric.closedBall 0 1) := by
    have hd0 : Differentiable ℂ (fun ζ : ℂ => 1 - conj a * ζ) := by fun_prop
    apply hd0.differentiableOn.clog
    intro ζ hζ
    exact one_sub_conj_mul_mem_slitPlane ha (by simpa using hζ)
  have hf : DiffContOnCl ℂ f (Metric.ball 0 1) :=
    (hd.mono Metric.closure_ball_subset_closedBall).diffContOnCl
  have hpball : p ∈ Metric.ball (0 : ℂ) 1 := by simpa using hp
  have hnot : p ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using ne_of_lt hp
  have hpc : ContinuousOn (poissonKernel 0 p) (Metric.sphere 0 1) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    simpa only [abs_one] using
      Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hnot)
  have hfc : ContinuousOn f (Metric.sphere 0 1) :=
    hd.continuousOn.mono Metric.sphere_subset_closedBall
  have hi : CircleIntegrable (fun ζ => poissonKernel 0 p ζ • f ζ) 0 1 :=
    (hpc.smul hfc).circleIntegrable (by norm_num)
  have hP := hf.circleAverage_poissonKernel_smul hpball
  change Real.circleAverage (fun ζ => poissonKernel 0 p ζ • f ζ) 0 1 = f p at hP
  have hR := Complex.reCLM.circleAverage_comp_comm hi
  rw [hP] at hR
  have hmean : Real.circleAverage
      (fun ζ => poissonKernel 0 p ζ * Real.log ‖1 - conj a * ζ‖) 0 1 =
        Real.log ‖1 - conj a * p‖ := by
    simpa only [Function.comp_def, hP, f, Complex.reCLM_apply,
      Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero, Complex.log_re] using hR
  calc
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 =
        Real.circleAverage
          (fun ζ => poissonKernel 0 p ζ * Real.log ‖1 - conj a * ζ‖) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hζ
      dsimp only
      rw [norm_one_sub_conj_mul_on_unit hζ']
    _ = _ := hmean

/-- Weighted logarithms are circle integrable, including boundary poles. -/
theorem poisson_log_circleIntegrable {a p : ℂ} (hp : ‖p‖ < 1) :
    CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 := by
  have hlog : CircleIntegrable (fun ζ : ℂ => Real.log ‖ζ - a‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by fun_prop)
  have hnot : p ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using ne_of_lt hp
  have hpc : ContinuousOn (poissonKernel 0 p) (Metric.sphere 0 |(1 : ℝ)|) := by
    rw [poissonKernel_eq_re_herglotzRieszKernel]
    exact Complex.continuous_re.comp_continuousOn
      (continuousOn_herglotzRieszKernel_sphere hnot)
  have hi := hlog.continuousOn_smul hpc
  change CircleIntegrable (fun ζ => poissonKernel 0 p ζ • Real.log ‖ζ - a‖) 0 1 at hi
  simpa only [smul_eq_mul] using hi

/-- Interior-root contribution to the actual exterior Poisson average. -/
theorem exterior_poisson_log_of_root_inside {a w : ℂ} (ha : ‖a‖ < 1) (hw : 1 < ‖w‖) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖w - a‖ - Real.log ‖w‖ := by
  have hp : ‖exteriorPoissonParameter w‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball hw
  rw [poisson_mean_log_norm_sub ha hp]
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hwa : w - a ≠ 0 := by
    intro h
    have heq := sub_eq_zero.mp h
    rw [heq] at hw
    linarith
  have heq : 1 - conj a * exteriorPoissonParameter w = conj ((w - a) / w) := by
    simp only [exteriorPoissonParameter, map_div₀, map_sub]
    have hc0 : conj w ≠ 0 := by simpa using hw0
    field_simp [hc0]
  rw [heq, Complex.norm_conj, norm_div,
    Real.log_div (norm_ne_zero_iff.mpr hwa) (norm_ne_zero_iff.mpr hw0)]

/-- Factoring out a nonzero source separates its logarithmic scale. -/
theorem log_norm_sub_factor_source {a ζ : ℂ} (ha : a ≠ 0) (hζ : ζ ≠ a) :
    Real.log ‖ζ - a‖ = Real.log ‖a‖ + Real.log ‖1 - ζ / a‖ := by
  have hn : 1 - ζ / a ≠ 0 := by
    intro h
    apply hζ
    have hdiv : ζ / a = 1 := by linear_combination -h
    exact (div_eq_one_iff_eq ha).mp hdiv
  have heq : ζ - a = -a * (1 - ζ / a) := by field_simp [ha] <;> ring
  rw [heq, norm_mul, norm_neg, Real.log_mul (norm_ne_zero_iff.mpr ha) (norm_ne_zero_iff.mpr hn)]

/-- Poisson averaging fixes logarithmic poles outside the closed unit disk. -/
theorem poisson_mean_log_norm_sub_outside {a p : ℂ} (ha : 1 < ‖a‖) (hp : ‖p‖ < 1) :
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖p - a‖ := by
  let b := (conj a)⁻¹
  have hb : ‖b‖ < 1 := by
    dsimp [b]
    rw [norm_inv, norm_conj]
    exact inv_lt_one_of_one_lt₀ ha
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  have hpa : p ≠ a := by intro h; rw [h] at hp; linarith
  have hPint : CircleIntegrable (poissonKernel 0 p) 0 1 :=
    (poissonKernel_unit_continuous hp).circleIntegrable (by norm_num)
  have hconst : CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log ‖a‖) 0 1 := by
    have h := hPint.const_smul (a := Real.log ‖a‖)
    change CircleIntegrable (fun ζ => Real.log ‖a‖ • poissonKernel 0 p ζ) 0 1 at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hlog := poisson_log_circleIntegrable (a := b) hp
  have hconstmean : Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖a‖) 0 1 =
      Real.log ‖a‖ := by
    have h := Real.circleAverage_fun_smul (a := Real.log ‖a‖)
      (f := poissonKernel 0 p) (c := (0 : ℂ)) (R := 1)
    simpa only [smul_eq_mul, mul_comm, poissonKernel_unit_mass hp, one_mul] using h
  have hreflect (ζ : ℂ) : 1 - conj b * ζ = 1 - ζ / a := by simp [b, div_eq_mul_inv, mul_comm]
  calc
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 =
        Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖a‖ +
          poissonKernel 0 p ζ * Real.log ‖ζ - b‖) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hζ
      have hζa : ζ ≠ a := by intro h; rw [h] at hζ'; linarith
      dsimp only
      rw [log_norm_sub_factor_source ha0 hζa, ← hreflect ζ, norm_one_sub_conj_mul_on_unit hζ']
      ring
    _ = Real.log ‖a‖ + Real.log ‖1 - conj b * p‖ := by
      rw [Real.circleAverage_fun_add hconst hlog, hconstmean, poisson_mean_log_norm_sub hb hp]
    _ = Real.log ‖p - a‖ := by
      rw [hreflect p, log_norm_sub_factor_source ha0 hpa]

end
end Li2Lean.P0
