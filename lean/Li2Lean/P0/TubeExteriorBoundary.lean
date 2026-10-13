/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorMeasure
import Mathlib.MeasureTheory.Integral.DominatedConvergence

/-! # Boundary-source Poisson logarithms, including their singular parameter -/

open MeasureTheory Complex Filter
open scoped Topology ComplexConjugate

namespace Li2Lean.P0

noncomputable section

/-- Exact radial distance identity on the unit circle. -/
theorem unit_radial_norm_sq (ζ a : ℂ) (r : ℝ) (hζ : ‖ζ‖ = 1) (ha : ‖a‖ = 1) :
    ‖ζ - (r : ℂ) * a‖ ^ 2 = r * ‖ζ - a‖ ^ 2 + (r - 1) ^ 2 := by
  have hζsq : ζ.re ^ 2 + ζ.im ^ 2 = 1 := by
    calc
      ζ.re ^ 2 + ζ.im ^ 2 = ‖ζ‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      _ = 1 := by rw [hζ]; norm_num
  have hasq : a.re ^ 2 + a.im ^ 2 = 1 := by
    calc
      a.re ^ 2 + a.im ^ 2 = ‖a‖ ^ 2 := by rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]; ring
      _ = 1 := by rw [ha]; norm_num
  simp only [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, add_zero]
  linear_combination (1 - r) * hζsq + (r ^ 2 - r) * hasq

/-- An integrable logarithmic majorant for radial approach from outside the disk. -/
theorem unit_radial_log_abs_le {ζ a : ℂ} {r : ℝ} (hζ : ‖ζ‖ = 1) (ha : ‖a‖ = 1)
    (hr : 1 ≤ r) (hr₂ : r ≤ 2) (hζa : ζ ≠ a) :
    |Real.log ‖ζ - (r : ℂ) * a‖| ≤ |Real.log ‖ζ - a‖| + Real.log 3 := by
  have hlo : ‖ζ - a‖ ≤ ‖ζ - (r : ℂ) * a‖ := by
    have hmul := mul_nonneg (sub_nonneg.mpr hr) (sq_nonneg ‖ζ - a‖)
    nlinarith [unit_radial_norm_sq ζ a r hζ ha, sq_nonneg (r - 1),
      norm_nonneg (ζ - a), norm_nonneg (ζ - (r : ℂ) * a)]
  have hhi : ‖ζ - (r : ℂ) * a‖ ≤ 3 := by
    calc
      ‖ζ - (r : ℂ) * a‖ ≤ ‖ζ‖ + ‖(r : ℂ) * a‖ := norm_sub_le _ _
      _ = 1 + r := by rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ha, hζ, abs_of_nonneg (by linarith), mul_one]
      _ ≤ 3 := by linarith
  have hpos : 0 < ‖ζ - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hζa)
  have hloglo := Real.log_le_log hpos hlo
  have hloghi := Real.log_le_log (hpos.trans_le hlo) hhi
  have hthree : 0 ≤ Real.log 3 := Real.log_nonneg (by norm_num)
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log ‖ζ - a‖)],
    by linarith [abs_nonneg (Real.log ‖ζ - a‖)]⟩

/-- The singular angular fiber is null; no separation condition is placed on the source. -/
theorem ae_circleMap_ne (a : ℂ) (μ : Measure ℝ) [NullSingletonClass μ] :
    ∀ᵐ θ ∂μ, circleMap 0 1 θ ≠ a := by
  have hc : (circleMap 0 1 ⁻¹' {a}).Countable :=
    (Set.countable_singleton a).preimage_circleMap 0 (by norm_num : (1 : ℝ) ≠ 0)
  simpa only [Set.mem_preimage, Set.mem_singleton_iff] using hc.ae_notMem μ

/-- Exact logarithmic Poisson formula for a boundary pole. The single singular parameter is
handled by a dominated limit from exterior poles, using the full integrable boundary logarithm. -/
theorem poisson_mean_log_norm_sub_boundary {a p : ℂ} (ha : ‖a‖ = 1) (hp : ‖p‖ < 1) :
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖p - a‖ := by
  let μ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let r : ℕ → ℝ := fun n => 1 + 1 / ((n : ℝ) + 1)
  let K : ℝ → ℝ := fun θ => poissonKernel 0 p (circleMap 0 1 θ)
  let F : ℕ → ℝ → ℝ := fun n θ => K θ * Real.log ‖circleMap 0 1 θ - (r n : ℂ) * a‖
  let f : ℝ → ℝ := fun θ => K θ * Real.log ‖circleMap 0 1 θ - a‖
  let bound : ℝ → ℝ := fun θ => |f θ| + K θ * Real.log 3
  have hπ : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hr₁ (n : ℕ) : 1 < r n := by
    dsimp [r]
    have h : 0 < 1 / ((n : ℝ) + 1) := by positivity
    linarith
  have hr₂ (n : ℕ) : r n ≤ 2 := by
    have hn : (1 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith [Nat.cast_nonneg (α := ℝ) n]
    have h := one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hn
    dsimp [r]
    rw [one_div]
    norm_num at h
    linarith
  have hr : Tendsto r atTop (𝓝 (1 : ℝ)) := by
    simpa [r] using tendsto_const_nhds.add
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hrC : Tendsto (fun n => (r n : ℂ) * a) atTop (𝓝 a) := by
    simpa using ((Complex.continuous_ofReal.continuousAt.tendsto.comp hr).mul_const a)
  have hKi : Integrable K μ := by
    have hi := (poissonKernel_unit_continuous hp).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ).mp hi
  have hfi : Integrable f μ :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hπ).mp (poisson_log_circleIntegrable (a := a) hp)
  have hbound : Integrable bound μ := hfi.abs.add (hKi.mul_const _)
  have hK (θ : ℝ) : 0 ≤ K θ := poissonKernel_unit_nonneg hp (by simp)
  have hlim := tendsto_integral_of_dominated_convergence bound
    (F := F) (f := f)
    (fun n => (by dsimp [F, K]; unfold poissonKernel; fun_prop : Measurable (F n)).aestronglyMeasurable)
    hbound
    (fun n => by
      filter_upwards [ae_circleMap_ne a μ] with θ hθ
      have h := mul_le_mul_of_nonneg_left
        (unit_radial_log_abs_le (by simp) ha (hr₁ n).le (hr₂ n) hθ) (hK θ)
      simpa only [F, f, bound, Real.norm_eq_abs, abs_mul, abs_of_nonneg (hK θ), mul_add] using h)
    (by
      filter_upwards [ae_circleMap_ne a μ] with θ hθ
      have hd : Tendsto (fun n => circleMap 0 1 θ - (r n : ℂ) * a) atTop
          (𝓝 (circleMap 0 1 θ - a)) := tendsto_const_nhds.sub hrC
      have hl := (Real.continuousAt_log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hθ))).tendsto.comp hd.norm
      simpa only [F, f, Function.comp_apply] using hl.const_mul (K θ))
  have hmean : Tendsto
      (fun n => Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - (r n : ℂ) * a‖) 0 1)
      atTop (𝓝 (Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1)) := by
    simpa only [Real.circleAverage_def, intervalIntegral.integral_of_le hπ, smul_eq_mul,
      F, f, K, μ] using hlim.const_mul (2 * Real.pi)⁻¹
  have hformula (n : ℕ) :
      Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - (r n : ℂ) * a‖) 0 1 =
        Real.log ‖p - (r n : ℂ) * a‖ := by
    apply poisson_mean_log_norm_sub_outside _ hp
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, ha, mul_one,
      abs_of_nonneg (show 0 ≤ r n by linarith [hr₁ n])]
    exact hr₁ n
  simp_rw [hformula] at hmean
  have hpa : p ≠ a := by intro h; rw [h, ha] at hp; exact (lt_irrefl _ hp)
  have hright := (Real.continuousAt_log (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hpa))).tendsto.comp
    (tendsto_const_nhds.sub hrC).norm
  exact tendsto_nhds_unique hmean hright


/-- The disk formula is valid through its entire closed set of source parameters. -/
theorem poisson_mean_log_norm_sub_closed {a p : ℂ} (ha : ‖a‖ ≤ 1) (hp : ‖p‖ < 1) :
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖1 - conj a * p‖ := by
  rcases lt_or_eq_of_le ha with ha | ha
  · exact poisson_mean_log_norm_sub ha hp
  rw [poisson_mean_log_norm_sub_boundary ha hp]
  congr 1
  symm
  calc
    ‖1 - conj a * p‖ = ‖conj (1 - conj p * a)‖ := by
      congr 1
      simp only [map_sub, map_one, map_mul, conj_conj]
      ring
    _ = ‖1 - conj p * a‖ := norm_conj _
    _ = ‖a - p‖ := norm_one_sub_conj_mul_on_unit ha
    _ = ‖p - a‖ := norm_sub_rev _ _

/-- Exterior Poisson averaging treats roots on the closed unit disk exactly. -/
theorem exterior_poisson_log_of_root_closed {a w : ℂ} (ha : ‖a‖ ≤ 1) (hw : 1 < ‖w‖) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * Real.log ‖ζ - a‖) 0 1 =
      Real.log ‖w - a‖ - Real.log ‖w‖ := by
  have hp : ‖exteriorPoissonParameter w‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball hw
  rw [poisson_mean_log_norm_sub_closed ha hp]
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

open TubeInterior

/-- Exact exterior mean shift for every boundary source, including its singular angle. -/
theorem exterior_poisson_log_source_boundary_parameter {w a : ℂ}
    (hw : 1 < ‖w‖) (ha : ‖a‖ = 1) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
        Real.log ‖joukowski ζ - joukowski a‖) 0 1 =
      Real.log ‖joukowski w - joukowski a‖ - Real.log ‖w‖ := by
  let b := (annulusRatio : ℂ) / a
  let p := exteriorPoissonParameter w
  have ha0 : a ≠ 0 := by intro h; norm_num [h] at ha
  have hb : ‖b‖ < 1 := by
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos annulusRatio_pos, ha, div_one]
    exact annulusRatio_lt_one
  have hp : ‖p‖ < 1 := by simpa [p] using exteriorPoissonParameter_mem_ball hw
  have hPint : CircleIntegrable (poissonKernel 0 p) 0 1 :=
    (poissonKernel_unit_continuous hp).circleIntegrable (by norm_num)
  have hconst : CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log coeffC) 0 1 := by
    have h := hPint.const_smul (a := Real.log coeffC)
    change CircleIntegrable (fun ζ => Real.log coeffC • poissonKernel 0 p ζ) 0 1 at h
    simpa only [smul_eq_mul, mul_comm] using h
  have hinta := poisson_log_circleIntegrable (a := a) hp
  have hintb := poisson_log_circleIntegrable (a := b) hp
  have hconstmean : Real.circleAverage (fun ζ => poissonKernel 0 p ζ * Real.log coeffC) 0 1 =
      Real.log coeffC := by
    have h := Real.circleAverage_fun_smul (a := Real.log coeffC)
      (f := poissonKernel 0 p) (c := (0 : ℂ)) (R := 1)
    simpa only [smul_eq_mul, mul_comm, poissonKernel_unit_mass hp, one_mul] using h
  have hamean := exterior_poisson_log_of_root_closed ha.le hw
  have hbmean := exterior_poisson_log_of_root_inside hb hw
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hwx : joukowski w ≠ joukowski a := by
    intro h
    have hwa := joukowski_injective_exterior hw.le ha.ge h
    rw [hwa, ha] at hw
    exact (lt_irrefl _ hw)
  have hsource := log_norm_joukowski_sub_twoRoot w a hw0 ha0 hwx
  calc
    Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
          Real.log ‖joukowski ζ - joukowski a‖) 0 1 =
        Real.circleAverage (fun ζ =>
          (poissonKernel 0 p ζ * Real.log coeffC + poissonKernel 0 p ζ * Real.log ‖ζ - a‖) +
            poissonKernel 0 p ζ * Real.log ‖ζ - b‖) 0 1 := by
      simp only [Real.circleAverage_def]
      congr 1
      apply intervalIntegral.integral_congr_ae
      filter_upwards [ae_circleMap_ne a volume] with θ hθ
      intro _
      have hζ : ‖circleMap 0 1 θ‖ = 1 := by simp
      have hζ0 : circleMap 0 1 θ ≠ 0 := by intro h; norm_num [h] at hζ
      have hneq : joukowski (circleMap 0 1 θ) ≠ joukowski a := by
        intro h
        exact hθ (joukowski_injective_exterior hζ.ge ha.ge h)
      have h := log_norm_joukowski_sub_twoRoot (circleMap 0 1 θ) a hζ0 ha0 hneq
      rw [hζ, Real.log_one, sub_zero] at h
      dsimp only [p, b]
      rw [h]
      ring
    _ = Real.log coeffC + (Real.log ‖w - a‖ - Real.log ‖w‖) +
        (Real.log ‖w - b‖ - Real.log ‖w‖) := by
      have hsum := hconst.add hinta
      change CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log coeffC +
        poissonKernel 0 p ζ * Real.log ‖ζ - a‖) 0 1 at hsum
      rw [Real.circleAverage_fun_add hsum hintb,
        Real.circleAverage_fun_add hconst hinta, hconstmean, hamean, hbmean]
    _ = Real.log ‖joukowski w - joukowski a‖ - Real.log ‖w‖ := by
      rw [hsource]
      dsimp [b]
      ring

/-- Boundary sources require no exclusion, even at the singular parameter of the integral. -/
theorem exterior_poisson_log_source_boundary {w x : ℂ} (hw : 1 < ‖w‖) (hx : x ∈ Gamma) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
        Real.log ‖joukowski ζ - x‖) 0 1 =
      Real.log ‖joukowski w - x‖ - Real.log ‖w‖ := by
  rcases hx with ⟨θ, rfl⟩
  rw [← joukowski_circleMap_eq_gammaPoint θ]
  exact exterior_poisson_log_source_boundary_parameter hw (by simp)

/-- Exact boundary-source Green identity for the actual constructed exterior probability law. -/
theorem exteriorSweep_boundary_source {z x : ℂ} (hz : ellipseLevel z < 0) (hx : x ∈ Gamma) :
    (∫ y, realLogKernel y x ∂exteriorSweep z) =
      realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  have hw := ellipseExteriorInverse_norm_gt_one hz
  have hp : ‖exteriorPoissonParameter (ellipseExteriorInverse z)‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball hw
  rw [exteriorSweep, integral_ellipsePoissonMeasure hp _ (by unfold realLogKernel; fun_prop)]
  have h := Real.circleAverage_fun_smul (a := (-1 : ℝ))
    (f := fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
      Real.log ‖joukowski ζ - x‖) (c := (0 : ℂ)) (R := 1)
  have hneg :
      Real.circleAverage (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        realLogKernel (joukowski ζ) x) 0 1 =
      - Real.circleAverage (fun ζ => poissonKernel 0 (exteriorPoissonParameter (ellipseExteriorInverse z)) ζ *
        Real.log ‖joukowski ζ - x‖) 0 1 := by
    simpa only [realLogKernel, smul_eq_mul, neg_one_mul, mul_neg] using h
  rw [hneg, exterior_poisson_log_source_boundary hw hx, joukowski_ellipseExteriorInverse]
  rw [exteriorCorrection, ite_eq_right (not_lt_of_ge hz.le)]
  unfold realLogKernel
  ring

end
end Li2Lean.P0
