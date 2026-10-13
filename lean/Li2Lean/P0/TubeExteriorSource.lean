/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorLogPoisson
import Li2Lean.P0.TubeExteriorInverse
import Li2Lean.P0.TubeInteriorFactorization

/-! # Exact exterior sweeping of interior logarithmic point sources -/

open MeasureTheory Complex

namespace Li2Lean.P0

noncomputable section

open TubeInterior

/-- The exterior preimage region cannot map to an interior ellipse point. -/
theorem joukowski_exterior_ne_interior {w x : ℂ} (hw : 1 ≤ ‖w‖)
    (hx : x ∈ ellipseInterior) : joukowski w ≠ x := by
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  intro h
  have hi : joukowski w ∈ ellipseInterior := by simpa [h] using hx
  exact (not_lt_of_ge hw) ((joukowski_mem_interior_iff w hw0).mp hi).2

/-- Every point-source boundary logarithm is integrable against the explicit Poisson density. -/
theorem exterior_poisson_source_circleIntegrable {p : ℂ} (hp : ‖p‖ < 1) (x : ℂ) :
    CircleIntegrable (fun ζ => poissonKernel 0 p ζ * Real.log ‖joukowski ζ - x‖) 0 1 := by
  have hlog : CircleIntegrable (fun ζ : ℂ => Real.log ‖joukowski ζ - x‖) 0 1 :=
    MeromorphicOn.circleIntegrable_log_norm (fun _ _ => by unfold joukowski; fun_prop)
  have hpc : ContinuousOn (poissonKernel 0 p) (Metric.sphere 0 |(1 : ℝ)|) := by
    simpa only [abs_one] using poissonKernel_unit_continuous hp
  have hi := hlog.continuousOn_smul hpc
  change CircleIntegrable (fun ζ => poissonKernel 0 p ζ • Real.log ‖joukowski ζ - x‖) 0 1 at hi
  simpa only [smul_eq_mul] using hi

/-- An interior source has the exact exterior mean shift `-log |w|` from `sec-tube.tex`. -/
theorem exterior_poisson_log_source_inside {w x : ℂ} (hw : 1 < ‖w‖)
    (hx : x ∈ ellipseInterior) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ *
        Real.log ‖joukowski ζ - x‖) 0 1 =
      Real.log ‖joukowski w - x‖ - Real.log ‖w‖ := by
  let a := interiorPreimage x
  let b := (annulusRatio : ℂ) / a
  let p := exteriorPoissonParameter w
  have ha0 : a ≠ 0 := interiorPreimage_ne_zero x
  have hax : joukowski a = x := joukowski_interiorPreimage x
  have ha : annulusRatio < ‖a‖ ∧ ‖a‖ < 1 := interiorPreimage_mem_annulus hx
  have hb : ‖b‖ < 1 := by
    dsimp [b]
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos annulusRatio_pos]
    exact (div_lt_one (norm_pos_iff.mpr ha0)).2 ha.1
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
  have hamean := exterior_poisson_log_of_root_inside ha.2 hw
  have hbmean := exterior_poisson_log_of_root_inside hb hw
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hwx : joukowski w ≠ joukowski a := by
    rw [hax]
    exact joukowski_exterior_ne_interior hw.le hx
  have hsource := log_norm_joukowski_sub_twoRoot w a hw0 ha0 hwx
  rw [hax] at hsource
  calc
    Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * Real.log ‖joukowski ζ - x‖) 0 1 =
        Real.circleAverage (fun ζ =>
          (poissonKernel 0 p ζ * Real.log coeffC + poissonKernel 0 p ζ * Real.log ‖ζ - a‖) +
            poissonKernel 0 p ζ * Real.log ‖ζ - b‖) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hζ
      have hζ0 : ζ ≠ 0 := by intro h; norm_num [h] at hζ'
      have hneq : joukowski ζ ≠ joukowski a := by
        rw [hax]
        exact joukowski_exterior_ne_interior hζ'.ge hx
      have h := log_norm_joukowski_sub_twoRoot ζ a hζ0 ha0 hneq
      rw [hax, hζ', Real.log_one, sub_zero] at h
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
    _ = Real.log ‖joukowski w - x‖ - Real.log ‖w‖ := by
      rw [hsource]
      dsimp [b]
      ring

/-- Exact one-sweep Green identity when the source lies inside the literal ellipse. -/
theorem exterior_poisson_point_green_inside {w x : ℂ} (hw : 1 < ‖w‖)
    (hx : x ∈ ellipseInterior) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * realLogKernel (joukowski ζ) x) 0 1 =
      realLogKernel (joukowski w) x + Real.log ‖w‖ := by
  have h := Real.circleAverage_fun_smul (a := (-1 : ℝ))
    (f := fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * Real.log ‖joukowski ζ - x‖)
    (c := (0 : ℂ)) (R := 1)
  calc
    Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * realLogKernel (joukowski ζ) x) 0 1 =
        - Real.circleAverage
          (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * Real.log ‖joukowski ζ - x‖) 0 1 := by
      simpa only [realLogKernel, smul_eq_mul, neg_one_mul, mul_neg] using h
    _ = _ := by
      rw [exterior_poisson_log_source_inside hw hx]
      simp only [realLogKernel]
      ring

/-- Literal v10 separation: every positive source in `[0,2]` has level greater than `1/5`. -/
theorem ellipse_positive_source_level (x : ℂ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (1 : ℝ) / 5 < ellipseLevel x := by
  have hxc : 0 ≤ 2 * center - x.re := by
    have hc : (2 : ℝ) < 2 * center := by norm_num [center]
    linarith [hx.2]
  have hsq : (x.re - center) ^ 2 ≤ center ^ 2 := by
    nlinarith [mul_nonneg hx.1 hxc]
  have hmargin : center ^ 2 < (4 : ℝ) / 5 * semiMajor ^ 2 := by
    norm_num [center, semiMajor]
  have hA : 0 < semiMajor ^ 2 := by norm_num [semiMajor]
  have hquot : ((x.re - center) / semiMajor) ^ 2 < (4 : ℝ) / 5 := by
    rw [div_pow]
    exact (div_lt_iff₀ hA).2 (hsq.trans_lt hmargin)
  simp only [ellipseLevel, hxim, zero_div, zero_pow (by decide : 2 ≠ 0), sub_zero]
  linarith

/-- Eq. `tube-green` is an equality for every actual positive source and exterior point. -/
theorem exterior_poisson_point_green_positive_source {w x : ℂ} (hw : 1 < ‖w‖)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * realLogKernel (joukowski ζ) x) 0 1 =
      realLogKernel (joukowski w) x + Real.log ‖w‖ := by
  apply exterior_poisson_point_green_inside hw
  change 0 < ellipseLevel x
  linarith [ellipse_positive_source_level x hx hxim]

end
end Li2Lean.P0
