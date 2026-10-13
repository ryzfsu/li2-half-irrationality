/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube.Gap.PhiSegment

/-! # Pointwise field cost of the actual harmonic sweep

For `f = A₀ - φ` and every tube center `z ∈ T_δ` (`0 ≤ δ ≤ 1/64`),

    ∫ f dω_z ≤ f(z) + 288 δ / B,

where `ω_z = tubeSweep z` is the actual sweep (interior Cauchy law, exterior
Poisson law, Dirac mass on `Γ`).  This is the pointwise form of the v10 field
inequality in `sec-tube.tex`:

* positive sources of `A₀` (total mass 3, carried by `[0,2]`): each source gains
  at most `96 δ / B` at interior centers (`interiorSweep_log_gain_le_96`), and
  loses `e(z) ≥ 0` at exterior centers (`exteriorSweep_positive_source`);
  Fubini over the source segments is legitimate because `Γ` is separated from
  `[0,2]`;
* the linear part of `φ` keeps its mean at interior centers (barycenter of the
  Cauchy law) and moves by at most `(A+B) δ / B` at exterior centers (Poisson
  mean coordinate);
* the logarithmic segment of `φ` satisfies `∫ L dω_z ≥ L(z) - e(z)/2`
  (`phiSeg_sweep_ge`), with `e = 0` on the closed ellipse and `e ≤ δ / B` on
  the tube.

The exterior total is `≤ (ℓ (A+B) + 1/2) δ / B < 3 δ / B ≤ 288 δ / B`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ComplexConjugate

namespace Li2Lean.P0.TubeGap

noncomputable section

open TubeInterior TubeEnergy

/-- One source-segment potential of `A₀`. -/
def segPot (a b : ℝ) (y : ℂ) : ℝ := ∫ x in a..b, Real.log ‖y - (x : ℂ)‖

theorem A0_eq_segPot (z : ℂ) : A0 z = segPot (1 / 4) (5 / 4) z + segPot 0 2 z := rfl

theorem log_norm_sub_source_bound {y : ℂ} (hy : y ∈ Gamma) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    |Real.log ‖y - (x : ℂ)‖| ≤ |Real.log (751 / 5000)| + |Real.log 6| := by
  have hl := positive_source_norm_sub_ge (x := (x : ℂ)) (by simpa using hx) (by simp) hy
  have hy4 := TubeVariance.norm_le_four_of_mem_Gamma hy
  have hu : ‖y - (x : ℂ)‖ ≤ 6 := by
    refine (norm_sub_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    linarith [hx.2]
  have hp : (0 : ℝ) < 751 / 5000 := by norm_num
  have h1 := Real.log_le_log hp hl
  have h2 := Real.log_le_log (lt_of_lt_of_le hp hl) hu
  rw [abs_le]
  constructor <;> linarith [le_abs_self (Real.log 6), neg_abs_le (Real.log (751 / 5000)),
    abs_nonneg (Real.log 6), abs_nonneg (Real.log (751 / 5000))]

theorem integrable_log_norm_sub_prod (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ 2) :
    Integrable (fun p : ℂ × ℝ => Real.log ‖p.1 - (p.2 : ℂ)‖)
      (ω.prod (volume.restrict (Set.Ioc a b))) := by
  apply (integrable_const (|Real.log (751 / 5000)| + |Real.log 6|)).mono'
    (Real.measurable_log.comp
      (by fun_prop : Measurable fun p : ℂ × ℝ => ‖p.1 - (p.2 : ℂ)‖)).aestronglyMeasurable
  have a1 := (Measure.quasiMeasurePreserving_fst
    (μ := ω) (ν := volume.restrict (Set.Ioc a b))).ae hω
  have a2 := (Measure.quasiMeasurePreserving_snd
    (μ := ω) (ν := volume.restrict (Set.Ioc a b))).ae
      (ae_restrict_mem measurableSet_Ioc : ∀ᵐ x ∂volume.restrict (Set.Ioc a b), x ∈ Set.Ioc a b)
  filter_upwards [a1, a2] with p hp1 hp2
  rw [Real.norm_eq_abs]
  exact log_norm_sub_source_bound hp1 ⟨by linarith [hp2.1], by linarith [hp2.2]⟩

theorem segPot_eq_setIntegral {a b : ℝ} (hab : a ≤ b) :
    segPot a b = fun y : ℂ => ∫ x in Set.Ioc a b, Real.log ‖y - (x : ℂ)‖ := by
  funext y
  rw [segPot, intervalIntegral.integral_of_le hab]

theorem integrable_segPot (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    Integrable (segPot a b) ω := by
  rw [segPot_eq_setIntegral hab]
  exact (integrable_log_norm_sub_prod ω hω ha hb).integral_prod_left

theorem integral_segPot (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2) :
    (∫ y, segPot a b y ∂ω) = ∫ x in a..b, ∫ y, Real.log ‖y - (x : ℂ)‖ ∂ω := by
  rw [segPot_eq_setIntegral hab, intervalIntegral.integral_of_le hab]
  exact integral_integral_swap (integrable_log_norm_sub_prod ω hω ha hb)

/-- Sweep gap of one source segment from a pointwise bracket bound. -/
theorem segPot_sweep_gap (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ 2)
    (z : ℂ) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc a b,
      (∫ y, Real.log ‖y - (x : ℂ)‖ ∂ω) - Real.log ‖z - (x : ℂ)‖ ≤ C) :
    (∫ y, segPot a b y ∂ω) - segPot a b z ≤ (b - a) * C := by
  rw [integral_segPot ω hω ha hab hb]
  have hg : IntervalIntegrable (fun x : ℝ => ∫ y, Real.log ‖y - (x : ℂ)‖ ∂ω) volume a b :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hab).2
      (integrable_log_norm_sub_prod ω hω ha hb).integral_prod_right
  have hfun : (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) =
      fun x : ℝ => Real.log ‖-z + (x : ℂ)‖ := by
    funext x
    rw [norm_sub_rev, sub_eq_neg_add]
  have hh : IntervalIntegrable (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) volume a b := by
    rw [hfun]
    exact intervalIntegrable_log_norm_add (-z) a b
  unfold segPot
  rw [← intervalIntegral.integral_sub hg hh]
  calc (∫ x in a..b, ((∫ y, Real.log ‖y - (x : ℂ)‖ ∂ω) - Real.log ‖z - (x : ℂ)‖))
      ≤ ∫ _x in a..b, C :=
        intervalIntegral.integral_mono_on hab (hg.sub hh) intervalIntegrable_const hC
    _ = (b - a) * C := by rw [intervalIntegral.integral_const, smul_eq_mul]

theorem tubeSweep_eq_interior {z : ℂ} (hz : ¬ ellipseLevel z < 0) :
    tubeSweep z = interiorSweep z := by
  simp [tubeSweep, hz]

theorem tubeSweep_eq_exterior {z : ℂ} (hz : ellipseLevel z < 0) :
    tubeSweep z = exteriorSweep z := by
  simp [tubeSweep, hz]

/-- Positive-source bracket at an interior collar center. -/
theorem source_bracket_interior {δ : ℝ} (hδ : δ ≤ tubeRadiusMax) {z : ℂ}
    (hz : 0 < ellipseLevel z) (hzt : z ∈ tube δ) {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    (∫ y, Real.log ‖y - (x : ℂ)‖ ∂tubeSweep z) - Real.log ‖z - (x : ℂ)‖ ≤
      96 * δ / semiMinor := by
  rw [tubeSweep_eq_interior (not_lt.mpr hz.le)]
  exact interiorSweep_log_gain_le_96 hδ hz hzt (by simpa using hx) (by simp)

/-- Positive-source bracket at an exterior center: the exact loss `e(z) ≥ 0`. -/
theorem source_bracket_exterior {z : ℂ} (hz : ellipseLevel z < 0) {x : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    (∫ y, Real.log ‖y - (x : ℂ)‖ ∂tubeSweep z) - Real.log ‖z - (x : ℂ)‖ ≤ 0 := by
  rw [tubeSweep_eq_exterior hz]
  have h := exteriorSweep_positive_source z (x : ℂ) hz (by simpa using hx) (by simp)
  have he : 0 ≤ exteriorCorrection ellipseExteriorInverse z := tubeCorrection_nonneg z
  simp only [realLogKernel, integral_neg] at h
  linarith

/-- The `A₀` sweep gap from a uniform bracket bound over `[0,2]`. -/
theorem A0_sweep_gap_of_bracket (z : ℂ) {C : ℝ}
    (hC : ∀ x ∈ Set.Icc (0 : ℝ) 2,
      (∫ y, Real.log ‖y - (x : ℂ)‖ ∂tubeSweep z) - Real.log ‖z - (x : ℂ)‖ ≤ C) :
    (∫ y, A0 y ∂tubeSweep z) - A0 z ≤ 3 * C := by
  have hω := tubeSweep_ae_mem_Gamma z
  have h1 := segPot_sweep_gap (tubeSweep z) hω (a := 1 / 4) (b := 5 / 4)
    (by norm_num) (by norm_num) (by norm_num) z
    (fun x hx => hC x ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  have h2 := segPot_sweep_gap (tubeSweep z) hω (a := 0) (b := 2)
    le_rfl (by norm_num) le_rfl z hC
  have hi1 := integrable_segPot (tubeSweep z) hω (a := 1 / 4) (b := 5 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have hi2 := integrable_segPot (tubeSweep z) hω (a := 0) (b := 2) le_rfl (by norm_num) le_rfl
  have hsplit : (∫ y, A0 y ∂tubeSweep z) =
      (∫ y, segPot (1 / 4) (5 / 4) y ∂tubeSweep z) + ∫ y, segPot 0 2 y ∂tubeSweep z := by
    rw [← integral_add hi1 hi2]
    rfl
  rw [hsplit, A0_eq_segPot z]
  linarith

/-- Interior barycenter: the linear part keeps its mean. -/
theorem re_sweep_interior {z : ℂ} (hz : 0 < ellipseLevel z) :
    (∫ y, y.re ∂tubeSweep z) = z.re := by
  rw [tubeSweep_eq_interior (not_lt.mpr hz.le)]
  have hω : ∀ᵐ y ∂interiorSweep z, y ∈ Gamma := by
    rw [ae_iff]
    exact interiorSweep_boundary_support z
  have hm := interiorSweep_barycenter hz
  have hre : (∫ y, y.re ∂interiorSweep z) = (∫ y, y ∂interiorSweep z).re :=
    integral_re (TubeVariance.continuous_integrable _ hω continuous_id)
  rw [hre, hm]

theorem continuousOn_joukowski_sphere : ContinuousOn joukowski (Metric.sphere (0 : ℂ) 1) := by
  intro ζ hζ
  have hζ0 : ζ ≠ 0 := by
    rintro rfl
    simp at hζ
  unfold joukowski
  exact ((continuousAt_const.add (continuousAt_const.mul continuousAt_id)).add
    (continuousAt_const.mul (continuousAt_inv₀ hζ0))).continuousWithinAt

/-- Exterior mean shift of the linear part. -/
theorem re_sweep_exterior {δ : ℝ} {z : ℂ} (hz : ellipseLevel z < 0) (hzt : z ∈ tube δ) :
    |(∫ y, y.re ∂tubeSweep z) - z.re| ≤ (semiMajor + semiMinor) * δ / semiMinor := by
  rw [tubeSweep_eq_exterior hz]
  set w := ellipseExteriorInverse z with hwdef
  have hw := ellipseExteriorInverse_norm_gt_one hz
  have hp : ‖exteriorPoissonParameter w‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball hw
  have hint : (∫ y, y.re ∂exteriorSweep z) =
      Real.circleAverage
        (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * (joukowski ζ).re) 0 1 :=
    integral_ellipsePoissonMeasure hp (fun y => y.re) Complex.continuous_re.measurable
  have hci : CircleIntegrable
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ • joukowski ζ) 0 1 :=
    ((poissonKernel_unit_continuous hp).smul continuousOn_joukowski_sphere).circleIntegrable
      (by norm_num)
  have hcomm := Complex.reCLM.circleAverage_comp_comm hci
  have hfun : (Complex.reCLM ∘
      fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ • joukowski ζ) =
      fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ * (joukowski ζ).re := by
    funext ζ
    simp
  rw [hfun, exterior_poisson_mean_coordinate hw, Complex.reCLM_apply] at hcomm
  rw [hint, hcomm]
  have hjz : joukowski w = z := joukowski_ellipseExteriorInverse z
  have hzt' : joukowski w ∈ tube δ := by rw [hjz]; exact hzt
  have hd := exteriorMeanCoordinate_distance_of_mem_tube hw.le hzt'
  rw [hjz] at hd
  have hre := Complex.abs_re_le_norm (z - exteriorMeanCoordinate w)
  rw [Complex.sub_re] at hre
  rw [abs_sub_comm]
  exact hre.trans hd

theorem ell_nonneg : 0 ≤ ell := Real.log_nonneg (by norm_num)

theorem ell_le_one : ell ≤ 1 := EnergyLowerBound.log_two_le_one

theorem integrable_A0_of_Gamma (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) : Integrable (fun y => A0 y) ω := by
  have hi1 := integrable_segPot ω hω (a := 1 / 4) (b := 5 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  have hi2 := integrable_segPot ω hω (a := 0) (b := 2) le_rfl (by norm_num) le_rfl
  exact hi1.add hi2

/-- **Pointwise field cost.**  For every tube center `z ∈ T_δ`, the actual sweep
increases the companion field `A₀ - φ` by at most `288 δ / B`. -/
theorem companionField_sweep_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ tubeRadiusMax) {z : ℂ}
    (hzt : z ∈ tube δ) :
    (∫ y, p0CompanionField y ∂tubeSweep z) ≤ p0CompanionField z + 288 * δ / semiMinor := by
  have hB : 0 < semiMinor := semiMinor_pos
  have hdB : 0 ≤ δ / semiMinor := div_nonneg hδ0 hB.le
  have h288 : 288 * δ / semiMinor = 288 * (δ / semiMinor) := by ring
  rcases lt_trichotomy (ellipseLevel z) 0 with hneg | hzero | hpos
  rotate_left
  · -- boundary center: Dirac mass
    rw [tubeSweep_eq_dirac_of_mem_Gamma (mem_Gamma_of_ellipseLevel_eq_zero hzero),
      integral_dirac]
    nlinarith
  all_goals
    set c0 : ℝ := (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) with hc0
    have hω := tubeSweep_ae_mem_Gamma z
    have hA := integrable_A0_of_Gamma (tubeSweep z) hω
    have hre : Integrable (fun y : ℂ => y.re) (tubeSweep z) :=
      TubeVariance.continuous_integrable _ hω Complex.continuous_re
    have hL := integrable_phiSeg (tubeSweep z) hω
    have hfun : (fun y => p0CompanionField y) =
        fun y => A0 y - ((y.re * ell + phiSeg y) + c0) := by
      funext y
      rw [p0CompanionField, phi_eq_phiSeg]
    have hsplit : (∫ y, p0CompanionField y ∂tubeSweep z) =
        (∫ y, A0 y ∂tubeSweep z) -
          ((∫ y, y.re ∂tubeSweep z) * ell + (∫ y, phiSeg y ∂tubeSweep z) + c0) := by
      have hI1 : Integrable (fun y : ℂ => y.re * ell) (tubeSweep z) := hre.mul_const ell
      have hI2 : Integrable (fun y : ℂ => y.re * ell + phiSeg y) (tubeSweep z) := hI1.add hL
      have hI3 : Integrable (fun y : ℂ => y.re * ell + phiSeg y + c0) (tubeSweep z) :=
        hI2.add (integrable_const c0)
      rw [hfun, integral_sub hA hI3, integral_add hI2 (integrable_const c0),
        integral_add hI1 hL, integral_mul_const, integral_const]
      simp
    have hfz : p0CompanionField z = A0 z - (z.re * ell + phiSeg z + c0) := by
      rw [p0CompanionField, phi_eq_phiSeg]
    rw [hsplit, hfz]
    have hLg := phiSeg_sweep_ge z
  · -- interior center
    have hAg := A0_sweep_gap_of_bracket z (C := 96 * δ / semiMinor)
      (fun x hx => source_bracket_interior hδ hpos hzt hx)
    have hlin := re_sweep_interior hpos
    have he : tubeCorrection z = 0 := tubeCorrection_eq_zero_of_nonneg_level hpos.le
    rw [hlin]
    rw [he] at hLg
    have h96 : 3 * (96 * δ / semiMinor) = 288 * δ / semiMinor := by ring
    linarith
  · -- exterior center
    have hAg := A0_sweep_gap_of_bracket z (C := 0)
      (fun x hx => source_bracket_exterior hneg hx)
    have hlin := re_sweep_exterior hneg hzt
    have he := (tubeCorrection_bounds hδ0 hzt).2
    have hell0 := ell_nonneg
    have hell1 := ell_le_one
    set r := (∫ y, y.re ∂tubeSweep z) - z.re with hr
    have hAB : (semiMajor + semiMinor) * δ / semiMinor =
        (semiMajor + semiMinor) * (δ / semiMinor) := by ring
    have hABv : semiMajor + semiMinor ≤ 5 / 2 := by norm_num [semiMajor, semiMinor]
    have hrabs : -r ≤ (semiMajor + semiMinor) * (δ / semiMinor) := by
      rw [← hAB]
      exact (neg_le_abs r).trans hlin
    have hrabs' : (semiMajor + semiMinor) * (δ / semiMinor) ≤ 5 / 2 * (δ / semiMinor) :=
      mul_le_mul_of_nonneg_right hABv hdB
    have hlinterm : -(ell * r) ≤ 5 / 2 * (δ / semiMinor) := by
      have hr' : -r ≤ 5 / 2 * (δ / semiMinor) := hrabs.trans hrabs'
      rcases le_total 0 r with hr0 | hr0
      · nlinarith
      · nlinarith
    have hexp : (∫ y, y.re ∂tubeSweep z) * ell = z.re * ell + ell * r := by
      rw [hr]; ring
    rw [hexp]
    nlinarith

end
end Li2Lean.P0.TubeGap
