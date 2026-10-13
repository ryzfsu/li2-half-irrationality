/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.CircleBasic

/-!
# Circle averages of the companion field

Paper v13 `p0-analytic.tex` ll. 281-283: on a circle of radius `r ≤ 1/64`
centred on `Γ`, the fixed-grid potential `A_0` is harmonic (its sources
`[0,2]` stay at distance `≥ d_+ > r`), so its circle average is the centre
value; `φ` is subharmonic (its source `[-1/2,0]` may cross `Γ`), so its circle
average is at least the centre value.  Hence the circle average of the
companion field `A_0 - φ` is at most its centre value.
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

theorem norm_circlePoint_sub_center (z : ℂ) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    ‖circlePoint z r t - z‖ = r := by
  simp [Li2Lean.ContourKit.p0CirclePoint_eq_circleMap, abs_of_pos hr]

theorem circlePoint_mem_tube {z : ℂ} (hz : z ∈ Gamma) {r : ℝ} (hr : 0 < r) (t : ℝ) :
    circlePoint z r t ∈ tube r := by
  change Metric.infDist (circlePoint z r t) Gamma ≤ r
  calc Metric.infDist (circlePoint z r t) Gamma ≤ dist (circlePoint z r t) z :=
        Metric.infDist_le_dist_of_mem hz
    _ = r := by rw [dist_eq_norm, norm_circlePoint_sub_center z hr t]

theorem circlePoint_re (z : ℂ) (r t : ℝ) :
    (circlePoint z r t).re = z.re + r * Real.cos t := by
  simp [circlePoint, Complex.exp_re]

theorem circleAngle_integral_eq (f : ℝ → ℝ) :
    ∫ t, f t ∂circleAngleMeasure = ∫ t in (0 : ℝ)..(2 * Real.pi), f t := by
  rw [intervalIntegral.integral_of_le Real.two_pi_pos.le]
  rfl

/-! ## The harmonic part `A_0` -/

/-- One source segment of `A_0` averaged over the circle. -/
theorem circle_segment_average {z : ℂ} (hz : z ∈ Gamma) {r : ℝ} (hr : 0 < r)
    (hr64 : r ≤ 1 / 64) {a b : ℝ} (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 2) :
    Integrable (fun t => ∫ x in a..b, Real.log ‖circlePoint z r t - (x : ℂ)‖)
        circleAngleMeasure ∧
      ∫ t, (∫ x in a..b, Real.log ‖circlePoint z r t - (x : ℂ)‖) ∂circleAngleMeasure =
        2 * Real.pi * ∫ x in a..b, Real.log ‖z - (x : ℂ)‖ := by
  have hrd : r ≤ dPlus := by norm_num [dPlus] at *; linarith
  set F : ℝ × ℝ → ℝ := fun q => Real.log ‖circlePoint z r q.1 - (q.2 : ℂ)‖
  have hmeas : Measurable F := by
    have := (continuous_circlePoint z r).measurable
    simp only [F]
    fun_prop
  have hint : Integrable F (circleAngleMeasure.prod (volume.restrict (Set.Ioc a b))) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.log 6 - Real.log (1 / 8)) ?_
    filter_upwards [(Measure.quasiMeasurePreserving_snd (μ := circleAngleMeasure)
        (ν := volume.restrict (Set.Ioc a b))).ae (ae_restrict_mem measurableSet_Ioc)]
      with q hq
    rw [Real.norm_eq_abs]
    have hw := circlePoint_mem_tube hz hr q.1
    have hlo : (1 / 8 : ℝ) ≤ ‖circlePoint z r q.1 - (q.2 : ℂ)‖ :=
      tube_pinned_clearance hr64 hw ⟨by linarith [hq.1], by linarith [hq.2]⟩
    have hwn := tube_norm_le hr64 hw
    have hhi : ‖circlePoint z r q.1 - (q.2 : ℂ)‖ ≤ 6 := by
      have := norm_sub_le (circlePoint z r q.1) (q.2 : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hq.1])] at this
      linarith [hq.2]
    exact abs_log_le_of_bounds (by norm_num) (by norm_num) (by norm_num) hlo hhi
  have hfun : (fun t => ∫ x in a..b, Real.log ‖circlePoint z r t - (x : ℂ)‖) =
      fun t => ∫ x, F (t, x) ∂(volume.restrict (Set.Ioc a b)) := by
    funext t
    rw [intervalIntegral.integral_of_le hab]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hint.integral_prod_left
  · rw [hfun]
    have hswap := integral_integral_swap (f := fun t x => F (t, x)) hint
    rw [hswap, intervalIntegral.integral_of_le hab, ← integral_const_mul]
    apply setIntegral_congr_fun measurableSet_Ioc
    intro x hx
    have hcl : dPlus ≤ ‖z - (x : ℂ)‖ :=
      mixedCellClearance_full.1 z (Gamma_subset_baseEllipseSet hz) x
        ⟨by linarith [hx.1], by linarith [hx.2]⟩
    have h := integral_realLogKernel_circlePoint (x : ℂ) z hr
    simp only [realLogKernel, integral_neg] at h
    simp only [F]
    have heq : (∫ t, Real.log ‖circlePoint z r t - (x : ℂ)‖ ∂circleAngleMeasure) =
        ∫ t, Real.log ‖(x : ℂ) - circlePoint z r t‖ ∂circleAngleMeasure := by
      congr 1; funext t; rw [norm_sub_rev]
    rw [heq, norm_sub_rev (x : ℂ) z, max_eq_right (hrd.trans hcl)] at *
    linarith

theorem circle_A0_average {z : ℂ} (hz : z ∈ Gamma) {r : ℝ} (hr : 0 < r)
    (hr64 : r ≤ 1 / 64) :
    Integrable (fun t => P0.A0 (circlePoint z r t)) circleAngleMeasure ∧
      ∫ t, P0.A0 (circlePoint z r t) ∂circleAngleMeasure = 2 * Real.pi * P0.A0 z := by
  obtain ⟨h1i, h1⟩ := circle_segment_average hz hr hr64 (a := 1 / 4) (b := 5 / 4)
    (by norm_num) (by norm_num) (by norm_num)
  obtain ⟨h2i, h2⟩ := circle_segment_average hz hr hr64 (a := 0) (b := 2)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨?_, ?_⟩
  · exact h1i.add h2i
  · unfold P0.A0
    rw [integral_add h1i h2i, h1, h2]
    ring

/-! ## The subharmonic part `φ` -/

theorem circle_phiSegment_average {z : ℂ} (hz : z ∈ Gamma) {r : ℝ} (hr : 0 < r)
    (hr64 : r ≤ 1 / 64) :
    Integrable (fun t => ∫ s in (0 : ℝ)..(1 / 2 : ℝ),
        Real.log ‖circlePoint z r t + (s : ℂ)‖) circleAngleMeasure ∧
      2 * Real.pi * (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) ≤
        ∫ t, (∫ s in (0 : ℝ)..(1 / 2 : ℝ),
          Real.log ‖circlePoint z r t + (s : ℂ)‖) ∂circleAngleMeasure := by
  set ν : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (1 / 2))
  set H : ℝ × ℝ → ℝ := fun q => Real.log ‖circlePoint z r q.1 + (q.2 : ℂ)‖
  have hmeas : Measurable H := by
    have := (continuous_circlePoint z r).measurable
    simp only [H]
    fun_prop
  -- slice in the angle
  have hslice : ∀ s : ℝ, Integrable (fun t => H (t, s)) circleAngleMeasure := by
    intro s
    refine ((integrable_realLogKernel_circlePoint (-(s : ℂ)) z r).neg).congr
      (ae_of_all _ (fun t => ?_))
    simp only [H, realLogKernel, Pi.neg_apply, neg_neg]
    rw [show -(s : ℂ) - circlePoint z r t = -(circlePoint z r t + (s : ℂ)) by ring, norm_neg]
  have hsliceval : ∀ s : ℝ, ∫ t, H (t, s) ∂circleAngleMeasure =
      2 * Real.pi * Real.log (max r ‖z + (s : ℂ)‖) := by
    intro s
    have h := integral_realLogKernel_circlePoint (-(s : ℂ)) z hr
    simp only [realLogKernel, integral_neg] at h
    have heq : (∫ t, H (t, s) ∂circleAngleMeasure) =
        ∫ t, Real.log ‖-(s : ℂ) - circlePoint z r t‖ ∂circleAngleMeasure := by
      congr 1; funext t
      simp only [H]
      rw [show -(s : ℂ) - circlePoint z r t = -(circlePoint z r t + (s : ℂ)) by ring,
        norm_neg]
    rw [heq, show -(s : ℂ) - z = -(z + (s : ℂ)) by ring, norm_neg] at *
    linarith
  have hD : ∀ t s, s ∈ Set.Icc (0 : ℝ) (1 / 2) → H (t, s) ≤ 5 := by
    intro t s hs
    have hwn := tube_norm_le hr64 (circlePoint_mem_tube hz hr t)
    have hn : ‖circlePoint z r t + (s : ℂ)‖ ≤ 5 := by
      have := norm_add_le (circlePoint z r t) (s : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1] at this
      linarith [hs.2]
    exact (Real.log_le_self (norm_nonneg _)).trans hn
  have hnormbd : ∀ s ∈ Set.Icc (0 : ℝ) (1 / 2),
      ∫ t, ‖H (t, s)‖ ∂circleAngleMeasure ≤ 2 * Real.pi * (2 * 5 - Real.log r) := by
    intro s hs
    have hp : ∀ t, ‖H (t, s)‖ ≤ 2 * 5 - H (t, s) := by
      intro t
      have := hD t s hs
      rw [Real.norm_eq_abs, abs_le]
      constructor <;> linarith
    calc ∫ t, ‖H (t, s)‖ ∂circleAngleMeasure ≤
          ∫ t, (2 * 5 - H (t, s)) ∂circleAngleMeasure :=
          integral_mono (hslice s).norm ((integrable_const _).sub (hslice s)) hp
      _ = 2 * Real.pi * (2 * 5) - 2 * Real.pi * Real.log (max r ‖z + (s : ℂ)‖) := by
          rw [integral_sub (integrable_const _) (hslice s), integral_const,
            circleAngleMeasure_mass, hsliceval, smul_eq_mul]
      _ ≤ 2 * Real.pi * (2 * 5 - Real.log r) := by
          have := Real.log_le_log hr (le_max_left r ‖z + (s : ℂ)‖)
          have := Real.two_pi_pos
          nlinarith
  have hint : Integrable H (circleAngleMeasure.prod ν) := by
    apply (integrable_prod_iff' hmeas.aestronglyMeasurable).mpr
    constructor
    · exact ae_of_all _ hslice
    · apply (integrable_const (2 * Real.pi * (2 * 5 - Real.log r))).mono'
        hmeas.aestronglyMeasurable.norm.prod_swap.integral_prod_right'
      filter_upwards [ae_restrict_mem measurableSet_Ioc] with s hs
      rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
      exact hnormbd s ⟨hs.1.le, hs.2⟩
  have hfun : (fun t => ∫ s in (0 : ℝ)..(1 / 2 : ℝ),
        Real.log ‖circlePoint z r t + (s : ℂ)‖) = fun t => ∫ s, H (t, s) ∂ν := by
    funext t
    rw [intervalIntegral.integral_of_le (by norm_num)]
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact hint.integral_prod_left
  · rw [hfun, integral_integral_swap (f := fun t s => H (t, s)) hint,
      intervalIntegral.integral_of_le (by norm_num), ← integral_const_mul]
    have hlogint : Integrable (fun s : ℝ => Real.log ‖z + (s : ℂ)‖) ν :=
      (Config.cp_integrable z 0 (1 / 2)).1
    apply integral_mono_ae (hlogint.const_mul _) hint.integral_prod_right
    filter_upwards [Measure.ae_ne ν (-z.re)] with s hs
    rw [hsliceval]
    apply mul_le_mul_of_nonneg_left _ Real.two_pi_pos.le
    have hne : z + (s : ℂ) ≠ 0 := by
      intro h0
      apply hs
      have := congrArg Complex.re h0
      simp at this
      linarith
    exact Real.log_le_log (norm_pos_iff.mpr hne) (le_max_right _ _)

theorem circle_phi_average {z : ℂ} (hz : z ∈ Gamma) {r : ℝ} (hr : 0 < r)
    (hr64 : r ≤ 1 / 64) :
    Integrable (fun t => P0.phi (circlePoint z r t)) circleAngleMeasure ∧
      2 * Real.pi * P0.phi z ≤ ∫ t, P0.phi (circlePoint z r t) ∂circleAngleMeasure := by
  obtain ⟨hGi, hG⟩ := circle_phiSegment_average hz hr hr64
  have hre : Integrable (fun t => (circlePoint z r t).re * ell) circleAngleMeasure := by
    have : Continuous (fun t => (circlePoint z r t).re * ell) := by
      have := continuous_circlePoint z r
      fun_prop
    unfold circleAngleMeasure
    exact (this.integrableOn_Icc (a := 0) (b := 2 * Real.pi)).mono_set
      Set.Ioc_subset_Icc_self
  have hc : Integrable (fun _ : ℝ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))
      circleAngleMeasure := integrable_const _
  have hfun : (fun t => P0.phi (circlePoint z r t)) = fun t =>
      (circlePoint z r t).re * ell +
        (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖circlePoint z r t + (s : ℂ)‖) +
        ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) := by
    funext t; unfold P0.phi; ring
  have hreval : ∫ t, (circlePoint z r t).re * ell ∂circleAngleMeasure =
      2 * Real.pi * (z.re * ell) := by
    rw [circleAngle_integral_eq]
    simp_rw [circlePoint_re]
    rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_add
      (f := fun _ => z.re) (g := fun x => r * Real.cos x)
      intervalIntegrable_const ((continuous_const.mul Real.continuous_cos).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, integral_cos]
    simp
    ring
  refine ⟨?_, ?_⟩
  · rw [hfun]; exact (hre.add hGi).add hc
  · rw [hfun, integral_add (f := fun t => (circlePoint z r t).re * ell +
        ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖circlePoint z r t + (s : ℂ)‖)
        (g := fun _ => (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) (hre.add hGi) hc,
      integral_add (f := fun t => (circlePoint z r t).re * ell) (g := fun t =>
        ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖circlePoint z r t + (s : ℂ)‖) hre hGi,
      hreval, integral_const,
      circleAngleMeasure_mass, smul_eq_mul]
    unfold P0.phi
    nlinarith [hG]

/-- The circle average of the companion field is at most its centre value. -/
theorem integral_companion_circleProbability_le {z : ℂ} (hz : z ∈ Gamma) {r : ℝ}
    (hr : 0 < r) (hr64 : r ≤ 1 / 64) :
    Integrable (fun w => p0CompanionField w) (circleProbability z r) ∧
      ∫ w, p0CompanionField w ∂(circleProbability z r) ≤ p0CompanionField z := by
  obtain ⟨hAi, hA⟩ := circle_A0_average hz hr hr64
  obtain ⟨hφi, hφ⟩ := circle_phi_average hz hr hr64
  have hsm := EnergyLowerBound.stronglyMeasurable_companionField
  have hcomp : Integrable (fun t => p0CompanionField (circlePoint z r t)) circleAngleMeasure :=
    hAi.sub hφi
  refine ⟨integrable_circleProbability_of hsm z r hcomp, ?_⟩
  rw [integral_circleProbability_eq hsm]
  have hval : ∫ t, p0CompanionField (circlePoint z r t) ∂circleAngleMeasure ≤
      2 * Real.pi * p0CompanionField z := by
    unfold p0CompanionField
    rw [integral_sub hAi hφi, hA]
    linarith
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  rw [inv_mul_le_iff₀ hpi]
  exact hval

end

end Li2Lean.P0.CellBound
