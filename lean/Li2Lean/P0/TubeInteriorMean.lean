/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorJensen
import Li2Lean.P0.TubeInteriorFactorization
import Li2Lean.P0.TubeCauchyCircle

open MeasureTheory Filter Metric
open scoped Topology

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- An explicit sequence of strictly interior radii tending to one. -/
def radialSequence (n : ℕ) : ℝ := 1 - 1 / ((n : ℝ) + 2)

/-- Circle parametrization matching the half-plane boundary bridge literally. -/
def radialPoint (r θ : ℝ) : ℂ := (r : ℂ) * Complex.exp (Complex.I * (θ : ℂ))

theorem radialSequence_pos (n : ℕ) : 0 < radialSequence n := by
  unfold radialSequence
  have hn : 0 ≤ (n : ℝ) := Nat.cast_nonneg n
  have hi : 1 / ((n : ℝ) + 2) < 1 := (div_lt_one (by positivity)).mpr (by linarith)
  linarith

theorem radialSequence_lt_one (n : ℕ) : radialSequence n < 1 := by
  unfold radialSequence
  have hi : 0 < 1 / ((n : ℝ) + 2) := by positivity
  linarith

theorem tendsto_radialSequence :
    Tendsto radialSequence atTop (𝓝[Set.Ioo (0 : ℝ) 1] 1) := by
  apply tendsto_nhdsWithin_iff.mpr
  constructor
  · unfold radialSequence
    have ht : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 2)) atTop (𝓝 (0 : ℝ)) :=
      tendsto_const_nhds.div_atTop
        (tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop)
    simpa only [sub_zero, radialSequence] using (tendsto_const_nhds (x := (1 : ℝ))).sub ht
  · exact Eventually.of_forall (fun n => ⟨radialSequence_pos n, radialSequence_lt_one n⟩)

@[simp]
theorem norm_radialPoint (r θ : ℝ) : ‖radialPoint r θ‖ = |r| := by
  simp [radialPoint, norm_mul, Complex.norm_exp, Complex.mul_re]

theorem integral_radialPoint_eq_circleAverage {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : ℂ → E) (r : ℝ) :
    (∫ θ, f (radialPoint r θ) ∂circleAngleProbability) = Real.circleAverage f 0 r := by
  simp only [circleAngleProbability, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le), Real.circleAverage,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, circleAngleMeasure,
    circleMap, zero_add, radialPoint, mul_comm Complex.I]

theorem continuous_interiorDiskMap_radialPoint {z : ℂ} (hz : z ∈ ellipseInterior)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    Continuous (fun θ => interiorDiskMap z (radialPoint r θ)) := by
  apply (analyticOnNhd_interiorDiskMap hz).continuousOn.comp_continuous
  · unfold radialPoint
    fun_prop
  · intro θ
    simp only [mem_ball, dist_zero_right, norm_radialPoint, abs_of_nonneg hr]
    exact hr1

/-- Exact finite-radius mean, already expressed with the probability angle law. -/
theorem integral_interiorDiskMap_radialPoint {z : ℂ} (hz : z ∈ ellipseInterior)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) :
    (∫ θ, interiorDiskMap z (radialPoint r θ) ∂circleAngleProbability) = z := by
  rw [integral_radialPoint_eq_circleAverage]
  exact circleAverage_interiorDiskMap hz hr hr1

/-- The actual interior sweep is exactly the boundary map of this same disk lift. -/
theorem interiorSweep_eq_map_boundary {z : ℂ} (hz : z ∈ ellipseInterior) :
    interiorSweep z = Measure.map (fun θ => stripBoundaryPoint
      (cauchyCircleBoundary (stripLocation z) (stripScale z) θ)) circleAngleProbability := by
  exact (map_comp_cauchyCircleBoundary stripBoundaryPoint measurable_stripBoundaryPoint
    (stripLocation z) (stripScale_pos hz)).symm

/-- Exact integral adapter, with the original Cauchy sweep on the left. -/
theorem integral_interiorSweep_eq_boundary {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E] [SecondCountableTopology E]
    {z : ℂ} (hz : z ∈ ellipseInterior) (f : ℂ → E) (hf : Measurable f) :
    (∫ y, f y ∂interiorSweep z) = ∫ θ, f (stripBoundaryPoint
      (cauchyCircleBoundary (stripLocation z) (stripScale z) θ)) ∂circleAngleProbability := by
  rw [interiorSweep_eq_map_boundary hz]
  exact integral_map_of_stronglyMeasurable
    (measurable_stripBoundaryPoint.comp (measurable_cauchyCircleBoundary _ _))
    hf.stronglyMeasurable

private theorem radialUnit_denominator_ne_zero {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    1 - Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := by
  have hspos : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  intro h
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) = 1 := (sub_eq_zero.mp h).symm
  have hzero : Complex.exp (Complex.I * (θ : ℂ)) - 1 = 0 := sub_eq_zero.mpr hexp
  have hnorm : ‖Complex.exp (Complex.I * (θ : ℂ)) - 1‖ = 0 := by rw [hzero, norm_zero]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one] at hnorm
  have hpos : 0 < ‖2 * Real.sin (θ / 2)‖ :=
    norm_pos_iff.mpr (mul_ne_zero (by norm_num) hspos.ne')
  linarith

private theorem interiorDiskMap_radialPoint_boundary {z : ℂ} (hz : z ∈ ellipseInterior)
    {θ : ℝ} (hθ : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)
    ) (ht : cauchyCircleBoundary (stripLocation z) (stripScale z) θ ≠ 0) :
    Tendsto (fun n : ℕ => interiorDiskMap z (radialPoint (radialSequence n) θ)) atTop
      (𝓝 (stripBoundaryPoint (cauchyCircleBoundary (stripLocation z) (stripScale z) θ))) := by
  let a : ℝ := stripLocation z
  let b : ℝ := stripScale z
  let t : ℝ := cauchyCircleBoundary a (stripScale z) θ
  let e : ℂ := Complex.exp (Complex.I * (θ : ℂ))
  let c : ℂ := ((annulusWidth / Real.pi : ℝ) : ℂ) * Complex.I
  have hradial : Tendsto (fun n : ℕ => radialPoint (radialSequence n) θ)
      atTop (𝓝 e) := by
    have hr : Tendsto (fun n : ℕ => (radialSequence n : ℂ)) atTop (𝓝 (1 : ℂ)) := by
      have hr' : Tendsto radialSequence atTop (𝓝 (1 : ℝ)) :=
        tendsto_radialSequence.mono_right nhdsWithin_le_nhds
      exact hr'.ofReal
    simpa [radialPoint, e] using hr.mul_const (Complex.exp (Complex.I * (θ : ℂ)))
  have hden : 1 - e ≠ 0 := by
    exact radialUnit_denominator_ne_zero hθ
  have hcont : ContinuousAt (diskToHalfPlane a b) e := by
    unfold diskToHalfPlane
    fun_prop
  have heq : diskToHalfPlane a b e = (t : ℂ) := by
    simpa [a, b, t, e, diskToHalfPlane, cauchyDiskMap] using
      cauchyDiskMap_exp_eq a (stripScale z) hθ
  have hhalf : Tendsto (fun n : ℕ =>
      diskToHalfPlane a b (radialPoint (radialSequence n) θ)) atTop (𝓝 (t : ℂ)) := by
    convert hcont.tendsto.comp hradial using 1
    · funext n
      rfl
    · simp [a, b, e, t, heq]
  have hhalf_nonneg : Tendsto (fun n : ℕ =>
      diskToHalfPlane a b (radialPoint (radialSequence n) θ)) atTop
      (𝓝[{w : ℂ | 0 ≤ w.im}] (t : ℂ)) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨hhalf, Eventually.of_forall fun n => ?_⟩
    have hnorm : ‖radialPoint (radialSequence n) θ‖ < 1 := by
      rw [norm_radialPoint, abs_of_pos (radialSequence_pos n)]
      exact radialSequence_lt_one n
    change 0 ≤ (diskToHalfPlane a b (radialPoint (radialSequence n) θ)).im
    exact (diskToHalfPlane_im_pos (by exact_mod_cast stripScale_pos hz) hnorm).le
  by_cases htpos : 0 < t
  · let u : ℝ := annulusWidth / Real.pi * Real.log |t|
    have ht_slit : (t : ℂ) ∈ Complex.slitPlane := by
      change 0 < (t : ℂ).re ∨ (t : ℂ).im ≠ 0
      exact Or.inl (by simpa using htpos)
    have hlog_base : Tendsto (fun n : ℕ => Complex.log
        (diskToHalfPlane a b (radialPoint (radialSequence n) θ))) atTop
        (𝓝 (Complex.log (t : ℂ))) := hhalf.clog ht_slit
    have hlog_id : Complex.log (t : ℂ) = (Real.log |t| : ℂ) := by
      rw [abs_of_pos htpos]
      exact (Complex.ofReal_log htpos.le).symm
    have hlog : Tendsto (fun n : ℕ => Complex.log
        (diskToHalfPlane a b (radialPoint (radialSequence n) θ))) atTop
        (𝓝 (Real.log |t| : ℂ)) := by
      simpa only [hlog_id] using hlog_base
    have harg : c * (Real.log |t| : ℂ) = Complex.I * (u : ℂ) := by
      dsimp [c, u]
      push_cast
      ring
    have hcover : Tendsto (fun n : ℕ => annulusCover
        (diskToHalfPlane a b (radialPoint (radialSequence n) θ))) atTop
        (𝓝 (Complex.exp (Complex.I * (u : ℂ)))) := by
      have h := (Complex.continuous_exp.continuousAt.tendsto.comp (hlog.const_mul c))
      convert h using 1
      · funext n
        rfl
      · congr 1
        simpa [c, abs_of_pos htpos] using congrArg Complex.exp harg.symm
    let w : ℂ := Complex.exp (Complex.I * (u : ℂ))
    have hw : w ≠ 0 := Complex.exp_ne_zero _
    have hj : ContinuousAt joukowski w := by
      unfold joukowski
      fun_prop
    have hmap : Tendsto (fun n : ℕ => interiorDiskMap z
        (radialPoint (radialSequence n) θ)) atTop (𝓝 (joukowski w)) := by
      convert hj.tendsto.comp hcover using 1
      · funext n
        rfl
    have hboundary : stripBoundaryPoint
        (cauchyCircleBoundary (stripLocation z) (stripScale z) θ) = gammaPoint u := by
      change stripBoundaryPoint t = gammaPoint u
      unfold stripBoundaryPoint
      rw [if_pos htpos.le, abs_of_pos htpos]
      simp [u, abs_of_pos htpos]
    have hmap' : Tendsto (fun n : ℕ => interiorDiskMap z
        (radialPoint (radialSequence n) θ)) atTop (𝓝 (gammaPoint u)) := by
      simpa only [w, joukowski_unit_circle_eq_gammaPoint] using hmap
    simpa only [hboundary] using hmap'
  · have htt : t ≠ 0 := by simpa [t, a] using ht
    have htneg : t < 0 := lt_of_le_of_ne (le_of_not_gt htpos) htt
    let u : ℝ := annulusWidth / Real.pi * Real.log |t|
    have hlog_base :=
      (Complex.tendsto_log_nhdsWithin_im_nonneg_of_re_neg_of_im_zero
        (z := (t : ℂ)) (by simpa using htneg) (by simp)).comp hhalf_nonneg
    have hlog : Tendsto (fun n : ℕ => Complex.log
        (diskToHalfPlane a b (radialPoint (radialSequence n) θ))) atTop
        (𝓝 ((Real.log |t| : ℂ) + (Real.pi : ℂ) * Complex.I)) := by
      convert hlog_base using 1
      · funext n
        rfl
      · simp
    have harg : c * ((Real.log |t| : ℂ) + (Real.pi : ℂ) * Complex.I) =
        -(annulusWidth : ℂ) + Complex.I * (u : ℂ) := by
      dsimp [c, u]
      push_cast
      field_simp [Real.pi_ne_zero]
      have hI : Complex.I * Complex.I = -1 := by simpa [pow_two] using Complex.I_sq
      calc
        _ = (annulusWidth : ℂ) * Complex.I * (Real.log |t| : ℂ) +
            (annulusWidth : ℂ) * (Real.pi : ℂ) * (Complex.I * Complex.I) := by ring
        _ = (annulusWidth : ℂ) * Complex.I * (Real.log |t| : ℂ) -
            (annulusWidth : ℂ) * (Real.pi : ℂ) := by rw [hI]; ring
        _ = _ := by ring
    have hρreal : Real.exp (-annulusWidth) = annulusRatio := by
      unfold annulusWidth
      rw [neg_neg, Real.exp_log annulusRatio_pos]
    have hρ : Complex.exp (-(annulusWidth : ℂ)) = (annulusRatio : ℂ) := by
      calc
        Complex.exp (-(annulusWidth : ℂ)) = (Real.exp (-annulusWidth) : ℂ) := by simp
        _ = (annulusRatio : ℂ) := congrArg Complex.ofReal hρreal
    have hcover : Tendsto (fun n : ℕ => annulusCover
        (diskToHalfPlane a b (radialPoint (radialSequence n) θ))) atTop
        (𝓝 ((annulusRatio : ℂ) * Complex.exp (Complex.I * (u : ℂ)))) := by
      have h := (Complex.continuous_exp.continuousAt.tendsto.comp (hlog.const_mul c))
      have h' : Tendsto (fun n : ℕ => annulusCover
          (diskToHalfPlane a b (radialPoint (radialSequence n) θ))) atTop
          (𝓝 (Complex.exp (c * ((Real.log |t| : ℂ) + (Real.pi : ℂ) * Complex.I)))) := by
        convert h using 1
        · funext n
          rfl
      rw [harg, Complex.exp_add, hρ] at h'
      exact h'
    let w : ℂ := (annulusRatio : ℂ) * Complex.exp (Complex.I * (u : ℂ))
    have hw : w ≠ 0 := mul_ne_zero (by exact_mod_cast annulusRatio_pos.ne')
      (Complex.exp_ne_zero _)
    have hj : ContinuousAt joukowski w := by
      unfold joukowski
      fun_prop
    have hmap : Tendsto (fun n : ℕ => interiorDiskMap z
        (radialPoint (radialSequence n) θ)) atTop (𝓝 (joukowski w)) := by
      convert hj.tendsto.comp hcover using 1
      · funext n
        rfl
    have hboundary : stripBoundaryPoint
        (cauchyCircleBoundary (stripLocation z) (stripScale z) θ) = gammaPoint (-u) := by
      change stripBoundaryPoint t = gammaPoint (-u)
      unfold stripBoundaryPoint
      rw [if_neg (not_le_of_gt htneg), abs_of_neg htneg]
      simp [u, abs_of_neg htneg]
    have hmap' : Tendsto (fun n : ℕ => interiorDiskMap z
        (radialPoint (radialSequence n) θ)) atTop (𝓝 (gammaPoint (-u))) := by
      simpa only [w, joukowski_inner_circle_eq_gammaPoint] using hmap
    simpa only [hboundary] using hmap'

/-- The positive and negative ends of the fixed truncation have an explicit
uniform finite bound. This statement includes `v = 0`. -/
theorem norm_truncatedLogNorm_le {ε M : ℝ} (hε : 0 < ε) {v : ℂ} (hv : ‖v‖ ≤ M) :
    ‖truncatedLogNorm ε v‖ ≤ |Real.log ε| + |Real.log (max ε M)| := by
  have hlo : Real.log ε ≤ truncatedLogNorm ε v :=
    Real.log_le_log hε (le_max_left _ _)
  have hhi : truncatedLogNorm ε v ≤ Real.log (max ε M) :=
    Real.log_le_log (lt_of_lt_of_le hε (le_max_left _ _)) (max_le_max le_rfl hv)
  rw [Real.norm_eq_abs, abs_le]
  constructor
  · linarith [neg_abs_le (Real.log ε), abs_nonneg (Real.log (max ε M))]
  · linarith [le_abs_self (Real.log (max ε M)), abs_nonneg (Real.log ε)]

private theorem mean_from_radialLimit {z : ℂ} (hz : z ∈ ellipseInterior)
    (hlim : ∀ᵐ θ ∂circleAngleProbability,
      Tendsto (fun n : ℕ => interiorDiskMap z (radialPoint (radialSequence n) θ))
        atTop
        (𝓝 (stripBoundaryPoint (cauchyCircleBoundary (stripLocation z) (stripScale z) θ)))) :
    (∫ y, y ∂interiorSweep z) = z := by
  rw [integral_interiorSweep_eq_boundary hz (fun y => y) measurable_id]
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := circleAngleProbability)
    (F := fun n θ => interiorDiskMap z (radialPoint (radialSequence n) θ))
    (f := fun θ => stripBoundaryPoint (cauchyCircleBoundary (stripLocation z) (stripScale z) θ))
    (fun _ => semiMajor + ‖(center : ℂ)‖)
    (fun n => (continuous_interiorDiskMap_radialPoint hz
      (radialSequence_pos n).le (radialSequence_lt_one n)).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (fun θ => ?_)) ?_
  · have heq : (fun n : ℕ => ∫ θ, interiorDiskMap z (radialPoint (radialSequence n) θ)
        ∂circleAngleProbability) = fun _ => z := by
      funext n
      exact integral_interiorDiskMap_radialPoint hz
        (radialSequence_pos n).le (radialSequence_lt_one n)
    rw [heq] at hDCT
    exact tendsto_nhds_unique hDCT tendsto_const_nhds
  · have hnorm : ‖radialPoint (radialSequence n) θ‖ < 1 := by
      simp only [norm_radialPoint, abs_of_pos (radialSequence_pos n)]
      exact radialSequence_lt_one n
    simpa only [sub_zero] using interiorDiskMap_norm_sub_le (x := 0) hz hnorm
  · filter_upwards [hlim] with θ hθ
    exact hθ

private theorem truncatedJensen_from_radialLimit {z x : ℂ} (hz : z ∈ ellipseInterior)
    {ε : ℝ} (hε : 0 < ε)
    (hlim : ∀ᵐ θ ∂circleAngleProbability,
      Tendsto (fun n : ℕ => interiorDiskMap z (radialPoint (radialSequence n) θ))
        atTop
        (𝓝 (stripBoundaryPoint (cauchyCircleBoundary (stripLocation z) (stripScale z) θ)))) :
    truncatedLogNorm ε (z - x) ≤ ∫ y, truncatedLogNorm ε (y - x) ∂interiorSweep z := by
  have hmeas : Measurable (fun y : ℂ => truncatedLogNorm ε (y - x)) :=
    ((continuous_truncatedLogNorm hε).comp (continuous_id.sub continuous_const)).measurable
  rw [integral_interiorSweep_eq_boundary hz _ hmeas]
  have hDCT := tendsto_integral_of_dominated_convergence
    (μ := circleAngleProbability)
    (F := fun n θ => truncatedLogNorm ε (interiorDiskMap z (radialPoint (radialSequence n) θ) - x))
    (f := fun θ => truncatedLogNorm ε
      (stripBoundaryPoint (cauchyCircleBoundary (stripLocation z) (stripScale z) θ) - x))
    (fun _ => |Real.log ε| + |Real.log (max ε (semiMajor + ‖(center : ℂ) - x‖))|)
    (fun n => ((continuous_truncatedLogNorm hε).comp
      ((continuous_interiorDiskMap_radialPoint hz (radialSequence_pos n).le
        (radialSequence_lt_one n)).sub continuous_const)).aestronglyMeasurable)
    (integrable_const _) (fun n => Eventually.of_forall (fun θ => ?_)) ?_
  · apply ge_of_tendsto hDCT
    apply Eventually.of_forall
    intro n
    rw [integral_radialPoint_eq_circleAverage
      (fun u => truncatedLogNorm ε (interiorDiskMap z u - x)) (radialSequence n)]
    exact truncatedLogNorm_interiorDiskMap hz (radialSequence_pos n)
      (radialSequence_lt_one n) hε
  · apply norm_truncatedLogNorm_le hε
    apply interiorDiskMap_norm_sub_le hz
    simp only [norm_radialPoint, abs_of_pos (radialSequence_pos n)]
    exact radialSequence_lt_one n
  · filter_upwards [hlim] with θ hθ
    exact ((continuous_truncatedLogNorm hε).continuousAt.tendsto).comp
      (hθ.sub tendsto_const_nhds)

/-- The actual Cauchy-mapped boundary sweep has the original point as its
barycenter; the proof uses its concrete disk lift and its a.e. boundary limit. -/
theorem interiorSweep_barycenter {z : ℂ} (hz : z ∈ ellipseInterior) :
    (∫ y, y ∂interiorSweep z) = z := by
  apply mean_from_radialLimit hz
  filter_upwards [circleAngleProbability_ae_mem,
    cauchyCircleBoundary_ne_zero_ae (stripLocation z) (stripScale_pos hz)]
    with θ hθ hzero
  exact interiorDiskMap_radialPoint_boundary hz hθ hzero

/- The same radial-limit argument gives the truncated logarithmic Jensen
   inequality for the concrete Cauchy sweep.  Keeping this theorem public
   lets the paper-facing adapter use the actual `interiorSweep` family
   without introducing an abstract harmonic measure. -/
theorem interiorSweep_truncated_jensen {z x : ℂ} (hz : z ∈ ellipseInterior)
    {ε : ℝ} (hε : 0 < ε) :
    truncatedLogNorm ε (z - x) ≤
      ∫ y, truncatedLogNorm ε (y - x) ∂interiorSweep z := by
  apply truncatedJensen_from_radialLimit hz hε
  filter_upwards [circleAngleProbability_ae_mem,
    cauchyCircleBoundary_ne_zero_ae (stripLocation z) (stripScale_pos hz)]
    with θ hθ hzero
  exact interiorDiskMap_radialPoint_boundary hz hθ hzero

end
end Li2Lean.P0.TubeInterior
