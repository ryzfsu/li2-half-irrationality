/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeSweepSources
import Li2Lean.P0.ContourFieldFinite

/-! # The logarithmic segment of `phi` under the harmonic sweep

`phi` contains the logarithmic potential
`L(y) = ∫_0^{1/2} log |y + s| ds` of the segment `[-1/2, 0]`.  This segment
meets `Γ` (at `-751/5000`) and the interior of the ellipse, so no separated
Green bound applies to it.  The proof below uses only the truncated point
inequality `tubeSweep_truncK_le`, valid for every center and every source, and
removes the truncation by two dominated-convergence passages:

* for fixed `y`, the truncated segment potential converges to `L(y)`
  (dominated by `|log |y + s||`, which is interval integrable);
* the truncated potentials are uniformly bounded on `Γ`, so their sweep
  integrals converge to the sweep integral of `L`.

The result is `∫ L dω_z ≥ L(z) - e(z)/2` for every `z`, the favorable sign of
the logarithmic part of `-phi` used in v10 `sec-tube.tex`.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Li2Lean.P0.TubeGap

noncomputable section

open TubeInterior TubeEnergy

/-- The logarithmic segment potential inside `phi`. -/
def phiSeg (y : ℂ) : ℝ := ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖y + (s : ℂ)‖

/-- Its truncation at level `ε`. -/
def phiSegTrunc (ε : ℝ) (y : ℂ) : ℝ :=
  ∫ s in (0 : ℝ)..(1 / 2 : ℝ), truncatedLogNorm ε (y + (s : ℂ))

/-- `phi` written with its segment potential. -/
theorem phi_eq_phiSeg (z : ℂ) :
    phi z = z.re * ell + phiSeg z + ((1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) := by
  unfold phi phiSeg
  ring

/-- A real-shifted logarithm is interval integrable on every interval, including the
case where the source lies on the interval. -/
theorem intervalIntegrable_log_norm_add (y : ℂ) (a b : ℝ) :
    IntervalIntegrable (fun s : ℝ => Real.log ‖y + (s : ℂ)‖) volume a b := by
  by_cases hy : y.im = 0
  · have h := (intervalIntegral.intervalIntegrable_log'
      (a := a + y.re) (b := b + y.re)).comp_add_right y.re
    have heq : (fun s : ℝ => Real.log ‖y + (s : ℂ)‖) = fun s => Real.log (s + y.re) := by
      funext s
      have hc : y + (s : ℂ) = ((s + y.re : ℝ) : ℂ) := by
        apply Complex.ext
        · simp only [Complex.add_re, Complex.ofReal_re]
          ring
        · simp [hy]
      rw [hc, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
    rw [heq]
    simpa using h
  · apply Continuous.intervalIntegrable
    apply Continuous.log (by fun_prop)
    intro s hs
    rw [norm_eq_zero] at hs
    apply hy
    have := congrArg Complex.im hs
    simpa using this

theorem ae_add_ne_zero (y : ℂ) : ∀ᵐ s : ℝ ∂volume, y + (s : ℂ) ≠ 0 := by
  filter_upwards [volume.ae_ne (-y.re)] with s hs
  intro h
  apply hs
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at hr
  linarith

theorem log_norm_le_truncatedLogNorm {ε : ℝ} {v : ℂ} (hv : v ≠ 0) :
    Real.log ‖v‖ ≤ truncatedLogNorm ε v :=
  Real.log_le_log (norm_pos_iff.mpr hv) (le_max_right _ _)

theorem abs_truncatedLogNorm_le_abs_log {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {v : ℂ}
    (hv : v ≠ 0) : |truncatedLogNorm ε v| ≤ |Real.log ‖v‖| := by
  unfold truncatedLogNorm
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rcases le_total ε ‖v‖ with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h]
    have h1 : Real.log ‖v‖ ≤ Real.log ε := Real.log_le_log hr h
    have h2 : Real.log ε ≤ 0 := Real.log_nonpos hε.le hε1
    rw [abs_of_nonpos h2, abs_of_nonpos (h1.trans h2)]
    linarith

/-- The truncation levels `1/(n+1)`. -/
def epsSeq (n : ℕ) : ℝ := 1 / ((n : ℝ) + 1)

theorem epsSeq_pos (n : ℕ) : 0 < epsSeq n := by
  unfold epsSeq
  positivity

theorem epsSeq_le_one (n : ℕ) : epsSeq n ≤ 1 := by
  unfold epsSeq
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  linarith

theorem tendsto_epsSeq : Tendsto epsSeq atTop (𝓝 0) :=
  tendsto_one_div_add_atTop_nhds_zero_nat

theorem tendsto_truncatedLogNorm {v : ℂ} (hv : v ≠ 0) :
    Tendsto (fun n => truncatedLogNorm (epsSeq n) v) atTop (𝓝 (Real.log ‖v‖)) := by
  have hr : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have hev : ∀ᶠ n in atTop, epsSeq n ≤ ‖v‖ := tendsto_epsSeq.eventually (ge_mem_nhds hr)
  apply tendsto_const_nhds.congr'
  filter_upwards [hev] with n hn
  show Real.log ‖v‖ = Real.log (max (epsSeq n) ‖v‖)
  rw [max_eq_right hn]

theorem continuous_truncatedLogNorm_add {ε : ℝ} (hε : 0 < ε) (y : ℂ) :
    Continuous (fun s : ℝ => truncatedLogNorm ε (y + (s : ℂ))) :=
  (continuous_truncatedLogNorm hε).comp (by fun_prop)

/-- Inner limit: the truncated segment potential converges at every point. -/
theorem tendsto_phiSegTrunc (y : ℂ) :
    Tendsto (fun n => phiSegTrunc (epsSeq n) y) atTop (𝓝 (phiSeg y)) := by
  unfold phiSegTrunc phiSeg
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (fun s : ℝ => |Real.log ‖y + (s : ℂ)‖|)
  · exact Eventually.of_forall fun n =>
      (continuous_truncatedLogNorm_add (epsSeq_pos n) y).aestronglyMeasurable
  · exact Eventually.of_forall fun n => by
      filter_upwards [ae_add_ne_zero y] with s hs _
      rw [Real.norm_eq_abs]
      exact abs_truncatedLogNorm_le_abs_log (epsSeq_pos n) (epsSeq_le_one n) hs
  · exact (intervalIntegrable_log_norm_add y 0 (1 / 2)).abs
  · filter_upwards [ae_add_ne_zero y] with s hs _
    exact tendsto_truncatedLogNorm hs

theorem phiSeg_le_trunc {ε : ℝ} (hε : 0 < ε) (y : ℂ) : phiSeg y ≤ phiSegTrunc ε y := by
  unfold phiSeg phiSegTrunc
  apply intervalIntegral.integral_mono_ae (by norm_num)
    (intervalIntegrable_log_norm_add y _ _)
    ((continuous_truncatedLogNorm_add hε y).intervalIntegrable _ _)
  filter_upwards [ae_add_ne_zero y] with s hs
  exact log_norm_le_truncatedLogNorm hs

theorem phiSegTrunc_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : ℂ} (hy : ‖y‖ ≤ 4) :
    phiSegTrunc ε y ≤ 2 := by
  unfold phiSegTrunc
  have h : (∫ s in (0 : ℝ)..(1 / 2 : ℝ), truncatedLogNorm ε (y + (s : ℂ))) ≤
      ∫ _s in (0 : ℝ)..(1 / 2 : ℝ), (4 : ℝ) := by
    apply intervalIntegral.integral_mono_on (by norm_num)
      ((continuous_truncatedLogNorm_add hε y).intervalIntegrable _ _) intervalIntegrable_const
    intro s hs
    have hs' : ‖(s : ℂ)‖ ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
      exact hs.2
    have hn : ‖y + (s : ℂ)‖ ≤ 5 := (norm_add_le _ _).trans (by linarith)
    have hm : max ε ‖y + (s : ℂ)‖ ≤ 5 := max_le (by linarith) hn
    unfold truncatedLogNorm
    calc Real.log (max ε ‖y + (s : ℂ)‖) ≤ Real.log 5 :=
          Real.log_le_log (lt_of_lt_of_le hε (le_max_left _ _)) hm
      _ ≤ 5 - 1 := Real.log_le_sub_one_of_pos (by norm_num)
      _ = 4 := by norm_num
  rw [intervalIntegral.integral_const, smul_eq_mul] at h
  linarith

theorem abs_phiSegTrunc_le {ε : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) {y : ℂ} (hy : ‖y‖ ≤ 4) :
    |phiSegTrunc ε y| ≤ 86 := by
  have hlo : (-86 : ℝ) ≤ phiSeg y := EnergyLowerBound.phi_segment_ge hy
  have h1 := phiSeg_le_trunc hε y
  have h2 := phiSegTrunc_le hε hε1 hy
  rw [abs_le]
  constructor <;> linarith

theorem abs_phiSeg_le {y : ℂ} (hy : ‖y‖ ≤ 4) : |phiSeg y| ≤ 86 := by
  have hlo : (-86 : ℝ) ≤ phiSeg y := EnergyLowerBound.phi_segment_ge hy
  have h1 := phiSeg_le_trunc (ε := 1) one_pos y
  have h2 := phiSegTrunc_le (ε := 1) one_pos le_rfl hy
  rw [abs_le]
  constructor <;> linarith

theorem stronglyMeasurable_phiSegTrunc {ε : ℝ} (hε : 0 < ε) :
    StronglyMeasurable (phiSegTrunc ε) := by
  have hfun : phiSegTrunc ε = fun y : ℂ =>
      ∫ s in Set.Ioc (0 : ℝ) (1 / 2), truncatedLogNorm ε (y + (s : ℂ)) := by
    funext y
    rw [phiSegTrunc, intervalIntegral.integral_of_le (by norm_num)]
  rw [hfun]
  apply StronglyMeasurable.integral_prod_right
  exact ((continuous_truncatedLogNorm hε).comp
    (by fun_prop : Continuous (fun p : ℂ × ℝ => p.1 + (p.2 : ℂ)))).stronglyMeasurable

theorem stronglyMeasurable_phiSeg : StronglyMeasurable phiSeg := by
  have hfun : phiSeg = fun y : ℂ =>
      ∫ s in Set.Ioc (0 : ℝ) (1 / 2), Real.log ‖y + (s : ℂ)‖ := by
    funext y
    rw [phiSeg, intervalIntegral.integral_of_le (by norm_num)]
  rw [hfun]
  apply StronglyMeasurable.integral_prod_right
  fun_prop

theorem integrable_phiSeg (ω : Measure ℂ) [IsFiniteMeasure ω] (hω : ∀ᵐ y ∂ω, y ∈ Gamma) :
    Integrable phiSeg ω := by
  apply (integrable_const (86 : ℝ)).mono' stronglyMeasurable_phiSeg.aestronglyMeasurable
  filter_upwards [hω] with y hy
  rw [Real.norm_eq_abs]
  exact abs_phiSeg_le (TubeVariance.norm_le_four_of_mem_Gamma hy)

/-- Outer limit: sweep integrals of the truncated potentials converge. -/
theorem tendsto_integral_phiSegTrunc (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) :
    Tendsto (fun n => ∫ y, phiSegTrunc (epsSeq n) y ∂ω) atTop (𝓝 (∫ y, phiSeg y ∂ω)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun _ => (86 : ℝ))
  · exact Eventually.of_forall fun n =>
      (stronglyMeasurable_phiSegTrunc (epsSeq_pos n)).aestronglyMeasurable
  · exact Eventually.of_forall fun n => by
      filter_upwards [hω] with y hy
      rw [Real.norm_eq_abs]
      exact abs_phiSegTrunc_le (epsSeq_pos n) (epsSeq_le_one n)
        (TubeVariance.norm_le_four_of_mem_Gamma hy)
  · exact integrable_const _
  · exact Eventually.of_forall fun y => tendsto_phiSegTrunc y

/-- Truncated sweep inequality for the segment, at every center. -/
theorem phiSegTrunc_sweep_ge {ε : ℝ} (hε : 0 < ε) (z : ℂ) :
    phiSegTrunc ε z - tubeCorrection z / 2 ≤ ∫ y, phiSegTrunc ε y ∂tubeSweep z := by
  set ρ : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (1 / 2)) with hρ
  have hint : Integrable (fun p : ℂ × ℝ => truncatedLogNorm ε (p.1 + (p.2 : ℂ)))
      ((tubeSweep z).prod ρ) := by
    have hc : Continuous (fun p : ℂ × ℝ => truncatedLogNorm ε (p.1 + (p.2 : ℂ))) :=
      (continuous_truncatedLogNorm hε).comp (by fun_prop)
    apply (integrable_const (|Real.log ε| + |Real.log (max ε 5)|)).mono'
      hc.aestronglyMeasurable
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := tubeSweep z) (ν := ρ)).ae
      (tubeSweep_ae_mem_Gamma z)
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := tubeSweep z) (ν := ρ)).ae
      (ae_restrict_mem measurableSet_Ioc : ∀ᵐ s ∂ρ, s ∈ Set.Ioc (0 : ℝ) (1 / 2))
    filter_upwards [a1, a2] with p hp1 hp2
    have hy := TubeVariance.norm_le_four_of_mem_Gamma hp1
    have hs' : ‖(p.2 : ℂ)‖ ≤ 1 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hp2.1.le]
      exact hp2.2
    exact norm_truncatedLogNorm_le hε ((norm_add_le _ _).trans (by linarith))
  have hswap : (∫ y, phiSegTrunc ε y ∂tubeSweep z) =
      ∫ s in (0 : ℝ)..(1 / 2 : ℝ), ∫ y, truncatedLogNorm ε (y + (s : ℂ)) ∂tubeSweep z := by
    rw [intervalIntegral.integral_of_le (by norm_num)]
    simp only [phiSegTrunc, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 / 2 by norm_num)]
    exact integral_integral_swap hint
  have hpt : ∀ s : ℝ, truncatedLogNorm ε (z + (s : ℂ)) - tubeCorrection z ≤
      ∫ y, truncatedLogNorm ε (y + (s : ℂ)) ∂tubeSweep z := by
    intro s
    have h := tubeSweep_truncK_le hε z (-(s : ℂ))
    simp only [truncK, sub_neg_eq_add, integral_neg] at h
    linarith
  have hgi : IntervalIntegrable
      (fun s : ℝ => ∫ y, truncatedLogNorm ε (y + (s : ℂ)) ∂tubeSweep z) volume 0 (1 / 2) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).2 hint.integral_prod_right
  have hfi : IntervalIntegrable
      (fun s : ℝ => truncatedLogNorm ε (z + (s : ℂ)) - tubeCorrection z) volume 0 (1 / 2) :=
    ((continuous_truncatedLogNorm_add hε z).sub continuous_const).intervalIntegrable _ _
  have hmono := intervalIntegral.integral_mono_on (by norm_num) hfi hgi (fun s _ => hpt s)
  rw [intervalIntegral.integral_sub ((continuous_truncatedLogNorm_add hε z).intervalIntegrable _ _)
    intervalIntegrable_const, intervalIntegral.integral_const, smul_eq_mul] at hmono
  rw [hswap]
  unfold phiSegTrunc
  linarith

/-- The favorable sign of the logarithmic part of `-phi` under the actual sweep:
`∫ L dω_z ≥ L(z) - e(z)/2` for every center `z`. -/
theorem phiSeg_sweep_ge (z : ℂ) :
    phiSeg z - tubeCorrection z / 2 ≤ ∫ y, phiSeg y ∂tubeSweep z := by
  have hlim := tendsto_integral_phiSegTrunc (tubeSweep z) (tubeSweep_ae_mem_Gamma z)
  apply ge_of_tendsto hlim
  filter_upwards with n
  linarith [phiSegTrunc_sweep_ge (epsSeq_pos n) z, phiSeg_le_trunc (epsSeq_pos n) z]

end
end Li2Lean.P0.TubeGap
