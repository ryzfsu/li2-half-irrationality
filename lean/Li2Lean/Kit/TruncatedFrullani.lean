/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Analysis.SpecialFunctions.FrullaniIntegral
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Tactic

/-!+# Truncated Frullani kernels for logarithmic energy

These scalar lemmas concern the actual finite-band Gaussian kernel. They do
not assume a Frullani representation or positivity of logarithmic energy.
-/

open Set Filter MeasureTheory
open scoped Topology

namespace Li2Lean.LogEnergy

/-- The Gaussian difference with the logarithmic-energy normalization. -/
noncomputable def frullaniIntegrand (r t : ℝ) : ℝ :=
  (Real.exp (-(r ^ 2 * t)) - Real.exp (-t)) / (2 * t)

/-- A finite-band kernel; its endpoints are positive in the analytic lemmas. -/
noncomputable def truncatedFrullani (r ε R : ℝ) : ℝ :=
  ∫ t in ε..R, frullaniIntegrand r t

private theorem exp_neg_locallyIntegrable :
    LocallyIntegrableOn (fun x : ℝ => Real.exp (-x)) (Ioi 0) :=
  (Real.continuous_exp.comp continuous_neg).locallyIntegrable.locallyIntegrableOn _

theorem frullaniIntegrand_intervalIntegrable (r : ℝ) {ε R : ℝ}
    (hε : 0 < ε) (hR : 0 < R) :
    IntervalIntegrable (frullaniIntegrand r) volume ε R := by
  apply ContinuousOn.intervalIntegrable
  apply ContinuousOn.div
  · exact (Real.continuous_exp.comp (continuous_const.mul continuous_id).neg).sub
      (Real.continuous_exp.comp continuous_neg) |>.continuousOn
  · exact (continuous_const.mul continuous_id).continuousOn
  · intro t ht
    have ht0 : 0 < t := lt_of_lt_of_le (lt_min hε hR) ht.1
    exact mul_ne_zero (by norm_num) ht0.ne'

/-- Frullani's limit, with both cutoffs free and the factor `1/2` preserved. -/
theorem tendsto_truncatedFrullani {r : ℝ} (hr : 0 < r) :
    Tendsto (fun p : ℝ × ℝ => truncatedFrullani r p.1 p.2)
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 (-Real.log r)) := by
  have hzero : Tendsto (fun x : ℝ => Real.exp (-x)) (𝓝[>] 0) (𝓝 1) := by
    simpa [Function.comp_def] using
      (Real.continuous_exp.comp continuous_neg).continuousAt.tendsto.mono_left
      (nhdsWithin_le_nhds : 𝓝[>] (0 : ℝ) ≤ 𝓝 0)
  have hinfty : Tendsto (fun x : ℝ => Real.exp (-x)) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp tendsto_neg_atTop_atBot
  have h := Frullani.tendsto_intervalIntegral exp_neg_locallyIntegrable
    (sq_pos_of_pos hr) (by norm_num : (0 : ℝ) < 1) hzero hinfty
  have hvalue : Real.log (1 / r ^ 2) * ((1 : ℝ) - 0) / 2 = -Real.log r := by
    rw [Real.log_div one_ne_zero (pow_ne_zero _ hr.ne'), Real.log_one,
      Real.log_pow]
    ring
  have hkernel (p : ℝ × ℝ) : truncatedFrullani r p.1 p.2 =
      (∫ t in p.1..p.2, t⁻¹ • (Real.exp (-(r ^ 2 * t)) -
        Real.exp (-(1 * t)))) / 2 := by
    rw [← intervalIntegral.integral_div]
    apply intervalIntegral.integral_congr
    intro t ht
    simp only [frullaniIntegrand, one_mul, smul_eq_mul, div_eq_mul_inv, mul_inv_rev]
    ring
  simpa only [hkernel, hvalue, smul_eq_mul] using h.div_const 2

theorem frullaniIntegrand_nonneg {r t : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (ht : 0 ≤ t) : 0 ≤ frullaniIntegrand r t := by
  apply div_nonneg _ (mul_nonneg (by norm_num) ht)
  apply sub_nonneg.mpr
  apply Real.exp_le_exp.mpr
  have hsq : r ^ 2 ≤ 1 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq ht]

theorem frullaniIntegrand_nonpos {r t : ℝ} (hr : 1 ≤ r)
    (ht : 0 ≤ t) : frullaniIntegrand r t ≤ 0 := by
  apply div_nonpos_of_nonpos_of_nonneg _ (mul_nonneg (by norm_num) ht)
  apply sub_nonpos.mpr
  apply Real.exp_le_exp.mpr
  have hsq : 1 ≤ r ^ 2 := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_right hsq ht]

private theorem bandIntegral_le_of_nonneg_tendsto {f : ℝ → ℝ} {L ε R : ℝ}
    (hε : 0 < ε) (hεR : ε ≤ R)
    (hint : ∀ a b, 0 < a → 0 < b → IntervalIntegrable f volume a b)
    (hpos : ∀ t, 0 < t → 0 ≤ f t)
    (hlim : Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2, f t)
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 L)) :
    (∫ t in ε..R, f t) ≤ L := by
  apply ge_of_tendsto hlim
  have hlo : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a ≤ ε := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds hε)] with a ha hae
    exact ⟨ha, hae.le⟩
  filter_upwards [prod_mem_prod hlo (eventually_ge_atTop R)] with p hp
  apply intervalIntegral.integral_mono_interval hp.1.2 hεR hp.2
  · exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht =>
      hpos t (hp.1.1.trans ht.1)
  · exact hint _ _ hp.1.1 (hε.trans_le (hεR.trans hp.2))

/-- Uniform domination needed for the pair-measure dominated convergence step.
The distance is strictly positive: this statement does not hide a diagonal
value behind the convention `Real.log 0 = 0`. -/
theorem abs_truncatedFrullani_le {r ε R : ℝ} (hr : 0 < r)
    (hε : 0 < ε) (hεR : ε ≤ R) :
    |truncatedFrullani r ε R| ≤ |Real.log r| := by
  by_cases hr1 : r ≤ 1
  · have hpos : ∀ t, 0 < t → 0 ≤ frullaniIntegrand r t :=
      fun t ht => frullaniIntegrand_nonneg hr.le hr1 ht.le
    have hk : 0 ≤ truncatedFrullani r ε R :=
      intervalIntegral.integral_nonneg hεR fun t ht => hpos t (hε.trans_le ht.1)
    have hbound : truncatedFrullani r ε R ≤ -Real.log r :=
      bandIntegral_le_of_nonneg_tendsto hε hεR
        (fun _ _ ha hb => frullaniIntegrand_intervalIntegrable r ha hb)
        hpos (tendsto_truncatedFrullani hr)
    have hlog : Real.log r ≤ 0 := by linarith
    simpa only [abs_of_nonneg hk, abs_of_nonpos hlog] using hbound
  · have hr1' : 1 ≤ r := (lt_of_not_ge hr1).le
    have hpos : ∀ t, 0 < t → 0 ≤ -frullaniIntegrand r t :=
      fun t ht => neg_nonneg.mpr (frullaniIntegrand_nonpos hr1' ht.le)
    have hk : 0 ≤ -truncatedFrullani r ε R := by
      simpa only [truncatedFrullani, intervalIntegral.integral_neg] using
        intervalIntegral.integral_nonneg hεR (fun t ht => hpos t (hε.trans_le ht.1))
    have hlim : Tendsto (fun p : ℝ × ℝ => ∫ t in p.1..p.2,
        -frullaniIntegrand r t) ((𝓝[>] 0) ×ˢ atTop) (𝓝 (Real.log r)) := by
      simpa only [truncatedFrullani, intervalIntegral.integral_neg, neg_neg] using
        (tendsto_truncatedFrullani hr).neg
    have hbound : -truncatedFrullani r ε R ≤ Real.log r := by
      simpa only [truncatedFrullani, intervalIntegral.integral_neg] using
        bandIntegral_le_of_nonneg_tendsto (f := fun t => -frullaniIntegrand r t) hε hεR
          (fun _ _ ha hb => (frullaniIntegrand_intervalIntegrable r ha hb).neg)
          hpos hlim
    have hlog : 0 ≤ Real.log r := hk.trans hbound
    simpa only [abs_of_nonpos (neg_nonneg.mp hk), abs_of_nonneg hlog] using hbound

theorem measurable_truncatedFrullani {α : Type*} [MeasurableSpace α]
    {d : α → ℝ} (hd : Measurable d) (ε R : ℝ) :
    Measurable (fun x => truncatedFrullani (d x) ε R) := by
  have hf : StronglyMeasurable (fun p : α × ℝ => frullaniIntegrand (d p.1) p.2) := by
    apply Measurable.stronglyMeasurable
    unfold frullaniIntegrand
    fun_prop
  change Measurable (fun x =>
    (∫ t in Ioc ε R, frullaniIntegrand (d x) t) -
    ∫ t in Ioc R ε, frullaniIntegrand (d x) t)
  exact (hf.integral_prod_right' (ν := volume.restrict (Ioc ε R))).measurable.sub
    (hf.integral_prod_right' (ν := volume.restrict (Ioc R ε))).measurable

private theorem eventually_frullani_cutoffs :
    ∀ᶠ p : ℝ × ℝ in ((𝓝[>] 0) ×ˢ atTop), 0 < p.1 ∧ p.1 ≤ p.2 := by
  have hlo : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a ha ha1
    exact ⟨ha, ha1.le⟩
  filter_upwards [prod_mem_prod hlo (eventually_ge_atTop (1 : ℝ))] with p hp
  exact ⟨hp.1.1, hp.1.2.trans hp.2⟩

/-- Dominated convergence for a weighted finite-band kernel over any measure.
The explicit a.e. positive-distance hypothesis is the collision requirement;
no planar absolute continuity or smooth approximation is imposed. -/
theorem tendsto_integral_truncatedFrullani_mul {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {d a : α → ℝ} (hd : Measurable d) (ha : Measurable a)
    (hdpos : ∀ᵐ x ∂μ, 0 < d x)
    (hlog : Integrable (fun x => Real.log (d x) * a x) μ) :
    Tendsto (fun p : ℝ × ℝ => ∫ x, truncatedFrullani (d x) p.1 p.2 * a x ∂μ)
      ((𝓝[>] 0) ×ˢ atTop) (𝓝 (∫ x, -Real.log (d x) * a x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence
    (fun x => |Real.log (d x) * a x|)
  · exact Eventually.of_forall fun p =>
      ((measurable_truncatedFrullani hd p.1 p.2).mul ha).aestronglyMeasurable
  · filter_upwards [eventually_frullani_cutoffs] with p hp
    filter_upwards [hdpos] with x hx
    simp only [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_right (abs_truncatedFrullani_le hx hp.1 hp.2)
      (abs_nonneg (a x))
  · exact hlog.abs
  · filter_upwards [hdpos] with x hx
    exact (tendsto_truncatedFrullani hx).mul_const (a x)

/-- Pair-measure specialization: diagonal nullity is sufficient, including for
contour and circle measures that are singular relative to planar volume. -/
theorem tendsto_integral_truncatedFrullani_pair {μ ν : Measure ℂ}
    (hne : ∀ᵐ p : ℂ × ℂ ∂(μ.prod ν), p.1 ≠ p.2)
    (hlog : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖) (μ.prod ν)) :
    Tendsto (fun q : ℝ × ℝ =>
      ∫ p : ℂ × ℂ, truncatedFrullani ‖p.1 - p.2‖ q.1 q.2 ∂(μ.prod ν))
      ((𝓝[>] 0) ×ˢ atTop)
      (𝓝 (∫ p : ℂ × ℂ, -Real.log ‖p.1 - p.2‖ ∂(μ.prod ν))) := by
  have hdpos : ∀ᵐ p : ℂ × ℂ ∂(μ.prod ν), 0 < ‖p.1 - p.2‖ := by
    filter_upwards [hne] with p hp
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hp)
  simpa only [mul_one] using tendsto_integral_truncatedFrullani_mul
    (d := fun p : ℂ × ℂ => ‖p.1 - p.2‖) (a := fun _ => (1 : ℝ))
    (by fun_prop) measurable_const hdpos (by simpa only [mul_one] using hlog)

/-- A finite-band bound valid even at zero distance. This is for Fubini on
finite intervals, not a substitute for the diagonal condition in the limit. -/
theorem norm_frullaniIntegrand_le (r : ℝ) {ε t : ℝ} (hε : 0 < ε) (hεt : ε ≤ t) :
    ‖frullaniIntegrand r t‖ ≤ 1 / ε := by
  have ht : 0 < t := hε.trans_le hεt
  have h1 : Real.exp (-(r ^ 2 * t)) ≤ 1 :=
    Real.exp_le_one_iff.mpr (neg_nonpos.mpr (mul_nonneg (sq_nonneg r) ht.le))
  have h2 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (neg_nonpos.mpr ht.le)
  have hn : |Real.exp (-(r ^ 2 * t)) - Real.exp (-t)| ≤ 2 := by
    calc
      _ ≤ |Real.exp (-(r ^ 2 * t))| + |Real.exp (-t)| := abs_sub _ _
      _ ≤ 2 := by rw [abs_of_pos (Real.exp_pos _), abs_of_pos (Real.exp_pos _)]; linarith
  rw [Real.norm_eq_abs, frullaniIntegrand, abs_div, abs_of_pos (mul_pos (by norm_num) ht)]
  calc
    _ ≤ 2 / (2 * t) := div_le_div_of_nonneg_right hn (by positivity)
    _ = 1 / t := by ring
    _ ≤ 1 / ε := one_div_le_one_div_of_le hε hεt

/-- Absolute integrability on a finite band follows from the integrability of
the weight. There is no global improper-integral assumption. -/
theorem integrable_frullaniIntegrand_mul_band {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d a : α → ℝ} (hd : Measurable d)
    (ha : Measurable a) (hai : Integrable a μ) {ε R : ℝ} (hε : 0 < ε) :
    Integrable (fun p : ℝ × α => frullaniIntegrand (d p.2) p.1 * a p.2)
      ((volume.restrict (Ioc ε R)).prod μ) := by
  have hdom : Integrable (fun p : ℝ × α => (1 / ε) * |a p.2|)
      ((volume.restrict (Ioc ε R)).prod μ) :=
    (integrable_const (1 / ε)).mul_prod hai.abs
  apply hdom.mono'
  · apply Measurable.aestronglyMeasurable
    unfold frullaniIntegrand
    fun_prop
  · have hm : ∀ᵐ p : ℝ × α ∂((volume.restrict (Ioc ε R)).prod μ), p.1 ∈ Ioc ε R := by
      apply (Measure.ae_prod_iff_ae_ae (measurable_fst measurableSet_Ioc)).mpr
      exact (ae_restrict_mem measurableSet_Ioc).mono fun t ht => Eventually.of_forall fun _ => ht
    filter_upwards [hm] with p hp
    rw [norm_mul, Real.norm_eq_abs (a p.2)]
    exact mul_le_mul_of_nonneg_right (norm_frullaniIntegrand_le (d p.2) hε hp.1.le)
      (abs_nonneg _)

/-- Finite-band Fubini for the weighted Frullani kernel. -/
theorem integral_truncatedFrullani_mul_eq {α : Type*} [MeasurableSpace α]
    {μ : Measure α} [SFinite μ] {d a : α → ℝ} (hd : Measurable d)
    (ha : Measurable a) (hai : Integrable a μ) {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    (∫ x, truncatedFrullani (d x) ε R * a x ∂μ) =
      ∫ t in ε..R, ∫ x, frullaniIntegrand (d x) t * a x ∂μ := by
  simp only [truncatedFrullani, intervalIntegral.integral_of_le hεR]
  simp_rw [← integral_mul_const]
  exact (integral_integral_swap (integrable_frullaniIntegrand_mul_band hd ha hai hε)).symm

end Li2Lean.LogEnergy
