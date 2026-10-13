/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Frullani
import Li2Lean.Kit.TruncatedFrullani

/-!
# Generic L6 positivity and the three variations of `lem:dual-lower`

* Diagonal nullity of a product measure is derived from an atomless
  *marginal*; an atomless measure on the pair space is never used.
* The kernel `K_0(z,w) = -log|z-w|` is split into an `ℝ≥0∞` positive part,
  which is `⊤` at a collision (so `Real.log 0 = 0` cannot leak), and the
  finite negative part `log⁺|z-w|`, dominated by
  `log(1+|z|) + log(1+|w|)`.  No compact support is assumed.
* `l6FiniteLogPairDifference_nonneg`: for two finite measures of equal
  mass, null diagonals and integrable kernels,
  `I(μ) + I(ν) - 2 I(μ,ν) ≥ 0`.  The proof uses the truncated Frullani
  kernels and the Gaussian sum-of-squares identity; the constant `e^{-t}`
  parts cancel exactly because the masses agree.  All Gaussian Fubini and
  score integrability facts are proved for arbitrary finite measures.
* `l6QuadraticRemainder_eq_half_sum` / `_nonneg`: the paper identity
  `I(σ)+I(τ)+I(σ,τ) = ½I(σ)+½I(τ)+½I(σ+τ) ≥ 0` with `σ = η - η₀`,
  `τ = φ - φ₀`, obtained from the three applications to `(η,η₀)`,
  `(φ,φ₀)` and `(η+φ, η₀+φ₀)` (the last pair has mass `|η|+|φ|`).
-/

open MeasureTheory Set Filter
open scoped ENNReal Topology

namespace Li2Lean
namespace P0
namespace L6Variations

noncomputable section

/-! ### Diagonal nullity from a marginal -/

theorem prod_diagonal_null_of_right_atomless (μ ν : Measure ℂ) [SFinite ν]
    (hν : ∀ z : ℂ, ν {z} = 0) : (μ.prod ν) (Set.diagonal ℂ) = 0 := by
  rw [Measure.measure_prod_null measurableSet_diagonal]
  filter_upwards with z
  have hset : Prod.mk z ⁻¹' Set.diagonal ℂ = {z} := by
    ext w
    simp [Set.diagonal, eq_comm]
  simp [hset, hν z]

theorem prod_diagonal_null_of_left_atomless (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (hμ : ∀ z : ℂ, μ {z} = 0) : (μ.prod ν) (Set.diagonal ℂ) = 0 := by
  rw [Measure.prod_apply_symm measurableSet_diagonal]
  have hzero : ∀ y : ℂ, μ ((fun x => (x, y)) ⁻¹' Set.diagonal ℂ) = 0 := by
    intro y
    have hset : (fun x : ℂ => (x, y)) ⁻¹' Set.diagonal ℂ = {y} := by
      ext x
      simp [Set.diagonal]
    rw [hset]
    exact hμ y
  simp [hzero]

theorem ae_ne_of_diagonal_null {μ ν : Measure ℂ}
    (h : (μ.prod ν) (Set.diagonal ℂ) = 0) :
    ∀ᵐ x : ℂ × ℂ ∂(μ.prod ν), x.1 ≠ x.2 := by
  rw [ae_iff]
  have hset : {a : ℂ × ℂ | ¬a.1 ≠ a.2} = Set.diagonal ℂ := by
    ext a
    simp [Set.diagonal]
  rw [hset]
  exact h

/-! ### The `ℝ≥0∞` positive/negative kernel split -/

theorem measurable_posLog : Measurable Real.posLog := by
  show Measurable (fun x : ℝ => max 0 (Real.log x))
  exact measurable_const.max Real.measurable_log

/-- Positive part of `K_0 = -log|z-w|`; the collision value is `⊤`. -/
def l6PosKernel (z w : ℂ) : ℝ≥0∞ :=
  if z = w then ⊤ else ENNReal.ofReal (Real.posLog ‖z - w‖⁻¹)

/-- Negative part of `K_0`, namely `log⁺|z-w|`; finite everywhere. -/
def l6NegKernel (z w : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (Real.posLog ‖z - w‖)

theorem measurable_l6PosKernel :
    Measurable (fun x : ℂ × ℂ => l6PosKernel x.1 x.2) := by
  unfold l6PosKernel
  refine Measurable.ite (p := fun x : ℂ × ℂ => x.1 = x.2)
    measurableSet_diagonal measurable_const ?_
  exact ENNReal.measurable_ofReal.comp
    (measurable_posLog.comp (by fun_prop : Measurable fun x : ℂ × ℂ => ‖x.1 - x.2‖⁻¹))

theorem li2LogKernel_eq_posLog_sub (z w : ℂ) :
    li2LogKernel z w = Real.posLog ‖z - w‖⁻¹ - Real.posLog ‖z - w‖ := by
  rw [li2LogKernel, ← Real.posLog_sub_posLog_inv]
  ring

theorem li2LogKernel_comm (z w : ℂ) : li2LogKernel z w = li2LogKernel w z := by
  simp [li2LogKernel, norm_sub_rev]

/-- The dominating function for the negative part: no compact support. -/
theorem posLog_norm_sub_le (z w : ℂ) :
    Real.posLog ‖z - w‖ ≤ Real.log (1 + ‖z‖) + Real.log (1 + ‖w‖) := by
  have hz := norm_nonneg z
  have hw := norm_nonneg w
  have h1 : 0 < 1 + ‖z‖ := by positivity
  have h2 : 0 < 1 + ‖w‖ := by positivity
  rw [← Real.log_mul h1.ne' h2.ne']
  have hge : (1 : ℝ) ≤ (1 + ‖z‖) * (1 + ‖w‖) := by nlinarith
  show max 0 (Real.log ‖z - w‖) ≤ _
  apply max_le (Real.log_nonneg hge)
  rcases eq_or_lt_of_le (norm_nonneg (z - w)) with h | h
  · rw [← h, Real.log_zero]
    exact Real.log_nonneg hge
  · apply Real.log_le_log h
    calc
      ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
      _ ≤ (1 + ‖z‖) * (1 + ‖w‖) := by nlinarith

/-- The finite `ℝ≥0∞` positive energy forces a null diagonal (atoms cost `⊤`). -/
theorem ae_ne_of_posKernel_lintegral_ne_top {μ ν : Measure ℂ}
    (hpos : ∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν) ≠ ⊤) :
    ∀ᵐ x : ℂ × ℂ ∂(μ.prod ν), x.1 ≠ x.2 := by
  filter_upwards [ae_lt_top measurable_l6PosKernel hpos] with x hx hxe
  simp [l6PosKernel, hxe] at hx

/-- Integrability of `K_0` from the `ℝ≥0∞` positive part and logarithmic
moments of the marginals (dominating function `posLog_norm_sub_le`). -/
theorem integrable_li2LogKernel_of_split {μ ν : Measure ℂ}
    [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hpos : ∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν) ≠ ⊤)
    (hμ : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) μ)
    (hν : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) ν) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν) := by
  have hmeas : Measurable (fun x : ℂ × ℂ => ‖x.1 - x.2‖) := by fun_prop
  have hP : Integrable (fun x : ℂ × ℂ => Real.posLog ‖x.1 - x.2‖⁻¹) (μ.prod ν) := by
    refine ⟨(measurable_posLog.comp hmeas.inv).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    refine lt_of_le_of_lt ?_ (lt_top_iff_ne_top.mpr hpos)
    apply lintegral_mono
    intro x
    show ‖Real.posLog ‖x.1 - x.2‖⁻¹‖ₑ ≤ l6PosKernel x.1 x.2
    rw [Real.enorm_eq_ofReal Real.posLog_nonneg]
    by_cases hx : x.1 = x.2
    · simp [l6PosKernel, hx]
    · simp [l6PosKernel, hx]
  have hN : Integrable (fun x : ℂ × ℂ => Real.posLog ‖x.1 - x.2‖) (μ.prod ν) := by
    refine Integrable.mono' ((hμ.comp_fst ν).add (hν.comp_snd μ))
      (measurable_posLog.comp hmeas).aestronglyMeasurable ?_
    filter_upwards with x
    rw [Real.norm_of_nonneg Real.posLog_nonneg]
    exact posLog_norm_sub_le x.1 x.2
  refine (hP.sub hN).congr ?_
  filter_upwards with x
  exact (li2LogKernel_eq_posLog_sub x.1 x.2).symm

/-- A reference with uniformly bounded `ℝ≥0∞` positive potential gives a
finite cross positive energy against any finite measure. -/
theorem lintegral_posKernel_prod_le {μ ν : Measure ℂ} [SFinite ν] {C : ℝ≥0∞}
    (hC : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂ν ≤ C) :
    ∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν) ≤ C * μ univ := by
  rw [lintegral_prod _ measurable_l6PosKernel.aemeasurable]
  calc
    (∫⁻ z, ∫⁻ w, l6PosKernel (z, w).1 (z, w).2 ∂ν ∂μ) ≤ ∫⁻ _z, C ∂μ :=
      lintegral_mono fun z => hC z
    _ = C * μ univ := lintegral_const C

/-- The first moment controls the logarithmic moment. -/
theorem integrable_log_one_add_norm_of_norm {μ : Measure ℂ}
    (h : Integrable (fun z : ℂ => ‖z‖) μ) :
    Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) μ := by
  refine h.mono' ?_ ?_
  · exact (Real.measurable_log.comp (by fun_prop : Measurable fun z : ℂ => 1 + ‖z‖)).aestronglyMeasurable
  · filter_upwards with z
    have hpos : 0 < 1 + ‖z‖ := by positivity
    rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith [norm_nonneg z]))]
    linarith [Real.log_le_sub_one_of_pos hpos]

/-! ### Gaussian Fubini and score integrability for finite measures -/

theorem integrable_gaussian_sub (a : ℝ) (ha : 0 < a) (z : ℂ) :
    Integrable (fun u : ℂ => Real.exp (-a * ‖z - u‖ ^ 2)) volume := by
  apply Integrable.of_integral_ne_zero
  have h := ContourKit.integral_exp_neg_mul_sq_norm_sub_complex ha z
  have hcongr : (∫ u : ℂ, Real.exp (-a * ‖z - u‖ ^ 2)) =
      ∫ u : ℂ, Real.exp (-a * ‖u - z‖ ^ 2) := by
    congr 1
    funext u
    rw [norm_sub_rev]
  rw [hcongr, h]
  exact div_ne_zero Real.pi_ne_zero ha.ne'

theorem gaussianFubini_integrable (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (t : ℝ) (ht : 0 < t) :
    Integrable (p0GaussianFubiniIntegrand μ ν t) (volume.prod (μ.prod ν)) := by
  have hcont : Continuous (p0GaussianFubiniIntegrand μ ν t) := by
    unfold p0GaussianFubiniIntegrand
    fun_prop
  rw [integrable_prod_iff' hcont.aestronglyMeasurable]
  constructor
  · filter_upwards with y
    apply Integrable.of_integral_ne_zero
    change (∫ u : ℂ, Real.exp (-2 * t * ‖y.1 - u‖ ^ 2) *
      Real.exp (-2 * t * ‖y.2 - u‖ ^ 2)) ≠ 0
    rw [ContourKit.gaussianKernelConvolution_eq t ht y.1 y.2]
    exact mul_ne_zero (div_ne_zero Real.pi_ne_zero (by positivity)) (Real.exp_pos _).ne'
  · have hpair := (p0GaussianPairIntegrable_of_finite_mass μ ν (measure_lt_top μ univ)
      (measure_lt_top ν univ) t ht.le).const_mul (Real.pi / (4 * t))
    refine hpair.congr ?_
    filter_upwards with y
    have hnorm : (fun u : ℂ => ‖p0GaussianFubiniIntegrand μ ν t (u, y)‖) =
        fun u : ℂ => Real.exp (-2 * t * ‖y.1 - u‖ ^ 2) *
          Real.exp (-2 * t * ‖y.2 - u‖ ^ 2) := by
      funext u
      simp only [p0GaussianFubiniIntegrand]
      rw [Real.norm_of_nonneg (mul_nonneg (Real.exp_pos _).le (Real.exp_pos _).le)]
    rw [hnorm, ContourKit.gaussianKernelConvolution_eq t ht y.1 y.2]
    rfl

theorem gaussianScore_integrable (ν : Measure ℂ) [IsFiniteMeasure ν]
    (t : ℝ) (ht : 0 < t) :
    Integrable (p0GaussianScore ν t) volume := by
  have hcont : Continuous (fun p : ℂ × ℂ => Real.exp (-2 * t * ‖p.2 - p.1‖ ^ 2)) := by
    fun_prop
  have hprod : Integrable (fun p : ℂ × ℂ => Real.exp (-2 * t * ‖p.2 - p.1‖ ^ 2))
      (volume.prod ν) := by
    rw [integrable_prod_iff' hcont.aestronglyMeasurable]
    constructor
    · filter_upwards with z
      refine (integrable_gaussian_sub (2 * t) (by positivity) z).congr
        (Eventually.of_forall fun u => ?_)
      change Real.exp (-(2 * t) * ‖z - u‖ ^ 2) = Real.exp (-2 * t * ‖z - u‖ ^ 2)
      congr 1
      ring
    · refine (integrable_const (Real.pi / (2 * t))).congr ?_
      filter_upwards with z
      have hnorm : (fun u : ℂ => ‖Real.exp (-2 * t * ‖(u, z).2 - (u, z).1‖ ^ 2)‖) =
          fun u : ℂ => Real.exp (-(2 * t) * ‖u - z‖ ^ 2) := by
        funext u
        rw [Real.norm_of_nonneg (Real.exp_pos _).le, norm_sub_rev]
        ring_nf
      rw [hnorm, ContourKit.integral_exp_neg_mul_sq_norm_sub_complex (by positivity) z]
  exact hprod.integral_prod_left

theorem gaussianScore_le (μ : Measure ℂ) [IsFiniteMeasure μ] (t : ℝ) (ht : 0 ≤ t)
    (u : ℂ) : ‖p0GaussianScore μ t u‖ ≤ μ.real univ := by
  have h := norm_integral_le_of_norm_le_const (μ := μ)
    (f := fun z : ℂ => Real.exp (-2 * t * ‖z - u‖ ^ 2)) (C := 1) (by
      filter_upwards with z
      rw [Real.norm_of_nonneg (Real.exp_pos _).le, Real.exp_le_one_iff]
      have : 0 ≤ t * ‖z - u‖ ^ 2 := mul_nonneg ht (sq_nonneg _)
      linarith)
  simpa [p0GaussianScore] using h

theorem gaussianScore_mul_integrable (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (t : ℝ) (ht : 0 < t) :
    Integrable (fun u : ℂ => p0GaussianScore μ t u * p0GaussianScore ν t u) volume := by
  have hsm : StronglyMeasurable (p0GaussianScore μ t) := by
    unfold p0GaussianScore
    exact StronglyMeasurable.integral_prod_right
      (f := fun u z : ℂ => Real.exp (-2 * t * ‖z - u‖ ^ 2))
      (by
        apply Continuous.stronglyMeasurable
        unfold Function.uncurry
        fun_prop)
  exact (gaussianScore_integrable ν t ht).bdd_mul hsm.aestronglyMeasurable
    (Eventually.of_forall fun u => gaussianScore_le μ t ht.le u)

/-- Gaussian positivity for arbitrary finite measures; every Fubini premise of
`p0GaussianDifference_nonneg_of_fubini` is discharged. -/
theorem gaussianDifference_nonneg (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (t : ℝ) (ht : 0 < t) :
    0 ≤ p0GaussianPair μ μ t + p0GaussianPair ν ν t - 2 * p0GaussianPair μ ν t :=
  p0GaussianDifference_nonneg_of_fubini μ ν t ht
    (gaussianFubini_integrable μ μ t ht) (gaussianFubini_integrable ν ν t ht)
    (gaussianFubini_integrable μ ν t ht) (gaussianScore_mul_integrable μ μ t ht)
    (gaussianScore_mul_integrable ν ν t ht) (gaussianScore_mul_integrable μ ν t ht)

/-! ### Finite-band Frullani evaluation -/

theorem integral_frullaniIntegrand_pair (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (t : ℝ) (ht : 0 ≤ t) :
    ∫ x : ℂ × ℂ, LogEnergy.frullaniIntegrand ‖x.1 - x.2‖ t ∂(μ.prod ν) =
      (p0GaussianPair μ ν t - μ.real univ * ν.real univ * Real.exp (-t)) / (2 * t) := by
  have hG := p0GaussianPairIntegrable_of_finite_mass μ ν (measure_lt_top μ univ)
    (measure_lt_top ν univ) t ht
  have hpt : (fun x : ℂ × ℂ => LogEnergy.frullaniIntegrand ‖x.1 - x.2‖ t) =
      fun x => (p0GaussianPairIntegrand t x - Real.exp (-t)) / (2 * t) := by
    funext x
    simp only [LogEnergy.frullaniIntegrand, p0GaussianPairIntegrand]
    congr 2
    ring_nf
  rw [hpt, integral_div, integral_sub hG (integrable_const _), integral_const,
    ← univ_prod_univ, measureReal_prod_prod, smul_eq_mul]
  rfl

/-- The finite-band energy as a single band integral of the Frullani
integrand. -/
theorem integral_truncatedFrullani_pair_eq (ρ : Measure (ℂ × ℂ)) [IsFiniteMeasure ρ]
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    ∫ x, LogEnergy.truncatedFrullani ‖x.1 - x.2‖ ε R ∂ρ =
      ∫ t in ε..R, ∫ x, LogEnergy.frullaniIntegrand ‖x.1 - x.2‖ t ∂ρ := by
  have h := LogEnergy.integral_truncatedFrullani_mul_eq (μ := ρ)
    (d := fun x : ℂ × ℂ => ‖x.1 - x.2‖) (a := fun _ => (1 : ℝ)) (by fun_prop)
    measurable_const (integrable_const 1) hε hεR
  simpa only [mul_one] using h

theorem intervalIntegrable_frullani_pair (ρ : Measure (ℂ × ℂ)) [IsFiniteMeasure ρ]
    {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) :
    IntervalIntegrable
      (fun t => ∫ x, LogEnergy.frullaniIntegrand ‖x.1 - x.2‖ t ∂ρ) volume ε R := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hεR]
  have h := (LogEnergy.integrable_frullaniIntegrand_mul_band (μ := ρ) (R := R)
    (d := fun x : ℂ × ℂ => ‖x.1 - x.2‖) (a := fun _ => (1 : ℝ)) (by fun_prop)
    measurable_const (integrable_const 1) hε).integral_prod_left
  simp only [mul_one] at h
  exact h

private theorem eventually_cutoffs :
    ∀ᶠ p : ℝ × ℝ in ((𝓝[>] 0) ×ˢ atTop), 0 < p.1 ∧ p.1 ≤ p.2 := by
  have hlo : ∀ᶠ a : ℝ in 𝓝[>] 0, 0 < a ∧ a ≤ 1 := by
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds (Iio_mem_nhds (by norm_num : (0 : ℝ) < 1))] with a ha ha1
    exact ⟨ha, ha1.le⟩
  filter_upwards [prod_mem_prod hlo (eventually_ge_atTop (1 : ℝ))] with p hp
  exact ⟨hp.1.1, hp.1.2.trans hp.2⟩

/-- The truncated mass-zero energy is nonnegative on every band. -/
theorem truncatedPairDifference_nonneg (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hmass : μ univ = ν univ) {ε R : ℝ} (hε : 0 < ε)
    (hεR : ε ≤ R) :
    0 ≤ (∫ x, LogEnergy.truncatedFrullani ‖x.1 - x.2‖ ε R ∂(μ.prod μ)) +
      (∫ x, LogEnergy.truncatedFrullani ‖x.1 - x.2‖ ε R ∂(ν.prod ν)) -
      2 * ∫ x, LogEnergy.truncatedFrullani ‖x.1 - x.2‖ ε R ∂(μ.prod ν) := by
  have hreal : μ.real univ = ν.real univ := by simp [Measure.real, hmass]
  rw [integral_truncatedFrullani_pair_eq _ hε hεR, integral_truncatedFrullani_pair_eq _ hε hεR,
    integral_truncatedFrullani_pair_eq _ hε hεR]
  have i1 := intervalIntegrable_frullani_pair (μ.prod μ) hε hεR
  have i2 := intervalIntegrable_frullani_pair (ν.prod ν) hε hεR
  have i3 := intervalIntegrable_frullani_pair (μ.prod ν) hε hεR
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_add i1 i2,
    ← intervalIntegral.integral_sub (i1.add i2) (i3.const_mul 2)]
  apply intervalIntegral.integral_nonneg hεR
  intro t ht
  have htpos : 0 < t := hε.trans_le ht.1
  rw [integral_frullaniIntegrand_pair μ μ t htpos.le,
    integral_frullaniIntegrand_pair ν ν t htpos.le,
    integral_frullaniIntegrand_pair μ ν t htpos.le, hreal]
  have hG := gaussianDifference_nonneg μ ν t htpos
  have key :
      (p0GaussianPair μ μ t - ν.real univ * ν.real univ * Real.exp (-t)) / (2 * t) +
        (p0GaussianPair ν ν t - ν.real univ * ν.real univ * Real.exp (-t)) / (2 * t) -
        2 * ((p0GaussianPair μ ν t - ν.real univ * ν.real univ * Real.exp (-t)) / (2 * t)) =
      (p0GaussianPair μ μ t + p0GaussianPair ν ν t - 2 * p0GaussianPair μ ν t) /
        (2 * t) := by
    ring
  rw [key]
  exact div_nonneg hG (by positivity)

/-- **Generic L6 positivity.**  Finite measures of equal mass, null diagonals
(see `prod_diagonal_null_of_right_atomless` for the marginal criterion) and
integrable `K_0` on the three products; no compact support. -/
theorem l6FiniteLogPairDifference_nonneg (μ ν : Measure ℂ) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] (hmass : μ univ = ν univ)
    (hμμ : ∀ᵐ x : ℂ × ℂ ∂(μ.prod μ), x.1 ≠ x.2)
    (hνν : ∀ᵐ x : ℂ × ℂ ∂(ν.prod ν), x.1 ≠ x.2)
    (hμν : ∀ᵐ x : ℂ × ℂ ∂(μ.prod ν), x.1 ≠ x.2)
    (iμμ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod μ))
    (iνν : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (ν.prod ν))
    (iμν : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    0 ≤ li2LogInteraction μ μ + li2LogInteraction ν ν - 2 * li2LogInteraction μ ν := by
  have hlog : ∀ {ρ : Measure (ℂ × ℂ)},
      Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) ρ →
      Integrable (fun x : ℂ × ℂ => Real.log ‖x.1 - x.2‖) ρ := by
    intro ρ h
    simpa [li2LogKernel] using h.neg
  have t1 := LogEnergy.tendsto_integral_truncatedFrullani_pair hμμ (hlog iμμ)
  have t2 := LogEnergy.tendsto_integral_truncatedFrullani_pair hνν (hlog iνν)
  have t3 := LogEnergy.tendsto_integral_truncatedFrullani_pair hμν (hlog iμν)
  have hlim := (t1.add t2).sub (t3.const_mul 2)
  have heq : ∀ ρ : Measure (ℂ × ℂ),
      (∫ p : ℂ × ℂ, -Real.log ‖p.1 - p.2‖ ∂ρ) =
        ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂ρ := fun ρ => rfl
  rw [heq, heq, heq] at hlim
  apply ge_of_tendsto hlim
  filter_upwards [eventually_cutoffs] with p hp
  exact truncatedPairDifference_nonneg μ ν hmass hp.1 hp.2

/-- Atomless marginals version (diagonal nullity derived from a marginal). -/
theorem l6FiniteLogPairDifference_nonneg_of_atomless (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hmass : μ univ = ν univ)
    (hμ : ∀ z : ℂ, μ {z} = 0) (hν : ∀ z : ℂ, ν {z} = 0)
    (iμμ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod μ))
    (iνν : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (ν.prod ν))
    (iμν : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    0 ≤ li2LogInteraction μ μ + li2LogInteraction ν ν - 2 * li2LogInteraction μ ν :=
  l6FiniteLogPairDifference_nonneg μ ν hmass
    (ae_ne_of_diagonal_null (prod_diagonal_null_of_right_atomless μ μ hμ))
    (ae_ne_of_diagonal_null (prod_diagonal_null_of_right_atomless ν ν hν))
    (ae_ne_of_diagonal_null (prod_diagonal_null_of_right_atomless μ ν hν))
    iμμ iνν iμν

/-- `ℝ≥0∞` split version: finite positive energies (collisions cost `⊤`)
and logarithmic moments; no compact support and no separate atom clause. -/
theorem l6FiniteLogPairDifference_nonneg_of_split (μ ν : Measure ℂ)
    [IsFiniteMeasure μ] [IsFiniteMeasure ν] (hmass : μ univ = ν univ)
    (pμμ : ∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod μ) ≠ ⊤)
    (pνν : ∫⁻ x, l6PosKernel x.1 x.2 ∂(ν.prod ν) ≠ ⊤)
    (pμν : ∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν) ≠ ⊤)
    (mμ : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) μ)
    (mν : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) ν) :
    0 ≤ li2LogInteraction μ μ + li2LogInteraction ν ν - 2 * li2LogInteraction μ ν :=
  l6FiniteLogPairDifference_nonneg μ ν hmass
    (ae_ne_of_posKernel_lintegral_ne_top pμμ) (ae_ne_of_posKernel_lintegral_ne_top pνν)
    (ae_ne_of_posKernel_lintegral_ne_top pμν)
    (integrable_li2LogKernel_of_split pμμ mμ mμ)
    (integrable_li2LogKernel_of_split pνν mν mν)
    (integrable_li2LogKernel_of_split pμν mμ mν)


/-! ### Symmetry and bilinearity of the interaction -/

theorem li2LogInteraction_comm (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    li2LogInteraction μ ν = li2LogInteraction ν μ := by
  unfold li2LogInteraction
  rw [← integral_prod_swap (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)]
  congr 1
  funext x
  exact li2LogKernel_comm _ _

theorem integrable_kernel_swap {μ ν : Measure ℂ} [SFinite μ] [SFinite ν]
    (h : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (ν.prod μ) := by
  refine h.swap.congr ?_
  filter_upwards with x
  exact li2LogKernel_comm _ _

theorem integrable_kernel_add_left {a b c : Measure ℂ} [SFinite a] [SFinite b] [SFinite c]
    (hac : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod c)) (hbc : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (b.prod c)) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) ((a + b).prod c) := by
  rw [Measure.add_prod]
  exact hac.add_measure hbc

theorem integrable_kernel_add_right {a b c : Measure ℂ} [SFinite a] [SFinite b] [SFinite c]
    (hab : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod b)) (hac : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod c)) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod (b + c)) := by
  rw [Measure.prod_add]
  exact hab.add_measure hac

theorem li2LogInteraction_add_left {a b c : Measure ℂ} [SFinite a] [SFinite b] [SFinite c]
    (hac : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod c)) (hbc : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (b.prod c)) :
    li2LogInteraction (a + b) c = li2LogInteraction a c + li2LogInteraction b c := by
  unfold li2LogInteraction
  rw [Measure.add_prod, integral_add_measure hac hbc]

theorem li2LogInteraction_add_right {a b c : Measure ℂ} [SFinite a] [SFinite b] [SFinite c]
    (hab : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod b)) (hac : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (a.prod c)) :
    li2LogInteraction a (b + c) = li2LogInteraction a b + li2LogInteraction a c := by
  unfold li2LogInteraction
  rw [Measure.prod_add, integral_add_measure hab hac]

/-! ### The three variations of `lem:dual-lower` -/

/-- `I(μ - ν) = I(μ) + I(ν) - 2 I(μ,ν)` for a positive pair. -/
def l6PairDifference (μ ν : Measure ℂ) : ℝ :=
  li2LogInteraction μ μ + li2LogInteraction ν ν - 2 * li2LogInteraction μ ν

/-- The paper's quadratic remainder `I(σ) + I(τ) + I(σ,τ)` with
`σ = η - η₀` and `τ = φ - φ₀` (here `φ = μ⁻`, `φ₀ = μ₀⁻`). -/
def l6QuadraticRemainder (η η₀ φ φ₀ : Measure ℂ) : ℝ :=
  l6PairDifference η η₀ + l6PairDifference φ φ₀ +
    (li2LogInteraction η φ - li2LogInteraction η φ₀ -
      li2LogInteraction η₀ φ + li2LogInteraction η₀ φ₀)

/-- Hypotheses of the three applications: finite masses, equal masses within
each variation, atomless marginals, and integrable `K₀` on the ten
unordered products. -/
structure L6FourMeasureData (η η₀ φ φ₀ : Measure ℂ) : Prop where
  fin_η : IsFiniteMeasure η
  fin_η₀ : IsFiniteMeasure η₀
  fin_φ : IsFiniteMeasure φ
  fin_φ₀ : IsFiniteMeasure φ₀
  mass_η : η univ = η₀ univ
  mass_φ : φ univ = φ₀ univ
  atomless_η : ∀ z : ℂ, η {z} = 0
  atomless_η₀ : ∀ z : ℂ, η₀ {z} = 0
  atomless_φ : ∀ z : ℂ, φ {z} = 0
  atomless_φ₀ : ∀ z : ℂ, φ₀ {z} = 0
  int_ηη : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η.prod η)
  int_η₀η₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η₀.prod η₀)
  int_φφ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (φ.prod φ)
  int_φ₀φ₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (φ₀.prod φ₀)
  int_ηη₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η.prod η₀)
  int_φφ₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (φ.prod φ₀)
  int_ηφ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η.prod φ)
  int_ηφ₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η.prod φ₀)
  int_η₀φ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η₀.prod φ)
  int_η₀φ₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (η₀.prod φ₀)

/-- The exact identity
`I(σ)+I(τ)+I(σ,τ) = ½ I(σ) + ½ I(τ) + ½ I(σ+τ)`, where `I(σ+τ)` is the pair
difference of the mass-`(|η|+|φ|)` measures `η+φ` and `η₀+φ₀`. -/
theorem l6QuadraticRemainder_eq_half_sum {η η₀ φ φ₀ : Measure ℂ}
    (h : L6FourMeasureData η η₀ φ φ₀) :
    l6QuadraticRemainder η η₀ φ φ₀ =
      (1 / 2 : ℝ) * l6PairDifference η η₀ + (1 / 2 : ℝ) * l6PairDifference φ φ₀ +
        (1 / 2 : ℝ) * l6PairDifference (η + φ) (η₀ + φ₀) := by
  have := h.fin_η
  have := h.fin_η₀
  have := h.fin_φ
  have := h.fin_φ₀
  have iφη := integrable_kernel_swap h.int_ηφ
  have iφ₀η₀ := integrable_kernel_swap h.int_η₀φ₀
  have iφη₀ := integrable_kernel_swap h.int_η₀φ
  have iφ₀η := integrable_kernel_swap h.int_ηφ₀
  have e1 : li2LogInteraction (η + φ) (η + φ) =
      li2LogInteraction η η + li2LogInteraction η φ +
        (li2LogInteraction φ η + li2LogInteraction φ φ) := by
    rw [li2LogInteraction_add_left (integrable_kernel_add_right h.int_ηη h.int_ηφ)
        (integrable_kernel_add_right iφη h.int_φφ),
      li2LogInteraction_add_right h.int_ηη h.int_ηφ,
      li2LogInteraction_add_right iφη h.int_φφ]
  have e2 : li2LogInteraction (η₀ + φ₀) (η₀ + φ₀) =
      li2LogInteraction η₀ η₀ + li2LogInteraction η₀ φ₀ +
        (li2LogInteraction φ₀ η₀ + li2LogInteraction φ₀ φ₀) := by
    rw [li2LogInteraction_add_left (integrable_kernel_add_right h.int_η₀η₀ h.int_η₀φ₀)
        (integrable_kernel_add_right iφ₀η₀ h.int_φ₀φ₀),
      li2LogInteraction_add_right h.int_η₀η₀ h.int_η₀φ₀,
      li2LogInteraction_add_right iφ₀η₀ h.int_φ₀φ₀]
  have e3 : li2LogInteraction (η + φ) (η₀ + φ₀) =
      li2LogInteraction η η₀ + li2LogInteraction η φ₀ +
        (li2LogInteraction φ η₀ + li2LogInteraction φ φ₀) := by
    rw [li2LogInteraction_add_left (integrable_kernel_add_right h.int_ηη₀ h.int_ηφ₀)
        (integrable_kernel_add_right iφη₀ h.int_φφ₀),
      li2LogInteraction_add_right h.int_ηη₀ h.int_ηφ₀,
      li2LogInteraction_add_right iφη₀ h.int_φφ₀]
  have c1 := li2LogInteraction_comm φ η
  have c2 := li2LogInteraction_comm φ₀ η₀
  have c3 := li2LogInteraction_comm φ η₀
  unfold l6QuadraticRemainder l6PairDifference
  rw [e1, e2, e3, c1, c2, c3]
  ring

/-- **The three applications of L6** (σ, τ, σ+τ) give the nonnegativity of
the quadratic remainder in `lem:dual-lower`. -/
theorem l6QuadraticRemainder_nonneg {η η₀ φ φ₀ : Measure ℂ}
    (h : L6FourMeasureData η η₀ φ φ₀) : 0 ≤ l6QuadraticRemainder η η₀ φ φ₀ := by
  have := h.fin_η
  have := h.fin_η₀
  have := h.fin_φ
  have := h.fin_φ₀
  have iφη := integrable_kernel_swap h.int_ηφ
  have iφ₀η₀ := integrable_kernel_swap h.int_η₀φ₀
  have iφη₀ := integrable_kernel_swap h.int_η₀φ
  have p1 : 0 ≤ l6PairDifference η η₀ :=
    l6FiniteLogPairDifference_nonneg_of_atomless η η₀ h.mass_η h.atomless_η h.atomless_η₀
      h.int_ηη h.int_η₀η₀ h.int_ηη₀
  have p2 : 0 ≤ l6PairDifference φ φ₀ :=
    l6FiniteLogPairDifference_nonneg_of_atomless φ φ₀ h.mass_φ h.atomless_φ h.atomless_φ₀
      h.int_φφ h.int_φ₀φ₀ h.int_φφ₀
  have hmass : (η + φ) univ = (η₀ + φ₀) univ := by
    simp only [Measure.coe_add, Pi.add_apply, h.mass_η, h.mass_φ]
  have p3 : 0 ≤ l6PairDifference (η + φ) (η₀ + φ₀) :=
    l6FiniteLogPairDifference_nonneg_of_atomless (η + φ) (η₀ + φ₀) hmass
      (fun z => by simp [h.atomless_η z, h.atomless_φ z])
      (fun z => by simp [h.atomless_η₀ z, h.atomless_φ₀ z])
      (integrable_kernel_add_left (integrable_kernel_add_right h.int_ηη h.int_ηφ)
        (integrable_kernel_add_right iφη h.int_φφ))
      (integrable_kernel_add_left (integrable_kernel_add_right h.int_η₀η₀ h.int_η₀φ₀)
        (integrable_kernel_add_right iφ₀η₀ h.int_φ₀φ₀))
      (integrable_kernel_add_left (integrable_kernel_add_right h.int_ηη₀ h.int_ηφ₀)
        (integrable_kernel_add_right iφη₀ h.int_φφ₀))
  rw [l6QuadraticRemainder_eq_half_sum h]
  have := add_nonneg (add_nonneg p1 p2) p3
  linarith

/-- The quadratic part of `eq:contour-energy`, `I(η)+I(μ)+I(η,μ⁻)`, written on
the common plane (`φ = μ⁻`).  Reflection invariance `I(μ) = I(μ⁻)` is
`li2LogInteraction_reflect` in the admissible layer. -/
def l6EnergyQuadratic (η φ : Measure ℂ) : ℝ :=
  li2LogInteraction η η + li2LogInteraction φ φ + li2LogInteraction η φ

/-- The common-plane value `Q_log = -(I(η₀)+I(μ₀)+I(η₀,μ₀⁻))` of `sec-dual`. -/
def l6QLog (η₀ φ₀ : Measure ℂ) : ℝ :=
  -(li2LogInteraction η₀ η₀ + li2LogInteraction φ₀ φ₀ + li2LogInteraction η₀ φ₀)

/-- Linearization in the exact normalization of `lem:dual-lower`:
the energy quadratic is at least `Q_log` plus the first variations
`2 I(η,η₀) + I(η,φ₀)` and `2 I(φ,φ₀) + I(η₀,φ)`. -/
theorem l6EnergyQuadratic_ge_linearization {η η₀ φ φ₀ : Measure ℂ}
    (h : L6FourMeasureData η η₀ φ φ₀) :
    l6QLog η₀ φ₀ + (2 * li2LogInteraction η η₀ + li2LogInteraction η φ₀) +
        (2 * li2LogInteraction φ φ₀ + li2LogInteraction η₀ φ) ≤
      l6EnergyQuadratic η φ := by
  have hQ := l6QuadraticRemainder_nonneg h
  unfold l6QuadraticRemainder l6PairDifference at hQ
  unfold l6QLog l6EnergyQuadratic
  linarith

/-- Logarithmic potential `L_σ(z) = ∫ log|z-w| dσ(w)` of `sec-dual`. -/
def l6LogPotential (σ : Measure ℂ) (z : ℂ) : ℝ :=
  ∫ w, Real.log ‖z - w‖ ∂σ

/-- Fubini: `I(μ,ν) = -∫ L_ν dμ`. -/
theorem li2LogInteraction_eq_neg_integral_potential {μ ν : Measure ℂ} [SFinite μ]
    [SFinite ν] (h : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    li2LogInteraction μ ν = -∫ z, l6LogPotential ν z ∂μ := by
  unfold li2LogInteraction l6LogPotential
  rw [integral_prod _ h, ← integral_neg]
  congr 1
  funext z
  rw [← integral_neg]
  rfl

theorem integrable_potential {μ ν : Measure ℂ} [SFinite μ] [SFinite ν]
    (h : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) : Integrable (l6LogPotential ν) μ := by
  have h' := h.integral_prod_left.neg
  refine h'.congr ?_
  filter_upwards with z
  unfold l6LogPotential
  simp only [Pi.neg_apply]
  rw [← integral_neg]
  simp [li2LogKernel]

/-- `lem:dual-lower`, quadratic step, potential form:
`I(η)+I(μ)+I(η,μ⁻) ≥ Q_log + ∫(-2L_{η₀} - L_{μ₀⁻}) dη + ∫(-2L_{μ₀⁻} - L_{η₀}) dμ⁻`. -/
theorem l6EnergyQuadratic_ge_potential_form {η η₀ φ φ₀ : Measure ℂ}
    (h : L6FourMeasureData η η₀ φ φ₀) :
    l6QLog η₀ φ₀ +
        (∫ z, (-2 * l6LogPotential η₀ z - l6LogPotential φ₀ z) ∂η) +
        (∫ z, (-2 * l6LogPotential φ₀ z - l6LogPotential η₀ z) ∂φ) ≤
      l6EnergyQuadratic η φ := by
  have := h.fin_η
  have := h.fin_η₀
  have := h.fin_φ
  have := h.fin_φ₀
  have iφη₀ := integrable_kernel_swap h.int_η₀φ
  have hη : (∫ z, (-2 * l6LogPotential η₀ z - l6LogPotential φ₀ z) ∂η) =
      2 * li2LogInteraction η η₀ + li2LogInteraction η φ₀ := by
    rw [integral_sub ((integrable_potential h.int_ηη₀).const_mul (-2))
        (integrable_potential h.int_ηφ₀), integral_const_mul,
      li2LogInteraction_eq_neg_integral_potential h.int_ηη₀,
      li2LogInteraction_eq_neg_integral_potential h.int_ηφ₀]
    ring
  have hφ : (∫ z, (-2 * l6LogPotential φ₀ z - l6LogPotential η₀ z) ∂φ) =
      2 * li2LogInteraction φ φ₀ + li2LogInteraction η₀ φ := by
    rw [integral_sub ((integrable_potential h.int_φφ₀).const_mul (-2))
        (integrable_potential iφη₀), integral_const_mul,
      li2LogInteraction_eq_neg_integral_potential h.int_φφ₀,
      li2LogInteraction_comm η₀ φ,
      li2LogInteraction_eq_neg_integral_potential iφη₀]
    ring
  rw [hη, hφ]
  exact l6EnergyQuadratic_ge_linearization h

end

end L6Variations
end P0
end Li2Lean
