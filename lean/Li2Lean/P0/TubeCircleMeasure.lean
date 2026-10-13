/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeCircle

open MeasureTheory Filter

namespace Li2Lean.P0

noncomputable section

/-- Unnormalized angular Lebesgue measure for v10 circle smoothing. -/
def circleAngleMeasure : Measure ℝ :=
  volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))

instance circleAngleMeasure_finite : IsFiniteMeasure circleAngleMeasure := by
  unfold circleAngleMeasure
  infer_instance

instance circleAngleMeasure_nullSingleton : NullSingletonClass circleAngleMeasure := by
  unfold circleAngleMeasure
  infer_instance

@[simp]
theorem circleAngleMeasure_mass : circleAngleMeasure.real Set.univ = 2 * Real.pi := by
  simp [circleAngleMeasure, Measure.real, Real.pi_nonneg]

/-- Continuity of the literal v10 circle parametrization. -/
theorem continuous_circlePoint (z : ℂ) (r : ℝ) : Continuous (circlePoint z r) := by
  have heq : circlePoint z r = circleMap z r :=
    funext (ContourKit.p0CirclePoint_eq_circleMap z r)
  rw [heq]
  exact continuous_circleMap z r

/-- Measurability of the finite-valued log kernel, including its finite
convention at zero; actual singularities will have measure zero. -/
theorem measurable_realLogKernel : Measurable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) := by
  unfold realLogKernel
  fun_prop

/-- Every one-circle logarithmic slice is absolutely integrable, even when
its pole lies on the circle. -/
theorem integrable_realLogKernel_circlePoint (x z : ℂ) (r : ℝ) :
    Integrable (fun t : ℝ => realLogKernel x (circlePoint z r t)) circleAngleMeasure := by
  have h := (circleIntegrable_log_norm_sub_const (a := x) (c := z) r).1.neg
  change Integrable (fun t : ℝ => -Real.log ‖circleMap z r t - x‖)
    (volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))) at h
  simpa only [circleAngleMeasure, realLogKernel, IntegrableOn, Pi.neg_apply,
    ContourKit.p0CirclePoint_eq_circleMap, norm_sub_rev] using h

/-- Exact one-circle potential for the angular measure. -/
theorem integral_realLogKernel_circlePoint (x z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ t, realLogKernel x (circlePoint z r t) ∂circleAngleMeasure) =
      -(Real.log (max r ‖x - z‖) * (2 * Real.pi)) := by
  have h := g_l7_circle_average x z r hr
  change (∫ t in (0 : ℝ)..(2 * Real.pi),
    Real.log ‖x - circlePoint z r t‖) / (2 * Real.pi) =
      Real.log (max r ‖x - z‖) at h
  rw [div_eq_iff (mul_ne_zero two_ne_zero Real.pi_ne_zero)] at h
  simpa only [realLogKernel, integral_neg, intervalIntegral.integral_neg,
    intervalIntegral.integral_of_le Real.two_pi_pos.le, circleAngleMeasure] using
    congrArg Neg.neg h

/-- Uniform distance bound for two circle points. -/
theorem circlePoint_sub_norm_le (z w : ℂ) {r : ℝ} (hr : 0 < r) (u v : ℝ) :
    ‖circlePoint z r u - circlePoint w r v‖ ≤ ‖z - w‖ + 2 * r := by
  have hzu : ‖circlePoint z r u - z‖ = r := by
    simp [ContourKit.p0CirclePoint_eq_circleMap, abs_of_pos hr]
  have hwv : ‖w - circlePoint w r v‖ = r := by
    rw [norm_sub_rev]
    simp [ContourKit.p0CirclePoint_eq_circleMap, abs_of_pos hr]
  have hdecomp : circlePoint z r u - circlePoint w r v =
      (circlePoint z r u - z) + (z - w) + (w - circlePoint w r v) := by ring
  rw [hdecomp]
  calc
    ‖(circlePoint z r u - z) + (z - w) + (w - circlePoint w r v)‖ ≤
        ‖circlePoint z r u - z‖ + ‖z - w‖ + ‖w - circlePoint w r v‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖z - w‖ + 2 * r := by rw [hzu, hwv]; ring

/-- A uniform L1 estimate on every slice of the double-circle log kernel.
This supplies absolute integrability at intersecting and coincident circles. -/
theorem integral_norm_circle_kernel_le (z w : ℂ) {r : ℝ} (hr : 0 < r) (u : ℝ) :
    (∫ v, ‖realLogKernel (circlePoint z r u) (circlePoint w r v)‖ ∂circleAngleMeasure) ≤
      (2 * Real.pi) * (2 * (‖z - w‖ + 2 * r) - Real.log r) := by
  let D : ℝ := ‖z - w‖ + 2 * r
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hslice := integrable_realLogKernel_circlePoint (circlePoint z r u) w r
  have hpoint (v : ℝ) :
      ‖realLogKernel (circlePoint z r u) (circlePoint w r v)‖ ≤
        2 * D + realLogKernel (circlePoint z r u) (circlePoint w r v) := by
    have hlog : Real.log ‖circlePoint z r u - circlePoint w r v‖ ≤ D :=
      (Real.log_le_self (norm_nonneg _)).trans (circlePoint_sub_norm_le z w hr u v)
    rw [realLogKernel, Real.norm_eq_abs]
    apply abs_le.mpr
    constructor <;> linarith
  calc
    (∫ v, ‖realLogKernel (circlePoint z r u) (circlePoint w r v)‖ ∂circleAngleMeasure) ≤
        ∫ v, (2 * D + realLogKernel (circlePoint z r u) (circlePoint w r v))
          ∂circleAngleMeasure :=
      integral_mono hslice.norm ((integrable_const (2 * D)).add hslice) hpoint
    _ = (2 * Real.pi) *
        (2 * D - Real.log (max r ‖circlePoint z r u - w‖)) := by
      rw [integral_add (integrable_const (2 * D)) hslice,
        integral_const, circleAngleMeasure_mass,
        integral_realLogKernel_circlePoint (circlePoint z r u) w hr]
      simp only [smul_eq_mul]
      ring
    _ ≤ (2 * Real.pi) * (2 * D - Real.log r) := by
      apply mul_le_mul_of_nonneg_left _ Real.two_pi_pos.le
      exact sub_le_sub_left (Real.log_le_log hr (le_max_left _ _)) _

/-- The full double-circle log kernel is absolutely integrable. There is no
separation or distinct-center hypothesis, and no Fubini premise is assumed. -/
theorem integrable_circle_kernel_prod (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    Integrable
      (fun p : ℝ × ℝ => realLogKernel (circlePoint z r p.1) (circlePoint w r p.2))
      (circleAngleMeasure.prod circleAngleMeasure) := by
  have hmeas : AEStronglyMeasurable
      (fun p : ℝ × ℝ => realLogKernel (circlePoint z r p.1) (circlePoint w r p.2))
      (circleAngleMeasure.prod circleAngleMeasure) := by
    apply Measurable.aestronglyMeasurable
    exact measurable_realLogKernel.comp
      (((continuous_circlePoint z r).measurable.comp measurable_fst).prodMk
        ((continuous_circlePoint w r).measurable.comp measurable_snd))
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · exact ae_of_all _ (fun u => integrable_realLogKernel_circlePoint (circlePoint z r u) w r)
  · apply (integrable_const ((2 * Real.pi) *
      (2 * (‖z - w‖ + 2 * r) - Real.log r))).mono' hmeas.norm.integral_prod_right'
    apply ae_of_all
    intro u
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    exact integral_norm_circle_kernel_le z w hr u

/-- The paper's probability arclength measure `σ_{z,r}`, defined as the
normalized pushforward of angular Lebesgue measure under the literal circle
parametrization. -/
def circleProbability (z : ℂ) (r : ℝ) : Measure ℂ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) •
    Measure.map (circlePoint z r) circleAngleMeasure

instance circleProbability_probability (z : ℂ) (r : ℝ) :
    IsProbabilityMeasure (circleProbability z r) := by
  constructor
  simp only [circleProbability, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_circlePoint z r).measurable MeasurableSet.univ,
    Set.preimage_univ, circleAngleMeasure, Measure.restrict_apply_univ,
    Real.volume_Ioc, sub_zero]
  rw [← ENNReal.ofReal_mul (inv_nonneg.mpr Real.two_pi_pos.le),
    inv_mul_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
  simp

/-- The smoothed probability is supported on the radius-`r` circle. -/
theorem circleProbability_outside_sphere (z : ℂ) {r : ℝ} (hr : 0 < r) :
    circleProbability z r (Metric.sphere z r)ᶜ = 0 := by
  have hpre : (circlePoint z r) ⁻¹' (Metric.sphere z r)ᶜ = ∅ := by
    ext t
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_empty_iff_false,
      iff_false, not_not]
    rw [ContourKit.p0CirclePoint_eq_circleMap]
    exact circleMap_mem_sphere z hr.le t
  simp only [circleProbability, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_circlePoint z r).measurable Metric.isClosed_sphere.measurableSet.compl,
    hpre, measure_empty, mul_zero]

/-- Absolute integrability of the actual probability-circle product energy.
This includes intersecting circles and equal centers. -/
theorem integrable_realLogKernel_circleProbability_prod (z w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2)
      ((circleProbability z r).prod (circleProbability w r)) := by
  have hmap : Measurable (Prod.map (circlePoint z r) (circlePoint w r)) :=
    (continuous_circlePoint z r).measurable.prodMap (continuous_circlePoint w r).measurable
  simp only [circleProbability, Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.map_prod_map circleAngleMeasure circleAngleMeasure
    (continuous_circlePoint z r).measurable (continuous_circlePoint w r).measurable]
  apply (integrable_map_measure measurable_realLogKernel.aestronglyMeasurable hmap.aemeasurable).mpr
  exact integrable_circle_kernel_prod z w hr

/-- Fubini identifies the angular product integral with the literal pair
energy. All absolute integrability premises are discharged above. -/
theorem integral_circle_kernel_prod_eq (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ p : ℝ × ℝ,
      realLogKernel (circlePoint z r p.1) (circlePoint w r p.2)
      ∂(circleAngleMeasure.prod circleAngleMeasure)) / (2 * Real.pi) ^ 2 =
      circlePairEnergy z w r := by
  rw [integral_prod _ (integrable_circle_kernel_prod z w hr)]
  simp only [circlePairEnergy, intervalIntegral.integral_of_le Real.two_pi_pos.le,
    circleAngleMeasure]

/-- Exact semantic adapter from the actual circle-probability product energy
in v10 to `circlePairEnergy`; no integrability assumption is left to callers. -/
theorem integral_realLogKernel_circleProbability_prod_eq (z w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleProbability z r).prod (circleProbability w r))) =
      circlePairEnergy z w r := by
  have hmap : Measurable (Prod.map (circlePoint z r) (circlePoint w r)) :=
    (continuous_circlePoint z r).measurable.prodMap (continuous_circlePoint w r).measurable
  simp only [circleProbability, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le), smul_eq_mul]
  rw [Measure.map_prod_map circleAngleMeasure circleAngleMeasure
    (continuous_circlePoint z r).measurable (continuous_circlePoint w r).measurable,
    integral_map_of_stronglyMeasurable hmap measurable_realLogKernel.stronglyMeasurable]
  simp only [Prod.map]
  have h := integral_circle_kernel_prod_eq z w hr
  convert h using 1
  ring

/-- Exact self-energy of the actual probability-circle measure. -/
theorem circleProbability_self_energy (z : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleProbability z r).prod (circleProbability z r))) = Real.log (1 / r) := by
  rw [integral_realLogKernel_circleProbability_prod_eq z z hr, circlePairEnergy_self z hr]

/-- The actual double-circle interaction upper bound, with no separation
condition even when the two support circles intersect. -/
theorem circleProbability_pair_energy_le (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleProbability z r).prod (circleProbability w r))) ≤
        -Real.log (max r ‖z - w‖) := by
  rw [integral_realLogKernel_circleProbability_prod_eq z w hr]
  exact circlePairEnergy_le_neg_log_max z w hr

/-- Circle probabilities of positive radius have no atoms. This justifies
ignoring the finite-valued logarithm's convention on the geometric diagonal. -/
theorem circleProbability_nullSingleton (z : ℂ) {r : ℝ} (hr : 0 < r) :
    NullSingletonClass (circleProbability z r) := by
  constructor
  intro x
  have hcount : ((circlePoint z r) ⁻¹' {x}).Countable := by
    have heq : circlePoint z r = circleMap z r :=
      funext (ContourKit.p0CirclePoint_eq_circleMap z r)
    rw [heq]
    exact (Set.countable_singleton x).preimage_circleMap z hr.ne'
  simp only [circleProbability, Measure.smul_apply, smul_eq_mul,
    Measure.map_apply (continuous_circlePoint z r).measurable (measurableSet_singleton x),
    hcount.measure_zero circleAngleMeasure, mul_zero]

/-- The possible pointwise collisions in two circles form a null set for the
actual product probability measure, including equal or intersecting circles. -/
theorem circleProbability_prod_diagonal_null (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    ((circleProbability z r).prod (circleProbability w r))
      {p : ℂ × ℂ | p.1 = p.2} = 0 := by
  let := circleProbability_nullSingleton w hr
  apply Measure.measure_prod_null_of_ae_null
    (isClosed_eq continuous_fst continuous_snd).measurableSet
  apply ae_of_all
  intro x
  simp [Set.preimage]

/-- The actual circle interaction agrees almost everywhere with the
collision-faithful extended kernel from v10. -/
theorem extendedLogKernel_circleProbability_ae_eq (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    (fun p : ℂ × ℂ => extendedLogKernel p.1 p.2) =ᵐ[
      (circleProbability z r).prod (circleProbability w r)]
    (fun p : ℂ × ℂ => (realLogKernel p.1 p.2 : WithTop ℝ)) := by
  have hne : ∀ᵐ p : ℂ × ℂ ∂((circleProbability z r).prod (circleProbability w r)),
      p.1 ≠ p.2 := by
    rw [ae_iff]
    simpa only [not_not] using circleProbability_prod_diagonal_null z w hr
  filter_upwards [hne] with p hp
  exact extendedLogKernel_eq_real_of_ne hp

/-- The exact smoothed empirical contour measure in v10 `sec-tube`:
`ν_r = m⁻¹ ∑_{a=1}^d σ_{z_a,r}`. -/
def circleEmpiricalMeasure {d : ℕ} (z : Fin d → ℂ) (r : ℝ) (m : ℕ) : Measure ℂ :=
  ENNReal.ofReal ((m : ℝ)⁻¹) • Measure.sum (fun i : Fin d => circleProbability (z i) r)

instance circleEmpiricalMeasure_finite {d : ℕ} (z : Fin d → ℂ) (r : ℝ) (m : ℕ) :
    IsFiniteMeasure (circleEmpiricalMeasure z r m) := by
  unfold circleEmpiricalMeasure
  exact Measure.smul_finite _ ENNReal.ofReal_ne_top

/-- The empirical smoothing measure has finite absolute logarithmic
self-energy, with no distinctness or separation condition on the centers. -/
theorem integrable_realLogKernel_circleEmpiricalMeasure_prod {d : ℕ}
    (z : Fin d → ℂ) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2)
      ((circleEmpiricalMeasure z r m).prod (circleEmpiricalMeasure z r m)) := by
  simp only [circleEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.prod_sum, Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  exact integrable_realLogKernel_circleProbability_prod (z ij.1) (z ij.2) hr

/-- Exact finite-sum energy expansion for the actual v10 empirical smoothing
measure, obtained with discharged product-integrability premises. -/
theorem circleEmpiricalMeasure_energy_eq {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleEmpiricalMeasure z r m).prod (circleEmpiricalMeasure z r m))) =
        (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) / (m : ℝ) ^ 2 := by
  simp only [circleEmpiricalMeasure, Measure.prod_smul_left, Measure.prod_smul_right,
    integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m)), smul_eq_mul]
  rw [Measure.prod_sum, Measure.sum_fintype,
    integral_finsetSum_measure (fun ij _ =>
      integrable_realLogKernel_circleProbability_prod (z ij.1) (z ij.2) hr)]
  simp_rw [integral_realLogKernel_circleProbability_prod_eq _ _ hr]
  rw [Fintype.sum_prod_type]
  ring

/-- The literal measure-energy statement of v10 `eq:tube-circle` for the
actual smoothed empirical measure. Distinct centers are used only for the
finite-valued point kernel; the collision branch is retained below. -/
theorem circleEmpiricalMeasure_energy_transfer {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (hz : ∀ i j, i ≠ j → z i ≠ z j) (m : ℕ) :
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else realLogKernel (z i) (z j)) / (m : ℝ) ^ 2 ≥
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleEmpiricalMeasure z r m).prod (circleEmpiricalMeasure z r m))) -
        (d : ℝ) / (m : ℝ) ^ 2 * Real.log (1 / r) := by
  rw [circleEmpiricalMeasure_energy_eq z hr m]
  exact finite_configuration_transfer_normalized z hr hz m

/-- The full v10 finite-configuration split with the actual empirical
measure: colliding centers have zero Vandermonde weight. -/
theorem circleEmpiricalMeasure_energy_collision_split {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    vandermondeSq d z = 0 ∨
      (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else realLogKernel (z i) (z j)) / (m : ℝ) ^ 2 ≥
      (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
        ∂((circleEmpiricalMeasure z r m).prod (circleEmpiricalMeasure z r m))) -
          (d : ℝ) / (m : ℝ) ^ 2 * Real.log (1 / r) := by
  rcases l7_collision_split d z r hr with hzero | ⟨hz, htransfer⟩
  · exact Or.inl hzero
  · exact Or.inr (circleEmpiricalMeasure_energy_transfer z hr hz m)

/-- The exact total mass `d/m` of the empirical circle measure. -/
theorem circleEmpiricalMeasure_mass {d : ℕ} (z : Fin d → ℂ) (r : ℝ) (m : ℕ) :
    (circleEmpiricalMeasure z r m).real Set.univ = (d : ℝ) / (m : ℝ) := by
  simp [circleEmpiricalMeasure, Measure.real,
    ENNReal.toReal_mul, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m)),
    div_eq_mul_inv, mul_comm]

/-- A circle centered on the manuscript contour is contained in its tube. -/
theorem circleProbability_outside_tube_of_mem {z : ℂ} (hz : z ∈ Gamma)
    {r : ℝ} (hr : 0 < r) : circleProbability z r (tube r)ᶜ = 0 := by
  apply measure_mono_null _ (circleProbability_outside_sphere z hr)
  intro x hx hxs
  apply hx
  change Metric.infDist x Gamma ≤ r
  calc
    Metric.infDist x Gamma ≤ dist x z := Metric.infDist_le_dist_of_mem hz
    _ = r := hxs

/-- The actual empirical smoothing measure is supported in `T_r`, preserving
v10's contour support condition without requiring separated circles. -/
theorem circleEmpiricalMeasure_outside_tube {d : ℕ} (z : Fin d → ℂ)
    (hz : ∀ i, z i ∈ Gamma) {r : ℝ} (hr : 0 < r) (m : ℕ) :
    circleEmpiricalMeasure z r m (tube r)ᶜ = 0 := by
  have hmeas : MeasurableSet (tube r)ᶜ :=
    (isClosed_le (Metric.continuous_infDist_pt Gamma) continuous_const).measurableSet.compl
  have hzero (i : Fin d) : circleProbability (z i) r (tube r)ᶜ = 0 :=
    circleProbability_outside_tube_of_mem (hz i) hr
  unfold circleEmpiricalMeasure
  rw [Measure.smul_apply, Measure.sum_apply _ hmeas]
  simp only [hzero, tsum_zero, smul_zero]

/-- The finite empirical smoothing measure remains atomless, so the
collision-faithful logarithmic kernel has the same almost-everywhere values. -/
theorem circleEmpiricalMeasure_nullSingleton {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    NullSingletonClass (circleEmpiricalMeasure z r m) := by
  constructor
  intro x
  have hzero (i : Fin d) : circleProbability (z i) r {x} = 0 :=
    (circleProbability_nullSingleton (z i) hr).measure_singleton x
  unfold circleEmpiricalMeasure
  rw [Measure.smul_apply, Measure.sum_apply _ (measurableSet_singleton x)]
  simp only [hzero, tsum_zero, smul_zero]

/-- Compact support of the literal smoothed empirical measure, also valid
for the empty configuration. This is the compactness premise needed by L6. -/
theorem circleEmpiricalMeasure_compact_support {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    ∃ K : Set ℂ, IsCompact K ∧ circleEmpiricalMeasure z r m Kᶜ = 0 := by
  let K : Set ℂ := ⋃ i : Fin d, Metric.sphere (z i) r
  have hK : IsCompact K := isCompact_iUnion (fun i => isCompact_sphere (z i) r)
  refine ⟨K, hK, ?_⟩
  have hzero (i : Fin d) : circleProbability (z i) r Kᶜ = 0 := by
    apply measure_mono_null _ (circleProbability_outside_sphere (z i) hr)
    exact Set.compl_subset_compl.mpr
      (Set.subset_iUnion (fun j : Fin d => Metric.sphere (z j) r) i)
  unfold circleEmpiricalMeasure
  rw [Measure.smul_apply, Measure.sum_apply _ hK.isClosed.measurableSet.compl]
  simp only [hzero, tsum_zero, smul_zero]

/-- The exact empirical energy expansion stated in the existing L6
`li2LogInteraction` vocabulary, with the same kernel and normalization. -/
theorem circleEmpiricalMeasure_li2LogInteraction_eq {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (m : ℕ) :
    li2LogInteraction (circleEmpiricalMeasure z r m) (circleEmpiricalMeasure z r m) =
      (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) / (m : ℝ) ^ 2 := by
  exact circleEmpiricalMeasure_energy_eq z hr m

end
end Li2Lean.P0
