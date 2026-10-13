/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeCircleMeasure
import Mathlib.Probability.Distributions.Cauchy
import Mathlib.MeasureTheory.Function.JacobianOneDim

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace Li2Lean.P0

noncomputable section

/-- Probability angular measure used by the actual circle smoothing. -/
def circleAngleProbability : Measure ℝ :=
  ENNReal.ofReal ((2 * Real.pi)⁻¹) • circleAngleMeasure

/-- The real boundary coordinate of the disk-to-upper-half-plane map
`a + i*b*(1+u)/(1-u)`. On `(0,2*pi)` this is `a-b*cot(theta/2)`. -/
def cauchyCircleBoundary (a : ℝ) (b : ℝ≥0) (θ : ℝ) : ℝ :=
  a + (b : ℝ) * Real.tan (θ / 2 - Real.pi / 2)

/-- The increasing inverse angular coordinate for the Cauchy boundary map. -/
def cauchyCircleAngle (a : ℝ) (b : ℝ≥0) (x : ℝ) : ℝ :=
  Real.pi + 2 * Real.arctan ((x - a) / (b : ℝ))

theorem measurable_cauchyCircleBoundary (a : ℝ) (b : ℝ≥0) :
    Measurable (cauchyCircleBoundary a b) := by
  unfold cauchyCircleBoundary
  simp only [Real.tan_eq_sin_div_cos]
  fun_prop

theorem continuous_cauchyCircleAngle (a : ℝ) (b : ℝ≥0) :
    Continuous (cauchyCircleAngle a b) := by
  unfold cauchyCircleAngle
  fun_prop

/-- The Jacobian of the inverse coordinate is exactly `2*pi` times the
existing Mathlib Cauchy density, with its original scale normalization. -/
theorem hasDerivAt_cauchyCircleAngle (a : ℝ) {b : ℝ≥0} (hb : 0 < b) (x : ℝ) :
    HasDerivAt (cauchyCircleAngle a b)
      ((2 * Real.pi) * cauchyPDFReal a b x) x := by
  have h := (((Real.hasDerivAt_arctan' ((x - a) / (b : ℝ))).comp x
    (((hasDerivAt_id x).sub_const a).div_const (b : ℝ))).const_mul 2).const_add Real.pi
  convert h using 1
  · rfl
  · rw [cauchyPDFReal_def']
    simp only [NNReal.coe_inv, one_div]
    field_simp

/-- The real boundary map is a left inverse of the angular coordinate. -/
theorem cauchyCircleBoundary_angle (a : ℝ) {b : ℝ≥0} (hb : 0 < b) (x : ℝ) :
    cauchyCircleBoundary a b (cauchyCircleAngle a b x) = x := by
  have hb' : (b : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < b from hb)
  unfold cauchyCircleBoundary cauchyCircleAngle
  have hangle : (Real.pi + 2 * Real.arctan ((x - a) / (b : ℝ))) / 2 - Real.pi / 2 =
      Real.arctan ((x - a) / (b : ℝ)) := by ring
  rw [hangle, Real.tan_arctan]
  field_simp
  ring

/-- The angular coordinate is a right inverse on the open fundamental interval. -/
theorem cauchyCircleAngle_boundary (a : ℝ) {b : ℝ≥0} (hb : 0 < b) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    cauchyCircleAngle a b (cauchyCircleBoundary a b θ) = θ := by
  have hb' : (b : ℝ) ≠ 0 := ne_of_gt (show (0 : ℝ) < b from hb)
  have hlo : -(Real.pi / 2) < θ / 2 - Real.pi / 2 := by linarith [hθ.1]
  have hhi : θ / 2 - Real.pi / 2 < Real.pi / 2 := by linarith [hθ.2]
  unfold cauchyCircleAngle cauchyCircleBoundary
  rw [add_sub_cancel_left, mul_div_cancel_left₀ _ hb', Real.arctan_tan hlo hhi]
  ring

/-- The inverse coordinate has exactly the open full angular interval as its
range; the omitted endpoints have zero angular measure. -/
theorem range_cauchyCircleAngle (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    Set.range (cauchyCircleAngle a b) = Set.Ioo (0 : ℝ) (2 * Real.pi) := by
  ext θ
  constructor
  · rintro ⟨x, rfl⟩
    constructor
    · have h := Real.neg_pi_div_two_lt_arctan ((x - a) / (b : ℝ))
      dsimp [cauchyCircleAngle]
      linarith
    · have h := Real.arctan_lt_pi_div_two ((x - a) / (b : ℝ))
      dsimp [cauchyCircleAngle]
      linarith
  · intro hθ
    exact ⟨cauchyCircleBoundary a b θ, cauchyCircleAngle_boundary a hb hθ⟩

/-- The angular inverse pushes the actual Mathlib Cauchy law to normalized
angular Lebesgue measure. This is an unconditional Jacobian computation. -/
theorem map_cauchyCircleAngle (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    Measure.map (cauchyCircleAngle a b) (cauchyMeasure a b) = circleAngleProbability := by
  apply Measure.ext_of_lintegral
  intro f hf
  have hangle := (continuous_cauchyCircleAngle a b).measurable
  have hinj : Function.Injective (cauchyCircleAngle a b) :=
    (show Function.LeftInverse (cauchyCircleBoundary a b) (cauchyCircleAngle a b) from
      cauchyCircleBoundary_angle a hb).injective
  have hchange := lintegral_image_eq_lintegral_abs_deriv_mul
    (s := Set.univ) MeasurableSet.univ
    (fun x _ => (hasDerivAt_cauchyCircleAngle a hb x).hasDerivWithinAt) hinj.injOn f
  have habs (x : ℝ) : |(2 * Real.pi) * cauchyPDFReal a b x| =
      (2 * Real.pi) * cauchyPDFReal a b x :=
    abs_of_nonneg (mul_nonneg Real.two_pi_pos.le (cauchyPDF_pos a hb.ne' x).le)
  simp_rw [habs, ENNReal.ofReal_mul Real.two_pi_pos.le, ← cauchyPDF_def, mul_assoc] at hchange
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top] at hchange
  have hraw : (∫⁻ θ, f θ ∂circleAngleMeasure) = ENNReal.ofReal (2 * Real.pi) *
      ∫⁻ x, cauchyPDF a b x * f (cauchyCircleAngle a b x) := by
    simpa only [Set.image_univ, range_cauchyCircleAngle a hb,
      restrict_Ioo_eq_restrict_Ioc, Measure.restrict_univ, circleAngleMeasure] using hchange
  rw [lintegral_map hf hangle, cauchyMeasure_of_scale_ne_zero a hb.ne',
    lintegral_withDensity_eq_lintegral_mul volume (measurable_cauchyPDF a b)
      (show Measurable (fun x => f (cauchyCircleAngle a b x)) from hf.comp hangle)]
  rw [circleAngleProbability, lintegral_smul_measure, hraw, smul_eq_mul, ← mul_assoc]
  have hnorm : ENNReal.ofReal ((2 * Real.pi)⁻¹) * ENNReal.ofReal (2 * Real.pi) = 1 := by
    rw [← ENNReal.ofReal_mul (inv_nonneg.mpr Real.two_pi_pos.le),
      inv_mul_cancel₀ (mul_ne_zero two_ne_zero Real.pi_ne_zero)]
    simp
  rw [hnorm, one_mul]
  rfl

/-- The real boundary coordinate of the disk-to-half-plane map sends uniform
circle angles to the exact Cauchy measure, including its scale constant. -/
theorem map_cauchyCircleBoundary (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    Measure.map (cauchyCircleBoundary a b) circleAngleProbability = cauchyMeasure a b := by
  rw [← map_cauchyCircleAngle a hb,
    Measure.map_map (measurable_cauchyCircleBoundary a b) (continuous_cauchyCircleAngle a b).measurable]
  have heq : cauchyCircleBoundary a b ∘ cauchyCircleAngle a b = id := by
    funext x
    exact cauchyCircleBoundary_angle a hb x
  rw [heq, Measure.map_id]

/-- Actual boundary-map correspondence for every measurable target map; the
v10 `stripBoundaryPoint` is an immediate certified instance of this theorem. -/
theorem map_comp_cauchyCircleBoundary {β : Type*} [MeasurableSpace β]
    (B : ℝ → β) (hB : Measurable B) (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    Measure.map (fun θ => B (cauchyCircleBoundary a b θ)) circleAngleProbability =
      Measure.map B (cauchyMeasure a b) := by
  change Measure.map (B ∘ cauchyCircleBoundary a b) circleAngleProbability = _
  rw [← Measure.map_map hB (measurable_cauchyCircleBoundary a b), map_cauchyCircleBoundary a hb]

instance circleAngleProbability_isProbability : IsProbabilityMeasure circleAngleProbability := by
  rw [← map_cauchyCircleAngle (a := 0) (b := 1) (by norm_num)]
  infer_instance

instance circleAngleProbability_nullSingleton : NullSingletonClass circleAngleProbability := by
  constructor
  intro θ
  simp [circleAngleProbability, Measure.smul_apply]

/-- The two angular endpoints are excluded only on a zero-measure set. -/
theorem circleAngleProbability_ae_mem :
    ∀ᵐ θ ∂circleAngleProbability, θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi) := by
  rw [ae_iff]
  change circleAngleProbability (Set.Ioo (0 : ℝ) (2 * Real.pi))ᶜ = 0
  have hsub : (Set.Ioo (0 : ℝ) (2 * Real.pi))ᶜ ∩ Set.Ioc (0 : ℝ) (2 * Real.pi) ⊆
      {2 * Real.pi} := by
    intro θ hθ
    apply Set.mem_singleton_iff.mpr
    by_contra hne
    exact hθ.1 ⟨hθ.2.1, lt_of_le_of_ne hθ.2.2 hne⟩
  have hnull : volume ((Set.Ioo (0 : ℝ) (2 * Real.pi))ᶜ ∩
      Set.Ioc (0 : ℝ) (2 * Real.pi)) = 0 :=
    measure_mono_null hsub (measure_singleton _)
  simp only [circleAngleProbability, circleAngleMeasure, Measure.smul_apply,
    Measure.restrict_apply measurableSet_Ioo.compl, hnull, smul_zero]

/-- The preimage of the exceptional real point zero is angularly null for
positive Cauchy scale. -/
theorem cauchyCircleBoundary_ne_zero_ae (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    ∀ᵐ θ ∂circleAngleProbability, cauchyCircleBoundary a b θ ≠ 0 := by
  have hnull : cauchyMeasure a b {0} = 0 := by
    rw [cauchyMeasure_of_scale_ne_zero a hb.ne']
    exact measure_singleton _
  rw [← map_cauchyCircleBoundary a hb,
    Measure.map_apply (measurable_cauchyCircleBoundary a b) (measurableSet_singleton 0)] at hnull
  rw [ae_iff]
  simpa only [not_not, Set.preimage, Set.mem_singleton_iff] using hnull

/-- The boundary coordinate equals `a-b*cot(theta/2)` with the literal sine
and cosine quotient; this identity also respects totalization at the poles. -/
theorem cauchyCircleBoundary_eq_sub_cot (a : ℝ) (b : ℝ≥0) (θ : ℝ) :
    cauchyCircleBoundary a b θ = a - (b : ℝ) * Real.cos (θ / 2) / Real.sin (θ / 2) := by
  rw [cauchyCircleBoundary, Real.tan_eq_sin_div_cos,
    Real.sin_sub_pi_div_two, Real.cos_sub_pi_div_two]
  ring

/-- The normalized real integral form of the exact boundary correspondence. -/
theorem integral_cauchyCircleBoundary (f : ℝ → ℝ) (hf : Measurable f)
    (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    (∫ θ in (0 : ℝ)..(2 * Real.pi), f (cauchyCircleBoundary a b θ)) / (2 * Real.pi) =
      ∫ x, f x ∂cauchyMeasure a b := by
  rw [← map_cauchyCircleBoundary a hb,
    integral_map_of_stronglyMeasurable (measurable_cauchyCircleBoundary a b) hf.stronglyMeasurable]
  simp only [circleAngleProbability, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le), smul_eq_mul,
    circleAngleMeasure, intervalIntegral.integral_of_le Real.two_pi_pos.le]
  ring

/-- The disk-to-half-plane map with the same normalization as the interior
cover construction. The scale is nonnegative to match `cauchyMeasure`. -/
def cauchyDiskMap (a : ℝ) (b : ℝ≥0) (u : ℂ) : ℂ :=
  (a : ℂ) + Complex.I * (b : ℂ) * (1 + u) / (1 - u)

/-- Exact identification of the Möbius boundary with the real Cauchy variable,
away from the endpoint pole of the angular parametrization. -/
theorem cauchyDiskMap_exp_eq (a : ℝ) (b : ℝ≥0) {θ : ℝ}
    (hθ : θ ∈ Set.Ioo (0 : ℝ) (2 * Real.pi)) :
    cauchyDiskMap a b (Complex.exp (Complex.I * (θ : ℂ))) =
      (cauchyCircleBoundary a b θ : ℂ) := by
  have hspos : 0 < Real.sin (θ / 2) :=
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2])
  have hsne : (Real.sin (θ / 2) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hspos.ne'
  have hdouble : 2 * (θ / 2) = θ := by ring
  have hcos : Real.cos θ = 2 * Real.cos (θ / 2) ^ 2 - 1 := by
    simpa only [hdouble] using Real.cos_two_mul (θ / 2)
  have hsin : Real.sin θ = 2 * Real.sin (θ / 2) * Real.cos (θ / 2) := by
    simpa only [hdouble] using Real.sin_two_mul (θ / 2)
  have hexp : Complex.exp (Complex.I * (θ : ℂ)) =
      ((2 * Real.cos (θ / 2) ^ 2 - 1 : ℝ) : ℂ) +
        ((2 * Real.sin (θ / 2) * Real.cos (θ / 2) : ℝ) : ℂ) * Complex.I := by
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I, hcos, hsin]
  have hden : 1 - Complex.exp (Complex.I * (θ : ℂ)) ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp only [hexp, Complex.sub_re, Complex.one_re, Complex.zero_re,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, add_zero] at hre
    nlinarith [Real.sin_sq_add_cos_sq (θ / 2), sq_pos_of_pos hspos]
  have hsq : (Real.sin (θ / 2) : ℂ) ^ 2 + (Real.cos (θ / 2) : ℂ) ^ 2 = 1 := by
    exact_mod_cast Real.sin_sq_add_cos_sq (θ / 2)
  have hcayley : Complex.I * (1 + Complex.exp (Complex.I * (θ : ℂ))) /
      (1 - Complex.exp (Complex.I * (θ : ℂ))) =
        -(Real.cos (θ / 2) : ℂ) / (Real.sin (θ / 2) : ℂ) := by
    apply (div_eq_iff hden).mpr
    field_simp [hsne]
    rw [hexp]
    simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
      Complex.ofReal_ofNat, Complex.ofReal_one]
    linear_combination -2 * (Real.cos (θ / 2) : ℂ) * hsq +
      2 * (Real.cos (θ / 2) : ℂ) * (Real.sin (θ / 2) : ℂ) ^ 2 * Complex.I_sq
  rw [cauchyDiskMap, cauchyCircleBoundary_eq_sub_cot]
  simp only [Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div]
  calc
    (a : ℂ) + Complex.I * (b : ℂ) * (1 + Complex.exp (Complex.I * (θ : ℂ))) /
        (1 - Complex.exp (Complex.I * (θ : ℂ))) =
      (a : ℂ) + (b : ℂ) * (Complex.I * (1 + Complex.exp (Complex.I * (θ : ℂ))) /
        (1 - Complex.exp (Complex.I * (θ : ℂ)))) := by ring
    _ = (a : ℂ) - (b : ℂ) * (Real.cos (θ / 2) : ℂ) / (Real.sin (θ / 2) : ℂ) := by
      rw [hcayley]
      ring

/-- Complex-valued boundary pushforward for the literal Möbius map. -/
theorem map_cauchyDiskMap_exp (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    Measure.map (fun θ : ℝ => cauchyDiskMap a b (Complex.exp (Complex.I * (θ : ℂ))))
      circleAngleProbability = Measure.map Complex.ofReal (cauchyMeasure a b) := by
  calc
    _ = Measure.map (fun θ => (cauchyCircleBoundary a b θ : ℂ)) circleAngleProbability := by
      apply Measure.map_congr
      filter_upwards [circleAngleProbability_ae_mem] with θ hθ
      exact cauchyDiskMap_exp_eq a b hθ
    _ = _ := map_comp_cauchyCircleBoundary Complex.ofReal Complex.continuous_ofReal.measurable a hb

/-- The angular law is exactly the parameter law of the already constructed
uniform probability measure on the unit circle. -/
theorem map_exp_circleAngleProbability :
    Measure.map (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) circleAngleProbability =
      circleProbability 0 1 := by
  have he : Measurable (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) := by fun_prop
  have heq : circlePoint 0 1 = fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ)) := by
    funext θ
    simp [circlePoint]
  rw [circleAngleProbability, Measure.map_smul _ he.aemeasurable, circleProbability, heq]

/-- The genuine uniform unit-circle probability, pushed by the Möbius map,
is the real-axis embedding of the exact Cauchy law. -/
theorem map_cauchyDiskMap_circleProbability (a : ℝ) {b : ℝ≥0} (hb : 0 < b) :
    Measure.map (cauchyDiskMap a b) (circleProbability 0 1) =
      Measure.map Complex.ofReal (cauchyMeasure a b) := by
  have hM : Measurable (cauchyDiskMap a b) := by unfold cauchyDiskMap; fun_prop
  have he : Measurable (fun θ : ℝ => Complex.exp (Complex.I * (θ : ℂ))) := by fun_prop
  rw [← map_exp_circleAngleProbability, Measure.map_map hM he]
  exact map_cauchyDiskMap_exp a hb

end
end Li2Lean.P0
