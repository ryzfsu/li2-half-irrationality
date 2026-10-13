/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ContourEnergyLowerBound
import Li2Lean.P0.TubeVarianceSupport

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

namespace EnergyLowerBound

/-!
Uniform finite bounds for the branch-free companion field on the four-ball.
The only new point beyond the coarse lower bound is the lower estimate for
`phi`: its source interval is `[-1/2,0]`, so it is reduced by `z ↦ -z` to the
already verified segment estimate.  This includes points of `Gamma` lying on
the source segment, where a pointwise separation argument would be invalid.
-/

/-- The logarithmic segment in `phi` is bounded below, including source crossings. -/
theorem phi_segment_ge {z : ℂ} (hz : ‖z‖ ≤ 4) :
    -86 ≤ ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖ := by
  have hneg : ‖(-z : ℂ)‖ ≤ 4 := by simpa using hz
  have hseg := segment_log_ge (z := (-z : ℂ)) hneg
    (a := (0 : ℝ)) (b := (1 / 2 : ℝ)) (by norm_num) (by norm_num) (by norm_num)
  have heq :
      (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) =
        ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖(-z : ℂ) - (s : ℂ)‖ := by
    apply intervalIntegral.integral_congr_ae
    filter_upwards [] with s hs
    have harg : (-z : ℂ) - (s : ℂ) = -(z + (s : ℂ)) := by ring
    rw [harg, norm_neg]
  rw [heq]
  exact hseg

/-- A uniform lower bound for the literal v10 `phi` on the four-ball. -/
theorem phi_ge {z : ℂ} (hz : ‖z‖ ≤ 4) : (-100 : ℝ) ≤ phi z := by
  have hzre : -(4 : ℝ) ≤ z.re := by
    have h := Complex.abs_re_le_norm z
    rw [abs_le] at h
    linarith
  have hlog := log_two_le_one
  have hseg := phi_segment_ge hz
  unfold phi ell
  have hconst : (0 : ℝ) ≤ (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) := by
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hhalf]
    have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    linarith
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hmul : -(4 : ℝ) * Real.log 2 ≤ z.re * Real.log 2 :=
    mul_le_mul_of_nonneg_right hzre hlog0
  nlinarith

/-- `phi` is absolutely bounded on the support of the swept companion measure. -/
theorem phi_abs_le {z : ℂ} (hz : ‖z‖ ≤ 4) : |phi z| ≤ 100 := by
  have hlo := phi_ge hz
  have hhi := phi_le hz
  rw [abs_le]
  exact ⟨hlo, hhi.trans (by norm_num)⟩

/-- A coarse upper bound for one source segment on the four-ball. -/
theorem segment_log_le {z : ℂ} (hz : ‖z‖ ≤ 4) {a b : ℝ}
    (hab : a ≤ b) (ha : 0 ≤ a) (hb : b ≤ 2) :
    (∫ x in a..b, Real.log ‖z - (x : ℂ)‖) ≤ 6 * (b - a) := by
  by_cases hint : IntervalIntegrable (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) volume a b
  · calc
      (∫ x in a..b, Real.log ‖z - (x : ℂ)‖) ≤ ∫ _x in a..b, (6 : ℝ) := by
        apply intervalIntegral.integral_mono_on hab hint intervalIntegrable_const
        intro x hx
        have hnorm : ‖z - (x : ℂ)‖ ≤ 6 := by
          calc
            ‖z - (x : ℂ)‖ ≤ ‖z‖ + ‖(x : ℂ)‖ := norm_sub_le _ _
            _ ≤ 6 := by
              rw [Complex.norm_real, Real.norm_eq_abs,
                abs_of_nonneg (by linarith [hx.1])]
              linarith [hz, hx.2]
        exact (Real.log_le_self (norm_nonneg _)).trans hnorm
      _ = 6 * (b - a) := by rw [intervalIntegral.integral_const, smul_eq_mul]; ring
  · rw [intervalIntegral.integral_undef hint]
    positivity

/-- The companion field is absolutely bounded on the four-ball. -/
theorem companionField_abs_le {z : ℂ} (hz : ‖z‖ ≤ 4) :
    |p0CompanionField z| ≤ 300 := by
  have hAlo := A0_ge hz
  have hAhi : A0 z ≤ 18 := by
    unfold A0
    have h1 := segment_log_le hz (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ))
      (by norm_num) (by norm_num) (by norm_num)
    have h2 := segment_log_le hz (a := (0 : ℝ)) (b := 2)
      (by norm_num) (by norm_num) (by norm_num)
    linarith
  have hφlo := phi_ge hz
  have hφhi := phi_le hz
  unfold p0CompanionField
  rw [abs_le]
  constructor <;> linarith

/-- The logarithmic interval potentials are strongly measurable in the field
variable.  This is a parameter-measure statement, so it remains valid at
source crossings where the logarithm itself is singular. -/
theorem stronglyMeasurable_companionField :
    StronglyMeasurable (fun z : ℂ => p0CompanionField z) := by
  have hminus (a b : ℝ) (hab : a ≤ b) :
      StronglyMeasurable (fun z : ℂ =>
        ∫ x in a..b, Real.log ‖z - (x : ℂ)‖) := by
    have hfun : (fun z : ℂ => ∫ x in a..b, Real.log ‖z - (x : ℂ)‖) =
        (fun z : ℂ => ∫ x in Set.Ioc a b, Real.log ‖z - (x : ℂ)‖) := by
      funext z
      rw [intervalIntegral.integral_of_le hab]
    rw [hfun]
    apply StronglyMeasurable.integral_prod_right
    fun_prop
  have hplus : StronglyMeasurable (fun z : ℂ =>
      ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) := by
    have hfun : (fun z : ℂ =>
        ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) =
        (fun z : ℂ => ∫ s in Set.Ioc (0 : ℝ) (1 / 2),
          Real.log ‖z + (s : ℂ)‖) := by
      funext z
      rw [intervalIntegral.integral_of_le (by norm_num)]
    rw [hfun]
    apply StronglyMeasurable.integral_prod_right
    fun_prop
  have hA : StronglyMeasurable (fun z : ℂ => A0 z) := by
    unfold A0
    exact hminus _ _ (by norm_num) |>.add (hminus _ _ (by norm_num))
  have hphi : StronglyMeasurable (fun z : ℂ => phi z) := by
    unfold phi
    have hre : StronglyMeasurable (fun z : ℂ => z.re) :=
      Complex.continuous_re.stronglyMeasurable
    have hconst : StronglyMeasurable (fun _ : ℂ =>
        (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) :=
      stronglyMeasurable_const
    have hh := ((hre.mul_const ell).add hplus).add hconst
    convert hh using 1 <;> ext z <;> simp only [Pi.add_apply] <;> ring
  exact hA.sub hphi

/-- Any finite measure carried by the four-ball integrates the companion field. -/
theorem integrable_companionField_of_ae_norm_le {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hμ : ∀ᵐ z ∂μ, ‖z‖ ≤ 4) : Integrable (fun z : ℂ => p0CompanionField z) μ := by
  apply (integrable_const (300 : ℝ)).mono' stronglyMeasurable_companionField.aestronglyMeasurable
  filter_upwards [hμ] with z hz
  rw [Real.norm_eq_abs]
  exact companionField_abs_le hz


/-- A finite measure carried by `Gamma` integrates the companion field; the
crossing points of `Gamma` with the `phi` source interval are included. -/
theorem integrable_companionField_of_ae_mem_Gamma {μ : Measure ℂ} [IsFiniteMeasure μ]
    (hΓ : ∀ᵐ z ∂μ, z ∈ Gamma) :
    Integrable (fun z : ℂ => p0CompanionField z) μ := by
  apply integrable_companionField_of_ae_norm_le
  filter_upwards [hΓ] with z hz
  exact TubeVariance.norm_le_four_of_mem_Gamma hz

end EnergyLowerBound
end
end Li2Lean.P0
