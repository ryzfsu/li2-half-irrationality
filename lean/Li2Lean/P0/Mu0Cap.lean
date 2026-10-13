/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Variations
import Li2Lean.P0.DualL6Reference
import Li2Lean.Kit.LogSegment

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0

noncomputable section

/-- Reflection map from the positive half-line to the negative real axis. -/
def p0FrequencyReflection (t : ℝ) : ℂ := -(t : ℂ)

/-- The one-dimensional half-line positive logarithmic kernel before reflection. -/
def frequencyHalfLinePosKernel (z : ℂ) (t : ℝ) : ℝ≥0∞ :=
  L6Variations.l6PosKernel z (p0FrequencyReflection t)

/-- Exact support-local analytic input needed for the reflected-frequency cap.
This is a one-dimensional logarithmic integral statement; no global bound is
silently included. -/
def frequencyHalfLineOneDimensionalCap : Prop :=
  ∀ z : ℂ,
    (∫⁻ t, frequencyHalfLinePosKernel z t ∂
      (volume.restrict (Set.Ici (1 / 2 : ℝ)))) ≤ ENNReal.ofReal 2

/-- Pushforward of the half-line density cap to the reflected frequency line.
The only analytic input is the explicitly named one-dimensional cap above. -/
theorem frequencyReference_l6PosKernel_bound_of_density_le_one
    (μ : Measure ℝ)
    (hμ : μ ≤ volume.restrict (Set.Ici (1 / 2 : ℝ)))
    (hHalf : frequencyHalfLineOneDimensionalCap) :
    ∀ z : ℂ,
      (∫⁻ w, L6Variations.l6PosKernel z w ∂
        (p0ReflectedFrequencyMeasure μ)) ≤ ENNReal.ofReal 2 := by
  intro z
  have hreflection : Measurable p0FrequencyReflection := by
    unfold p0FrequencyReflection
    fun_prop
  have hmap : Measure.map p0FrequencyReflection μ ≤
      Measure.map p0FrequencyReflection
        (volume.restrict (Set.Ici (1 / 2 : ℝ))) :=
    Measure.map_mono hμ hreflection
  have hkernel : Measurable (fun w : ℂ => L6Variations.l6PosKernel z w) := by
    have hp : Measurable (fun w : ℂ => (z, w)) := by
      apply Measurable.prod
      · exact measurable_const
      · change Measurable (fun w : ℂ => w)
        exact measurable_id
    have hcomp := L6Variations.measurable_l6PosKernel.comp hp
    convert hcomp using 1 <;> rfl
  have hleMap :
      (∫⁻ w, L6Variations.l6PosKernel z w ∂
        (Measure.map p0FrequencyReflection μ)) ≤
      (∫⁻ w, L6Variations.l6PosKernel z w ∂
        (Measure.map p0FrequencyReflection
          (volume.restrict (Set.Ici (1 / 2 : ℝ))))) :=
    lintegral_mono' hmap (fun _ => le_rfl)
  have hhalfMap :
      (∫⁻ w, L6Variations.l6PosKernel z w ∂
        (Measure.map p0FrequencyReflection
          (volume.restrict (Set.Ici (1 / 2 : ℝ))))) ≤ ENNReal.ofReal 2 := by
    rw [lintegral_map hkernel hreflection]
    simpa [frequencyHalfLinePosKernel, p0FrequencyReflection] using hHalf z

  change (∫⁻ w, L6Variations.l6PosKernel z w ∂
      (Measure.map p0FrequencyReflection μ)) ≤ ENNReal.ofReal 2
  exact hleMap.trans hhalfMap

/-- The literal reference measure inherits the same cap once its density
certificate and the one-dimensional half-line lemma are supplied. -/
theorem frequencyReference_l6PosKernel_bound_of_reference_density
    (hRef : P0ReferenceFiniteEnergyData)
    (hHalf : frequencyHalfLineOneDimensionalCap) :
    ∀ z : ℂ,
      (∫⁻ w, L6Variations.l6PosKernel z w ∂
        (p0FrequencyMeasure (p0ReferenceMeasures hRef))) ≤ ENNReal.ofReal 2 := by
  intro z
  apply frequencyReference_l6PosKernel_bound_of_density_le_one
    (p0ReferenceMeasures hRef).mu hRef.mu_le_density hHalf z

/-- The reflected half-line logarithmic kernel has total positive mass at most 2.
The proof isolates the collision/projection singletons, dominates by the real
one-dimensional logarithmic profile, and evaluates its compact support exactly. -/
theorem frequencyHalfLineOneDimensionalCap_proof : frequencyHalfLineOneDimensionalCap := by
  intro z
  let a : ℝ := -z.re
  let S : Set ℝ := Set.Ico (a - 1) (a + 1)
  let f : ℝ → ℝ := S.indicator (fun t => -Real.log |a - t|)
  have hS : MeasurableSet S := measurableSet_Ico
  have hab : a - 1 ≤ a + 1 := by linarith
  have hlogInt : IntegrableOn (fun t : ℝ => Real.log |a - t|) S := by
    exact Li2Lean.LogSegment.integrableOn_Ico_log_abs_sub a hab
  have hfInt : Integrable f volume := by
    exact hlogInt.neg.integrable_indicator hS
  have hfNonneg : ∀ᵐ t : ℝ ∂volume, 0 ≤ f t := by
    filter_upwards [] with t
    by_cases ht : t ∈ S
    · simp only [f, Set.indicator_of_mem ht]
      have hdist : |a - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> dsimp [S] at ht <;> linarith [ht.1, ht.2]
      exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) hdist)
    · simp [f, ht]
  have hfIntegral : (∫ t, f t ∂volume) = 2 := by
    rw [integral_indicator hS]
    rw [integral_neg]
    rw [Li2Lean.LogSegment.integral_Ico_log_abs_sub a hab]
    dsimp [a]
    norm_num [Li2Lean.LogSegment.primitive]
  have hlinf : (∫⁻ t, ENNReal.ofReal (f t) ∂volume) = ENNReal.ofReal 2 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfInt hfNonneg]
    exact congrArg ENNReal.ofReal hfIntegral
  have hcoll : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 / 2 : ℝ))),
      z ≠ p0FrequencyReflection t := by
    have hae : ∀ᵐ t : ℝ ∂volume, t ≠ -z.re := by
      apply ae_iff.2
      have hset : {t : ℝ | ¬t ≠ -z.re} = ({-z.re} : Set ℝ) := by ext t; simp
      rw [hset]
      simp
    rw [ae_restrict_iff' measurableSet_Ici]
    filter_upwards [hae] with t ht hti
    intro heq
    apply ht
    have hre := congrArg Complex.re heq
    dsimp [p0FrequencyReflection] at hre
    linarith [hre]
  have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 / 2 : ℝ))),
      frequencyHalfLinePosKernel z t ≤ ENNReal.ofReal (f t) := by
    have haeA : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Ici (1 / 2 : ℝ))), t ≠ a := by
      rw [ae_restrict_iff' measurableSet_Ici]
      have ha : ∀ᵐ t : ℝ ∂volume, t ≠ a := by
        apply ae_iff.2
        have hset : {t : ℝ | ¬t ≠ a} = ({a} : Set ℝ) := by ext t; simp
        rw [hset]
        simp
      filter_upwards [ha] with t ht hti
      exact ht
    filter_upwards [hcoll, haeA] with t hne hta
    have hnorm : |a - t| ≤ ‖z - p0FrequencyReflection t‖ := by
      have hsq : |a - t| ^ 2 ≤ ‖z - p0FrequencyReflection t‖ ^ 2 := by
        rw [sq_abs, Complex.sq_norm, Complex.normSq_apply]
        dsimp [a, p0FrequencyReflection]
        nlinarith [sq_nonneg (z.im)]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsq
    by_cases ht : t ∈ S
    · have hdist : |a - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> dsimp [S] at ht <;> linarith [ht.1, ht.2]
      have hinv : ‖z - p0FrequencyReflection t‖⁻¹ ≤ |a - t|⁻¹ := by
        by_cases hz : |a - t| = 0
        · exact False.elim (hta (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm)
        · simpa [one_div] using
            (one_div_le_one_div_of_le (abs_pos.mpr hz) (by simpa [abs_abs] using hnorm))
      have hpos : Real.posLog ‖z - p0FrequencyReflection t‖⁻¹ ≤
          Real.posLog |a - t|⁻¹ := by
        exact Real.posLog_le_posLog (by
          exact le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))) hinv
      have hlog : Real.posLog (|a - t|⁻¹) = -Real.log |a - t| := by
        rw [Real.posLog_apply]
        have hnon : 0 ≤ Real.log (|a - t|⁻¹) := by
          rw [Real.log_inv]
          exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) hdist)
        rw [max_eq_right hnon, Real.log_inv]
      simp only [frequencyHalfLinePosKernel, f, Set.indicator_of_mem ht,
        L6Variations.l6PosKernel, hne]
      simpa [hlog] using ENNReal.ofReal_le_ofReal hpos
    · have hdist : 1 ≤ |a - t| := by
        by_contra hlt
        have : |a - t| < 1 := lt_of_not_ge hlt
        have : t ∈ S := by
          rw [mem_Ico]
          constructor <;> linarith [abs_lt.mp this]
        exact ht this
      have hzeroNorm : Real.posLog (‖z - p0FrequencyReflection t‖⁻¹) = 0 := by
        apply (Real.posLog_eq_zero_iff _).2
        rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        exact (inv_le_one₀ (norm_pos_iff.mpr (by exact sub_ne_zero.mpr hne))).2 (le_trans hdist hnorm)
      simp [frequencyHalfLinePosKernel, L6Variations.l6PosKernel, hne, hzeroNorm, f, ht]
  have hleS : (∫⁻ t, frequencyHalfLinePosKernel z t ∂
      (volume.restrict (Set.Ici (1 / 2 : ℝ)))) ≤
      (∫⁻ t, ENNReal.ofReal (f t) ∂
      (volume.restrict (Set.Ici (1 / 2 : ℝ)))) :=
    lintegral_mono_ae hpoint
  calc
    (∫⁻ t, frequencyHalfLinePosKernel z t ∂
      (volume.restrict (Set.Ici (1 / 2 : ℝ)))) ≤
      (∫⁻ t, ENNReal.ofReal (f t) ∂volume) :=
        hleS.trans (lintegral_mono' Measure.restrict_le_self le_rfl)
    _ = ENNReal.ofReal 2 := hlinf


end
end Li2Lean.P0
