/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigReferenceSymmetry
import Li2Lean.P0.ContourProductIntegrability
import Li2Lean.P0.TubeSweepSources

/-!
# Exact cross interactions in the actual reference energy

All six terms below integrate the literal Appendix A measures.  The two
Fubini exchanges use the proved geometric clearances from the actual
ellipse.  No supplied finite-energy or numerical hypothesis is required.
-/

open MeasureTheory Set Filter

namespace Li2Lean.P0.ActualReferenceQLogCross

noncomputable section

open ConfigSegment ConfigReferenceSymmetry ConfigContourReference
open ConfigContourMeasure

instance referenceMeasure_isFinite (start : ℝ) (count : ℕ) (units : List ℕ) :
    IsFiniteMeasure (referenceMeasure start count units) := by
  unfold referenceMeasure
  haveI (j : ℕ) : IsFiniteMeasure
      (ENNReal.ofReal (referenceDensity units j) •
        volume.restrict (Ico (referenceCellLeft start j) (referenceCellRight start j))) :=
    (volume.restrict (Ico (referenceCellLeft start j)
      (referenceCellRight start j))).smul_finite ENNReal.ofReal_ne_top
  infer_instance

instance pinnedReferenceMeasure_isFinite : IsFiniteMeasure pinnedReferenceMeasure := by
  unfold pinnedReferenceMeasure
  infer_instance

instance frequencyReferenceMeasure_isFinite : IsFiniteMeasure frequencyReferenceMeasure := by
  unfold frequencyReferenceMeasure
  infer_instance

theorem referenceMeasure_ae_interval (start : ℝ) (count : ℕ) (units : List ℕ) :
    ∀ᵐ x ∂referenceMeasure start count units, x ∈ Icc start (start + count / 32) := by
  unfold referenceMeasure
  rw [ae_finsetSum_measure_iff]
  intro j hj
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  have hjc : j + 1 ≤ count := Nat.succ_le_of_lt (Finset.mem_range.mp hj)
  have hjr : ((j + 1 : ℕ) : ℝ) ≤ count := by exact_mod_cast hjc
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  dsimp [referenceCellLeft, referenceCellRight] at hx
  constructor <;> linarith [hx.1, hx.2]

theorem pinnedReferenceMeasure_ae_interval :
    ∀ᵐ x ∂pinnedReferenceMeasure, x ∈ Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
  convert referenceMeasure_ae_interval (1 / 4) 32 ConfigData.pinnedMassUnits using 1 <;>
    norm_num [pinnedReferenceMeasure]

theorem frequencyReferenceMeasure_ae_interval :
    ∀ᵐ t ∂frequencyReferenceMeasure, t ∈ Icc (1 / 2 : ℝ) (11 / 2 : ℝ) := by
  convert referenceMeasure_ae_interval (1 / 2) 160 ConfigData.frequencyMassUnits using 1 <;>
    norm_num [frequencyReferenceMeasure]

theorem contourReferenceMeasure_ae_Gamma :
    ∀ᵐ z ∂contourReferenceMeasure, z ∈ Gamma := by
  rw [contourReferenceMeasure]
  apply (ae_map_iff continuous_ellipse.aemeasurable
    TubeInterior.measurable_Gamma).2
  filter_upwards [] with u
  change Config.baseEllipse u ∈ Gamma
  rw [← TubeEnergy.gammaPoint_eq_baseEllipse]
  exact ⟨u, rfl⟩

theorem continuous_integrable_referenceMeasure {f : ℝ → ℝ}
    (hf : Continuous f) (start : ℝ) (count : ℕ) (units : List ℕ) :
    Integrable f (referenceMeasure start count units) := by
  unfold referenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (hf.integrableOn_Icc.mono_set Ico_subset_Icc_self).smul_measure
    ENNReal.ofReal_ne_top

private theorem integrable_log_norm_of_bounds
    {α : Type*} [MeasurableSpace α] {μ : Measure α} [IsFiniteMeasure μ]
    {f : α → ℂ} (hf : Measurable f) {lo hi : ℝ} (hlo : 0 < lo)
    (hbound : ∀ᵐ p ∂μ, lo ≤ ‖f p‖ ∧ ‖f p‖ ≤ hi) :
    Integrable (fun p => Real.log ‖f p‖) μ := by
  apply (integrable_const (|Real.log lo| + |Real.log hi|)).mono'
    (Real.measurable_log.comp (continuous_norm.measurable.comp hf)).aestronglyMeasurable
  filter_upwards [hbound] with p hp
  have h1 := Real.log_le_log hlo hp.1
  have h2 := Real.log_le_log (lt_of_lt_of_le hlo hp.1) hp.2
  change ‖Real.log ‖f p‖‖ ≤ _
  rw [Real.norm_eq_abs, abs_le]
  constructor <;> linarith [neg_abs_le (Real.log lo), le_abs_self (Real.log hi),
    abs_nonneg (Real.log lo), abs_nonneg (Real.log hi)]

theorem contour_pinned_log_integrable :
    Integrable (fun p : ℂ × ℝ => Real.log ‖p.1 - (p.2 : ℂ)‖)
      (contourReferenceMeasure.prod pinnedReferenceMeasure) := by
  apply integrable_log_norm_of_bounds (by fun_prop)
    (lo := 751 / 5000) (hi := 6) (by norm_num)
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := contourReferenceMeasure) (ν := pinnedReferenceMeasure)).ae
      contourReferenceMeasure_ae_Gamma
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := contourReferenceMeasure) (ν := pinnedReferenceMeasure)).ae
      pinnedReferenceMeasure_ae_interval
  filter_upwards [h1, h2] with p hz hx
  constructor
  · apply TubeEnergy.positive_source_norm_sub_ge
    · simp only [Complex.ofReal_re]
      constructor <;> linarith [hx.1, hx.2]
    · simp
    · exact hz
  · have hzn := TubeVariance.norm_le_four_of_mem_Gamma hz
    have hxn : ‖(p.2 : ℂ)‖ ≤ 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
      linarith [hx.2]
    exact (norm_sub_le _ _).trans (by linarith)

theorem contour_frequency_log_integrable :
    Integrable (fun p : ℂ × ℝ => Real.log ‖p.1 + (p.2 : ℂ)‖)
      (contourReferenceMeasure.prod frequencyReferenceMeasure) := by
  apply integrable_log_norm_of_bounds (by fun_prop)
    (lo := 1749 / 5000) (hi := 10) (by norm_num)
  have h1 := (Measure.quasiMeasurePreserving_fst
    (μ := contourReferenceMeasure) (ν := frequencyReferenceMeasure)).ae
      contourReferenceMeasure_ae_Gamma
  have h2 := (Measure.quasiMeasurePreserving_snd
    (μ := contourReferenceMeasure) (ν := frequencyReferenceMeasure)).ae
      frequencyReferenceMeasure_ae_interval
  filter_upwards [h1, h2] with p hz ht
  constructor
  · have hsep := TubeEnergy.frequency_source_norm_sub_ge
      (x := -(p.2 : ℂ)) (by
        simp only [Complex.neg_re, Complex.ofReal_re]
        linarith [ht.1]) hz
    simpa only [sub_neg_eq_add] using hsep
  · have hzn := TubeVariance.norm_le_four_of_mem_Gamma hz
    have htn : ‖(p.2 : ℂ)‖ ≤ 11 / 2 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])]
      exact ht.2
    exact (norm_add_le _ _).trans (by linarith)

theorem pinnedReferencePotential_integrable :
    Integrable pinnedReferencePotential pinnedReferenceMeasure := by
  exact continuous_integrable_referenceMeasure
    (continuous_referencePotential (1 / 4) 32 ConfigData.pinnedMassUnits)
    (1 / 4) 32 ConfigData.pinnedMassUnits

theorem contourReferencePotential_pinned_integrable :
    Integrable (fun x : ℝ => contourReferencePotential (x : ℂ))
      pinnedReferenceMeasure := by
  have h := contour_pinned_log_integrable.integral_prod_right
  apply h.congr
  filter_upwards [] with x
  rw [contourReferencePotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [norm_sub_rev]

theorem pinnedReferenceComplexPotential_contour_integrable :
    Integrable pinnedReferenceComplexPotential contourReferenceMeasure :=
  contour_pinned_log_integrable.integral_prod_left

theorem reflectedFrequencyPotential_contour_integrable :
    Integrable reflectedFrequencyPotential contourReferenceMeasure := by
  apply contour_frequency_log_integrable.integral_prod_left.congr
  filter_upwards [] with z
  exact (reflectedFrequencyPotential_eq_mixed z).symm

theorem contourReferencePotential_frequency_integrable :
    Integrable (fun t : ℝ => contourReferencePotential (-(t : ℂ)))
      frequencyReferenceMeasure := by
  apply contour_frequency_log_integrable.integral_prod_right.congr
  filter_upwards [] with t
  rw [contourReferencePotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [show -(t : ℂ) - z = -(z + (t : ℂ)) by ring, norm_neg]

theorem contourReferencePotential_contour_integrable :
    Integrable contourReferencePotential contourReferenceMeasure := by
  have h := ConfigContourProductIntegrability.contourReferenceMeasure_prod_integrable.neg
  have hh : Integrable (fun p : ℂ × ℂ => Real.log ‖p.1 - p.2‖)
      (contourReferenceMeasure.prod contourReferenceMeasure) := by
    apply h.congr
    filter_upwards [] with p
    change -(-Real.log ‖p.1 - p.2‖) = Real.log ‖p.1 - p.2‖
    ring
  apply hh.integral_prod_left.congr
  filter_upwards [] with z
  exact (contourReferencePotential_eq_integral z).symm

def pinnedSelfEnergy : ℝ :=
  ∫ x, pinnedReferencePotential x ∂pinnedReferenceMeasure

def frequencySelfEnergy : ℝ :=
  ∫ t, frequencyReferencePotential t ∂frequencyReferenceMeasure

def pinnedFrequencyCross : ℝ :=
  ∫ x, reflectedFrequencyPotential (x : ℂ) ∂pinnedReferenceMeasure

def pinnedContour : ℝ :=
  ∫ x, contourReferencePotential (x : ℂ) ∂pinnedReferenceMeasure

def frequencyContour : ℝ :=
  ∫ t, contourReferencePotential (-(t : ℂ)) ∂frequencyReferenceMeasure

def contourSelf : ℝ := contourReferenceIntegral contourReferencePotential

theorem pinnedContour_exchange :
    contourReferenceIntegral pinnedReferenceComplexPotential = pinnedContour := by
  rw [contourReferenceIntegral_eq_integral
    pinnedReferenceComplexPotential_contour_integrable.aestronglyMeasurable]
  unfold pinnedReferenceComplexPotential pinnedContour
  rw [integral_integral_swap contour_pinned_log_integrable]
  apply integral_congr_ae
  filter_upwards [] with x
  rw [contourReferencePotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [norm_sub_rev]

theorem frequencyContour_exchange :
    contourReferenceIntegral reflectedFrequencyPotential = frequencyContour := by
  rw [contourReferenceIntegral_eq_integral
    reflectedFrequencyPotential_contour_integrable.aestronglyMeasurable]
  simp_rw [reflectedFrequencyPotential_eq_mixed]
  rw [integral_integral_swap contour_frequency_log_integrable]
  unfold frequencyContour
  apply integral_congr_ae
  filter_upwards [] with t
  rw [contourReferencePotential_eq_integral]
  apply integral_congr_ae
  filter_upwards [] with z
  rw [show -(t : ℂ) - z = -(z + (t : ℂ)) by ring, norm_neg]

theorem pinned_eta_split :
    (∫ x, etaReferencePotential (x : ℂ) ∂pinnedReferenceMeasure) =
      pinnedSelfEnergy + pinnedContour := by
  simp only [etaReferencePotential, pinnedReferenceComplexPotential_ofReal]
  rw [integral_add pinnedReferencePotential_integrable
    contourReferencePotential_pinned_integrable]
  rfl

theorem contour_eta_split :
    contourReferenceIntegral etaReferencePotential = pinnedContour + contourSelf := by
  rw [contourReferenceIntegral_eq_integral (f := etaReferencePotential)
    (pinnedReferenceComplexPotential_contour_integrable.add
      contourReferencePotential_contour_integrable).aestronglyMeasurable]
  unfold etaReferencePotential
  rw [integral_add pinnedReferenceComplexPotential_contour_integrable
    contourReferencePotential_contour_integrable,
    ← contourReferenceIntegral_eq_integral
      pinnedReferenceComplexPotential_contour_integrable.aestronglyMeasurable,
    ← contourReferenceIntegral_eq_integral
      contourReferencePotential_contour_integrable.aestronglyMeasurable,
    pinnedContour_exchange]
  rfl

/-- Unconditional six-component identity for the same actual reference. -/
theorem actualReference_qLog_eq_six_terms :
    actualReference.qLog =
      pinnedSelfEnergy + frequencySelfEnergy + pinnedFrequencyCross +
        2 * pinnedContour + contourSelf + frequencyContour := by
  change (∫ x, etaReferencePotential (x : ℂ) ∂pinnedReferenceMeasure) +
    contourReferenceIntegral etaReferencePotential + frequencySelfEnergy +
    ((∫ x, reflectedFrequencyPotential (x : ℂ) ∂pinnedReferenceMeasure) +
      contourReferenceIntegral reflectedFrequencyPotential) = _
  rw [pinned_eta_split, contour_eta_split, frequencyContour_exchange]
  unfold pinnedFrequencyCross
  ring

end

end Li2Lean.P0.ActualReferenceQLogCross

#print axioms Li2Lean.P0.ActualReferenceQLogCross.pinnedContour_exchange
#print axioms Li2Lean.P0.ActualReferenceQLogCross.frequencyContour_exchange
#print axioms Li2Lean.P0.ActualReferenceQLogCross.actualReference_qLog_eq_six_terms
