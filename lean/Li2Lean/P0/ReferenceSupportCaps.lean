/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Kappa0Cap
import Li2Lean.P0.ReferenceClosure
import Li2Lean.P0.MixedCellClearanceFull
import Li2Lean.P0.U2GlobalFejer
import Li2Lean.P0.U2NegativeEtaL6Cap
import Li2Lean.P0.Mu0Cap
import Li2Lean.P0.U2SupportRestrictedCross
import Li2Lean.P0.TubeInteriorSweep

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0

noncomputable section

open L6Variations
open L6Admissible
open EnergyLowerBound
open U2GlobalFejer
open U2NegativeEtaL6Cap

/-! The three source regions on which the literal eta reference potential is
controlled.  They are kept explicit because the contour cap is support-local.
-/
def pinnedRealSourceSupport : Set ℂ :=
  {z | z.im = 0 ∧ z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)}

def negativeRealSourceSupport : Set ℂ :=
  {z | z.im = 0 ∧ z.re ≤ -(1 / 2 : ℝ)}

def referenceEtaSourceSupport : Set ℂ :=
  pinnedRealSourceSupport ∪ Gamma ∪ negativeRealSourceSupport

private theorem measurableSet_pinnedRealSourceSupport :
    MeasurableSet pinnedRealSourceSupport := by
  exact (measurableSet_singleton 0).preimage (by fun_prop) |>.inter
    (measurableSet_Icc.preimage (by fun_prop))

private theorem measurableSet_negativeRealSourceSupport :
    MeasurableSet negativeRealSourceSupport := by
  exact (measurableSet_singleton 0).preimage (by fun_prop) |>.inter
    (measurableSet_Iic.preimage (by
      fun_prop : Measurable (fun z : ℂ => z.re)))

private theorem measurableSet_referenceEtaSourceSupport :
    MeasurableSet referenceEtaSourceSupport := by
  exact (measurableSet_pinnedRealSourceSupport.union
    (TubeInterior.measurable_Gamma)).union
    measurableSet_negativeRealSourceSupport

private noncomputable def etaPinnedContourCap : ℝ≥0∞ :=
  ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ

private noncomputable def etaGammaContourCap : ℝ≥0∞ :=
  ENNReal.ofReal (ConfigContourSelfPotential.contourMass * Real.log 5 +
    U2GlobalFejer.contourPotentialLowerCost)

private noncomputable def etaNegativeCap : ℝ≥0∞ :=
  ENNReal.ofReal (Real.posLog U2NegativeEtaL6Cap.negativeEtaClearance⁻¹)

private theorem pinnedContour_l6PosKernel_bound {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4)) :
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂nu0) ≤ etaPinnedContourCap := by
  have hx02 : x ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hx.1], by linarith [hx.2]⟩
  have hpoint : ∀ᵐ w ∂nu0,
      l6PosKernel (x : ℂ) w ≤
        ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) := by
    filter_upwards [Measure.support_mem_ae (μ := nu0)] with w hw
    rcases ReferencePackaging.nu0_supported hw with ⟨u, rfl⟩
    have hbase : Config.baseEllipse u = Li2Lean.P0.gammaPoint u := by
      simpa [Config.baseEllipse, Li2Lean.P0.ellipsePoint] using
        (Li2Lean.P0.ellipsePoint_one_eq_gammaPoint u)
    rw [← hbase]
    have hclear := Config.s2_mixed_left_candidate
      (Config.baseEllipse u) ⟨u, rfl⟩ x hx02
    have hdist : (751 / 5000 : ℝ) ≤
        ‖(x : ℂ) - Config.baseEllipse u‖ := by
      rw [norm_sub_rev]
      exact hclear
    have hne : (x : ℂ) ≠ Config.baseEllipse u := by
      intro heq
      have hzero : ‖(x : ℂ) - Config.baseEllipse u‖ = 0 := by rw [heq]; simp
      have : (751 / 5000 : ℝ) ≤ 0 := by simpa [hzero] using hdist
      norm_num at this
    simp only [l6PosKernel, ne_of_ne_of_eq hne rfl, ↓reduceIte]
    have hinv : ‖(x : ℂ) - Config.baseEllipse u‖⁻¹ ≤ (751 / 5000 : ℝ)⁻¹ := by
      simpa [one_div] using one_div_le_one_div_of_le (by norm_num) hdist
    have hpos : Real.posLog ‖(x : ℂ) - Config.baseEllipse u‖⁻¹ ≤
        Real.posLog (751 / 5000 : ℝ)⁻¹ :=
      Real.posLog_le_posLog
        (le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))) hinv
    exact ENNReal.ofReal_le_ofReal hpos
  calc
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂nu0) ≤
        ∫⁻ _w : ℂ,
          ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) ∂nu0 :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ := by
      rw [lintegral_const]
    _ = etaPinnedContourCap := rfl

private noncomputable def referenceEtaCap : ℝ≥0∞ :=
  ENNReal.ofReal 2 + etaPinnedContourCap + etaGammaContourCap + etaNegativeCap

private theorem referenceEtaCap_ne_top : referenceEtaCap ≠ ⊤ := by
  simp [referenceEtaCap, etaPinnedContourCap, etaGammaContourCap,
    etaNegativeCap, ENNReal.add_ne_top, ENNReal.mul_ne_top, nu0,
    ConfigContourMeasure.contourReferenceMeasure_univ]

private theorem pinned_source_eta_cap
    (hRef : P0ReferenceFiniteEnergyData) {z : ℂ}
    (hz : z ∈ pinnedRealSourceSupport) :
    (∫⁻ w, l6PosKernel z w ∂(p0ReferenceMeasures hRef).eta) ≤
      referenceEtaCap := by
  have hzreal : z = (z.re : ℂ) := by
    apply Complex.ext
    · simp
    · simpa [hz.1]
  have hk := pinnedReference_l6PosKernel_bound hRef z.re
  have hn := pinnedContour_l6PosKernel_bound hz.2
  rw [P0AdmissibleMeasures.eta, p0CompanionMeasure, lintegral_add_measure]
  rw [hzreal]
  calc
    (∫⁻ (w : ℂ), l6PosKernel (z.re : ℂ) w ∂
        (Measure.map Complex.ofReal (p0ReferenceMeasures hRef).kappa)) +
        ∫⁻ (w : ℂ), l6PosKernel (z.re : ℂ) w ∂nu0 ≤
      ENNReal.ofReal 2 + etaPinnedContourCap := by
        exact add_le_add hk (by simpa [etaPinnedContourCap] using hn)
    _ ≤ referenceEtaCap := by
      unfold referenceEtaCap
      have htail : etaPinnedContourCap ≤
          etaPinnedContourCap + etaGammaContourCap + etaNegativeCap := by
        exact le_add_right (le_add_right (le_refl _))
      simpa [add_assoc] using
        (add_le_add (le_refl (ENNReal.ofReal 2)) htail)

private theorem gamma_source_eta_cap
    (hRef : P0ReferenceFiniteEnergyData) {z : ℂ}
    (hz : z ∈ Gamma) :
    (∫⁻ w, l6PosKernel z w ∂(p0ReferenceMeasures hRef).eta) ≤
      referenceEtaCap := by
  have hk := pinnedReference_l6PosKernel_bound hRef z
  have hn := U2GlobalFejer.contourReference_l6PosKernel_bound_on_Gamma hz
  rw [P0AdmissibleMeasures.eta, p0CompanionMeasure, lintegral_add_measure]
  calc
    (∫⁻ (w : ℂ), l6PosKernel z w ∂
        (Measure.map Complex.ofReal (p0ReferenceMeasures hRef).kappa)) +
        ∫⁻ (w : ℂ), l6PosKernel z w ∂nu0 ≤
      ENNReal.ofReal 2 + etaGammaContourCap := by
        exact add_le_add hk (by simpa [etaGammaContourCap, nu0] using hn)
    _ ≤ referenceEtaCap := by
      unfold referenceEtaCap
      have htail : etaGammaContourCap ≤
          etaPinnedContourCap + etaGammaContourCap + etaNegativeCap := by
        calc
          etaGammaContourCap ≤ etaGammaContourCap + etaNegativeCap :=
            le_add_right (le_refl _)
          _ ≤ etaPinnedContourCap + (etaGammaContourCap + etaNegativeCap) :=
            le_add_left (le_refl _)
          _ = etaPinnedContourCap + etaGammaContourCap + etaNegativeCap := by
            ac_rfl
      have hsum := add_le_add (le_refl (ENNReal.ofReal 2)) htail
      simpa [add_assoc, add_comm, add_left_comm] using hsum

private theorem negative_source_eta_cap
    (hRef : P0ReferenceFiniteEnergyData) {z : ℂ}
    (hz : z ∈ negativeRealSourceSupport) :
    (∫⁻ w, l6PosKernel z w ∂(p0ReferenceMeasures hRef).eta) ≤
      referenceEtaCap := by
  have hn := reference_eta_l6PosKernel_bound_on_negative_axis hRef hz.2
  calc
    (∫⁻ w, l6PosKernel z w ∂(p0ReferenceMeasures hRef).eta) ≤ etaNegativeCap := by
      have hzreal : z = (z.re : ℂ) := by
        apply Complex.ext
        · simp
        · simpa [hz.1]
      rw [hzreal] at hn ⊢
      simpa [etaNegativeCap] using hn
    _ ≤ referenceEtaCap := by
      unfold referenceEtaCap
      calc
        etaNegativeCap ≤ etaGammaContourCap + etaNegativeCap :=
          le_add_left (le_refl _)
        _ ≤ etaPinnedContourCap + (etaGammaContourCap + etaNegativeCap) :=
          le_add_left (le_refl _)
        _ ≤ ENNReal.ofReal 2 + (etaPinnedContourCap +
            (etaGammaContourCap + etaNegativeCap)) :=
          le_add_left (le_refl _)
        _ = ENNReal.ofReal 2 + etaPinnedContourCap + etaGammaContourCap +
            etaNegativeCap := by ac_rfl

/-- Explicit support-local eta cap for the literal reference. -/
theorem p0Reference_eta_posKernel_cap
    (hRef : P0ReferenceFiniteEnergyData) :
    ∀ z ∈ referenceEtaSourceSupport,
      (∫⁻ w, l6PosKernel z w ∂(p0ReferenceMeasures hRef).eta) ≤
        referenceEtaCap := by
  intro z hz
  rcases hz with hz | hz
  · rcases hz with hz | hz
    · exact pinned_source_eta_cap hRef hz
    · exact gamma_source_eta_cap hRef hz
  · exact negative_source_eta_cap hRef hz

/-- The reflected-frequency target has a global cap from the one-dimensional
half-line calculation. -/
theorem p0Reference_frequency_posKernel_cap
    (hRef : P0ReferenceFiniteEnergyData) :
    ∀ z : ℂ,
      (∫⁻ w, l6PosKernel z w ∂
        (p0FrequencyMeasure (p0ReferenceMeasures hRef))) ≤ ENNReal.ofReal 2 := by
  intro z
  exact frequencyReference_l6PosKernel_bound_of_reference_density hRef
    frequencyHalfLineOneDimensionalCap_proof z

private theorem admissible_eta_ae_mem_referenceEtaSourceSupport
    (M : P0AdmissibleMeasures) :
    ∀ᵐ z ∂M.eta, z ∈ referenceEtaSourceSupport := by
  change ∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa + M.nu),
    z ∈ referenceEtaSourceSupport
  rw [ae_add_measure_iff]
  constructor
  · apply (ae_map_iff Complex.measurable_ofReal.aemeasurable
      measurableSet_referenceEtaSourceSupport).2
    filter_upwards [kappa_ae_mem M] with x hx
    exact Or.inl (Or.inl (by
      show (x : ℂ).im = 0 ∧ (x : ℂ).re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4)
      exact ⟨by simp, hx⟩))
  · filter_upwards [nu_ae_mem_Gamma M] with z hz
    exact Or.inl (Or.inr hz)

private theorem admissible_frequency_ae_mem_referenceEtaSourceSupport
    (M : P0AdmissibleMeasures) :
    ∀ᵐ z ∂(p0FrequencyMeasure M), z ∈ referenceEtaSourceSupport := by
  rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure]
  apply (ae_map_iff measurable_reflect.aemeasurable
      measurableSet_referenceEtaSourceSupport).2
  filter_upwards [mu_ae_ge M] with t ht
  exact Or.inr (by
    simp [negativeRealSourceSupport]
    linarith)

/-- Assemble arbitrary-reference cross energy from the explicit support caps.
This keeps the literal reference witness and all support transfers visible. -/
theorem p0L6CrossEnergy_of_literal_reference_support_caps
    (M : P0AdmissibleMeasures) (hfin : P0FiniteEnergyCondition M)
    (hRef : P0ReferenceFiniteEnergyData) :
    P0L6CrossEnergy M (p0ReferenceMeasures hRef) := by
  let M₀ : P0AdmissibleMeasures := p0ReferenceMeasures hRef
  have hfin₀ : P0FiniteEnergyCondition M₀ := p0ReferenceMeasures_finite_energy hRef
  apply p0L6CrossEnergy_of_support_restricted_of_admissible M M₀ hfin hfin₀
    (Sη := referenceEtaSourceSupport) (Sφ := Set.univ)
    (Cη := referenceEtaCap) (Cφ := ENNReal.ofReal 2)
  · intro z hz
    simpa [M₀] using p0Reference_eta_posKernel_cap hRef z hz
  · intro z _
    simpa [M₀] using p0Reference_frequency_posKernel_cap hRef z
  · simpa using admissible_eta_ae_mem_referenceEtaSourceSupport M
  · simpa using admissible_frequency_ae_mem_referenceEtaSourceSupport M
  · exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  · exact Filter.Eventually.of_forall (fun _ => Set.mem_univ _)
  · exact referenceEtaCap_ne_top
  · exact ENNReal.ofReal_ne_top

end
end Li2Lean.P0
