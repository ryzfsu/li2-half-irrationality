/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Duality
import Li2Lean.P0.Dual
import Li2Lean.P0.DualL6CrossEnergy
import Li2Lean.P0.DualL6Reference

/-!
# The L6 linearization at the actual reference, from the U2 L6 layer

`ActualReferenceLinearization` (Duality.lean) is derived here from the
merged U2 L6 theorem `p0Dual_regularizedEnergy_ge_of_caps`, applied to the
packaged reference `p0ReferenceMeasures h`. The bridge proves:

* the U2 fields `p0DualWeta`, `p0DualWmu` agree with the literal
  `Config.Weta actualReference`, `Config.Wmu actualReference` almost
  everywhere for every finite-energy competitor (pointwise wherever the
  reference kernel is integrable, which the cross energy gives a.e.);
* `l6QLog η₀ μ₀⁻ = actualReference.qLog` (three Fubini identities).

The remaining hypotheses are exactly the U2 residuals: the reference
finite-energy data `P0ReferenceFiniteEnergyData` and the cross energies
`P0L6CrossEnergy M M₀` (e.g. from uniform reference-potential bounds).
-/

open MeasureTheory Set

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.L6Variations
open Li2Lean.P0.L6Admissible

noncomputable section

section Bridge

variable (h : P0ReferenceFiniteEnergyData)

local notation "M₀" => p0ReferenceMeasures h

theorem ref_eta_eq : (M₀).eta = p0CompanionMeasure kappa0 nu0 := rfl

theorem ref_freq_eq :
    p0FrequencyMeasure (M₀) = Measure.map (fun t : ℝ => (-(t : ℂ))) mu0 := rfl

theorem measurable_log_norm_sub (z : ℂ) : Measurable fun w : ℂ => Real.log ‖z - w‖ :=
  Real.measurable_log.comp (continuous_norm.comp (continuous_const.sub continuous_id)).measurable

/-- The reflected-frequency potential of the reference. -/
theorem ref_freq_potential (z : ℂ) :
    l6LogPotential (p0FrequencyMeasure (M₀)) z = reflectedFrequencyPotential z := by
  rw [ref_freq_eq, l6LogPotential, integral_map measurable_reflect.aemeasurable
    (measurable_log_norm_sub z).aestronglyMeasurable, reflectedFrequencyPotential_eq_mixed]
  simp only [sub_neg_eq_add]
  rfl

theorem ref_freq_potential_neg (t : ℝ) :
    l6LogPotential (p0FrequencyMeasure (M₀)) (-(t : ℂ)) =
      ConfigSegment.frequencyReferencePotential t := by
  rw [ref_freq_potential, reflectedFrequencyPotential_eq_mixed]
  unfold ConfigSegment.frequencyReferencePotential
  apply integral_congr_ae
  filter_upwards with s
  congr 1
  rw [show -(t : ℂ) + (s : ℂ) = ((s - t : ℝ) : ℂ) by push_cast; ring, Complex.norm_real,
    Real.norm_eq_abs, abs_sub_comm]

/-- The companion potential of the reference, wherever its kernel is integrable. -/
theorem ref_eta_potential {z : ℂ}
    (hz : Integrable (fun w : ℂ => Real.log ‖z - w‖) (M₀).eta) :
    l6LogPotential (M₀).eta z = etaReferencePotential z := by
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  rw [ref_eta_eq] at hz ⊢
  have hmap : Integrable (fun w : ℂ => Real.log ‖z - w‖)
      (Measure.map Complex.ofReal kappa0) :=
    hz.mono_measure (Measure.le_add_right le_rfl)
  have hnu : Integrable (fun w : ℂ => Real.log ‖z - w‖) nu0 :=
    hz.mono_measure (Measure.le_add_left le_rfl)
  rw [l6LogPotential, p0CompanionMeasure, integral_add_measure hmap hnu,
    hemb.integral_map, etaReferencePotential,
    ConfigContourMeasure.contourReferencePotential_eq_integral]
  rfl

theorem kernel_integrable_of_prod_right {μ ν : Measure ℂ} [SFinite μ] [SFinite ν]
    (hint : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    ∀ᵐ z ∂μ, Integrable (fun w : ℂ => Real.log ‖z - w‖) ν := by
  filter_upwards [hint.prod_right_ae] with z hz
  have := hz.neg
  simpa [li2LogKernel] using this

theorem kernel_integrable_of_prod_left {μ ν : Measure ℂ} [SFinite μ] [SFinite ν]
    (hint : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    ∀ᵐ w ∂ν, Integrable (fun z : ℂ => Real.log ‖w - z‖) μ := by
  filter_upwards [hint.prod_left_ae] with w hw
  have := hw.neg
  simpa [li2LogKernel, norm_sub_rev] using this

theorem companionField_eq (z : ℂ) :
    p0CompanionField z = Config.A0 z - Config.phi z := by
  simp only [p0CompanionField, A0, phi, Config.A0, Config.phi, ell]

theorem B0_sub_psi_eq (t : ℝ) : B0 t - psi t = Config.B0 t - Config.psi t := by
  simp only [B0, psi, Config.B0, Config.psi, ell]

/-- `p0DualWeta = Weta actualReference`, `M.eta`-a.e. -/
theorem dualWeta_ae_eq (M : P0AdmissibleMeasures) (hcross : P0L6CrossEnergy M (M₀)) :
    p0DualWeta (M₀) =ᵐ[M.eta] Config.Weta actualReference := by
  filter_upwards [kernel_integrable_of_prod_right hcross.eta_eta₀] with z hz
  rw [p0DualWeta, ref_eta_potential h hz, ref_freq_potential, companionField_eq]
  rfl

/-- `p0DualWmu = Wmu actualReference`, `M.mu`-a.e. -/
theorem dualWmu_ae_eq (M : P0AdmissibleMeasures) (hcross : P0L6CrossEnergy M (M₀)) :
    p0DualWmu (M₀) =ᵐ[M.mu] Config.Wmu actualReference := by
  have hw := kernel_integrable_of_prod_left hcross.eta₀_freq
  rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure] at hw
  have ht := ae_of_ae_map measurable_reflect.aemeasurable hw
  filter_upwards [ht] with t hti
  rw [p0DualWmu, ref_eta_potential h hti, ref_freq_potential_neg, B0_sub_psi_eq]
  simp only [Config.Wmu, actualReference]
  rw [show ((-t : ℝ) : ℂ) = -(t : ℂ) by push_cast; ring]

/-- `l6QLog η₀ μ₀⁻ = actualReference.qLog`. -/
theorem ref_qLog :
    l6QLog (M₀).eta (p0FrequencyMeasure (M₀)) = actualReference.qLog := by
  have hfin := h.finite_energy
  have hEE := eta_kernel_integrable (M₀) hfin
  have hFF := freq_kernel_integrable (M₀) hfin
  have hEF := eta_freq_kernel_integrable (M₀) hfin
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  -- eta-eta
  have hpotE : l6LogPotential (M₀).eta =ᵐ[(M₀).eta] etaReferencePotential := by
    filter_upwards [kernel_integrable_of_prod_right hEE] with z hz
    exact ref_eta_potential h hz
  have hintE : Integrable etaReferencePotential (M₀).eta :=
    (integrable_potential hEE).congr hpotE
  have hsplit : ∀ f : ℂ → ℝ, Integrable f (M₀).eta →
      ∫ z, f z ∂(M₀).eta = etaReferenceIntegral f := by
    intro f hf
    rw [ref_eta_eq] at hf ⊢
    have hmap : Integrable f (Measure.map Complex.ofReal kappa0) :=
      hf.mono_measure (Measure.le_add_right le_rfl)
    have hnu : Integrable f nu0 := hf.mono_measure (Measure.le_add_left le_rfl)
    rw [p0CompanionMeasure, integral_add_measure hmap hnu, hemb.integral_map,
      etaReferenceIntegral,
      ConfigContourMeasure.contourReferenceIntegral_eq_integral hnu.aestronglyMeasurable]
    rfl
  have hI1 : li2LogInteraction (M₀).eta (M₀).eta = -qEtaEta := by
    rw [li2LogInteraction_eq_neg_integral_potential hEE, integral_congr_ae hpotE,
      hsplit _ hintE]
    rfl
  -- eta-freq
  have hintF : Integrable reflectedFrequencyPotential (M₀).eta := by
    have := integrable_potential hEF
    exact this.congr (Filter.Eventually.of_forall fun z => ref_freq_potential h z)
  have hI3 : li2LogInteraction (M₀).eta (p0FrequencyMeasure (M₀)) = -qEtaMu := by
    rw [li2LogInteraction_eq_neg_integral_potential hEF]
    rw [show (fun z => l6LogPotential (p0FrequencyMeasure (M₀)) z) =
        reflectedFrequencyPotential from funext (ref_freq_potential h),
      hsplit _ hintF]
    rfl
  -- freq-freq
  have hI2 : li2LogInteraction (p0FrequencyMeasure (M₀)) (p0FrequencyMeasure (M₀)) =
      -qMuMu := by
    have hpot := integrable_potential hFF
    rw [li2LogInteraction_eq_neg_integral_potential hFF]
    rw [ref_freq_eq] at hpot ⊢
    rw [integral_map measurable_reflect.aemeasurable hpot.aestronglyMeasurable]
    rw [← ref_freq_eq h]
    simp only [ref_freq_potential_neg]
    rfl
  rw [l6QLog, hI1, hI2, hI3]
  simp only [actualReference]
  ring

/-- The L6 linearization at the actual reference, from the U2 residuals. -/
theorem actualReferenceLinearization_of_L6
    (hCross : ∀ M : P0AdmissibleMeasures, P0FiniteEnergyCondition M →
      P0L6CrossEnergy M (M₀)) :
    ActualReferenceLinearization := by
  intro M hM
  have hcross := hCross M hM
  have hWη := p0DualWeta_integrable M (M₀) hM hcross
  have hWμ := p0DualWmu_integrable M (M₀) hM hcross
  have hEq := dualWeta_ae_eq h M hcross
  have hMq := dualWmu_ae_eq h M hcross
  refine ⟨hWη.congr hEq, hWμ.congr hMq, ?_⟩
  have hge := p0Dual_regularizedEnergy_ge_of_caps M (M₀) hM h.finite_energy hcross
    (∫ z, p0DualWeta (M₀) z ∂M.eta) (∫ t, p0DualWmu (M₀) t ∂M.mu) 0 0
    (by simp) (by simp)
  rw [ref_qLog h, integral_congr_ae hEq, integral_congr_ae hMq] at hge
  unfold Config.cAConstant
  unfold ell at hge
  linarith

/-- The same, with the cross energies from uniform bounds on the positive
reference potentials (U2 `p0L6CrossEnergy_of_uniform_reference_potential`). -/
theorem actualReferenceLinearization_of_uniform_bounds {Cη Cφ : ENNReal}
    (hηbound : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂(M₀).eta ≤ Cη)
    (hφbound : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂(p0FrequencyMeasure (M₀)) ≤ Cφ)
    (hCη : Cη ≠ ⊤) (hCφ : Cφ ≠ ⊤) :
    ActualReferenceLinearization :=
  actualReferenceLinearization_of_L6 h fun M hM =>
    p0L6CrossEnergy_of_uniform_reference_potential_of_admissible M (M₀) hM
      h.finite_energy hηbound hφbound hCη hCφ

end Bridge

end

end Li2Lean.P0.CA.Receipt
