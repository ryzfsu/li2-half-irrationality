/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Dual
import Li2Lean.P0.ReferenceCrossEnergyActual
import Li2Lean.P0.ReferencePackaging
import Li2Lean.P0.ConfigReferenceSymmetry
import Li2Lean.P0.ConfigContourMeasure

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0

noncomputable section

open L6Admissible L6Variations
open ConfigReferenceSymmetry ReferencePackaging ConfigSegment ConfigContourMeasure

noncomputable def actualReferenceMeasures : P0AdmissibleMeasures :=
  p0ReferenceMeasures p0ReferenceFiniteEnergyData_literal

theorem actualReference_eta_eq :
    actualReferenceMeasures.eta = p0CompanionMeasure kappa0 nu0 := rfl

theorem actualReference_frequency_eq :
    p0FrequencyMeasure actualReferenceMeasures =
      Measure.map (fun t : ℝ => (-(t : ℂ))) mu0 := rfl

theorem measurable_log_norm_sub (z : ℂ) :
    Measurable (fun w : ℂ => Real.log ‖z - w‖) :=
  Real.measurable_log.comp
    (continuous_norm.comp (continuous_const.sub continuous_id)).measurable

theorem actualReference_frequency_potential (z : ℂ) :
    L6Variations.l6LogPotential (p0FrequencyMeasure actualReferenceMeasures) z =
      reflectedFrequencyPotential z := by
  rw [actualReference_frequency_eq, L6Variations.l6LogPotential,
    integral_map measurable_reflect.aemeasurable
      (measurable_log_norm_sub z).aestronglyMeasurable,
    reflectedFrequencyPotential_eq_mixed]
  simp only [sub_neg_eq_add]
  rfl

theorem actualReference_frequency_potential_neg (t : ℝ) :
    L6Variations.l6LogPotential (p0FrequencyMeasure actualReferenceMeasures)
      (-(t : ℂ)) =
      ConfigSegment.frequencyReferencePotential t := by
  rw [actualReference_frequency_potential,
    reflectedFrequencyPotential_eq_mixed]
  unfold ConfigSegment.frequencyReferencePotential
  apply integral_congr_ae
  filter_upwards with s
  congr 1
  rw [show -(t : ℂ) + (s : ℂ) = ((s - t : ℝ) : ℂ) by
      push_cast; ring, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

theorem actualReference_eta_potential {z : ℂ}
    (hz : Integrable (fun w : ℂ => Real.log ‖z - w‖)
      actualReferenceMeasures.eta) :
    L6Variations.l6LogPotential actualReferenceMeasures.eta z =
      etaReferencePotential z := by
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  rw [actualReference_eta_eq] at hz ⊢
  have hmap : Integrable (fun w : ℂ => Real.log ‖z - w‖)
      (Measure.map Complex.ofReal kappa0) :=
    hz.mono_measure (Measure.le_add_right le_rfl)
  have hnu : Integrable (fun w : ℂ => Real.log ‖z - w‖) nu0 :=
    hz.mono_measure (Measure.le_add_left le_rfl)
  rw [L6Variations.l6LogPotential, p0CompanionMeasure,
    integral_add_measure hmap hnu, hemb.integral_map,
    etaReferencePotential,
    ConfigContourMeasure.contourReferencePotential_eq_integral]
  rfl

theorem kernel_integrable_of_prod_right {μ ν : Measure ℂ} [SFinite μ] [SFinite ν]
    (hint : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    ∀ᵐ z ∂μ, Integrable (fun w : ℂ => Real.log ‖z - w‖) ν := by
  filter_upwards [hint.prod_right_ae] with z hz
  have hz' := hz.neg
  simpa [li2LogKernel] using hz'

theorem kernel_integrable_of_prod_left {μ ν : Measure ℂ} [SFinite μ] [SFinite ν]
    (hint : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν)) :
    ∀ᵐ w ∂ν, Integrable (fun z : ℂ => Real.log ‖w - z‖) μ := by
  filter_upwards [hint.prod_left_ae] with w hw
  have hw' := hw.neg
  simpa [li2LogKernel, norm_sub_rev] using hw'

theorem companionField_eq (z : ℂ) :
    p0CompanionField z = Config.A0 z - Config.phi z := by
  simp only [p0CompanionField, A0, phi, Config.A0, Config.phi, ell]

theorem regularizedField_eq (t : ℝ) :
    B0 t - psi t = Config.B0 t - Config.psi t := by
  simp only [B0, psi, Config.B0, Config.psi, ell]

theorem actualReference_dualWeta_ae_eq (M : P0AdmissibleMeasures)
    (hcross : P0L6CrossEnergy M actualReferenceMeasures) :
    p0DualWeta actualReferenceMeasures =ᵐ[M.eta]
      Config.Weta actualReference := by
  filter_upwards [kernel_integrable_of_prod_right hcross.eta_eta₀] with z hz
  rw [p0DualWeta, actualReference_eta_potential hz,
    actualReference_frequency_potential, companionField_eq]
  rfl

theorem actualReference_dualWmu_ae_eq (M : P0AdmissibleMeasures)
    (hcross : P0L6CrossEnergy M actualReferenceMeasures) :
    p0DualWmu actualReferenceMeasures =ᵐ[M.mu]
      Config.Wmu actualReference := by
  have hw := kernel_integrable_of_prod_left hcross.eta₀_freq
  rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure] at hw
  have ht := ae_of_ae_map measurable_reflect.aemeasurable hw
  filter_upwards [ht] with t hti
  rw [p0DualWmu, actualReference_eta_potential hti,
    actualReference_frequency_potential_neg, regularizedField_eq]
  simp only [Config.Wmu, actualReference]
  rw [show ((-t : ℝ) : ℂ) = -(t : ℂ) by push_cast; ring]

theorem actualReference_qLog_eq :
    L6Variations.l6QLog actualReferenceMeasures.eta
      (p0FrequencyMeasure actualReferenceMeasures) =
      actualReference.qLog := by
  have hfin := p0ReferenceFiniteEnergyData_literal.finite_energy
  have hEE := eta_kernel_integrable actualReferenceMeasures hfin
  have hFF := freq_kernel_integrable actualReferenceMeasures hfin
  have hEF := eta_freq_kernel_integrable actualReferenceMeasures hfin
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hpotE : L6Variations.l6LogPotential actualReferenceMeasures.eta =ᵐ[
      actualReferenceMeasures.eta] etaReferencePotential := by
    filter_upwards [kernel_integrable_of_prod_right hEE] with z hz
    exact actualReference_eta_potential hz
  have hintE : Integrable etaReferencePotential actualReferenceMeasures.eta :=
    (L6Variations.integrable_potential hEE).congr hpotE
  have hsplit : ∀ f : ℂ → ℝ, Integrable f actualReferenceMeasures.eta →
      ∫ z, f z ∂actualReferenceMeasures.eta = etaReferenceIntegral f := by
    intro f hf
    rw [actualReference_eta_eq] at hf ⊢
    have hmap : Integrable f (Measure.map Complex.ofReal kappa0) :=
      hf.mono_measure (Measure.le_add_right le_rfl)
    have hnu : Integrable f nu0 := hf.mono_measure (Measure.le_add_left le_rfl)
    rw [p0CompanionMeasure, integral_add_measure hmap hnu,
      hemb.integral_map, etaReferenceIntegral,
      ConfigContourMeasure.contourReferenceIntegral_eq_integral
        hnu.aestronglyMeasurable]
    rfl
  have hI1 : li2LogInteraction actualReferenceMeasures.eta
      actualReferenceMeasures.eta = -qEtaEta := by
    rw [L6Variations.li2LogInteraction_eq_neg_integral_potential hEE,
      integral_congr_ae hpotE, hsplit _ hintE]
    rfl
  have hintF : Integrable reflectedFrequencyPotential actualReferenceMeasures.eta := by
    have h := L6Variations.integrable_potential hEF
    exact h.congr (Filter.Eventually.of_forall
      (fun z => actualReference_frequency_potential z))
  have hI3 : li2LogInteraction actualReferenceMeasures.eta
      (p0FrequencyMeasure actualReferenceMeasures) = -qEtaMu := by
    rw [L6Variations.li2LogInteraction_eq_neg_integral_potential hEF]
    rw [show (fun z => L6Variations.l6LogPotential
        (p0FrequencyMeasure actualReferenceMeasures) z) =
          reflectedFrequencyPotential
      from funext actualReference_frequency_potential, hsplit _ hintF]
    rfl
  have hI2 : li2LogInteraction (p0FrequencyMeasure actualReferenceMeasures)
      (p0FrequencyMeasure actualReferenceMeasures) = -qMuMu := by
    have hpot := L6Variations.integrable_potential hFF
    rw [L6Variations.li2LogInteraction_eq_neg_integral_potential hFF]
    rw [actualReference_frequency_eq] at hpot ⊢
    rw [integral_map measurable_reflect.aemeasurable hpot.aestronglyMeasurable]
    rw [← actualReference_frequency_eq]
    simp only [actualReference_frequency_potential_neg]
    rfl
  rw [L6Variations.l6QLog, hI1, hI2, hI3]
  simp only [actualReference]
  ring

/-! ## The actual-reference density caps

The cap certificate below is deliberately independent of the directed-cell
receipt.  Its penalty fields are the exact integrals needed by the measure
argument; an adapter from a `Config.CAReceipt` must still prove the endpoint
and interval-integral identifications.
-/

theorem actual_kappa_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ x ∂M.kappa, x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
  have h0 : M.kappa (Set.Icc (1 / 4 : ℝ) (5 / 4))ᶜ = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      M.kappa (Set.Icc (1 / 4 : ℝ) (5 / 4))ᶜ ≤
          volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4))
            (Set.Icc (1 / 4 : ℝ) (5 / 4))ᶜ := M.kappa_le_density _
      _ = 0 := by
        rw [Measure.restrict_apply measurableSet_Icc.compl,
          Set.compl_inter_self, measure_empty]
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by
    simpa using hx

theorem actual_mu_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ t ∂M.mu, t ∈ Set.Ici (1 / 2 : ℝ) := by
  have h0 : M.mu (Set.Ici (1 / 2 : ℝ))ᶜ = 0 := by
    refine le_antisymm ?_ bot_le
    calc
      M.mu (Set.Ici (1 / 2 : ℝ))ᶜ ≤
          volume.restrict (Set.Ici (1 / 2 : ℝ))
            (Set.Ici (1 / 2 : ℝ))ᶜ := M.mu_le_density _
      _ = 0 := by
        rw [Measure.restrict_apply measurableSet_Ici.compl,
          Set.compl_inter_self, measure_empty]
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by
    simpa using hx

theorem actual_nu_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ z ∂M.nu, z ∈ Gamma := by
  have h0 : M.nu Gammaᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr M.nu_supported)
      (Measure.measure_compl_support)
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by
    simpa using hx

theorem actual_kappa_nu_real_mass (M : P0AdmissibleMeasures) :
    M.kappa.real Set.univ + M.nu.real Set.univ = 1 := by
  have hmass : M.kappa Set.univ + M.nu Set.univ = 1 := by
    have h := M.companion_mass
    rw [p0CompanionMeasure, Measure.add_apply,
      Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
      preimage_univ] at h
    exact h
  have hk_top : M.kappa Set.univ ≠ ⊤ := by
    intro hk
    have : (⊤ : ENNReal) = 1 := by simpa [hk] using hmass
    exact ENNReal.top_ne_one this
  have hn_top : M.nu Set.univ ≠ ⊤ := by
    intro hn
    have : (⊤ : ENNReal) = 1 := by simpa [hn] using hmass
    exact ENNReal.top_ne_one this
  have h := congrArg ENNReal.toReal hmass
  rw [ENNReal.toReal_add hk_top hn_top] at h
  simpa [Measure.real] using h

instance actual_kappa_isFinite (M : P0AdmissibleMeasures) :
    IsFiniteMeasure M.kappa := by
  constructor
  have h : M.kappa Set.univ + M.nu Set.univ = 1 := by
    have h' := M.companion_mass
    rw [p0CompanionMeasure, Measure.add_apply,
      Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
      preimage_univ] at h'
    exact h'
  have hle : M.kappa Set.univ ≤ 1 := by
    rw [← h]
    exact le_self_add
  exact lt_of_le_of_lt hle ENNReal.one_lt_top

instance actual_nu_isFinite (M : P0AdmissibleMeasures) :
    IsFiniteMeasure M.nu := by
  constructor
  have h : M.kappa Set.univ + M.nu Set.univ = 1 := by
    have h' := M.companion_mass
    rw [p0CompanionMeasure, Measure.add_apply,
      Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
      preimage_univ] at h'
    exact h'
  have hle : M.nu Set.univ ≤ 1 := by
    rw [← h]
    exact le_add_self
  exact lt_of_le_of_lt hle ENNReal.one_lt_top

theorem actual_integral_ge_of_cap {m : Measure ℝ} [IsFiniteMeasure m]
    {S : Set ℝ} (hS : MeasurableSet S)
    (hm : m ≤ volume.restrict S) (hmS : ∀ᵐ x ∂m, x ∈ S)
    {W p : ℝ → ℝ} {h : ℝ} (hW : Integrable W m)
    (hp0 : ∀ x ∈ S, 0 ≤ p x)
    (hpW : ∀ x ∈ S, h - W x ≤ p x)
    (hpInt : IntegrableOn p S) :
    h * m.real Set.univ - ∫ x in S, p x ≤ ∫ x, W x ∂m := by
  have hpm : Integrable p m :=
    (show Integrable p (volume.restrict S) from hpInt).mono_measure hm
  have hmono : ∫ x, (h - p x) ∂m ≤ ∫ x, W x ∂m := by
    apply integral_mono_ae ((integrable_const h).sub hpm) hW
    filter_upwards [hmS] with x hx
    change h - p x ≤ W x
    linarith [hpW x hx]
  have hsplit : ∫ x, (h - p x) ∂m =
      h * m.real Set.univ - ∫ x, p x ∂m := by
    rw [integral_sub (integrable_const h) hpm, integral_const,
      smul_eq_mul, mul_comm]
  have hpS : ∫ x, p x ∂m ≤ ∫ x in S, p x := by
    apply integral_mono_measure hm _ hpInt
    filter_upwards [ae_restrict_mem hS] with x hx
    exact hp0 x hx
  linarith

theorem actual_eta_cap (M : P0AdmissibleMeasures) {W : ℂ → ℝ} {h : ℝ}
    {p : ℝ → ℝ} (hW : Integrable W M.eta)
    (hGamma : ∀ z ∈ Gamma, h ≤ W z)
    (hp0 : ∀ x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4), 0 ≤ p x)
    (hpW : ∀ x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4),
      h - W (x : ℂ) ≤ p x)
    (hpInt : IntegrableOn p (Set.Icc (1 / 4 : ℝ) (5 / 4))) :
    h - ∫ x in Set.Icc (1 / 4 : ℝ) (5 / 4), p x ≤ ∫ z, W z ∂M.eta := by
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hWmap : Integrable W (Measure.map Complex.ofReal M.kappa) :=
    hW.mono_measure (Measure.le_add_right le_rfl)
  have hWnu : Integrable W M.nu :=
    hW.mono_measure (Measure.le_add_left le_rfl)
  have hWk : Integrable (fun x : ℝ => W (x : ℂ)) M.kappa :=
    (hemb.integrable_map_iff).mp hWmap
  have hsplit : ∫ z, W z ∂M.eta =
      (∫ x, W (x : ℂ) ∂M.kappa) + ∫ z, W z ∂M.nu := by
    rw [P0AdmissibleMeasures.eta, p0CompanionMeasure,
      integral_add_measure hWmap hWnu, hemb.integral_map]
  have hk := actual_integral_ge_of_cap measurableSet_Icc
    M.kappa_le_density (actual_kappa_ae_mem M) hWk hp0 hpW hpInt
  have hn : h * M.nu.real Set.univ ≤ ∫ z, W z ∂M.nu := by
    have hh := integral_mono_ae (integrable_const h) hWnu
      ((actual_nu_ae_mem M).mono fun z hz => hGamma z hz)
    rwa [integral_const, smul_eq_mul, mul_comm] at hh
  have hmass : h * M.kappa.real Set.univ + h * M.nu.real Set.univ = h := by
    rw [← mul_add, actual_kappa_nu_real_mass M, mul_one]
  rw [hsplit]
  linarith

theorem actual_mu_cap (M : P0AdmissibleMeasures) {W q : ℝ → ℝ} {h : ℝ}
    (hW : Integrable W M.mu)
    (hq0 : ∀ t ∈ Set.Ici (1 / 2 : ℝ), 0 ≤ q t)
    (hqW : ∀ t ∈ Set.Ici (1 / 2 : ℝ), h - W t ≤ q t)
    (hqInt : IntegrableOn q (Set.Ici (1 / 2 : ℝ))) :
    h - ∫ t in Set.Ici (1 / 2 : ℝ), q t ≤ ∫ t, W t ∂M.mu := by
  have hk := actual_integral_ge_of_cap measurableSet_Ici M.mu_le_density
    (actual_mu_ae_mem M) hW hq0 hqW hqInt
  have hmass : M.mu.real Set.univ = 1 := by
    simp [Measure.real, M.frequency_mass]
  rw [hmass, mul_one] at hk
  exact hk

structure ActualReferencePenaltyCertificate where
  hEta : ℝ
  hMu : ℝ
  eta_lower : ∀ z : ℂ, (z ∈ Gamma) →
    hEta ≤ ((Config.Weta ConfigReferenceSymmetry.actualReference) z)
  p : ℝ → ℝ
  q : ℝ → ℝ
  p_nonneg : ∀ x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4), 0 ≤ p x
  p_lower : ∀ x : ℝ, (x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4)) →
    hEta - ((Config.Weta ConfigReferenceSymmetry.actualReference) (x : ℂ)) ≤ p x
  p_integrable : IntegrableOn p (Set.Icc (1 / 4 : ℝ) (5 / 4))
  q_nonneg : ∀ t ∈ Set.Ici (1 / 2 : ℝ), 0 ≤ q t
  q_lower : ∀ t : ℝ, (t ∈ Set.Ici (1 / 2 : ℝ)) →
    hMu - ((Config.Wmu ConfigReferenceSymmetry.actualReference) t) ≤ q t
  q_integrable : IntegrableOn q (Set.Ici (1 / 2 : ℝ))
  P : ℝ
  T : ℝ
  P_eq : P = ∫ x in Set.Icc (1 / 4 : ℝ) (5 / 4), p x
  T_eq : T = ∫ t in Set.Ici (1 / 2 : ℝ), q t

noncomputable def actualReferencePenaltyCertificate_of_max
    {hEta hMu : ℝ}
    (hEtaLower : ∀ z : ℂ, (z ∈ Gamma) →
      hEta ≤ ((Config.Weta ConfigReferenceSymmetry.actualReference) z))
    (hpInt : IntegrableOn
      (fun x : ℝ => max (hEta -
        (Config.Weta ConfigReferenceSymmetry.actualReference) (x : ℂ)) 0)
      (Set.Icc (1 / 4 : ℝ) (5 / 4)))
    (hqInt : IntegrableOn
      (fun t : ℝ => max (hMu -
        (Config.Wmu ConfigReferenceSymmetry.actualReference) t) 0)
      (Set.Ici (1 / 2 : ℝ))) :
    ActualReferencePenaltyCertificate := by
  let p : ℝ → ℝ := fun x => max (hEta -
    (Config.Weta ConfigReferenceSymmetry.actualReference) (x : ℂ)) 0
  let q : ℝ → ℝ := fun t => max (hMu -
    (Config.Wmu ConfigReferenceSymmetry.actualReference) t) 0
  refine {
    hEta := hEta
    hMu := hMu
    eta_lower := hEtaLower
    p := p
    q := q
    p_nonneg := ?_
    p_lower := ?_
    p_integrable := ?_
    q_nonneg := ?_
    q_lower := ?_
    q_integrable := ?_
    P := ∫ x in Set.Icc (1 / 4 : ℝ) (5 / 4), p x
    T := ∫ t in Set.Ici (1 / 2 : ℝ), q t
    P_eq := rfl
    T_eq := rfl }
  · intro x hx
    exact le_max_right _ _
  · intro x hx
    exact le_max_left _ _
  · simpa [p] using hpInt
  · intro t ht
    exact le_max_right _ _
  · intro t ht
    exact le_max_left _ _
  · simpa [q] using hqInt

theorem actualReference_caps
    (C : ActualReferencePenaltyCertificate) :
    ∀ M : P0AdmissibleMeasures, P0FiniteEnergyCondition M →
      ∃ hcross : P0L6CrossEnergy M actualReferenceMeasures,
        C.hEta - C.P ≤ ∫ z, p0DualWeta actualReferenceMeasures z ∂M.eta ∧
        C.hMu - C.T ≤ ∫ t, p0DualWmu actualReferenceMeasures t ∂M.mu := by
  intro M hM
  have hcross := p0L6CrossEnergy_actual_reference M hM
  have hWeta := p0DualWeta_integrable M actualReferenceMeasures hM hcross
  have hWmu := p0DualWmu_integrable M actualReferenceMeasures hM hcross
  have hWeta_actual : Integrable
      (Config.Weta ConfigReferenceSymmetry.actualReference) M.eta :=
    hWeta.congr (actualReference_dualWeta_ae_eq M hcross)
  have hWmu_actual : Integrable
      (Config.Wmu ConfigReferenceSymmetry.actualReference) M.mu :=
    hWmu.congr (actualReference_dualWmu_ae_eq M hcross)
  have hEta := actual_eta_cap
    (W := Config.Weta ConfigReferenceSymmetry.actualReference) M hWeta_actual
    C.eta_lower
    C.p_nonneg C.p_lower C.p_integrable
  have hMu := actual_mu_cap
    (W := Config.Wmu ConfigReferenceSymmetry.actualReference) M hWmu_actual
    C.q_nonneg C.q_lower C.q_integrable
  rw [← C.P_eq] at hEta
  rw [← C.T_eq] at hMu
  rw [← integral_congr_ae (actualReference_dualWeta_ae_eq M hcross)] at hEta
  rw [← integral_congr_ae (actualReference_dualWmu_ae_eq M hcross)] at hMu
  exact ⟨hcross, hEta, hMu⟩

theorem actualReference_alphaGamma_lower
    (C : ActualReferencePenaltyCertificate) :
    ((9 / 2 : ℝ) - 2 * ell +
      L6Variations.l6QLog actualReferenceMeasures.eta
        (p0FrequencyMeasure actualReferenceMeasures) +
      C.hEta + C.hMu - C.P - C.T : WithTop ℝ) ≤ alphaGamma := by
  have hfin₀ : P0FiniteEnergyCondition actualReferenceMeasures :=
    p0ReferenceMeasures_finite_energy p0ReferenceFiniteEnergyData_literal
  exact p0AlphaGamma_ge_of_L6_caps actualReferenceMeasures hfin₀
    C.hEta C.hMu C.P C.T (actualReference_caps C)

theorem actualReference_alphaGamma_lower_qLog
    (C : ActualReferencePenaltyCertificate) :
    ((9 / 2 : ℝ) - 2 * ell + actualReference.qLog +
      C.hEta + C.hMu - C.P - C.T : WithTop ℝ) ≤ alphaGamma := by
  rw [← actualReference_qLog_eq]
  exact actualReference_alphaGamma_lower C

end
end Li2Lean.P0
