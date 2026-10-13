/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube.Gap.FieldPointwise
import Li2Lean.P0.TubeTransferCertificateAdapter

/-! # The tube cost ledger for the actual sweep

This file discharges the two semantic inputs of the tube transfer for the
concrete sweep `p0TubeSweep` (kappa and mu fixed, nu replaced by its harmonic
sweep):

* `p0TubeFieldGap_le`: `F ≤ 288 s δ / B` with `s = ν(ℂ)`;
* `p0TubeInteractionGap_le`: `I ≤ 3 b` with `b = ∫ e dν`.

Both are derived from the actual measures; no hypothesis restates either
inequality.  `p0TubeCostLedger` is the exact `cost_ledger` shape of
`P0TubeEnergyComparisonObligations`, and `p0TubeAlpha_ge_actual` closes the
`WithTop` infimum passage `inf_{T_δ} E ≥ α_Γ - 300 δ` with no remaining
certificate field.
-/

open MeasureTheory ProbabilityTheory Filter

namespace Li2Lean.P0.TubeGap

noncomputable section

open TubeInterior TubeEnergy

/-- Basic facts of a tube competitor: finiteness, supports, and the mass split. -/
theorem tube_competitor_facts {δ : ℝ} (M : P0TubeAdmissibleMeasures δ) :
    IsFiniteMeasure (Measure.map Complex.ofReal M.kappa) ∧ IsFiniteMeasure M.nu ∧
    IsFiniteMeasure M.mu ∧
    (∀ᵐ z ∂M.nu, z ∈ tube δ) ∧
    (∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa), z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0) ∧
    (∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa), ‖z‖ ≤ 4) ∧
    (∀ᵐ t ∂M.mu, t ∈ Set.Ici (1 / 2 : ℝ)) ∧
    (Measure.map Complex.ofReal M.kappa).real Set.univ + M.nu.real Set.univ = 1 := by
  have hηmass : (Measure.map Complex.ofReal M.kappa + M.nu) Set.univ = 1 := by
    simpa [p0CompanionMeasure] using M.companion_mass
  have hκfin : (Measure.map Complex.ofReal M.kappa) Set.univ ≠ ⊤ := by
    have h := le_self_add (a := (Measure.map Complex.ofReal M.kappa) Set.univ)
      (b := M.nu Set.univ)
    rw [← Measure.add_apply, hηmass] at h
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  have hνfin : M.nu Set.univ ≠ ⊤ := by
    have h := le_add_self (a := M.nu Set.univ)
      (b := (Measure.map Complex.ofReal M.kappa) Set.univ)
    rw [← Measure.add_apply, hηmass] at h
    exact ne_top_of_le_ne_top ENNReal.one_ne_top h
  have hk_ae : ∀ᵐ x ∂M.kappa, x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) :=
    (Measure.absolutelyContinuous_of_le M.kappa_le_density).ae_le
      (ae_restrict_mem measurableSet_Icc)
  refine ⟨⟨lt_top_iff_ne_top.mpr hκfin⟩, ⟨lt_top_iff_ne_top.mpr hνfin⟩,
    ⟨by rw [M.frequency_mass]; simp⟩, ?_, ?_, ?_, ?_, ?_⟩
  · rw [ae_iff]
    apply measure_mono_null (Set.compl_subset_compl.mpr M.nu_supported)
    exact Measure.measure_compl_support
  · have hset : MeasurableSet {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0} :=
      (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
        ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
    rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
    filter_upwards [hk_ae] with x hx
    constructor
    · simp only [Complex.ofReal_re]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · simp
  · have hset : MeasurableSet {z : ℂ | ‖z‖ ≤ 4} :=
      measurableSet_le (by fun_prop) measurable_const
    rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
    filter_upwards [hk_ae] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.1, hx.2]
  · exact (Measure.absolutelyContinuous_of_le M.mu_le_density).ae_le
      (ae_restrict_mem measurableSet_Ici)
  · have h := congrArg ENNReal.toReal hηmass
    rw [Measure.add_apply, ENNReal.toReal_add hκfin hνfin] at h
    simpa [Measure.real] using h

theorem p0TubeSweep_eta {δ : ℝ} (M : P0TubeAdmissibleMeasures δ) :
    (p0TubeSweep M).eta = Measure.map Complex.ofReal M.kappa + tubeSwept M.nu := rfl

theorem p0Tube_eta {δ : ℝ} (M : P0TubeAdmissibleMeasures δ) :
    M.eta = Measure.map Complex.ofReal M.kappa + M.nu := rfl

/-! ## Field gap -/

/-- **Field gap** for the actual sweep: `F ≤ 288 s δ / B`, `s = ν(ℂ)`. -/
theorem p0TubeFieldGap_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ) (hM : p0TubeFiniteEnergyCondition M) :
    p0TubeFieldGap M (p0TubeSweep M) ≤ 288 * M.nu.real Set.univ * δ / semiMinor := by
  obtain ⟨hκF, hνF, -, hνtube, -, hκnorm, -, -⟩ := tube_competitor_facts M
  have hfield : Integrable (fun z : ℂ => p0CompanionField z) M.eta := hM.2.1
  rw [p0Tube_eta] at hfield
  have hfκ : Integrable (fun z : ℂ => p0CompanionField z)
      (Measure.map Complex.ofReal M.kappa) := (integrable_add_measure.mp hfield).1
  have hfν : Integrable (fun z : ℂ => p0CompanionField z) M.nu :=
    (integrable_add_measure.mp hfield).2
  have hfs : Integrable (fun z : ℂ => p0CompanionField z) (tubeSwept M.nu) :=
    EnergyLowerBound.integrable_companionField_of_ae_mem_Gamma (tubeSwept_ae_mem_Gamma M.nu)
  set g : ℂ → ℝ := fun z => ∫ y, p0CompanionField y ∂tubeSweep z with hg
  have hgm : StronglyMeasurable g := by
    have := StronglyMeasurable.integral_kernel_prod_right' (κ := tubeKernel)
      (f := fun q : ℂ × ℂ => p0CompanionField q.2)
      (EnergyLowerBound.stronglyMeasurable_companionField.comp_measurable measurable_snd)
    simpa using this
  have hgb : ∀ z, |g z| ≤ 300 := by
    intro z
    have h := norm_integral_le_of_norm_le_const (μ := tubeSweep z)
      (f := fun y => p0CompanionField y) (C := 300)
      ((tubeSweep_ae_mem_Gamma z).mono fun y hy => by
        rw [Real.norm_eq_abs]
        exact EnergyLowerBound.companionField_abs_le
          (TubeVariance.norm_le_four_of_mem_Gamma hy))
    simpa [Real.norm_eq_abs, g] using h
  have hgi : Integrable g M.nu :=
    integrable_of_bound_ae hgm.aestronglyMeasurable (Eventually.of_forall hgb)
  have hbind : (∫ y, p0CompanionField y ∂tubeSwept M.nu) = ∫ z, g z ∂M.nu :=
    integral_sweptMeasure M.nu tubeSweep _ measurable_tubeSweep.aemeasurable hfs
  have hpt : ∀ᵐ z ∂M.nu, g z - p0CompanionField z ≤ 288 * δ / semiMinor := by
    filter_upwards [hνtube] with z hz
    have := companionField_sweep_le hδ0 hδ hz
    simp only [g]
    linarith
  have hmono : (∫ z, (g z - p0CompanionField z) ∂M.nu) ≤ ∫ _z, 288 * δ / semiMinor ∂M.nu :=
    integral_mono_ae (hgi.sub hfν) (integrable_const _) hpt
  rw [integral_const, smul_eq_mul, integral_sub hgi hfν] at hmono
  unfold p0TubeFieldGap
  rw [p0TubeSweep_eta, p0Tube_eta, integral_add_measure hfκ hfs,
    integral_add_measure hfκ hfν, hbind, p0TubeSweep_mu]
  have : 288 * M.nu.real Set.univ * δ / semiMinor =
      M.nu.real Set.univ * (288 * δ / semiMinor) := by ring
  rw [this]
  linarith

/-! ## Interaction gap -/

theorem li2LogInteraction_comm (μ ν : Measure ℂ) [SFinite μ] [SFinite ν] :
    li2LogInteraction μ ν = li2LogInteraction ν μ := by
  unfold li2LogInteraction
  conv_lhs => rw [← integral_prod_swap]
  congr 1
  funext p
  simp only [Prod.fst_swap, Prod.snd_swap, li2LogKernel, norm_sub_rev]

/-- **Interaction gap** for the actual sweep: `I ≤ 3 b`, `b = ∫ e dν`. -/
theorem p0TubeInteractionGap_le {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ) (hM : p0TubeFiniteEnergyCondition M) :
    p0TubeInteractionGap M (p0TubeSweep M) ≤ 3 * ∫ z, tubeCorrection z ∂M.nu := by
  obtain ⟨hκF, hνF, hμF, hνtube, hκsupp, -, hμae, hmass⟩ := tube_competitor_facts M
  set κc : Measure ℂ := Measure.map Complex.ofReal M.kappa with hκc
  set b : ℝ := ∫ z, tubeCorrection z ∂M.nu with hb
  have hηlog : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((κc + M.nu).prod (κc + M.nu)) := hM.2.2.2.1
  have hκη : κc ≤ κc + M.nu := Measure.le_add_right le_rfl
  have hνη : M.nu ≤ κc + M.nu := Measure.le_add_left le_rfl
  have hκκ := hηlog.mono_measure (Measure.prod_mono hκη hκη)
  have hκν := hηlog.mono_measure (Measure.prod_mono hκη hνη)
  have hνκ := hηlog.mono_measure (Measure.prod_mono hνη hκη)
  have hνν := hηlog.mono_measure (Measure.prod_mono hνη hνη)
  have hsplitM : li2LogInteraction (κc + M.nu) (κc + M.nu) =
      li2LogInteraction κc κc + li2LogInteraction κc M.nu +
        li2LogInteraction M.nu κc + li2LogInteraction M.nu M.nu :=
    li2LogInteraction_add_add κc M.nu κc M.nu hκκ hκν hνκ hνν
  have hsplitN := p0Tube_swept_eta_interaction_split hδ0 hδ M hM
  have hνatom : ∀ z : ℂ, M.nu {z} = 0 := by
    intro z
    have h0 : (κc + M.nu) {z} = 0 := hM.2.2.2.2.1 z
    exact le_antisymm ((hνη {z}).trans_eq h0) bot_le
  have hνlog : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (M.nu.prod M.nu) := by
    simpa [li2LogKernel, realLogKernel] using hνν
  have hself : li2LogInteraction (tubeSwept M.nu) (tubeSwept M.nu) ≤
      li2LogInteraction M.nu M.nu + 2 * M.nu.real Set.univ * b := by
    have h := (tubeSwept_energy_le hδ0 hδ M.nu hνtube hνatom hνlog).2
    simpa [li2LogInteraction, li2LogKernel, realLogKernel] using h
  have hpin : li2LogInteraction (tubeSwept M.nu) κc ≤
      li2LogInteraction M.nu κc + κc.real Set.univ * b := by
    have h := tubeSwept_pinned_transfer hδ0 hδ M.nu hνtube κc hκsupp
    simpa [li2LogInteraction, li2LogKernel, realLogKernel] using h
  have hcomm1 : li2LogInteraction κc (tubeSwept M.nu) =
      li2LogInteraction (tubeSwept M.nu) κc := li2LogInteraction_comm _ _
  have hcomm2 : li2LogInteraction κc M.nu = li2LogInteraction M.nu κc :=
    li2LogInteraction_comm _ _
  -- mixed kernel
  have hmix : Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((κc + M.nu).prod M.mu) := hM.2.2.2.2.2.2
  have hκμ := hmix.mono_measure (Measure.prod_mono hκη le_rfl)
  have hνμ := hmix.mono_measure (Measure.prod_mono hνη le_rfl)
  have hsμ := tubeSwept_mixed_integrable hδ0 hδ M.nu hνtube M.mu hμae
  have hmixT := tubeSwept_mixed_transfer hδ0 hδ M.nu hνtube M.mu hμae
  have hμone : M.mu.real Set.univ = 1 := by simp [Measure.real, M.frequency_mass]
  rw [hμone, one_mul] at hmixT
  have hb0 : 0 ≤ b := integral_nonneg_of_ae (hνtube.mono fun z hz =>
    (tubeCorrection_bounds hδ0 hz).1)
  unfold p0TubeInteractionGap
  rw [p0TubeSweep_eta, p0Tube_eta, p0TubeSweep_mu, hsplitN, hsplitM, sub_self, add_zero,
    Measure.add_prod, Measure.add_prod, integral_add_measure hκμ hsμ,
    integral_add_measure hκμ hνμ, hcomm1, hcomm2]
  have hmass' : κc.real Set.univ * b + M.nu.real Set.univ * b = b := by
    rw [← add_mul, hmass, one_mul]
  have e1 : 2 * M.nu.real Set.univ * b = 2 * (M.nu.real Set.univ * b) := by ring
  rw [e1] at hself
  linarith

/-! ## The cost ledger and the infimum passage -/

/-- `b ≤ s δ / B` for the actual correction integral. -/
theorem tubeCorrection_integral_le {δ : ℝ} (hδ0 : 0 ≤ δ) (M : P0TubeAdmissibleMeasures δ) :
    (∫ z, tubeCorrection z ∂M.nu) ≤ M.nu.real Set.univ * (δ / semiMinor) := by
  obtain ⟨-, hνF, -, hνtube, -, -, -, -⟩ := tube_competitor_facts M
  calc (∫ z, tubeCorrection z ∂M.nu) ≤ ∫ _z, δ / semiMinor ∂M.nu :=
        integral_mono_ae (integrable_tubeCorrection hδ0 M.nu hνtube) (integrable_const _)
          (hνtube.mono fun z hz => (tubeCorrection_bounds hδ0 hz).2)
    _ = M.nu.real Set.univ * (δ / semiMinor) := by rw [integral_const, smul_eq_mul]

/-- **The cost ledger** of `P0TubeEnergyComparisonObligations`, proved for the
actual sweep `p0TubeSweep`, with `s = ν(ℂ)` and `b = ∫ e dν`. -/
theorem p0TubeCostLedger {δ : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ tubeRadiusMax) :
    ∀ M : P0TubeAdmissibleMeasures δ, p0TubeFiniteEnergyCondition M →
      ∃ s b : ℝ,
        0 ≤ s ∧ s ≤ 1 ∧
        b ≤ s * (δ / semiMinor) ∧
        p0TubeFieldGap M (p0TubeSweep M) ≤ 288 * s * δ / semiMinor ∧
        p0TubeInteractionGap M (p0TubeSweep M) ≤ 3 * b := by
  intro M hM
  obtain ⟨hκF, hνF, -, -, -, -, -, hmass⟩ := tube_competitor_facts M
  refine ⟨M.nu.real Set.univ, ∫ z, tubeCorrection z ∂M.nu, measureReal_nonneg, ?_,
    tubeCorrection_integral_le hδ0 M, p0TubeFieldGap_le hδ0 hδ M hM,
    p0TubeInteractionGap_le hδ0 hδ M hM⟩
  have := (measureReal_nonneg : 0 ≤ (Measure.map Complex.ofReal M.kappa).real Set.univ)
  linarith

/-- The energy comparison for every finite-energy tube competitor:
`E(sweep M) ≤ E(M) + 300 δ`. -/
theorem p0Tube_energy_comparison_actual {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ) (hM : p0TubeFiniteEnergyCondition M) :
    p0RegularizedEnergyValue (p0TubeSweep M) ≤ p0TubeRegularizedEnergyValue M + 300 * δ := by
  obtain ⟨s, b, hs0, hs1, hb, hF, hI⟩ := p0TubeCostLedger hδ.le hδmax M hM
  exact p0Tube_energy_comparison_of_costs hδ M p0TubeSweep hs0 hs1 hb hF hI

/-- **Tube transfer, infimum form** (v10 `eq:tube-transfer`):
`inf_{T_δ} E ≥ α_Γ - 300 δ` for `0 < δ ≤ 1/64`, in `WithTop ℝ`, for every real
lower bound `alpha` of `α_Γ`.  No certificate or obligation field is assumed. -/
theorem p0TubeAlpha_ge_actual {δ alpha : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ tubeRadiusMax)
    (halpha : (alpha : WithTop ℝ) ≤ alphaGamma) :
    ((alpha - 300 * δ : ℝ) : WithTop ℝ) ≤ p0TubeAlpha δ := by
  unfold p0TubeAlpha
  apply le_csInf
  · rcases p0TubeAdmissibleMeasures_nonempty δ with ⟨M⟩
    exact ⟨p0TubeExtendedEnergy M, M, rfl⟩
  · intro y hy
    rcases hy with ⟨M, rfl⟩
    by_cases hM : p0TubeFiniteEnergyCondition M
    · have hfin := p0TubeSweep_finite hδ.le hδmax M hM
      have hGammaLe : alphaGamma ≤ p0ExtendedEnergy (p0TubeSweep M) := by
        change (sInf (Set.range p0ExtendedEnergy)) ≤ _
        exact csInf_le EnergyLowerBound.p0ExtendedEnergy_bddBelow
          (Set.mem_range_self (p0TubeSweep M))
      have hAlphaValue : alpha ≤ p0RegularizedEnergyValue (p0TubeSweep M) := by
        have hcast : (alpha : WithTop ℝ) ≤
            (p0RegularizedEnergyValue (p0TubeSweep M) : WithTop ℝ) := by
          calc (alpha : WithTop ℝ) ≤ alphaGamma := halpha
            _ ≤ p0ExtendedEnergy (p0TubeSweep M) := hGammaLe
            _ = (p0RegularizedEnergyValue (p0TubeSweep M) : WithTop ℝ) :=
              p0ExtendedEnergy_eq_value_of_finite (p0TubeSweep M) hfin
        exact_mod_cast hcast
      have hcmp := p0Tube_energy_comparison_actual hδ hδmax M hM
      have hTube : alpha - 300 * δ ≤ p0TubeRegularizedEnergyValue M := by linarith
      rw [p0TubeExtendedEnergy_eq_value_of_finite M hM]
      exact_mod_cast hTube
    · rw [show p0TubeExtendedEnergy M = ⊤ by
        unfold p0TubeExtendedEnergy
        simp [hM]]
      exact le_top

/-- Paper-facing real statement, given only the two real-valued naming bridges
(`alpha_Gamma` and the tube infimum as real numbers). -/
theorem p0Tube_transfer_statement_actual
    (energy : ℝ → ℝ) (alphaGammaReal : ℝ)
    (hAlphaEq : alphaGamma = (alphaGammaReal : WithTop ℝ))
    (hEnergy : ∀ δ, p0TubeEnergyInfimum energy δ) :
    tubeTransferStatement energy alphaGammaReal := by
  intro δ hδ hδmax
  have hbound := p0TubeAlpha_ge_actual hδ hδmax
    (show (alphaGammaReal : WithTop ℝ) ≤ alphaGamma by rw [hAlphaEq])
  rw [← hEnergy δ] at hbound
  exact_mod_cast hbound

end
end Li2Lean.P0.TubeGap
