/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Defs

/-!
# Cell inequality: decomposition of the witness energy

For the configuration witness `(κ_S + ν_δ, μ_R)` the regularized energy
`p0TubeRegularizedEnergyValue` splits into the ten pieces named in
`CellBound/Defs.lean`.  The pinned push-forward is undone by `integral_map`,
the companion self-energy splits bilinearly over `η = κ' + ν` (the cross
term appears twice by the symmetry of the kernel), and the `log (1 + t)`
regularizers cancel: `-3` from the frequency field, `+2` from the frequency
self-kernel (`|μ| = 1`), `+1` from the mixed kernel (`|η| = 1`).
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

variable (C : FiniteConfiguration)

/-- The pinned push-forward. -/
abbrev wA : Measure ℂ := Measure.map Complex.ofReal (wκ C)

theorem wA_le_eta : wA C ≤ (configTubeWitness C).eta := by
  rw [witness_eta_eq]; exact Measure.le_add_right le_rfl

theorem wν_le_eta : wν C ≤ (configTubeWitness C).eta := by
  rw [witness_eta_eq]; exact Measure.le_add_left le_rfl

/-! ## The companion field -/

theorem companion_integral_split :
    ∫ z : ℂ, p0CompanionField z ∂(configTubeWitness C).eta = ePk C + ePν C := by
  have hI := witness_integrable_companion C
  have hA : Integrable (fun z : ℂ => p0CompanionField z) (wA C) :=
    hI.mono_measure (wA_le_eta C)
  have hN : Integrable (fun z : ℂ => p0CompanionField z) (wν C) :=
    hI.mono_measure (wν_le_eta C)
  rw [witness_eta_eq, integral_add_measure hA hN]
  unfold ePk ePν
  rw [integral_map Complex.measurable_ofReal.aemeasurable hA.aestronglyMeasurable]

/-! ## The frequency field -/

theorem log_one_add_integrable (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    Integrable (fun t : ℝ => Real.log (1 + t)) (wμ C) := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc (1 / 2 : ℝ) 20) := by
    apply ContinuousOn.log
    · fun_prop
    · intro t ht h0
      linarith [ht.1]
  exact Integrable.mono_measure hlog.integrableOn_Icc (frequencyMeasure_le_head C hhead)

theorem frequencyField_integral_split (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    ∫ t : ℝ, p0RegularizedFrequencyField t ∂(configTubeWitness C).mu =
      eBμ C - eΨμ C - 3 * ∫ t : ℝ, Real.log (1 + t) ∂(wμ C) := by
  have hle := frequencyMeasure_le_head C hhead
  have hB0 : Continuous P0.B0 := ReferencePackaging.continuous_B0_literal
  have hpsi : Continuous P0.psi := ReferencePackaging.continuous_psi_literal
  have hB : Integrable (fun t : ℝ => P0.B0 t) (wμ C) :=
    Integrable.mono_measure (hB0.continuousOn.integrableOn_Icc (a := (1 / 2 : ℝ)) (b := 20)) hle
  have hP : Integrable (fun t : ℝ => P0.psi t) (wμ C) :=
    Integrable.mono_measure (hpsi.continuousOn.integrableOn_Icc (a := (1 / 2 : ℝ)) (b := 20)) hle
  have hL := log_one_add_integrable C hhead
  change ∫ t : ℝ, (P0.B0 t - P0.psi t - 3 * Real.log (1 + t)) ∂(wμ C) = _
  rw [integral_sub (f := fun t : ℝ => P0.B0 t - P0.psi t)
      (g := fun t : ℝ => 3 * Real.log (1 + t)) (hB.sub hP) (hL.const_mul 3),
    integral_sub (f := fun t : ℝ => P0.B0 t) (g := fun t : ℝ => P0.psi t) hB hP,
    integral_const_mul]
  rfl

/-! ## The companion self-energy -/

theorem li2LogKernel_swap (p : ℂ × ℂ) :
    li2LogKernel p.swap.1 p.swap.2 = li2LogKernel p.1 p.2 := by
  simp only [Prod.fst_swap, Prod.snd_swap, li2LogKernel, norm_sub_rev]

theorem etaSelf_split :
    li2LogInteraction (configTubeWitness C).eta (configTubeWitness C).eta =
      eIkk C + 2 * eIkν C + eIνν C := by
  have hI := witness_integrable_etaSelf C
  rw [witness_eta_eq, Measure.add_prod, Measure.prod_add, Measure.prod_add] at hI
  obtain ⟨⟨hAA, hAN⟩, ⟨hNA, hNN⟩⟩ := by
    rw [integrable_add_measure, integrable_add_measure, integrable_add_measure] at hI
    exact hI
  unfold li2LogInteraction
  rw [witness_eta_eq, Measure.add_prod, Measure.prod_add, Measure.prod_add,
    integral_add_measure (hAA.add_measure hAN) (hNA.add_measure hNN),
    integral_add_measure hAA hAN, integral_add_measure hNA hNN]
  -- the pinned self term
  have hmapAA : (wA C).prod (wA C) =
      Measure.map (Prod.map Complex.ofReal Complex.ofReal) ((wκ C).prod (wκ C)) :=
    Measure.map_prod_map _ _ Complex.measurable_ofReal Complex.measurable_ofReal
  have hAAeq : ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((wA C).prod (wA C)) = eIkk C := by
    rw [hmapAA, integral_map (Complex.measurable_ofReal.prodMap
      Complex.measurable_ofReal).aemeasurable (by rw [← hmapAA]; exact hAA.aestronglyMeasurable)]
    unfold eIkk
    rw [← integral_neg]
    congr 1
    funext p
    simp only [Prod.map, li2LogKernel]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  -- the swapped cross term
  have hNAeq : ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((wν C).prod (wA C)) = eIkν C := by
    unfold eIkν
    rw [← integral_prod_swap (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)]
    congr 1
    funext p
    exact li2LogKernel_swap p
  change ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((wA C).prod (wA C)) +
      ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((wA C).prod (wν C)) +
      (∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((wν C).prod (wA C)) +
        ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((wν C).prod (wν C))) = _
  rw [hAAeq, hNAeq]
  unfold eIkν eIνν li2LogInteraction
  ring

/-! ## The frequency self-kernel -/

theorem frequencyKernel_split (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    ∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2
        ∂((configTubeWitness C).mu.prod (configTubeWitness C).mu) =
      2 * (∫ t : ℝ, Real.log (1 + t) ∂(wμ C)) - eLLμ C := by
  set lam : Measure ℝ := volume.restrict (Set.Icc (1 / 2 : ℝ) 20) with hlam
  have hlamIco : lam = volume.restrict (Set.Ico (1 / 2 : ℝ) 20) :=
    (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  have : IsFiniteMeasure lam := by rw [hlam]; infer_instance
  have hle : wμ C ≤ lam := frequencyMeasure_le_head C hhead
  have hprodle : (wμ C).prod (wμ C) ≤ lam.prod lam := Measure.prod_mono hle hle
  have hlogLam : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|) (lam.prod lam) := by
    rw [hlamIco]
    exact LogSegment.integrable_log_abs_sub_rectangle (by norm_num)
  have hlog : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|) ((wμ C).prod (wμ C)) :=
    hlogLam.mono_measure hprodle
  have hae : ∀ᵐ t ∂(wμ C), t ∈ Set.Icc (1 / 2 : ℝ) 20 := frequencyMeasure_ae_mem C hhead
  have hbd : ∀ᵐ p : ℝ × ℝ ∂((wμ C).prod (wμ C)),
      p.1 ∈ Set.Icc (1 / 2 : ℝ) 20 ∧ p.2 ∈ Set.Icc (1 / 2 : ℝ) 20 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := wμ C) (ν := wμ C)).ae hae,
      (Measure.quasiMeasurePreserving_snd (μ := wμ C) (ν := wμ C)).ae hae] with p h1 h2
    exact ⟨h1, h2⟩
  have hdiag : (lam.prod lam) (Set.diagonal ℝ) = 0 := by
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards with t
    have hset : Prod.mk t ⁻¹' Set.diagonal ℝ = {t} := by
      ext s
      simp [Set.diagonal, eq_comm]
    rw [hset, hlam]
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_le_self _).trans
      (le_of_eq Real.volume_singleton))
  have hne : ∀ᵐ p : ℝ × ℝ ∂((wμ C).prod (wμ C)), p.1 ≠ p.2 := by
    rw [ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ p.2} = Set.diagonal ℝ := by
      ext p
      simp [Set.diagonal]
    rw [hset]
    exact nonpos_iff_eq_zero.mp ((hprodle _).trans (le_of_eq hdiag))
  have hL := log_one_add_integrable C hhead
  have h1 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.1)) ((wμ C).prod (wμ C)) :=
    hL.comp_fst (wμ C)
  have h2 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.2)) ((wμ C).prod (wμ C)) :=
    hL.comp_snd (wμ C)
  have hcongr : (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2) =ᵐ[(wμ C).prod (wμ C)]
      fun p => Real.log (1 + p.1) + Real.log (1 + p.2) - Real.log |p.1 - p.2| := by
    filter_upwards [hne, hbd] with p hne hp
    have h1ne : (1 + p.1) ≠ 0 := by linarith [hp.1.1]
    have h2ne : (1 + p.2) ≠ 0 := by linarith [hp.2.1]
    have hdiff : |p.1 - p.2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
    simp only [p0RegularizedFrequencyKernel, hne, ↓reduceIte]
    rw [Real.log_div (mul_ne_zero h1ne h2ne) hdiff, Real.log_mul h1ne h2ne]
  change ∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂((wμ C).prod (wμ C)) = _
  rw [integral_congr_ae hcongr,
    integral_sub (f := fun p : ℝ × ℝ => Real.log (1 + p.1) + Real.log (1 + p.2))
      (g := fun p : ℝ × ℝ => Real.log |p.1 - p.2|) (h1.add h2) hlog,
    integral_add (f := fun p : ℝ × ℝ => Real.log (1 + p.1))
      (g := fun p : ℝ × ℝ => Real.log (1 + p.2)) h1 h2,
    integral_fun_fst (fun t : ℝ => Real.log (1 + t)),
    integral_fun_snd (fun t : ℝ => Real.log (1 + t))]
  have hmass : (wμ C).real Set.univ = 1 := by
    rw [Measure.real, frequencyMeasure_univ C]; simp
  rw [hmass, one_smul]
  unfold eLLμ
  ring

/-! ## The mixed kernel -/

theorem eta_ae_ne_neg (C : FiniteConfiguration) :
    ∀ᵐ z ∂(configTubeWitness C).eta, ∀ t : ℝ, (1 / 2 : ℝ) ≤ t → 0 < ‖z + (t : ℂ)‖ := by
  rw [witness_eta_eq, ae_add_measure_iff]
  constructor
  · filter_upwards [mapPinned_ae C] with z hz t ht
    apply norm_pos_iff.mpr
    intro h0
    have := congrArg Complex.re h0
    simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re] at this
    linarith [hz.2.1]
  · filter_upwards [configContourMeasure_ae_tube C] with z hz t ht
    have := tube_frequency_clearance (configTubeRadius_le C) hz ht
    linarith

theorem mixedKernel_split (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    ∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2
        ∂((configTubeWitness C).eta.prod (configTubeWitness C).mu) =
      (∫ t : ℝ, Real.log (1 + t) ∂(wμ C)) - eMkμ C - eMνμ C := by
  set η := (configTubeWitness C).eta with hη
  have : IsFiniteMeasure η := witness_eta_finite C
  have : IsFiniteMeasure (wμ C) := frequencyMeasure_finite C
  have hK := witness_integrable_mixed C hhead
  have hL := log_one_add_integrable C hhead
  have hae : ∀ᵐ t ∂(wμ C), t ∈ Set.Icc (1 / 2 : ℝ) 20 := frequencyMeasure_ae_mem C hhead
  have hbd : ∀ᵐ p : ℂ × ℝ ∂(η.prod (wμ C)),
      (∀ t : ℝ, (1 / 2 : ℝ) ≤ t → 0 < ‖p.1 + (t : ℂ)‖) ∧ p.2 ∈ Set.Icc (1 / 2 : ℝ) 20 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := η) (ν := wμ C)).ae
        (eta_ae_ne_neg C),
      (Measure.quasiMeasurePreserving_snd (μ := η) (ν := wμ C)).ae hae] with p h1 h2
    exact ⟨h1, h2⟩
  have hL2 : Integrable (fun p : ℂ × ℝ => Real.log (1 + p.2)) (η.prod (wμ C)) :=
    hL.comp_snd η
  have hcongr : (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2) =ᵐ[η.prod (wμ C)]
      fun p => Real.log (1 + p.2) - Real.log ‖p.1 + (p.2 : ℂ)‖ := by
    filter_upwards [hbd] with p hp
    have h1ne : (1 + p.2) ≠ 0 := by linarith [hp.2.1]
    have h2ne : ‖p.1 + (p.2 : ℂ)‖ ≠ 0 := (hp.1 p.2 hp.2.1).ne'
    simp only [p0RegularizedMixedKernel]
    rw [Real.log_div h1ne h2ne]
  have hN : Integrable (fun p : ℂ × ℝ => Real.log ‖p.1 + (p.2 : ℂ)‖) (η.prod (wμ C)) := by
    have := hL2.sub (hK.congr hcongr)
    refine this.congr ?_
    filter_upwards with p
    simp
  change ∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(η.prod (wμ C)) = _
  rw [integral_congr_ae hcongr,
    integral_sub (f := fun p : ℂ × ℝ => Real.log (1 + p.2))
      (g := fun p : ℂ × ℝ => Real.log ‖p.1 + (p.2 : ℂ)‖) hL2 hN,
    integral_fun_snd (fun t : ℝ => Real.log (1 + t))]
  have hmass : η.real Set.univ = 1 := by
    rw [Measure.real, hη]
    change ((p0CompanionMeasure (pinnedMeasure C.m C.pinned) (configContourMeasure C))
      Set.univ).toReal = 1
    rw [configCompanion_mass C]; simp
  rw [hmass, one_smul]
  -- split the logarithmic term over `η = κ' + ν`
  rw [hη, witness_eta_eq, Measure.add_prod] at hN
  obtain ⟨hAN, hNN⟩ := (integrable_add_measure).mp hN
  have hsplit : ∫ p : ℂ × ℝ, Real.log ‖p.1 + (p.2 : ℂ)‖ ∂(η.prod (wμ C)) =
      eMkμ C + eMνμ C := by
    rw [hη, witness_eta_eq, Measure.add_prod, integral_add_measure hAN hNN]
    have hmap : Measure.map (Prod.map Complex.ofReal id) ((wκ C).prod (wμ C)) =
        (wA C).prod (wμ C) := by
      rw [← Measure.map_prod_map _ _ Complex.measurable_ofReal measurable_id, Measure.map_id]
    have hAeq : ∫ p : ℂ × ℝ, Real.log ‖p.1 + (p.2 : ℂ)‖ ∂((wA C).prod (wμ C)) = eMkμ C := by
      rw [← hmap, integral_map (Complex.measurable_ofReal.prodMap measurable_id).aemeasurable
        (by rw [hmap]; exact hAN.aestronglyMeasurable)]
      unfold eMkμ
      congr 1
      funext p
      simp only [Prod.map, id]
      rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
    change ∫ p : ℂ × ℝ, Real.log ‖p.1 + (p.2 : ℂ)‖ ∂((wA C).prod (wμ C)) +
      ∫ p : ℂ × ℝ, Real.log ‖p.1 + (p.2 : ℂ)‖ ∂((wν C).prod (wμ C)) = _
    rw [hAeq]
    rfl
  rw [hsplit]
  ring

/-! ## The decomposition -/

theorem energyDecomposition : EnergyDecomposition := by
  intro C hhead
  unfold p0TubeRegularizedEnergyValue
  rw [companion_integral_split C, frequencyField_integral_split C hhead,
    etaSelf_split C, frequencyKernel_split C hhead, mixedKernel_split C hhead]
  ring

end

end Li2Lean.P0.CellBound
