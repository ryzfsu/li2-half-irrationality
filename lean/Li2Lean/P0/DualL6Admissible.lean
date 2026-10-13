/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Variations

/-!
# L6 on the literal admissible domain of `eq:contour-admissible`

For `M : P0AdmissibleMeasures` with `P0FiniteEnergyCondition M` this file
derives (rather than assumes) the common-plane logarithmic integrability of
the reflected frequency measure `μ⁻` and of the pair `(η, μ⁻)` from the
regularized kernels of `eq:contour-regularized` and the first moment, with
the diagonal / collision sets made null through the atomless frequency
*marginal*.  It then proves:

* the regularized-to-common-plane transfer (both kernels lose exactly the
  `log(1+t)` terms because `|η| = |μ| = 1`);
* unconditional L6 positivity for the old pair `(η, μ⁻)`, replacing the
  `P0AdmissibleFrullaniCertificate` premises;
* the three-variation quadratic bound of `lem:dual-lower` for an admissible
  `M` against an admissible reference `M₀`, given the four cross
  integrabilities between `M` and `M₀` (`P0L6CrossEnergy`).
-/

open MeasureTheory Set Filter

namespace Li2Lean
namespace P0
namespace L6Admissible

noncomputable section

open L6Variations

theorem measurable_reflect : Measurable (fun t : ℝ => (-(t : ℂ))) :=
  measurable_neg.comp Complex.measurable_ofReal

theorem measurable_reflect_prodMap :
    Measurable (Prod.map (fun t : ℝ => (-(t : ℂ))) (fun t : ℝ => (-(t : ℂ)))) :=
  (measurable_reflect.comp measurable_fst).prodMk (measurable_reflect.comp measurable_snd)

theorem measurable_id_reflect_prodMap :
    Measurable (Prod.map (id : ℂ → ℂ) (fun t : ℝ => (-(t : ℂ)))) :=
  measurable_fst.prodMk (measurable_reflect.comp measurable_snd)

theorem measurable_li2LogKernel :
    Measurable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) := by
  unfold li2LogKernel
  exact (Real.measurable_log.comp (by fun_prop : Measurable fun x : ℂ × ℂ => ‖x.1 - x.2‖)).neg

instance eta_isFinite (M : P0AdmissibleMeasures) : IsFiniteMeasure M.eta :=
  ⟨by rw [show M.eta univ = 1 from M.companion_mass]; simp⟩

instance mu_isFinite (M : P0AdmissibleMeasures) : IsFiniteMeasure M.mu :=
  ⟨by rw [M.frequency_mass]; simp⟩

instance freq_isFinite (M : P0AdmissibleMeasures) : IsFiniteMeasure (p0FrequencyMeasure M) :=
  ⟨by rw [p0AdmissibleFrequencyMeasure_mass]; simp⟩

theorem mu_ae_ge (M : P0AdmissibleMeasures) : ∀ᵐ t ∂M.mu, (1 / 2 : ℝ) ≤ t := by
  rw [ae_iff]
  have hset : {t : ℝ | ¬(1 / 2 : ℝ) ≤ t} = Iio (1 / 2) := by
    ext t
    simp
  rw [hset]
  apply le_antisymm _ bot_le
  calc
    M.mu (Iio (1 / 2)) ≤ volume.restrict (Ici (1 / 2 : ℝ)) (Iio (1 / 2)) :=
      M.mu_le_density _
    _ = 0 := by
      rw [Measure.restrict_apply measurableSet_Iio]
      have hempty : Iio (1 / 2 : ℝ) ∩ Ici (1 / 2) = ∅ := by
        ext t
        simp only [mem_inter_iff, mem_Iio, mem_Ici, mem_empty_iff_false, iff_false, not_and]
        intro h h'
        linarith
      rw [hempty, measure_empty]

theorem mu_measure_subsingleton (M : P0AdmissibleMeasures) {s : Set ℝ}
    (hs : s.Subsingleton) : M.mu s = 0 := by
  rcases hs.eq_empty_or_singleton with h | ⟨t, h⟩
  · simp [h]
  · rw [h]
    exact p0AdmissibleMeasures_frequency_atomless M t

/-- The reflected frequency measure `μ⁻` has no atoms. -/
theorem freq_atomless (M : P0AdmissibleMeasures) (z : ℂ) : p0FrequencyMeasure M {z} = 0 := by
  unfold p0FrequencyMeasure p0ReflectedFrequencyMeasure
  rw [Measure.map_apply measurable_reflect (measurableSet_singleton z)]
  apply mu_measure_subsingleton
  intro s hs t ht
  simp only [mem_preimage, mem_singleton_iff] at hs ht
  have hst : (s : ℂ) = t := by
    have := hs.trans ht.symm
    linear_combination -this
  exact_mod_cast hst

theorem ae_fst_of {μ ν : Measure ℝ} [SFinite μ] [SFinite ν] {p : ℝ → Prop}
    (h : ∀ᵐ t ∂μ, p t) : ∀ᵐ x : ℝ × ℝ ∂(μ.prod ν), p x.1 :=
  QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_fst h

theorem ae_snd_of {α : Type*} [MeasurableSpace α] {μ : Measure α} {ν : Measure ℝ}
    [SFinite μ] [SFinite ν] {p : ℝ → Prop}
    (h : ∀ᵐ t ∂ν, p t) : ∀ᵐ x : α × ℝ ∂(μ.prod ν), p x.2 :=
  QuasiMeasurePreserving.ae Measure.quasiMeasurePreserving_snd h

/-- First moment gives the logarithmic moment `∫ log(1+t) dμ < ∞`. -/
theorem mu_log_moment (M : P0AdmissibleMeasures) (hfin : P0FiniteEnergyCondition M) :
    Integrable (fun t : ℝ => Real.log (1 + t)) M.mu := by
  have h1 : Integrable (fun t : ℝ => t) M.mu := hfin.1
  refine h1.abs.mono' (Real.measurable_log.comp (by fun_prop)).aestronglyMeasurable ?_
  filter_upwards [mu_ae_ge M] with t ht
  have hpos : 0 < 1 + t := by linarith
  rw [Real.norm_of_nonneg (Real.log_nonneg (by linarith)), abs_of_nonneg (by linarith)]
  linarith [Real.log_le_sub_one_of_pos hpos]

/-- Diagonal nullity of `μ ⊗ μ` from the atomless marginal. -/
theorem mu_prod_ae_ne (M : P0AdmissibleMeasures) :
    ∀ᵐ x : ℝ × ℝ ∂(M.mu.prod M.mu), x.1 ≠ x.2 := by
  have hnull : (M.mu.prod M.mu) (Set.diagonal ℝ) = 0 := by
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards with t
    have hset : Prod.mk t ⁻¹' Set.diagonal ℝ = {t} := by
      ext s
      simp [Set.diagonal, eq_comm]
    simp [hset, p0AdmissibleMeasures_frequency_atomless M t]
  rw [ae_iff]
  have hset : {a : ℝ × ℝ | ¬a.1 ≠ a.2} = Set.diagonal ℝ := by
    ext a
    simp [Set.diagonal]
  rw [hset]
  exact hnull

/-- Collision nullity of `η ⊗ μ` for the mixed kernel, again from the
atomless frequency marginal. -/
theorem eta_mu_ae_ne (M : P0AdmissibleMeasures) :
    ∀ᵐ x : ℂ × ℝ ∂(M.eta.prod M.mu), x.1 + (x.2 : ℂ) ≠ 0 := by
  have hmeas : MeasurableSet {x : ℂ × ℝ | x.1 + (x.2 : ℂ) = 0} :=
    measurableSet_eq_fun (by fun_prop) measurable_const
  have hnull : (M.eta.prod M.mu) {x : ℂ × ℝ | x.1 + (x.2 : ℂ) = 0} = 0 := by
    rw [Measure.measure_prod_null hmeas]
    filter_upwards with z
    apply mu_measure_subsingleton
    intro s hs t ht
    simp only [mem_preimage, Set.mem_ofPred_eq] at hs ht
    have hst : (s : ℂ) = t := by linear_combination hs - ht
    exact_mod_cast hst
  rw [ae_iff]
  simpa only [ne_eq, not_not] using hnull

theorem norm_reflect_sub (t s : ℝ) : ‖-(t : ℂ) - -(s : ℂ)‖ = |t - s| := by
  rw [neg_sub_neg, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]

theorem freq_prod_eq_map (M : P0AdmissibleMeasures) :
    (p0FrequencyMeasure M).prod (p0FrequencyMeasure M) =
      Measure.map (Prod.map (fun t : ℝ => (-(t : ℂ))) (fun t : ℝ => (-(t : ℂ))))
        (M.mu.prod M.mu) :=
  Measure.map_prod_map _ _ measurable_reflect measurable_reflect

theorem eta_freq_prod_eq_map (M : P0AdmissibleMeasures) :
    M.eta.prod (p0FrequencyMeasure M) =
      Measure.map (Prod.map id (fun t : ℝ => (-(t : ℂ)))) (M.eta.prod M.mu) := by
  have h := Measure.map_prod_map M.eta M.mu measurable_id measurable_reflect
  rw [Measure.map_id] at h
  exact h

/-- Pointwise form of the regularized self-kernel off the diagonal. -/
theorem regularizedFrequency_eq (t s : ℝ) (ht : (1 / 2 : ℝ) ≤ t) (hs : (1 / 2 : ℝ) ≤ s)
    (hne : t ≠ s) :
    p0RegularizedFrequencyKernel t s =
      li2LogKernel (-(t : ℂ)) (-(s : ℂ)) + (Real.log (1 + t) + Real.log (1 + s)) := by
  have h1 : (1 + t) ≠ 0 := by linarith
  have h2 : (1 + s) ≠ 0 := by linarith
  have h3 : |t - s| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  rw [p0RegularizedFrequencyKernel, if_neg hne, li2LogKernel, norm_reflect_sub,
    Real.log_div (mul_ne_zero h1 h2) h3, Real.log_mul h1 h2]
  ring

/-- Pointwise form of the regularized mixed kernel off collisions. -/
theorem regularizedMixed_eq (z : ℂ) (t : ℝ) (ht : (1 / 2 : ℝ) ≤ t)
    (hne : z + (t : ℂ) ≠ 0) :
    p0RegularizedMixedKernel z t = li2LogKernel z (-(t : ℂ)) + Real.log (1 + t) := by
  have h1 : (1 + t) ≠ 0 := by linarith
  have h2 : ‖z + (t : ℂ)‖ ≠ 0 := norm_ne_zero_iff.mpr hne
  rw [p0RegularizedMixedKernel, li2LogKernel, sub_neg_eq_add, Real.log_div h1 h2]
  ring

/-- `K₀` is integrable on `μ⁻ ⊗ μ⁻`: derived from the regularized kernel
and the first moment. -/
theorem freq_kernel_integrable (M : P0AdmissibleMeasures) (hfin : P0FiniteEnergyCondition M) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M)) := by
  rw [freq_prod_eq_map, integrable_map_measure measurable_li2LogKernel.aestronglyMeasurable
    measurable_reflect_prodMap.aemeasurable]
  have hreg : Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      (M.mu.prod M.mu) := hfin.2.2.2.2.2.1
  have hm := mu_log_moment M hfin
  refine (hreg.sub ((hm.comp_fst M.mu).add (hm.comp_snd M.mu))).congr ?_
  filter_upwards [mu_prod_ae_ne M, ae_fst_of (ν := M.mu) (mu_ae_ge M),
    ae_snd_of (μ := M.mu) (mu_ae_ge M)] with x hne h1 h2
  simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd]
  rw [regularizedFrequency_eq x.1 x.2 h1 h2 hne]
  ring

/-- `K₀` is integrable on `η ⊗ μ⁻`: derived from the regularized mixed
kernel and the first moment. -/
theorem eta_freq_kernel_integrable (M : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      (M.eta.prod (p0FrequencyMeasure M)) := by
  rw [eta_freq_prod_eq_map, integrable_map_measure
    measurable_li2LogKernel.aestronglyMeasurable
    measurable_id_reflect_prodMap.aemeasurable]
  have hreg : Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
      (M.eta.prod M.mu) := hfin.2.2.2.2.2.2
  have hm := mu_log_moment M hfin
  refine (hreg.sub (hm.comp_snd M.eta)).congr ?_
  filter_upwards [eta_mu_ae_ne M, ae_snd_of (μ := M.eta) (mu_ae_ge M)] with x hne h2
  simp only [Pi.sub_apply, Pi.add_apply, Function.comp_apply, Prod.map_fst, Prod.map_snd, id]
  rw [regularizedMixed_eq x.1 x.2 h2 hne]
  ring

theorem eta_kernel_integrable (M : P0AdmissibleMeasures) (hfin : P0FiniteEnergyCondition M) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (M.eta.prod M.eta) :=
  hfin.2.2.2.1

theorem eta_atomless (M : P0AdmissibleMeasures) (hfin : P0FiniteEnergyCondition M) :
    ∀ z : ℂ, M.eta {z} = 0 :=
  p0FiniteEnergyCondition_eta_atomless hfin

/-! ### Regularized-to-common-plane transfer -/

theorem freq_interaction_eq (M : P0AdmissibleMeasures) :
    li2LogInteraction (p0FrequencyMeasure M) (p0FrequencyMeasure M) =
      ∫ x : ℝ × ℝ, li2LogKernel (-(x.1 : ℂ)) (-(x.2 : ℂ)) ∂(M.mu.prod M.mu) := by
  rw [li2LogInteraction, freq_prod_eq_map,
    integral_map measurable_reflect_prodMap.aemeasurable
      measurable_li2LogKernel.aestronglyMeasurable]
  rfl

theorem eta_freq_interaction_eq (M : P0AdmissibleMeasures) :
    li2LogInteraction M.eta (p0FrequencyMeasure M) =
      ∫ x : ℂ × ℝ, li2LogKernel x.1 (-(x.2 : ℂ)) ∂(M.eta.prod M.mu) := by
  rw [li2LogInteraction, eta_freq_prod_eq_map,
    integral_map measurable_id_reflect_prodMap.aemeasurable
      measurable_li2LogKernel.aestronglyMeasurable]
  rfl

theorem integral_regularizedFrequency (M : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) :
    (∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂(M.mu.prod M.mu)) =
      li2LogInteraction (p0FrequencyMeasure M) (p0FrequencyMeasure M) +
        2 * ∫ t, Real.log (1 + t) ∂M.mu := by
  have hm := mu_log_moment M hfin
  have hK := freq_kernel_integrable M hfin
  rw [freq_prod_eq_map, integrable_map_measure measurable_li2LogKernel.aestronglyMeasurable
    measurable_reflect_prodMap.aemeasurable] at hK
  have hK' : Integrable (fun x : ℝ × ℝ => li2LogKernel (-(x.1 : ℂ)) (-(x.2 : ℂ)))
      (M.mu.prod M.mu) := hK
  have h1 : Integrable (fun x : ℝ × ℝ => Real.log (1 + x.1)) (M.mu.prod M.mu) :=
    hm.comp_fst M.mu
  have h2 : Integrable (fun x : ℝ × ℝ => Real.log (1 + x.2)) (M.mu.prod M.mu) :=
    hm.comp_snd M.mu
  have h12 : Integrable (fun x : ℝ × ℝ => Real.log (1 + x.1) + Real.log (1 + x.2))
      (M.mu.prod M.mu) := h1.add h2
  have hcongr : (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2) =ᵐ[M.mu.prod M.mu]
      fun x => li2LogKernel (-(x.1 : ℂ)) (-(x.2 : ℂ)) +
        (Real.log (1 + x.1) + Real.log (1 + x.2)) := by
    filter_upwards [mu_prod_ae_ne M, ae_fst_of (ν := M.mu) (mu_ae_ge M),
      ae_snd_of (μ := M.mu) (mu_ae_ge M)] with x hne hx1 hx2
    exact regularizedFrequency_eq x.1 x.2 hx1 hx2 hne
  have hreal : M.mu.real univ = 1 := by simp [Measure.real, M.frequency_mass]
  have hf : (∫ x : ℝ × ℝ, Real.log (1 + x.1) ∂(M.mu.prod M.mu)) =
      ∫ t, Real.log (1 + t) ∂M.mu := by
    rw [integral_fun_fst (fun t : ℝ => Real.log (1 + t)), hreal, one_smul]
  have hs : (∫ x : ℝ × ℝ, Real.log (1 + x.2) ∂(M.mu.prod M.mu)) =
      ∫ t, Real.log (1 + t) ∂M.mu := by
    rw [integral_fun_snd (fun t : ℝ => Real.log (1 + t)), hreal, one_smul]
  rw [integral_congr_ae hcongr, integral_add hK' h12, integral_add h1 h2, hf, hs,
    freq_interaction_eq]
  ring

theorem integral_regularizedMixed (M : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) :
    (∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(M.eta.prod M.mu)) =
      li2LogInteraction M.eta (p0FrequencyMeasure M) + ∫ t, Real.log (1 + t) ∂M.mu := by
  have hm := mu_log_moment M hfin
  have hK := eta_freq_kernel_integrable M hfin
  rw [eta_freq_prod_eq_map, integrable_map_measure
    measurable_li2LogKernel.aestronglyMeasurable
    measurable_id_reflect_prodMap.aemeasurable] at hK
  have hK' : Integrable (fun x : ℂ × ℝ => li2LogKernel x.1 (-(x.2 : ℂ)))
      (M.eta.prod M.mu) := hK
  have h2 : Integrable (fun x : ℂ × ℝ => Real.log (1 + x.2)) (M.eta.prod M.mu) :=
    hm.comp_snd M.eta
  have hcongr : (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2) =ᵐ[M.eta.prod M.mu]
      fun x => li2LogKernel x.1 (-(x.2 : ℂ)) + Real.log (1 + x.2) := by
    filter_upwards [eta_mu_ae_ne M, ae_snd_of (μ := M.eta) (mu_ae_ge M)] with x hne hx2
    exact regularizedMixed_eq x.1 x.2 hx2 hne
  have hreal : M.eta.real univ = 1 := by
    simp [Measure.real, show M.eta univ = 1 from M.companion_mass]
  have hs : (∫ x : ℂ × ℝ, Real.log (1 + x.2) ∂(M.eta.prod M.mu)) =
      ∫ t, Real.log (1 + t) ∂M.mu := by
    rw [integral_fun_snd (fun t : ℝ => Real.log (1 + t)), hreal, one_smul]
  rw [integral_congr_ae hcongr, integral_add hK' h2, hs, eta_freq_interaction_eq]

/-- The `regularized_kernel_transfer` field, now a theorem. -/
theorem p0AdmissibleLogEnergyDifference_eq_common (M : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) :
    p0AdmissibleLogEnergyDifference M = p0AdmissibleCommonLogEnergyDifference M := by
  unfold p0AdmissibleLogEnergyDifference p0AdmissibleCommonLogEnergyDifference
  rw [integral_regularizedFrequency M hfin, integral_regularizedMixed M hfin]
  ring

/-- Unconditional L6 positivity for `(η, μ⁻)` on the finite-energy domain:
no Frullani certificate, no compact support. -/
theorem p0FiniteEnergy_admissibleLogEnergy_nonneg' (M : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) : 0 ≤ p0AdmissibleLogEnergyDifference M := by
  rw [p0AdmissibleLogEnergyDifference_eq_common M hfin]
  have hmass : M.eta univ = p0FrequencyMeasure M univ := by
    rw [p0AdmissibleFrequencyMeasure_mass]
    exact M.companion_mass
  exact l6FiniteLogPairDifference_nonneg_of_atomless M.eta (p0FrequencyMeasure M) hmass
    (eta_atomless M hfin) (freq_atomless M) (eta_kernel_integrable M hfin)
    (freq_kernel_integrable M hfin) (eta_freq_kernel_integrable M hfin)

/-- The quadratic part of the regularized energy is the common-plane
quadratic `I(η)+I(μ⁻)+I(η,μ⁻)` plus `3∫log(1+t)dμ`, which is exactly the
`-3ℓ₁` moved into the regularized field. -/
theorem p0RegularizedQuadratic_eq (M : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) :
    li2LogInteraction M.eta M.eta +
        (∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂(M.mu.prod M.mu)) +
        (∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(M.eta.prod M.mu)) =
      l6EnergyQuadratic M.eta (p0FrequencyMeasure M) +
        3 * ∫ t, Real.log (1 + t) ∂M.mu := by
  rw [integral_regularizedFrequency M hfin, integral_regularizedMixed M hfin]
  unfold l6EnergyQuadratic
  ring

/-! ### Admissible pair against an admissible reference -/

/-- The four cross integrabilities between an admissible pair and the
reference; these are not consequences of the two finite-energy conditions
separately and remain explicit. -/
structure P0L6CrossEnergy (M M₀ : P0AdmissibleMeasures) : Prop where
  eta_eta₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (M.eta.prod M₀.eta)
  freq_freq₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
    ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M₀))
  eta_freq₀ : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
    (M.eta.prod (p0FrequencyMeasure M₀))
  eta₀_freq : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
    (M₀.eta.prod (p0FrequencyMeasure M))

/-- Logarithmic moment of `μ⁻` from the first moment of `μ`. -/
theorem freq_log_moment (M : P0AdmissibleMeasures) (hfin : P0FiniteEnergyCondition M) :
    Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) (p0FrequencyMeasure M) := by
  have hmeas : Measurable (fun z : ℂ => Real.log (1 + ‖z‖)) :=
    Real.measurable_log.comp (by fun_prop)
  unfold p0FrequencyMeasure p0ReflectedFrequencyMeasure
  rw [integrable_map_measure hmeas.aestronglyMeasurable measurable_reflect.aemeasurable]
  refine (mu_log_moment M hfin).congr ?_
  filter_upwards [mu_ae_ge M] with t ht
  have ht0 : (0 : ℝ) ≤ t := by linarith
  simp only [Function.comp_apply, norm_neg, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg ht0]

/-- The cross data from the `ℝ≥0∞` split: finite positive cross energies
plus logarithmic moments of the two companions (frequency moments come from
the first moment). -/
theorem p0L6CrossEnergy_of_split (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) (hfin₀ : P0FiniteEnergyCondition M₀)
    (hη : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M.eta)
    (hη₀ : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M₀.eta)
    (p1 : ∫⁻ x, l6PosKernel x.1 x.2 ∂(M.eta.prod M₀.eta) ≠ ⊤)
    (p2 : ∫⁻ x, l6PosKernel x.1 x.2 ∂((p0FrequencyMeasure M).prod (p0FrequencyMeasure M₀)) ≠ ⊤)
    (p3 : ∫⁻ x, l6PosKernel x.1 x.2 ∂(M.eta.prod (p0FrequencyMeasure M₀)) ≠ ⊤)
    (p4 : ∫⁻ x, l6PosKernel x.1 x.2 ∂(M₀.eta.prod (p0FrequencyMeasure M)) ≠ ⊤) :
    P0L6CrossEnergy M M₀ := by
  have hφ := freq_log_moment M hfin
  have hφ₀ := freq_log_moment M₀ hfin₀
  exact ⟨integrable_li2LogKernel_of_split p1 hη hη₀,
    integrable_li2LogKernel_of_split p2 hφ hφ₀,
    integrable_li2LogKernel_of_split p3 hη hφ₀,
    integrable_li2LogKernel_of_split p4 hη₀ hφ⟩

theorem p0L6FourMeasureData (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) (hfin₀ : P0FiniteEnergyCondition M₀)
    (hcross : P0L6CrossEnergy M M₀) :
    L6FourMeasureData M.eta M₀.eta (p0FrequencyMeasure M) (p0FrequencyMeasure M₀) where
  fin_η := inferInstance
  fin_η₀ := inferInstance
  fin_φ := inferInstance
  fin_φ₀ := inferInstance
  mass_η := by rw [show M.eta univ = 1 from M.companion_mass,
    show M₀.eta univ = 1 from M₀.companion_mass]
  mass_φ := by rw [p0AdmissibleFrequencyMeasure_mass, p0AdmissibleFrequencyMeasure_mass]
  atomless_η := eta_atomless M hfin
  atomless_η₀ := eta_atomless M₀ hfin₀
  atomless_φ := freq_atomless M
  atomless_φ₀ := freq_atomless M₀
  int_ηη := eta_kernel_integrable M hfin
  int_η₀η₀ := eta_kernel_integrable M₀ hfin₀
  int_φφ := freq_kernel_integrable M hfin
  int_φ₀φ₀ := freq_kernel_integrable M₀ hfin₀
  int_ηη₀ := hcross.eta_eta₀
  int_φφ₀ := hcross.freq_freq₀
  int_ηφ := eta_freq_kernel_integrable M hfin
  int_ηφ₀ := hcross.eta_freq₀
  int_η₀φ := hcross.eta₀_freq
  int_η₀φ₀ := eta_freq_kernel_integrable M₀ hfin₀

/-- **`lem:dual-lower`, quadratic step, on the admissible domain.**
`I(σ)+I(τ)+I(σ,τ) ≥ 0` for `σ = η - η₀`, `τ = μ⁻ - μ₀⁻`. -/
theorem p0_dualLower_quadraticRemainder_nonneg (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) (hfin₀ : P0FiniteEnergyCondition M₀)
    (hcross : P0L6CrossEnergy M M₀) :
    0 ≤ l6QuadraticRemainder M.eta M₀.eta (p0FrequencyMeasure M) (p0FrequencyMeasure M₀) :=
  l6QuadraticRemainder_nonneg (p0L6FourMeasureData M M₀ hfin hfin₀ hcross)

/-- **`lem:dual-lower`, energy form.**  The regularized quadratic part of
`p0RegularizedEnergyValue M` is bounded below by `Q_log`, the first
variations against the reference potentials, and `3∫log(1+t)dμ`. -/
theorem p0_dualLower_regularizedQuadratic_ge (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) (hfin₀ : P0FiniteEnergyCondition M₀)
    (hcross : P0L6CrossEnergy M M₀) :
    l6QLog M₀.eta (p0FrequencyMeasure M₀) +
        (∫ z, (-2 * l6LogPotential M₀.eta z - l6LogPotential (p0FrequencyMeasure M₀) z)
          ∂M.eta) +
        (∫ z, (-2 * l6LogPotential (p0FrequencyMeasure M₀) z - l6LogPotential M₀.eta z)
          ∂(p0FrequencyMeasure M)) +
        3 * ∫ t, Real.log (1 + t) ∂M.mu ≤
      li2LogInteraction M.eta M.eta +
        (∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂(M.mu.prod M.mu)) +
        (∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(M.eta.prod M.mu)) := by
  rw [p0RegularizedQuadratic_eq M hfin]
  have h := l6EnergyQuadratic_ge_potential_form (p0L6FourMeasureData M M₀ hfin hfin₀ hcross)
  linarith

end

end L6Admissible
end P0
end Li2Lean
