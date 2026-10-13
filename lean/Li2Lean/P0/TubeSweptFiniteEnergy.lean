/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeSweepSources
import Li2Lean.P0.TubeTransferAssembly
import Li2Lean.P0.ContourFieldFinite

open MeasureTheory ProbabilityTheory Filter

namespace Li2Lean.P0.TubeEnergy

noncomputable section
open TubeInterior

/-- A bounded cross interaction between the ellipse and the positive pinned
real segment.  The lower clearance is uniform, so this remains valid when the
swept measure meets the source interval elsewhere on the real axis. -/
theorem integrable_li2LogKernel_gamma_pinned
    (ν κ : Measure ℂ) [IsFiniteMeasure ν] [IsFiniteMeasure κ]
    (hν : ∀ᵐ y ∂ν, y ∈ Gamma)
    (hκ : ∀ᵐ x ∂κ, x.re ∈ Set.Icc (0 : ℝ) 2 ∧ x.im = 0) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (ν.prod κ) := by
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    fun_prop
  apply integrable_of_bound_ae hmeas.stronglyMeasurable.aestronglyMeasurable
    (C := |Real.log (751 / 5000 : ℝ)| + |Real.log 6|)
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := κ)).ae hν
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := κ)).ae hκ
  filter_upwards [h1, h2] with p hp hy
  have hlow : (751 / 5000 : ℝ) ≤ ‖p.1 - p.2‖ :=
    positive_source_norm_sub_ge hy.1 hy.2 hp
  have hpos : (0 : ℝ) < 751 / 5000 := by norm_num
  have hnorm1 : ‖p.1‖ ≤ 4 := TubeVariance.norm_le_four_of_mem_Gamma hp
  have hnorm2 : ‖p.2‖ ≤ 2 := by
    have heq : p.2 = Complex.ofReal p.2.re := by
      apply Complex.ext <;> simp [hy.2]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hy.1.1])]
    exact hy.1.2
  have hu : ‖p.1 - p.2‖ ≤ 6 := by
    linarith [norm_sub_le p.1 p.2]
  have hl := Real.log_le_log hpos hlow
  have hu' := Real.log_le_log (lt_of_lt_of_le hpos hlow) hu
  have hloglow : Real.log (751 / 5000 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlog6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have habslow : |Real.log (751 / 5000 : ℝ)| = -Real.log (751 / 5000 : ℝ) := abs_of_neg hloglow
  have habs6 : |Real.log (6 : ℝ)| = Real.log (6 : ℝ) := abs_of_nonneg hlog6
  unfold li2LogKernel
  rw [abs_neg, abs_le, habslow, habs6]
  constructor <;> linarith [le_abs_self (Real.log 6), neg_le_abs (Real.log (751 / 5000)),
    abs_nonneg (Real.log 6), abs_nonneg (Real.log (751 / 5000))]

/-- The opposite orientation of the pinned cross interaction. -/
theorem integrable_li2LogKernel_pinned_gamma
    (κ ν : Measure ℂ) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (hκ : ∀ᵐ x ∂κ, x.re ∈ Set.Icc (0 : ℝ) 2 ∧ x.im = 0)
    (hν : ∀ᵐ y ∂ν, y ∈ Gamma) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (κ.prod ν) := by
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    fun_prop
  apply integrable_of_bound_ae hmeas.stronglyMeasurable.aestronglyMeasurable
    (C := |Real.log (751 / 5000 : ℝ)| + |Real.log 6|)
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := κ) (ν := ν)).ae hκ
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := κ) (ν := ν)).ae hν
  filter_upwards [h1, h2] with p hx hy
  have hlow : (751 / 5000 : ℝ) ≤ ‖p.2 - p.1‖ :=
    positive_source_norm_sub_ge hx.1 hx.2 hy
  have hlow' : (751 / 5000 : ℝ) ≤ ‖p.1 - p.2‖ := by
    simpa [norm_sub_rev] using hlow
  have hpos : (0 : ℝ) < 751 / 5000 := by norm_num
  have hnorm1 : ‖p.1‖ ≤ 2 := by
    have heq : p.1 = Complex.ofReal p.1.re := by
      apply Complex.ext <;> simp [hx.2]
    rw [heq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1.1])]
    exact hx.1.2
  have hnorm2 : ‖p.2‖ ≤ 4 := TubeVariance.norm_le_four_of_mem_Gamma hy
  have hu : ‖p.1 - p.2‖ ≤ 6 := by
    linarith [norm_sub_le p.1 p.2]
  have hl : Real.log (751 / 5000 : ℝ) ≤ Real.log ‖p.1 - p.2‖ :=
    Real.log_le_log hpos hlow'
  have hu' : Real.log ‖p.1 - p.2‖ ≤ Real.log 6 :=
    Real.log_le_log (lt_of_lt_of_le hpos hlow') hu
  have hloglow : Real.log (751 / 5000 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlog6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have habslow : |Real.log (751 / 5000 : ℝ)| = -Real.log (751 / 5000 : ℝ) := abs_of_neg hloglow
  have habs6 : |Real.log (6 : ℝ)| = Real.log (6 : ℝ) := abs_of_nonneg hlog6
  unfold li2LogKernel
  rw [abs_neg, abs_le, habslow, habs6]
  constructor <;> linarith [le_abs_self (Real.log 6), neg_le_abs (Real.log (751 / 5000)),
    abs_nonneg (Real.log 6), abs_nonneg (Real.log (751 / 5000))]

/-- The actual harmonic sweep preserves finite logarithmic self-energy. -/
theorem integrable_li2LogKernel_tubeSwept_self
    {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (hatom : ∀ z, ν {z} = 0)
    (hI : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (ν.prod ν)) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((tubeSwept ν).prod (tubeSwept ν)) := by
  have h := tubeSwept_energy_le hδ hδmax ν hsupp hatom hI
  simpa [li2LogKernel, realLogKernel] using h.1

/-- Companion fields remain integrable after sweeping the tube component. -/
theorem integrable_companionField_companion_swept
    (κ ν : Measure ℂ) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (hκ : ∀ᵐ z ∂κ, ‖z‖ ≤ 4) :
    Integrable (fun z : ℂ => p0CompanionField z)
      (κ + tubeSwept ν) := by
  have hκf := EnergyLowerBound.integrable_companionField_of_ae_norm_le hκ
  have hνf := EnergyLowerBound.integrable_companionField_of_ae_mem_Gamma
    (μ := tubeSwept ν) (tubeSwept_ae_mem_Gamma ν)
  exact hκf.add_measure hνf


/-- Product integrability for the swept companion sum.  Each of the four
components is checked before expanding the product, so no finiteness is hidden
in an interaction-value identity. -/
theorem integrable_li2LogKernel_companion_swept_self
    (κ ν : Measure ℂ) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (hκκ : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (κ.prod κ))
    (hκν : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (κ.prod (tubeSwept ν)))
    (hνκ : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((tubeSwept ν).prod κ))
    (hνν : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((tubeSwept ν).prod (tubeSwept ν))) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((κ + tubeSwept ν).prod (κ + tubeSwept ν)) := by
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  exact (hκκ.add_measure hκν).add_measure (hνκ.add_measure hνν)

end
end Li2Lean.P0.TubeEnergy

namespace Li2Lean.P0

open TubeEnergy

/-- Concrete eta# interaction split for a finite-energy tube competitor.  The
four cross/self integrability obligations are discharged independently: the
swept self term uses the truncated-to-untruncated tube bound, while both
pinned cross terms use the positive-source clearance. -/
theorem p0Tube_swept_eta_interaction_split
    {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ)
    (hM : p0TubeFiniteEnergyCondition M) :
    li2LogInteraction
        (Measure.map Complex.ofReal M.kappa + tubeSwept M.nu)
        (Measure.map Complex.ofReal M.kappa + tubeSwept M.nu) =
      li2LogInteraction (Measure.map Complex.ofReal M.kappa)
        (Measure.map Complex.ofReal M.kappa) +
      li2LogInteraction (Measure.map Complex.ofReal M.kappa) (tubeSwept M.nu) +
      li2LogInteraction (tubeSwept M.nu) (Measure.map Complex.ofReal M.kappa) +
      li2LogInteraction (tubeSwept M.nu) (tubeSwept M.nu) := by
  let η : Measure ℂ := p0CompanionMeasure M.kappa M.nu
  have hηmass : η Set.univ = 1 := by
    simpa [η, p0CompanionMeasure] using M.companion_mass
  letI : IsFiniteMeasure η := ⟨by rw [hηmass]; simp⟩
  have hκη : Measure.map Complex.ofReal M.kappa ≤ η := by
    exact Measure.le_add_right le_rfl
  have hνη : M.nu ≤ η := by
    exact Measure.le_add_left le_rfl
  letI : IsFiniteMeasure (Measure.map Complex.ofReal M.kappa) := ⟨by
    calc
      (Measure.map Complex.ofReal M.kappa) Set.univ ≤ η Set.univ := hκη Set.univ
      _ < ⊤ := measure_lt_top η Set.univ⟩
  letI : IsFiniteMeasure M.nu := ⟨by
    calc
      M.nu Set.univ ≤ η Set.univ := hνη Set.univ
      _ < ⊤ := measure_lt_top η Set.univ⟩
  have hk_ae : ∀ᵐ x ∂M.kappa, x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    exact (Measure.absolutelyContinuous_of_le M.kappa_le_density).ae_le
      (ae_restrict_mem measurableSet_Icc)
  have hκsupp : ∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa),
      z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0 := by
    have hset : MeasurableSet {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0} := by
      exact (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
        ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
    rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
    filter_upwards [hk_ae] with x hx
    constructor
    · simp only [Complex.ofReal_re]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · simp
  have hνtube : ∀ᵐ z ∂M.nu, z ∈ tube δ := by
    rw [ae_iff]
    apply measure_mono_null (Set.compl_subset_compl.mpr M.nu_supported)
    exact Measure.measure_compl_support
  have hνatom : ∀ z : ℂ, M.nu {z} = 0 := by
    rcases hM with ⟨_, _, _, _, heta, _, _⟩
    intro z
    have hle : M.nu {z} ≤ η {z} := hνη {z}
    have heta' : η {z} = 0 := by
      simpa [η, P0TubeAdmissibleMeasures.eta] using heta z
    exact le_antisymm (hle.trans_eq heta') bot_le
  have hetaLog : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (η.prod η) := by
    simpa [η, P0TubeAdmissibleMeasures.eta] using hM.2.2.2.1
  have hνlog : Integrable
      (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (M.nu.prod M.nu) := by
    have h := hetaLog.mono_measure (Measure.prod_mono hνη hνη)
    simpa [li2LogKernel, realLogKernel] using h
  have hνν := integrable_li2LogKernel_tubeSwept_self
    hδ hδmax M.nu hνtube hνatom hνlog
  have hκκ : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal M.kappa).prod
        (Measure.map Complex.ofReal M.kappa)) :=
    hetaLog.mono_measure (Measure.prod_mono hκη hκη)
  have hκν := integrable_li2LogKernel_pinned_gamma
    (Measure.map Complex.ofReal M.kappa) (tubeSwept M.nu)
    hκsupp (tubeSwept_ae_mem_Gamma M.nu)
  have hνκ := integrable_li2LogKernel_gamma_pinned
    (tubeSwept M.nu) (Measure.map Complex.ofReal M.kappa)
    (tubeSwept_ae_mem_Gamma M.nu) hκsupp
  exact tubeSwept_companion_interaction_split
    (Measure.map Complex.ofReal M.kappa) M.nu hκκ hκν hνκ hνν


/-- A finite-energy tube competitor remains in the genuine contour finite-energy
class after the harmonic sweep.  The three component equalities are premises
so this theorem can be applied to any assembled `P0AdmissibleMeasures`; it
adds no conclusion-representing field to the transfer certificate. -/
theorem p0Tube_sweep_finite_energy
    {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ)
    (hM : p0TubeFiniteEnergyCondition M)
    (N : P0AdmissibleMeasures)
    (hκ : N.kappa = M.kappa)
    (hν : N.nu = TubeEnergy.tubeSwept M.nu)
    (hμ : N.mu = M.mu) :
    P0FiniteEnergyCondition N := by
  rcases hM with ⟨hfirst, hfield, hfreqfield, hself, hatom,
    hfreqkernel, hmix⟩
  let η : Measure ℂ := p0CompanionMeasure M.kappa M.nu
  have hηmass : η Set.univ = 1 := by
    simpa [η, P0TubeAdmissibleMeasures.eta] using M.companion_mass
  letI : IsFiniteMeasure η := ⟨by
    rw [hηmass]
    simp⟩
  have hκη : Measure.map Complex.ofReal M.kappa ≤ η := by
    exact Measure.le_add_right le_rfl
  have hνη : M.nu ≤ η := by
    exact Measure.le_add_left le_rfl
  letI : IsFiniteMeasure (Measure.map Complex.ofReal M.kappa) := ⟨by
    calc
      (Measure.map Complex.ofReal M.kappa) Set.univ ≤ η Set.univ := hκη Set.univ
      _ < ⊤ := measure_lt_top η Set.univ⟩
  letI : IsFiniteMeasure M.nu := ⟨by
    calc
      M.nu Set.univ ≤ η Set.univ := hνη Set.univ
      _ < ⊤ := measure_lt_top η Set.univ⟩
  letI : IsFiniteMeasure M.mu := ⟨by
    rw [M.frequency_mass]
    simp⟩
  have hk_ae : ∀ᵐ x ∂M.kappa,
      x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) := by
    exact (Measure.absolutelyContinuous_of_le M.kappa_le_density).ae_le
      (ae_restrict_mem measurableSet_Icc)
  have hκsupp : ∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa),
      z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0 := by
    have hset : MeasurableSet
        {z : ℂ | z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0} := by
      exact (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
        ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
    rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
    filter_upwards [hk_ae] with x hx
    constructor
    · simp only [Complex.ofReal_re]
      exact ⟨by linarith [hx.1], by linarith [hx.2]⟩
    · simp
  have hκnorm : ∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa), ‖z‖ ≤ 4 := by
    have hset : MeasurableSet {z : ℂ | ‖z‖ ≤ 4} := by
      exact measurableSet_le (by fun_prop) measurable_const
    rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
    filter_upwards [hk_ae] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.1, hx.2]
  have hνtube : ∀ᵐ z ∂M.nu, z ∈ tube δ := by
    rw [ae_iff]
    apply measure_mono_null (Set.compl_subset_compl.mpr M.nu_supported)
    exact Measure.measure_compl_support
  have hμae : ∀ᵐ t ∂M.mu, t ∈ Set.Ici (1 / 2 : ℝ) := by
    exact (Measure.absolutelyContinuous_of_le M.mu_le_density).ae_le
      (ae_restrict_mem measurableSet_Ici)
  have hfield_swept : Integrable
      (fun z : ℂ => p0CompanionField z)
      (Measure.map Complex.ofReal M.kappa + TubeEnergy.tubeSwept M.nu) := by
    exact TubeEnergy.integrable_companionField_companion_swept
      (Measure.map Complex.ofReal M.kappa) M.nu hκnorm
  have hνatom : ∀ z : ℂ, M.nu {z} = 0 := by
    intro z
    have hle : M.nu {z} ≤ η {z} := hνη {z}
    have heta : η {z} = 0 := by
      simpa [η, P0TubeAdmissibleMeasures.eta] using hatom z
    exact le_antisymm (hle.trans_eq heta) bot_le
  have hηlog : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (η.prod η) := by
    simpa [η, P0TubeAdmissibleMeasures.eta] using hself
  have hνlog : Integrable
      (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (M.nu.prod M.nu) := by
    have h := hηlog.mono_measure (Measure.prod_mono hνη hνη)
    simpa [li2LogKernel, realLogKernel] using h
  have hνν := TubeEnergy.integrable_li2LogKernel_tubeSwept_self
    hδ hδmax M.nu hνtube hνatom hνlog
  have hκκ : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal M.kappa).prod
        (Measure.map Complex.ofReal M.kappa)) :=
    hηlog.mono_measure (Measure.prod_mono hκη hκη)
  have hκν := TubeEnergy.integrable_li2LogKernel_pinned_gamma
    (Measure.map Complex.ofReal M.kappa) (TubeEnergy.tubeSwept M.nu)
    hκsupp (TubeEnergy.tubeSwept_ae_mem_Gamma M.nu)
  have hνκ := TubeEnergy.integrable_li2LogKernel_gamma_pinned
    (TubeEnergy.tubeSwept M.nu) (Measure.map Complex.ofReal M.kappa)
    (TubeEnergy.tubeSwept_ae_mem_Gamma M.nu) hκsupp
  have hηself : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal M.kappa + TubeEnergy.tubeSwept M.nu).prod
        (Measure.map Complex.ofReal M.kappa + TubeEnergy.tubeSwept M.nu)) :=
    TubeEnergy.integrable_li2LogKernel_companion_swept_self
      (Measure.map Complex.ofReal M.kappa) M.nu hκκ hκν hνκ hνν
  have hκμ : Integrable
      (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((Measure.map Complex.ofReal M.kappa).prod M.mu) := by
    exact hmix.mono_measure (Measure.prod_mono hκη le_rfl)
  have hνμ := TubeEnergy.tubeSwept_mixed_integrable
    hδ hδmax M.nu hνtube M.mu hμae
  have hημ : Integrable
      (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((Measure.map Complex.ofReal M.kappa + TubeEnergy.tubeSwept M.nu).prod M.mu) := by
    rw [Measure.add_prod]
    exact hκμ.add_measure hνμ
  have hNeta : N.eta =
      Measure.map Complex.ofReal M.kappa + TubeEnergy.tubeSwept M.nu := by
    simp only [P0AdmissibleMeasures.eta, p0CompanionMeasure, hκ, hν]
  have hNfield : Integrable
      (fun z : ℂ => p0CompanionField z) N.eta := by
    rw [hNeta]
    exact hfield_swept
  have hNself : Integrable
      (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (N.eta.prod N.eta) := by
    rw [hNeta]
    exact hηself
  have hNatom : ∀ z : ℂ, N.eta {z} = 0 := by
    intro z
    have hmap0 : (Measure.map Complex.ofReal M.kappa) {z} = 0 := by
      have hle := hκη {z}
      have heta : η {z} = 0 := by
        simpa [η, P0TubeAdmissibleMeasures.eta] using hatom z
      exact le_antisymm (hle.trans_eq heta) bot_le
    have hsweep0 := TubeEnergy.tubeSwept_singleton M.nu hνatom z
    rw [hNeta, Measure.add_apply]
    simp [hmap0, hsweep0]
  have hNmixed : Integrable
      (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      (N.eta.prod N.mu) := by
    rw [hNeta, hμ]
    exact hημ
  refine ⟨?_, hNfield, ?_, hNself, hNatom, ?_, hNmixed⟩
  · simpa [hμ] using hfirst
  · simpa [hμ] using hfreqfield
  · simpa [hμ] using hfreqkernel

end Li2Lean.P0
