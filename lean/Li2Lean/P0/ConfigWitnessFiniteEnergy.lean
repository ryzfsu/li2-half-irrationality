/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigTubeWitness
import Li2Lean.P0.MixedCellClearanceFull
import Li2Lean.P0.ContourFieldFinite
import Li2Lean.P0.TubeInteriorPotential
import Li2Lean.P0.TubeVarianceSupport
import Li2Lean.P0.ConfigSelfMeasure
import Li2Lean.P0.ReferenceFrequencyField
import Li2Lean.Kit.LogRectangle

/-!
# Finite energy of the configuration tube competitor

For every retained configuration (`r ≤ 20m`) the witness
`configTubeWitness C = (κ_S, ν_δ, μ_R)` satisfies all seven clauses of
`p0TubeFiniteEnergyCondition` (paper v13 l. 203: bounded densities and
compact support make every regularized logarithmic integral finite).

The pinned and frequency parts are dominated by Lebesgue measure on
`[1/4, 5/4]` and `[1/2, 20]`; the contour part is the circle empirical
measure, carried by the tube `T_δ`, `δ = m^{-2} ≤ 1/64`.  The two clearances
`d_+ = 751/5000`, `d_- = 1749/5000` (`mixedCellClearance_full`) keep the
cross kernels bounded on the tube.
-/

open MeasureTheory Set

namespace Li2Lean.P0.CoefficientAssembly

open Li2Lean.P0
open Li2Lean.P0.Config

noncomputable section

/-! ## Elementary bounds -/

/-- Two-sided bounds on a positive argument bound the absolute logarithm. -/
theorem abs_log_le_of_bounds {x a b : ℝ} (ha : 0 < a) (ha1 : a ≤ 1) (hb1 : 1 ≤ b)
    (hxa : a ≤ x) (hxb : x ≤ b) :
    |Real.log x| ≤ Real.log b - Real.log a := by
  have hx : 0 < x := lt_of_lt_of_le ha hxa
  have hla : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
  have hlb : 0 ≤ Real.log b := Real.log_nonneg hb1
  have h1 := Real.log_le_log ha hxa
  have h2 := Real.log_le_log hx hxb
  rw [abs_le]
  constructor <;> linarith

theorem Gamma_nonempty : Gamma.Nonempty := ⟨gammaPoint 0, 0, rfl⟩

theorem Gamma_subset_baseEllipseSet : Gamma ⊆ baseEllipseSet := by
  rintro z ⟨u, rfl⟩
  refine ⟨u, ?_⟩
  change p0EllipsePoint 1 u = gammaPoint u
  exact ellipsePoint_one_eq_gammaPoint u

/-- A tube point is within `δ` of a point of `Γ`. -/
theorem exists_Gamma_near {δ : ℝ} {z : ℂ} (hz : z ∈ tube δ) :
    ∃ w ∈ Gamma, ‖z - w‖ ≤ δ := by
  obtain ⟨w, hw, hd⟩ :=
    TubeInterior.isCompact_Gamma.exists_infDist_eq_dist Gamma_nonempty z
  refine ⟨w, hw, ?_⟩
  rw [← dist_eq_norm, ← hd]
  exact hz

theorem norm_gammaPoint_le_three (u : ℝ) : ‖gammaPoint u‖ ≤ 3 := by
  have hre : (gammaPoint u).re = center + semiMajor * Real.cos u := by
    rw [gammaPoint, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : (gammaPoint u).im = semiMinor * Real.sin u := by
    rw [gammaPoint, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : ‖gammaPoint u‖ ^ 2 ≤ 3 ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have hs := Real.sin_sq_add_cos_sq u
    have hc1 := Real.cos_le_one u
    have hc2 := Real.neg_one_le_cos u
    norm_num [center, semiMajor, semiMinor]
    nlinarith [sq_nonneg (Real.sin u), sq_nonneg (Real.cos u)]
  exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) hsq

theorem tube_norm_le {δ : ℝ} (hδ : δ ≤ 1 / 64) {z : ℂ} (hz : z ∈ tube δ) :
    ‖z‖ ≤ 3 + 1 / 64 := by
  obtain ⟨w, hw, hzw⟩ := exists_Gamma_near hz
  obtain ⟨u, rfl⟩ := hw
  have hw3 := norm_gammaPoint_le_three u
  calc ‖z‖ = ‖(z - gammaPoint u) + gammaPoint u‖ := by ring_nf
    _ ≤ ‖z - gammaPoint u‖ + ‖gammaPoint u‖ := norm_add_le _ _
    _ ≤ 3 + 1 / 64 := by linarith

/-- Clearance of the tube from the pinned segment. -/
theorem tube_pinned_clearance {δ : ℝ} (hδ : δ ≤ 1 / 64) {z : ℂ} (hz : z ∈ tube δ)
    {x : ℝ} (hx : x ∈ Set.Icc (0 : ℝ) 2) :
    (1 / 8 : ℝ) ≤ ‖z - (x : ℂ)‖ := by
  obtain ⟨w, hw, hzw⟩ := exists_Gamma_near hz
  have hcl := mixedCellClearance_full.1 w (Gamma_subset_baseEllipseSet hw) x hx
  have htri : ‖w - (x : ℂ)‖ ≤ ‖w - z‖ + ‖z - (x : ℂ)‖ := by
    calc ‖w - (x : ℂ)‖ = ‖(w - z) + (z - (x : ℂ))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev] at hzw
  norm_num [dPlus] at hcl
  linarith

/-- Clearance of the tube from the reflected frequency ray. -/
theorem tube_frequency_clearance {δ : ℝ} (hδ : δ ≤ 1 / 64) {z : ℂ} (hz : z ∈ tube δ)
    {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
    (1 / 4 : ℝ) ≤ ‖z + (t : ℂ)‖ := by
  obtain ⟨w, hw, hzw⟩ := exists_Gamma_near hz
  have hcl := mixedCellClearance_full.2 w (Gamma_subset_baseEllipseSet hw) t ht
  have htri : ‖w + (t : ℂ)‖ ≤ ‖w - z‖ + ‖z + (t : ℂ)‖ := by
    calc ‖w + (t : ℂ)‖ = ‖(w - z) + (z + (t : ℂ))‖ := by ring_nf
      _ ≤ _ := norm_add_le _ _
  rw [norm_sub_rev] at hzw
  norm_num [dMinus] at hcl
  linarith

/-! ## Almost-everywhere support of the three components -/

theorem configTubeRadius_le (C : FiniteConfiguration) :
    configTubeRadius C ≤ 1 / 64 := by
  have h8 : (8 : ℝ) ≤ C.m := by exact_mod_cast C.m_ge_eight
  unfold configTubeRadius
  rw [div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith

theorem pinnedMeasure_ae_mem (C : FiniteConfiguration) :
    ∀ᵐ x ∂(pinnedMeasure C.m C.pinned), x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) :=
  (Measure.absolutelyContinuous_of_le (pinnedMeasure_le C)).ae_le
    (ae_restrict_mem measurableSet_Icc)

/-- With the retained head, the frequency cells lie in `[1/2, 20]`. -/
theorem frequencyMeasure_le_head (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    frequencyMeasure C.m C.frequency ≤ volume.restrict (Set.Icc (1 / 2 : ℝ) 20) := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  unfold frequencyMeasure frequencyCell
  have hcell : ∀ r ∈ C.frequency,
      Set.Ico (((r - 1 : ℕ) : ℝ) / (C.m : ℝ)) ((r : ℝ) / (C.m : ℝ)) =
        Set.Ico (((r - 1 : ℕ) : ℝ) / (C.m : ℝ)) ((((r - 1) + 1 : ℕ) : ℝ) / (C.m : ℝ)) := by
    intro r hr
    have h1 := C.frequency_lower r hr
    have : r - 1 + 1 = r := by omega
    rw [this]
  rw [Finset.sum_congr rfl (fun r hr => by rw [hcell r hr])]
  apply sum_restrict_le_restrict C.frequency _ _ (fun i => measurableSet_Ico)
  · intro r hr s hs hrs
    have hr1 := C.frequency_lower r hr
    have hs1 := C.frequency_lower s hs
    have hne : r - 1 ≠ s - 1 := by omega
    exact Ico_cells_pairwiseDisjoint C.m {r - 1, s - 1}
      (fun i => (i : ℝ) / (C.m : ℝ)) (fun i => rfl) (by simp) (by simp) hne
  · intro r hr
    have h1 := C.frequency_lower r hr
    have h2 := hhead r hr
    have hr' : (2 * k : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
      have : 2 * k ≤ r - 1 := by omega
      exact_mod_cast this
    have hr'' : (((r - 1 + 1 : ℕ)) : ℝ) ≤ 80 * k := by
      have : r - 1 + 1 ≤ 80 * k := by omega
      exact_mod_cast this
    intro x hx
    rw [Set.mem_Ico] at hx
    have hlo : (1 / 2 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) := by
      rw [le_div_iff₀ hmR, hmk]
      linarith
    have hhi : (((r - 1 + 1 : ℕ)) : ℝ) / (C.m : ℝ) ≤ 20 := by
      rw [div_le_iff₀ hmR, hmk]
      linarith
    exact ⟨by linarith [hx.1], by linarith [hx.2]⟩

theorem frequencyMeasure_ae_mem (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    ∀ᵐ t ∂(frequencyMeasure C.m C.frequency), t ∈ Set.Icc (1 / 2 : ℝ) 20 :=
  (Measure.absolutelyContinuous_of_le (frequencyMeasure_le_head C hhead)).ae_le
    (ae_restrict_mem measurableSet_Icc)

theorem configContourMeasure_ae_tube (C : FiniteConfiguration) :
    ∀ᵐ z ∂(configContourMeasure C), z ∈ tube (configTubeRadius C) := by
  rw [ae_iff]
  exact circleEmpiricalMeasure_outside_tube C.contour (contour_mem_Gamma C)
    (configTubeRadius_pos C) C.m

instance pinnedMeasure_finite (C : FiniteConfiguration) :
    IsFiniteMeasure (pinnedMeasure C.m C.pinned) := by
  constructor
  rw [pinnedMeasure_univ]
  exact ENNReal.mul_lt_top (ENNReal.natCast_lt_top _) ENNReal.ofReal_lt_top

instance frequencyMeasure_finite (C : FiniteConfiguration) :
    IsFiniteMeasure (frequencyMeasure C.m C.frequency) := by
  constructor
  rw [frequencyMeasure_univ]
  exact ENNReal.one_lt_top

instance configContourMeasure_finite (C : FiniteConfiguration) :
    IsFiniteMeasure (configContourMeasure C) := by
  unfold configContourMeasure
  infer_instance

instance mapPinned_finite (C : FiniteConfiguration) :
    IsFiniteMeasure (Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned)) := by
  infer_instance

theorem mapPinned_ae (C : FiniteConfiguration) :
    ∀ᵐ z ∂(Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned)),
      z.im = 0 ∧ z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
  have hmeas : MeasurableSet {z : ℂ | z.im = 0 ∧ z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)} :=
    (measurableSet_eq_fun Complex.measurable_im measurable_const).inter
      (Complex.measurable_re measurableSet_Icc)
  rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hmeas]
  filter_upwards [pinnedMeasure_ae_mem C] with x hx
  simpa using hx

/-! ## The seven finite-energy clauses -/

theorem witness_eta_eq (C : FiniteConfiguration) :
    (configTubeWitness C).eta =
      Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned) + configContourMeasure C :=
  rfl

theorem witness_eta_ae_norm (C : FiniteConfiguration) :
    ∀ᵐ z ∂(configTubeWitness C).eta, ‖z‖ ≤ 3 + 1 / 64 := by
  rw [witness_eta_eq, ae_add_measure_iff]
  constructor
  · filter_upwards [mapPinned_ae C] with z hz
    have hzreal : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hz.1]
    rw [hzreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hz.2.1])]
    linarith [hz.2.2]
  · filter_upwards [configContourMeasure_ae_tube C] with z hz
    exact tube_norm_le (configTubeRadius_le C) hz

instance witness_eta_finite (C : FiniteConfiguration) :
    IsFiniteMeasure (configTubeWitness C).eta := by
  rw [witness_eta_eq]
  infer_instance

/-- Clause 1: the first moment. -/
theorem witness_integrable_id (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    Integrable (fun t : ℝ => t) (configTubeWitness C).mu := by
  have h : Integrable (fun t : ℝ => t) (volume.restrict (Set.Icc (1 / 2 : ℝ) 20)) :=
    continuousOn_id.integrableOn_Icc
  exact h.mono_measure (frequencyMeasure_le_head C hhead)

/-- Clause 2: the companion field. -/
theorem witness_integrable_companion (C : FiniteConfiguration) :
    Integrable (fun z : ℂ => p0CompanionField z) (configTubeWitness C).eta := by
  apply EnergyLowerBound.integrable_companionField_of_ae_norm_le
  filter_upwards [witness_eta_ae_norm C] with z hz
  linarith

/-- Clause 3: the regularized frequency field. -/
theorem witness_integrable_frequencyField (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    Integrable (fun t : ℝ => p0RegularizedFrequencyField t) (configTubeWitness C).mu := by
  have hlog : ContinuousOn (fun t : ℝ => Real.log (1 + t)) (Set.Icc (1 / 2 : ℝ) 20) := by
    apply ContinuousOn.log
    · fun_prop
    · intro t ht
      have := ht.1
      intro h0
      linarith
  have hfield : ContinuousOn (fun t : ℝ => p0RegularizedFrequencyField t)
      (Set.Icc (1 / 2 : ℝ) 20) := by
    unfold p0RegularizedFrequencyField
    exact ((ReferencePackaging.continuous_B0_literal.continuousOn.sub
      ReferencePackaging.continuous_psi_literal.continuousOn).sub (hlog.const_mul 3))
  have h : Integrable (fun t : ℝ => p0RegularizedFrequencyField t)
      (volume.restrict (Set.Icc (1 / 2 : ℝ) 20)) := hfield.integrableOn_Icc
  exact h.mono_measure (frequencyMeasure_le_head C hhead)

/-- Clause 5: `η` has no atoms. -/
theorem witness_eta_atomless (C : FiniteConfiguration) (z : ℂ) :
    (configTubeWitness C).eta {z} = 0 := by
  rw [witness_eta_eq, Measure.add_apply,
    Measure.map_apply Complex.measurable_ofReal (measurableSet_singleton z)]
  have hpre : Complex.ofReal ⁻¹' {z} ⊆ {z.re} := by
    intro x hx
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hx
    simp [← hx]
  have hκ : pinnedMeasure C.m C.pinned (Complex.ofReal ⁻¹' {z}) = 0 := by
    apply measure_mono_null hpre
    apply nonpos_iff_eq_zero.mp
    calc pinnedMeasure C.m C.pinned {z.re} ≤
        volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) {z.re} := pinnedMeasure_le C _
      _ ≤ volume {z.re} := Measure.restrict_le_self _
      _ = 0 := Real.volume_singleton
  have hν : configContourMeasure C {z} = 0 := by
    exact (circleEmpiricalMeasure_nullSingleton C.contour (configTubeRadius_pos C)
      C.m).measure_singleton z
  rw [hκ, hν, add_zero]

/-- Clause 6: the regularized frequency self-kernel. -/
theorem witness_integrable_frequencyKernel (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      ((configTubeWitness C).mu.prod (configTubeWitness C).mu) := by
  set lam : Measure ℝ := volume.restrict (Set.Icc (1 / 2 : ℝ) 20) with hlam
  have hlamIco : lam = volume.restrict (Set.Ico (1 / 2 : ℝ) 20) :=
    (Measure.restrict_congr_set Ico_ae_eq_Icc).symm
  have : IsFiniteMeasure lam := by rw [hlam]; infer_instance
  have hle : (configTubeWitness C).mu ≤ lam := frequencyMeasure_le_head C hhead
  have hae : ∀ᵐ t ∂lam, t ∈ Set.Icc (1 / 2 : ℝ) 20 := ae_restrict_mem measurableSet_Icc
  have hlog : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|) (lam.prod lam) := by
    rw [hlamIco]
    exact LogSegment.integrable_log_abs_sub_rectangle (by norm_num)
  have hbd : ∀ᵐ p : ℝ × ℝ ∂(lam.prod lam),
      p.1 ∈ Set.Icc (1 / 2 : ℝ) 20 ∧ p.2 ∈ Set.Icc (1 / 2 : ℝ) 20 := by
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := lam) (ν := lam)).ae hae,
      (Measure.quasiMeasurePreserving_snd (μ := lam) (ν := lam)).ae hae] with p h1 h2
    exact ⟨h1, h2⟩
  have hone : ∀ {x : ℝ}, x ∈ Set.Icc (1 / 2 : ℝ) 20 → |Real.log (1 + x)| ≤ Real.log 21 := by
    intro x hx
    have := abs_log_le_of_bounds (x := 1 + x) (a := 1) (b := 21) one_pos le_rfl
      (by norm_num) (by linarith [hx.1]) (by linarith [hx.2])
    simpa using this
  have h1 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.1)) (lam.prod lam) := by
    refine Integrable.of_bound
      (Real.measurable_log.comp (measurable_const.add measurable_fst)).aestronglyMeasurable
      (Real.log 21) ?_
    filter_upwards [hbd] with p hp
    rw [Real.norm_eq_abs]
    exact hone hp.1
  have h2 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.2)) (lam.prod lam) := by
    refine Integrable.of_bound
      (Real.measurable_log.comp (measurable_const.add measurable_snd)).aestronglyMeasurable
      (Real.log 21) ?_
    filter_upwards [hbd] with p hp
    rw [Real.norm_eq_abs]
    exact hone hp.2
  have hbase : Integrable (fun p : ℝ × ℝ =>
      Real.log (1 + p.1) + Real.log (1 + p.2) - Real.log |p.1 - p.2|) (lam.prod lam) :=
    (h1.add h2).sub hlog
  have hdiag : (lam.prod lam) (Set.diagonal ℝ) = 0 := by
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards with t
    have hset : Prod.mk t ⁻¹' Set.diagonal ℝ = {t} := by
      ext s
      simp [Set.diagonal, eq_comm]
    rw [hset, hlam]
    exact nonpos_iff_eq_zero.mp ((Measure.restrict_le_self _).trans
      (le_of_eq Real.volume_singleton))
  have hne : ∀ᵐ p : ℝ × ℝ ∂(lam.prod lam), p.1 ≠ p.2 := by
    rw [ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ p.2} = Set.diagonal ℝ := by
      ext p
      simp [Set.diagonal]
    rw [hset]
    exact hdiag
  have hfull : Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      (lam.prod lam) := by
    refine hbase.congr ?_
    filter_upwards [hne, hbd] with p hne hp
    have h1ne : (1 + p.1) ≠ 0 := by linarith [hp.1.1]
    have h2ne : (1 + p.2) ≠ 0 := by linarith [hp.2.1]
    have hdiff : |p.1 - p.2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
    simp only [p0RegularizedFrequencyKernel, if_neg hne]
    rw [Real.log_div (mul_ne_zero h1ne h2ne) hdiff, Real.log_mul h1ne h2ne]
  have : IsFiniteMeasure (configTubeWitness C).mu := frequencyMeasure_finite C
  exact hfull.mono_measure (Measure.prod_mono hle hle)

theorem measurable_li2LogKernel :
    Measurable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) := by
  unfold li2LogKernel
  exact (Real.measurable_log.comp (measurable_fst.sub measurable_snd).norm).neg

/-- Clause 4: the companion self-energy. -/
theorem witness_integrable_etaSelf (C : FiniteConfiguration) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      ((configTubeWitness C).eta.prod (configTubeWitness C).eta) := by
  set A : Measure ℂ := Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned) with hA
  set N : Measure ℂ := configContourMeasure C with hN
  have : IsFiniteMeasure A := by rw [hA]; infer_instance
  have : IsFiniteMeasure N := by rw [hN]; infer_instance
  have hδ := configTubeRadius_le C
  have hAae : ∀ᵐ z ∂A, z.im = 0 ∧ z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := mapPinned_ae C
  have hNae : ∀ᵐ z ∂N, z ∈ tube (configTubeRadius C) := configContourMeasure_ae_tube C
  -- the bounded cross kernel
  have hcross : ∀ {x w : ℂ}, (x.im = 0 ∧ x.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) →
      w ∈ tube (configTubeRadius C) →
      |li2LogKernel x w| ≤ Real.log 5 - Real.log (1 / 8) ∧
        |li2LogKernel w x| ≤ Real.log 5 - Real.log (1 / 8) := by
    intro x w hx hw
    have hxreal : x = (x.re : ℂ) := by apply Complex.ext <;> simp [hx.1]
    have hxIcc : x.re ∈ Set.Icc (0 : ℝ) 2 := ⟨by linarith [hx.2.1], by linarith [hx.2.2]⟩
    have hlo : (1 / 8 : ℝ) ≤ ‖w - x‖ := by
      rw [hxreal]
      exact tube_pinned_clearance hδ hw hxIcc
    have hwn := tube_norm_le hδ hw
    have hxn : ‖x‖ ≤ 5 / 4 := by
      rw [hxreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.2.1])]
      exact hx.2.2
    have hhi : ‖w - x‖ ≤ 5 := by
      have := norm_sub_le w x
      linarith
    have hb := abs_log_le_of_bounds (by norm_num) (by norm_num) (by norm_num) hlo hhi
    constructor
    · unfold li2LogKernel
      rw [abs_neg, norm_sub_rev]
      exact hb
    · unfold li2LogKernel
      rw [abs_neg]
      exact hb
  have hAN : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (A.prod N) := by
    refine Integrable.of_bound measurable_li2LogKernel.aestronglyMeasurable
      (Real.log 5 - Real.log (1 / 8)) ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := A) (ν := N)).ae hAae,
      (Measure.quasiMeasurePreserving_snd (μ := A) (ν := N)).ae hNae] with p h1 h2
    rw [Real.norm_eq_abs]
    exact (hcross h1 h2).1
  have hNA : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (N.prod A) := by
    refine Integrable.of_bound measurable_li2LogKernel.aestronglyMeasurable
      (Real.log 5 - Real.log (1 / 8)) ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := N) (ν := A)).ae hNae,
      (Measure.quasiMeasurePreserving_snd (μ := N) (ν := A)).ae hAae] with p h1 h2
    rw [Real.norm_eq_abs]
    exact (hcross h2 h1).2
  have hNN : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (N.prod N) := by
    rw [hN]
    exact integrable_realLogKernel_circleEmpiricalMeasure_prod C.contour
      (configTubeRadius_pos C) C.m
  have hAA : Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (A.prod A) := by
    rw [hA, Measure.map_prod_map _ _ Complex.measurable_ofReal Complex.measurable_ofReal,
      integrable_map_measure measurable_li2LogKernel.aestronglyMeasurable
        (Complex.measurable_ofReal.prodMap Complex.measurable_ofReal).aemeasurable]
    have hcell : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
        ((pinnedMeasure C.m C.pinned).prod (pinnedMeasure C.m C.pinned)) :=
      SelfCells.integrable_latticeCellMeasure_log C.m C.pinned
    refine hcell.neg.congr ?_
    filter_upwards with p
    simp only [Function.comp_apply, Prod.map, li2LogKernel, Pi.neg_apply]
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [witness_eta_eq, ← hA, ← hN, Measure.add_prod, Measure.prod_add, Measure.prod_add]
  exact (hAA.add_measure hAN).add_measure (hNA.add_measure hNN)

/-- Clause 7: the regularized companion-frequency kernel. -/
theorem witness_integrable_mixed (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
      ((configTubeWitness C).eta.prod (configTubeWitness C).mu) := by
  set A : Measure ℂ := Measure.map Complex.ofReal (pinnedMeasure C.m C.pinned) with hA
  set N : Measure ℂ := configContourMeasure C with hN
  set U : Measure ℝ := (configTubeWitness C).mu with hU
  have : IsFiniteMeasure A := by rw [hA]; infer_instance
  have : IsFiniteMeasure N := by rw [hN]; infer_instance
  have : IsFiniteMeasure U := by rw [hU]; exact frequencyMeasure_finite C
  have hδ := configTubeRadius_le C
  have hmeas : Measurable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2) := by
    unfold p0RegularizedMixedKernel
    fun_prop
  have hUae : ∀ᵐ t ∂U, t ∈ Set.Icc (1 / 2 : ℝ) 20 := frequencyMeasure_ae_mem C hhead
  have hbound : ∀ {z : ℂ} {t : ℝ}, t ∈ Set.Icc (1 / 2 : ℝ) 20 →
      (1 / 4 : ℝ) ≤ ‖z + (t : ℂ)‖ → ‖z‖ ≤ 4 →
      |p0RegularizedMixedKernel z t| ≤ Real.log 84 - Real.log (1 / 16) := by
    intro z t ht hlo hz
    have hhi : ‖z + (t : ℂ)‖ ≤ 24 := by
      have := norm_add_le z (t : ℂ)
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])] at this
      linarith [ht.2]
    have hpos : 0 < ‖z + (t : ℂ)‖ := lt_of_lt_of_le (by norm_num) hlo
    have hr1 : (1 / 16 : ℝ) ≤ (1 + t) / ‖z + (t : ℂ)‖ := by
      rw [le_div_iff₀ hpos]
      nlinarith [ht.1]
    have hr2 : (1 + t) / ‖z + (t : ℂ)‖ ≤ 84 := by
      rw [div_le_iff₀ hpos]
      nlinarith [ht.2]
    unfold p0RegularizedMixedKernel
    exact abs_log_le_of_bounds (by norm_num) (by norm_num) (by norm_num) hr1 hr2
  have hAU : Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2) (A.prod U) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      (Real.log 84 - Real.log (1 / 16)) ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := A) (ν := U)).ae (mapPinned_ae C),
      (Measure.quasiMeasurePreserving_snd (μ := A) (ν := U)).ae hUae] with p h1 h2
    rw [Real.norm_eq_abs]
    have hxreal : p.1 = (p.1.re : ℂ) := by apply Complex.ext <;> simp [h1.1]
    have hlo : (1 / 4 : ℝ) ≤ ‖p.1 + (p.2 : ℂ)‖ := by
      rw [hxreal, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
        abs_of_nonneg (by linarith [h1.2.1, h2.1])]
      linarith [h1.2.1, h2.1]
    have hz : ‖p.1‖ ≤ 4 := by
      rw [hxreal, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [h1.2.1])]
      linarith [h1.2.2]
    exact hbound h2 hlo hz
  have hNU : Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2) (N.prod U) := by
    refine Integrable.of_bound hmeas.aestronglyMeasurable
      (Real.log 84 - Real.log (1 / 16)) ?_
    filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := N) (ν := U)).ae
        (configContourMeasure_ae_tube C),
      (Measure.quasiMeasurePreserving_snd (μ := N) (ν := U)).ae hUae] with p h1 h2
    rw [Real.norm_eq_abs]
    have hlo := tube_frequency_clearance hδ h1 h2.1
    have hz : ‖p.1‖ ≤ 4 := by linarith [tube_norm_le hδ h1]
    exact hbound h2 hlo hz
  rw [witness_eta_eq, ← hA, ← hN, Measure.add_prod]
  exact hAU.add_measure hNU

/-- The witness has finite energy on the retained head. -/
theorem configWitnessFiniteEnergy : ConfigWitnessFiniteEnergy := by
  intro C hhead
  exact ⟨witness_integrable_id C hhead, witness_integrable_companion C,
    witness_integrable_frequencyField C hhead, witness_integrable_etaSelf C,
    witness_eta_atomless C, witness_integrable_frequencyKernel C hhead,
    witness_integrable_mixed C hhead⟩

/-- The cell comparison is reduced to the cell inequality alone. -/
theorem configEnergyComparisonHead_of_cellBound (hcell : ConfigWitnessCellBound) :
    ConfigEnergyComparisonHead :=
  configEnergyComparisonHead_of_witness configWitnessFiniteEnergy hcell

/-- `P0AnalyticEstimateAt (397/200)` for every family from the signed envelope
and the witness cell inequality. -/
theorem p0AnalyticEstimateAt_all_of_envelope_cellBound
    (henv : P0SignedCoefficientEnvelope) (hcell : ConfigWitnessCellBound) :
    ∀ F : P0Family, P0AnalyticEstimateAt ((caSlackAlphaTarget : ℚ) : ℝ) F :=
  p0AnalyticEstimateAt_all_of_inputs henv (configEnergyComparisonHead_of_cellBound hcell)

end

end Li2Lean.P0.CoefficientAssembly

namespace Li2Lean

open Li2Lean.P0.CoefficientAssembly

/-- Main consumer with the finite-energy witness discharged: irrationality of
`Li2(1/2)` from the signed envelope, the witness cell inequality and the
integerizer bound. -/
theorem li2_half_irrational_of_envelope_cellBound
    (henv : P0SignedCoefficientEnvelope) (hcell : ConfigWitnessCellBound)
    (hIntegerizer : P0IntegerizerBound p0A2CanonicalFamily) :
    Irrational (li2InvValue (2 : ℤ)) :=
  li2_half_irrational_of_coefficient_leaves henv
    (configEnergyComparisonHead_of_cellBound hcell) hIntegerizer

end Li2Lean
