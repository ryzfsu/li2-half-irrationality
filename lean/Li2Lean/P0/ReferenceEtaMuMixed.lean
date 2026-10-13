/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceCrossEnergy
import Li2Lean.P0.ReferenceMass

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment ConfigContourMeasure Config

private theorem kappa0_finite_eta_mu : IsFiniteMeasure kappa0 := by
  constructor
  unfold kappa0 ConfigSegment.pinnedReferenceMeasure ConfigSegment.referenceMeasure
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.restrict_apply_univ]
  rw [ENNReal.sum_lt_top]
  intro j hj
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  exact measure_Ico_lt_top

private theorem kappa0_ae_mem_Icc_eta_mu : ∀ᵐ x ∂kappa0,
    x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
  rw [ae_iff]
  unfold kappa0 ConfigSegment.pinnedReferenceMeasure ConfigSegment.referenceMeasure
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  change _ * (volume.restrict (Set.Ico (referenceCellLeft (1 / 4) (j : ℕ))
    (referenceCellRight (1 / 4) (j : ℕ))) ((Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))ᶜ)) = 0
  rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Icc)]
  apply mul_eq_zero_of_right
  have hj' : (j : ℕ) < 32 := Finset.mem_range.mp hj
  have hleft : (1 / 4 : ℝ) ≤ referenceCellLeft (1 / 4) (j : ℕ) := by
    simp [referenceCellLeft]
    positivity
  have hright : referenceCellRight (1 / 4) (j : ℕ) ≤ (5 / 4 : ℝ) := by
    have hj'' : (j : ℝ) < 32 := by exact_mod_cast hj'
    dsimp [referenceCellRight]
    have hjNat : j + 1 ≤ 32 := Nat.succ_le_of_lt hj'
    have hj3 : (j : ℝ) + 1 ≤ 32 := by exact_mod_cast hjNat
    norm_num at hj3 ⊢
    linarith [hj3]
  have hsub : Set.Ico (referenceCellLeft (1 / 4) (j : ℕ))
      (referenceCellRight (1 / 4) (j : ℕ)) ⊆ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
    intro x hx
    exact ⟨hleft.trans hx.1, le_of_lt (lt_of_lt_of_le hx.2 hright)⟩
  have hzero : volume ((Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))ᶜ ∩
      Set.Ico (referenceCellLeft (1 / 4) (j : ℕ))
        (referenceCellRight (1 / 4) (j : ℕ))) = 0 := by
    apply measure_mono_null
    · intro x hx
      exact (hx.1 (hsub hx.2)).elim
    · exact measure_empty
  rw [hzero]

private theorem kappa0_map_finite_eta_mu : IsFiniteMeasure
    (Measure.map Complex.ofReal kappa0) := by
  letI : IsFiniteMeasure kappa0 := kappa0_finite_eta_mu
  constructor
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ, preimage_univ]
  exact (measure_lt_top kappa0 Set.univ)

private theorem kappa0_map_ae_mem_segment_eta_mu :
    ∀ᵐ z ∂(Measure.map Complex.ofReal kappa0),
      z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) ∧ z.im = 0 := by
  have hset : MeasurableSet {z : ℂ |
      z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) ∧ z.im = 0} := by
    exact (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
      ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
  rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
  filter_upwards [kappa0_ae_mem_Icc_eta_mu] with x hx
  constructor
  · simp only [Complex.ofReal_re]
    exact hx
  · simp only [Complex.ofReal_im]

private theorem nu0_ae_mem_Gamma_eta_mu : ∀ᵐ z ∂nu0, z ∈ Gamma := by
  filter_upwards [Measure.support_mem_ae (μ := nu0)] with z hz
  exact nu0_supported hz

private theorem nu0_finite_eta_mu : IsFiniteMeasure nu0 := by
  constructor
  rw [nu0_mass]
  exact ENNReal.ofReal_lt_top

private theorem frequency_ae_mem_Icc_eta_mu : ∀ᵐ t ∂mu0,
    t ∈ Set.Icc (1 / 2 : ℝ) (11 / 2 : ℝ) := by
  rw [ae_iff]
  unfold mu0 ConfigSegment.frequencyReferenceMeasure ConfigSegment.referenceMeasure
  rw [Measure.finsetSum_apply]
  apply Finset.sum_eq_zero
  intro j hj
  rw [Measure.smul_apply]
  change _ * (volume.restrict (Set.Ico (referenceCellLeft (1 / 2) (j : ℕ))
    (referenceCellRight (1 / 2) (j : ℕ))) ((Set.Icc (1 / 2 : ℝ) (11 / 2 : ℝ))ᶜ)) = 0
  rw [Measure.restrict_apply (MeasurableSet.compl measurableSet_Icc)]
  apply mul_eq_zero_of_right
  have hj' : (j : ℕ) < 160 := Finset.mem_range.mp hj
  have hleft : (1 / 2 : ℝ) ≤ referenceCellLeft (1 / 2) (j : ℕ) := by
    simp [referenceCellLeft]
    positivity
  have hright : referenceCellRight (1 / 2) (j : ℕ) ≤ (11 / 2 : ℝ) := by
    have hjNat : j + 1 ≤ 160 := Nat.succ_le_of_lt hj'
    have hj3 : (j : ℝ) + 1 ≤ 160 := by exact_mod_cast hjNat
    dsimp [referenceCellRight]
    norm_num at hj3 ⊢
    linarith [hj3]
  have hsub : Set.Ico (referenceCellLeft (1 / 2) (j : ℕ))
      (referenceCellRight (1 / 2) (j : ℕ)) ⊆ Set.Icc (1 / 2 : ℝ) (11 / 2 : ℝ) := by
    intro x hx
    exact ⟨hleft.trans hx.1, le_of_lt (lt_of_lt_of_le hx.2 hright)⟩
  have hzero : volume ((Set.Icc (1 / 2 : ℝ) (11 / 2 : ℝ))ᶜ ∩
      Set.Ico (referenceCellLeft (1 / 2) (j : ℕ))
        (referenceCellRight (1 / 2) (j : ℕ))) = 0 := by
    apply measure_mono_null
    · intro x hx
      exact (hx.1 (hsub hx.2)).elim
    · exact measure_empty
  rw [hzero]

private theorem mu0_finite_eta_mu : IsFiniteMeasure mu0 := by
  constructor
  unfold mu0
  rw [frequencyReferenceMeasure_univ]
  norm_num

private theorem gamma_subset_baseEllipseSet_eta_mu : Gamma ⊆ baseEllipseSet := by
  intro z hz
  rcases hz with ⟨u, rfl⟩
  refine ⟨u, ?_⟩
  change p0EllipsePoint 1 u = gammaPoint u
  exact ellipsePoint_one_eq_gammaPoint u

private theorem measurable_mixed_eta_mu :
    Measurable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2) := by
  unfold p0RegularizedMixedKernel
  fun_prop

private theorem mixed_ratio_bound_kappa_eta_mu {z : ℂ} {t : ℝ}
    (hz : z.re ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) (hz_im : z.im = 0)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) (11 / 2 : ℝ)) :
    (1 / 20 : ℝ) ≤ (1 + t) / ‖z + (t : ℂ)‖ ∧
      (1 + t) / ‖z + (t : ℂ)‖ ≤ 20 := by
  have hzreal : z = Complex.ofReal z.re := by
    apply Complex.ext <;> simp [hz_im]
  have hdenpos : 0 < ‖z + (t : ℂ)‖ := by
    rw [hzreal, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    rw [abs_of_nonneg]
    · linarith [hz.1, ht.1]
    · linarith [hz.1, ht.1]
  have hdenlo : (3 / 4 : ℝ) ≤ ‖z + (t : ℂ)‖ := by
    rw [hzreal, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hz.1, ht.1])]
    linarith [hz.1, ht.1]
  have hdenhi : ‖z + (t : ℂ)‖ ≤ (27 / 4 : ℝ) := by
    rw [hzreal, ← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith [hz.1, ht.1])]
    linarith [hz.2, ht.2]
  have hnumlo : (3 / 2 : ℝ) ≤ 1 + t := by linarith [ht.1]
  have hnumhi : 1 + t ≤ (13 / 2 : ℝ) := by linarith [ht.2]
  have hratio_pos : 0 < (1 + t) / ‖z + (t : ℂ)‖ := div_pos (by linarith) hdenpos
  constructor
  · apply (le_div_iff₀ hdenpos).2
    nlinarith
  · apply (div_le_iff₀ hdenpos).2
    nlinarith

private theorem mixed_ratio_bound_nu_eta_mu {z : ℂ} {t : ℝ}
    (hz : z ∈ Gamma)
    (ht : t ∈ Set.Icc (1 / 2 : ℝ) (11 / 2 : ℝ)) :
    (1 / 20 : ℝ) ≤ (1 + t) / ‖z + (t : ℂ)‖ ∧
      (1 + t) / ‖z + (t : ℂ)‖ ≤ 20 := by
  have hbase : z ∈ baseEllipseSet := gamma_subset_baseEllipseSet_eta_mu hz
  have hdenlo : dMinus ≤ ‖z + Complex.ofReal t‖ :=
    mixedCellClearance_full.2 z hbase t ht.1
  have hznorm : ‖z‖ ≤ 4 := TubeVariance.norm_le_four_of_mem_Gamma hz
  have hdenhi : ‖z + (t : ℂ)‖ ≤ (19 / 2 : ℝ) := by
    have htri := norm_add_le z (t : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [ht.1])] at htri
    linarith [htri, hznorm, ht.2]
  have hdenpos : 0 < ‖z + (t : ℂ)‖ := lt_of_lt_of_le (by norm_num [dMinus]) hdenlo
  have hnumlo : (3 / 2 : ℝ) ≤ 1 + t := by linarith [ht.1]
  have hnumhi : 1 + t ≤ (13 / 2 : ℝ) := by linarith [ht.2]
  have hratio_pos : 0 < (1 + t) / ‖z + (t : ℂ)‖ := div_pos (by linarith) hdenpos
  constructor
  · apply (le_div_iff₀ hdenpos).2
    nlinarith [hdenhi]
  · apply (div_le_iff₀ hdenpos).2
    norm_num [dMinus] at hdenlo
    nlinarith [hdenlo, hnumhi]

private theorem integrable_mixed_kappa_eta_mu :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((Measure.map Complex.ofReal kappa0).prod mu0) := by
  letI : IsFiniteMeasure kappa0 := kappa0_finite_eta_mu
  letI : IsFiniteMeasure (Measure.map Complex.ofReal kappa0) := kappa0_map_finite_eta_mu
  letI : IsFiniteMeasure mu0 := mu0_finite_eta_mu
  refine Integrable.of_bound measurable_mixed_eta_mu.aestronglyMeasurable
    |Real.log (20 : ℝ)| ?_
  have hz := (Measure.quasiMeasurePreserving_fst (μ := Measure.map Complex.ofReal kappa0)
    (ν := mu0)).ae kappa0_map_ae_mem_segment_eta_mu
  have ht := (Measure.quasiMeasurePreserving_snd (μ := Measure.map Complex.ofReal kappa0)
    (ν := mu0)).ae frequency_ae_mem_Icc_eta_mu
  filter_upwards [hz, ht] with p hp htp
  have hratio := mixed_ratio_bound_kappa_eta_mu hp.1 hp.2 htp
  rw [p0RegularizedMixedKernel]
  change |Real.log ((1 + p.2) / ‖p.1 + (p.2 : ℂ)‖)| ≤ |Real.log (20 : ℝ)|
  rw [abs_le]
  have hratio_pos : 0 < (1 + p.2) / ‖p.1 + (p.2 : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) hratio.1
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 20) hratio.1
  have hloghi := Real.log_le_log hratio_pos hratio.2
  have h20 : 0 ≤ Real.log (20 : ℝ) := Real.log_nonneg (by norm_num)
  rw [abs_of_nonneg h20]
  have hloginv : Real.log (1 / 20 : ℝ) = -Real.log (20 : ℝ) := by
    have h : (1 / 20 : ℝ) = (20 : ℝ)⁻¹ := by norm_num
    rw [h, Real.log_inv]
  constructor <;> linarith [hloglo, hloghi, hloginv]

private theorem integrable_mixed_nu_eta_mu :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      (nu0.prod mu0) := by
  letI : IsFiniteMeasure nu0 := nu0_finite_eta_mu
  letI : IsFiniteMeasure mu0 := mu0_finite_eta_mu
  refine Integrable.of_bound measurable_mixed_eta_mu.aestronglyMeasurable
    |Real.log (20 : ℝ)| ?_
  have hz := (Measure.quasiMeasurePreserving_fst (μ := nu0) (ν := mu0)).ae
    nu0_ae_mem_Gamma_eta_mu
  have ht := (Measure.quasiMeasurePreserving_snd (μ := nu0) (ν := mu0)).ae
    frequency_ae_mem_Icc_eta_mu
  filter_upwards [hz, ht] with p hp htp
  have hratio := mixed_ratio_bound_nu_eta_mu hp htp
  rw [p0RegularizedMixedKernel]
  change |Real.log ((1 + p.2) / ‖p.1 + (p.2 : ℂ)‖)| ≤ |Real.log (20 : ℝ)|
  rw [abs_le]
  have hratio_pos : 0 < (1 + p.2) / ‖p.1 + (p.2 : ℂ)‖ :=
    lt_of_lt_of_le (by norm_num) hratio.1
  have hloglo := Real.log_le_log (by norm_num : (0 : ℝ) < 1 / 20) hratio.1
  have hloghi := Real.log_le_log hratio_pos hratio.2
  have h20 : 0 ≤ Real.log (20 : ℝ) := Real.log_nonneg (by norm_num)
  rw [abs_of_nonneg h20]
  have hloginv : Real.log (1 / 20 : ℝ) = -Real.log (20 : ℝ) := by
    have h : (1 / 20 : ℝ) = (20 : ℝ)⁻¹ := by norm_num
    rw [h, Real.log_inv]
  constructor <;> linarith [hloglo, hloghi, hloginv]

/-- Literal eta0 times mu0 regularized mixed kernel is integrable. -/
theorem integrable_p0RegularizedMixedKernel_eta0_mu0 :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      (eta0.prod mu0) := by
  letI : IsFiniteMeasure kappa0 := kappa0_finite_eta_mu
  letI : IsFiniteMeasure (Measure.map Complex.ofReal kappa0) := kappa0_map_finite_eta_mu
  letI : IsFiniteMeasure nu0 := nu0_finite_eta_mu
  letI : IsFiniteMeasure mu0 := mu0_finite_eta_mu
  rw [show eta0 = Measure.map Complex.ofReal kappa0 + nu0 by rfl, Measure.add_prod]
  exact integrable_mixed_kappa_eta_mu.add_measure integrable_mixed_nu_eta_mu

#print axioms integrable_p0RegularizedMixedKernel_eta0_mu0

end
end Li2Lean.P0.ReferencePackaging
