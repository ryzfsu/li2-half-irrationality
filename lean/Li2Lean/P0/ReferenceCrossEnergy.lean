/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceEtaEnergy
import Li2Lean.P0.MixedCellClearanceFull
import Li2Lean.P0.ConfigContourMeasure
import Li2Lean.P0.TubeVarianceSupport

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment ConfigContourMeasure Config

private theorem kappa0_finite : IsFiniteMeasure kappa0 := by
  constructor
  unfold kappa0 ConfigSegment.pinnedReferenceMeasure ConfigSegment.referenceMeasure
  rw [Measure.finsetSum_apply]
  simp only [Measure.smul_apply, Measure.restrict_apply_univ]
  rw [ENNReal.sum_lt_top]
  intro j hj
  apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
  exact measure_Ico_lt_top

private theorem kappa0_ae_mem_Icc : ∀ᵐ x ∂kappa0, x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
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

private theorem nu0_ae_mem_Gamma : ∀ᵐ z ∂nu0, z ∈ Gamma := by
  filter_upwards [Measure.support_mem_ae (μ := nu0)] with z hz
  exact nu0_supported hz

private theorem kappa0_map_finite : IsFiniteMeasure (Measure.map Complex.ofReal kappa0) := by
  letI : IsFiniteMeasure kappa0 := kappa0_finite
  constructor
  rw [Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ, preimage_univ]
  exact (measure_lt_top kappa0 Set.univ)

private theorem kappa0_map_ae_mem_segment :
    ∀ᵐ z ∂(Measure.map Complex.ofReal kappa0),
      z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0 := by
  have hset : MeasurableSet {z : ℂ |
      z.re ∈ Set.Icc (0 : ℝ) 2 ∧ z.im = 0} := by
    exact (measurableSet_Icc.preimage Complex.continuous_re.measurable).inter
      ((measurableSet_singleton (0 : ℝ)).preimage Complex.continuous_im.measurable)
  rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
  filter_upwards [kappa0_ae_mem_Icc] with x hx
  constructor
  · simp only [Complex.ofReal_re]
    constructor <;> linarith [hx.1, hx.2]
  · simp only [Complex.ofReal_im]

private theorem gamma_subset_baseEllipseSet : Gamma ⊆ baseEllipseSet := by
  intro z hz
  rcases hz with ⟨u, rfl⟩
  refine ⟨u, ?_⟩
  change p0EllipsePoint 1 u = gammaPoint u
  exact ellipsePoint_one_eq_gammaPoint u

private theorem integrable_pinned_gamma
    (κ ν : Measure ℂ) [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (hκ : ∀ᵐ x ∂κ, x.re ∈ Set.Icc (0 : ℝ) 2 ∧ x.im = 0)
    (hν : ∀ᵐ y ∂ν, y ∈ Gamma) :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (κ.prod ν) := by
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    fun_prop
  refine Integrable.of_bound hmeas.aestronglyMeasurable
    (|Real.log (751 / 5000 : ℝ)| + |Real.log 6|) ?_
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := κ) (ν := ν)).ae hκ
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := κ) (ν := ν)).ae hν
  filter_upwards [h1, h2] with p hx hy
  have hbase : p.2 ∈ baseEllipseSet := gamma_subset_baseEllipseSet hy
  have hclear := mixedCellClearance_full.1 p.2 hbase p.1.re hx.1
  have hp1 : p.1 = Complex.ofReal p.1.re := by
    apply Complex.ext <;> simp [hx.2]
  have hlow : (751 / 5000 : ℝ) ≤ ‖p.1 - p.2‖ := by
    rw [hp1]
    simpa [norm_sub_rev, dPlus] using hclear
  have hnorm1 : ‖p.1‖ ≤ 2 := by
    rw [hp1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1.1])]
    exact hx.1.2
  have hnorm2 : ‖p.2‖ ≤ 4 := Li2Lean.P0.TubeVariance.norm_le_four_of_mem_Gamma hy
  have hu : ‖p.1 - p.2‖ ≤ 6 := by
    linarith [norm_sub_le p.1 p.2]
  have hpos : (0 : ℝ) < 751 / 5000 := by norm_num
  have hl := Real.log_le_log hpos hlow
  have hu' := Real.log_le_log (lt_of_lt_of_le hpos hlow) hu
  have hloglow : Real.log (751 / 5000 : ℝ) < 0 := Real.log_neg (by norm_num) (by norm_num)
  have hlog6 : 0 ≤ Real.log (6 : ℝ) := Real.log_nonneg (by norm_num)
  have habslow : |Real.log (751 / 5000 : ℝ)| = -Real.log (751 / 5000 : ℝ) := abs_of_neg hloglow
  have habs6 : |Real.log (6 : ℝ)| = Real.log (6 : ℝ) := abs_of_nonneg hlog6
  unfold li2LogKernel
  rw [Real.norm_eq_abs, abs_neg]
  change |Real.log ‖p.1 - p.2‖| ≤ |Real.log (751 / 5000 : ℝ)| + |Real.log 6|
  rw [abs_le, habslow, habs6]
  constructor <;> linarith [le_abs_self (Real.log 6), neg_le_abs (Real.log (751 / 5000)),
    abs_nonneg (Real.log 6), abs_nonneg (Real.log (751 / 5000))]

/-- The literal C-A/Fejér cross interaction, with the pinned component first. -/
theorem integrable_li2LogKernel_kappa0_nu0 :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal kappa0).prod nu0) := by
  letI : IsFiniteMeasure kappa0 := kappa0_finite
  letI : IsFiniteMeasure (Measure.map Complex.ofReal kappa0) := kappa0_map_finite
  letI : IsFiniteMeasure nu0 := by unfold nu0; infer_instance
  exact integrable_pinned_gamma
    (Measure.map Complex.ofReal kappa0) nu0 kappa0_map_ae_mem_segment nu0_ae_mem_Gamma

/-- The same literal cross interaction with the contour component first. -/
theorem integrable_li2LogKernel_nu0_kappa0 :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (nu0.prod (Measure.map Complex.ofReal kappa0)) := by
  letI : IsFiniteMeasure kappa0 := kappa0_finite
  letI : IsFiniteMeasure (Measure.map Complex.ofReal kappa0) := kappa0_map_finite
  letI : IsFiniteMeasure nu0 := by unfold nu0; infer_instance
  have h := integrable_pinned_gamma
    (Measure.map Complex.ofReal kappa0) nu0 kappa0_map_ae_mem_segment nu0_ae_mem_Gamma
  have hmeas : Measurable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) := by
    unfold li2LogKernel
    fun_prop
  rw [← Measure.prod_swap]
  apply (integrable_map_measure hmeas.aestronglyMeasurable measurable_swap.aemeasurable).2
  simpa [Function.comp_def, Prod.swap, li2LogKernel, norm_sub_rev] using h

end
end Li2Lean.P0.ReferencePackaging

#print axioms Li2Lean.P0.ReferencePackaging.integrable_li2LogKernel_kappa0_nu0
#print axioms Li2Lean.P0.ReferencePackaging.integrable_li2LogKernel_nu0_kappa0
