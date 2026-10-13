/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Reference
import Li2Lean.P0.DualL6CrossEnergy
import Li2Lean.P0.ConfigSegment

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0

noncomputable section

open L6Variations

/-! A uniform positive-kernel cap for a real interval of length one. -/
private theorem realInterval_l6PosKernel_bound (z : ℂ) :
    (∫⁻ t, l6PosKernel z (t : ℂ) ∂
      (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)))) ≤ ENNReal.ofReal 2 := by
  let a : ℝ := z.re
  let S : Set ℝ := Set.Ico (a - 1) (a + 1)
  let f : ℝ → ℝ := S.indicator (fun t => -Real.log |a - t|)
  have hS : MeasurableSet S := measurableSet_Ico
  have hab : a - 1 ≤ a + 1 := by linarith
  have hlogInt : IntegrableOn (fun t : ℝ => Real.log |a - t|) S := by
    exact Li2Lean.LogSegment.integrableOn_Ico_log_abs_sub a hab
  have hfInt : Integrable f volume := by
    exact hlogInt.neg.integrable_indicator hS
  have hfNonneg : ∀ᵐ t : ℝ ∂volume, 0 ≤ f t := by
    filter_upwards [] with t
    by_cases ht : t ∈ S
    · simp only [f, Set.indicator_of_mem ht]
      have hdist : |a - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> dsimp [S] at ht <;> linarith [ht.1, ht.2]
      exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) hdist)
    · simp [f, ht]
  have hfIntegral : (∫ t, f t ∂volume) = 2 := by
    rw [integral_indicator hS]
    rw [integral_neg]
    rw [Li2Lean.LogSegment.integral_Ico_log_abs_sub a hab]
    dsimp [a]
    norm_num [Li2Lean.LogSegment.primitive]
  have hlinf : (∫⁻ t, ENNReal.ofReal (f t) ∂volume) = ENNReal.ofReal 2 := by
    rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hfInt hfNonneg]
    exact congrArg ENNReal.ofReal hfIntegral
  have hcoll : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))),
      z ≠ (t : ℂ) := by
    rw [ae_restrict_iff' measurableSet_Icc]
    have hae : ∀ᵐ t : ℝ ∂volume, t ≠ z.re := by
      apply ae_iff.2
      have hset : {t : ℝ | ¬t ≠ z.re} = ({z.re} : Set ℝ) := by ext t; simp
      rw [hset]
      simp
    filter_upwards [hae] with t ht hti heq
    apply ht
    have hre := congrArg Complex.re heq
    exact hre.symm
  have hpoint : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))),
      l6PosKernel z (t : ℂ) ≤ ENNReal.ofReal (f t) := by
    have haeA : ∀ᵐ t : ℝ ∂(volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))),
        t ≠ a := by
      rw [ae_restrict_iff' measurableSet_Icc]
      have hae : ∀ᵐ t : ℝ ∂volume, t ≠ a := by
        apply ae_iff.2
        have hset : {t : ℝ | ¬t ≠ a} = ({a} : Set ℝ) := by ext t; simp
        rw [hset]
        simp
      filter_upwards [hae] with t ht hti
      exact ht
    filter_upwards [hcoll, haeA] with t hne hta
    have hnorm : |a - t| ≤ ‖z - (t : ℂ)‖ := by
      have hsq : |a - t| ^ 2 ≤ ‖z - (t : ℂ)‖ ^ 2 := by
        rw [sq_abs, Complex.sq_norm, Complex.normSq_apply]
        dsimp [a]
        nlinarith [sq_nonneg z.im]
      exact (sq_le_sq₀ (abs_nonneg _) (norm_nonneg _)).mp hsq
    by_cases ht : t ∈ S
    · have hdist : |a - t| ≤ 1 := by
        rw [abs_le]
        constructor <;> dsimp [S] at ht <;> linarith [ht.1, ht.2]
      have hinv : ‖z - (t : ℂ)‖⁻¹ ≤ |a - t|⁻¹ := by
        by_cases hz : |a - t| = 0
        · exact False.elim (hta (sub_eq_zero.mp (abs_eq_zero.mp hz)).symm)
        · simpa [one_div] using
            (one_div_le_one_div_of_le (abs_pos.mpr hz) (by simpa [abs_abs] using hnorm))
      have hpos : Real.posLog ‖z - (t : ℂ)‖⁻¹ ≤
          Real.posLog |a - t|⁻¹ := by
        exact Real.posLog_le_posLog (by
          exact le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))) hinv
      have hlog : Real.posLog (|a - t|⁻¹) = -Real.log |a - t| := by
        rw [Real.posLog_apply]
        have hnon : 0 ≤ Real.log (|a - t|⁻¹) := by
          rw [Real.log_inv]
          exact neg_nonneg.mpr (Real.log_nonpos (abs_nonneg _) hdist)
        rw [max_eq_right hnon, Real.log_inv]
      simp only [l6PosKernel, hne, f, Set.indicator_of_mem ht]
      simpa [hlog] using ENNReal.ofReal_le_ofReal hpos
    · have hdist : 1 ≤ |a - t| := by
        by_contra hlt
        have hlt' : |a - t| < 1 := lt_of_not_ge hlt
        have : t ∈ S := by
          rw [mem_Ico]
          constructor <;> linarith [abs_lt.mp hlt']
        exact ht this
      have hzeroNorm : Real.posLog (‖z - (t : ℂ)‖⁻¹) = 0 := by
        apply (Real.posLog_eq_zero_iff _).2
        rw [abs_of_nonneg (inv_nonneg.mpr (norm_nonneg _))]
        exact (inv_le_one₀ (norm_pos_iff.mpr (by exact sub_ne_zero.mpr hne))).2
          (le_trans hdist hnorm)
      simp [l6PosKernel, hne, hzeroNorm, f, ht]
  have hleS : (∫⁻ t, l6PosKernel z (t : ℂ) ∂
      (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)))) ≤
      (∫⁻ t, ENNReal.ofReal (f t) ∂
      (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)))) :=
    lintegral_mono_ae hpoint
  calc
    (∫⁻ t, l6PosKernel z (t : ℂ) ∂
      (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)))) ≤
      (∫⁻ t, ENNReal.ofReal (f t) ∂volume) :=
        hleS.trans (lintegral_mono' Measure.restrict_le_self le_rfl)
    _ = ENNReal.ofReal 2 := hlinf

/-- The pinned reference target inherits the interval cap from its density. -/
theorem pinnedReference_l6PosKernel_bound_of_density
    (κ : Measure ℝ)
    (hκ : κ ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))) :
    ∀ z : ℂ,
      (∫⁻ w, l6PosKernel z w ∂(Measure.map Complex.ofReal κ)) ≤
        ENNReal.ofReal 2 := by
  intro z
  have hof : Measurable (Complex.ofReal : ℝ → ℂ) := Complex.measurable_ofReal
  have hmap : Measure.map Complex.ofReal κ ≤
      Measure.map Complex.ofReal
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))) :=
    Measure.map_mono hκ hof
  have hkernel : Measurable (fun w : ℂ => l6PosKernel z w) := by
    have hp : Measurable (fun w : ℂ => (z, w)) := measurable_const.prodMk measurable_id
    exact (measurable_l6PosKernel.comp hp)
  have hleMap :
      (∫⁻ w, l6PosKernel z w ∂(Measure.map Complex.ofReal κ)) ≤
      (∫⁻ w, l6PosKernel z w ∂
        (Measure.map Complex.ofReal (volume.restrict
          (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))))) :=
    lintegral_mono' hmap (fun _ => le_rfl)
  have hinterval :
      (∫⁻ t, l6PosKernel z (t : ℂ) ∂
        (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)))) ≤
      ENNReal.ofReal 2 := realInterval_l6PosKernel_bound z
  have hmapInterval :
      (∫⁻ w, l6PosKernel z w ∂
        (Measure.map Complex.ofReal (volume.restrict
          (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))))) ≤ ENNReal.ofReal 2 := by
    rw [lintegral_map hkernel hof]
    exact hinterval
  exact hleMap.trans hmapInterval

theorem pinnedReference_l6PosKernel_bound
    (hRef : P0ReferenceFiniteEnergyData) :
    ∀ z : ℂ,
      (∫⁻ w, l6PosKernel z w ∂
        (Measure.map Complex.ofReal (p0ReferenceMeasures hRef).kappa)) ≤
        ENNReal.ofReal 2 := by
  intro z
  exact pinnedReference_l6PosKernel_bound_of_density
    (p0ReferenceMeasures hRef).kappa hRef.kappa_le_density z

/-! The pointwise cap immediately gives the product-measure bound needed by
the L6 cross-energy split. -/
theorem pinnedReference_cross_l6PosKernel_bound_of_density
    (μ : Measure ℂ) (κ : Measure ℝ) [SFinite μ]
    (hκ : κ ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))) :
    (∫⁻ p, l6PosKernel p.1 p.2 ∂
      (μ.prod (Measure.map Complex.ofReal κ))) ≤
      ENNReal.ofReal 2 * μ Set.univ := by
  have hκtop : κ Set.univ < ⊤ := by
    apply lt_of_le_of_lt (hκ Set.univ)
    rw [Measure.restrict_apply_univ]
    norm_num [Real.volume_Icc]
  letI : IsFiniteMeasure κ := ⟨hκtop⟩
  exact lintegral_posKernel_prod_le (C := ENNReal.ofReal 2)
    (fun z => pinnedReference_l6PosKernel_bound_of_density κ hκ z)

theorem pinnedReference_cross_l6PosKernel_bound
    (hRef : P0ReferenceFiniteEnergyData) (μ : Measure ℂ) [SFinite μ] :
    (∫⁻ p, l6PosKernel p.1 p.2 ∂
      (μ.prod (Measure.map Complex.ofReal (p0ReferenceMeasures hRef).kappa))) ≤
      ENNReal.ofReal 2 * μ Set.univ := by
  exact pinnedReference_cross_l6PosKernel_bound_of_density μ
    (p0ReferenceMeasures hRef).kappa hRef.kappa_le_density

end
end Li2Lean.P0
