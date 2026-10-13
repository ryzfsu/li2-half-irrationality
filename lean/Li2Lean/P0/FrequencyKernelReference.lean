/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSegment
import Li2Lean.P0.DualL6Admissible
import Li2Lean.Kit.LogRectangle
set_option maxRecDepth 100000

open MeasureTheory Set
open Li2Lean
namespace Li2Lean.P0.ConfigSegment
noncomputable section

lemma integrable_log_referenceMeasure_prod (start : ℝ) (count : ℕ)
    (units : List ℕ) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((referenceMeasure start count units).prod (referenceMeasure start count units)) := by
  unfold referenceMeasure
  rw [← Measure.sum_coe_finset (Finset.range count), Measure.prod_sum,
    Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  exact ((Li2Lean.LogSegment.integrable_log_abs_sub_rectangle
    (referenceCellLeft_le_right start ij.2)).smul_measure ENNReal.ofReal_ne_top).smul_measure
      ENNReal.ofReal_ne_top

private lemma frequency_log_one_cell_integrable (j : ℕ) (hj : j < 160) :
    Integrable (fun x : ℝ => Real.log (1 + x))
      (volume.restrict (Set.Ico (referenceCellLeft (1 / 2) j)
        (referenceCellRight (1 / 2) j))) := by
  let a : ℝ := referenceCellLeft (1 / 2) j
  let b : ℝ := referenceCellRight (1 / 2) j
  have hab : a ≤ b := by
    dsimp [a, b]
    exact referenceCellLeft_le_right _ _
  have ha : (0 : ℝ) < 1 + a := by
    dsimp [a, referenceCellLeft]
    have : (0 : ℝ) ≤ (j : ℝ) := by positivity
    norm_num
    linarith
  have hcontarg : ContinuousOn (fun x : ℝ => 1 + x) (Set.Icc a b) := by
    exact continuousOn_const.add continuousOn_id
  have hmap : MapsTo (fun x : ℝ => 1 + x) (Set.Icc a b) ({0}ᶜ) := by
    intro x hx
    have hxb : a ≤ x := hx.1
    have hpos : 0 < 1 + x := lt_of_lt_of_le ha (add_le_add_right hxb 1)
    simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using (ne_of_gt hpos)
  have hcont : ContinuousOn (fun x : ℝ => Real.log (1 + x)) (Set.Icc a b) := by
    simpa only [Function.comp_def] using Real.continuousOn_log.comp hcontarg hmap
  have hIcc : Integrable (fun x : ℝ => Real.log (1 + x))
      (volume.restrict (Set.Icc a b)) := hcont.integrableOn_Icc
  have hmono : volume.restrict (Set.Ico a b) ≤ volume.restrict (Set.Icc a b) := by
    exact Measure.restrict_mono Set.Ico_subset_Icc_self le_rfl
  exact hIcc.mono_measure hmono

lemma integrable_log_one_frequency_prod :
    Integrable (fun p : ℝ × ℝ => Real.log (1 + p.1))
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) := by
  unfold frequencyReferenceMeasure referenceMeasure
  rw [← Measure.sum_coe_finset (Finset.range 160), Measure.prod_sum,
    Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hi : Integrable (fun x : ℝ => Real.log (1 + x))
      (volume.restrict (Set.Ico (referenceCellLeft (1 / 2) ij.1)
        (referenceCellRight (1 / 2) ij.1))) :=
    frequency_log_one_cell_integrable ij.1 (Finset.mem_range.mp ij.1.property)
  exact ((hi.comp_fst (volume.restrict (Set.Ico
      (referenceCellLeft (1 / 2) ij.2)
      (referenceCellRight (1 / 2) ij.2)))).smul_measure ENNReal.ofReal_ne_top).smul_measure
      ENNReal.ofReal_ne_top

end
end Li2Lean.P0.ConfigSegment

namespace Li2Lean.P0.ConfigSegment
noncomputable section
lemma frequencyReferenceMeasure_singleton (t : ℝ) : frequencyReferenceMeasure {t} = 0 := by
  unfold frequencyReferenceMeasure referenceMeasure
  simp [Measure.restrict_apply, measurableSet_singleton]
end
end Li2Lean.P0.ConfigSegment

namespace Li2Lean.P0.ConfigSegment
noncomputable section
lemma frequencyReferenceMeasure_ae_pos :
    ∀ᵐ t : ℝ ∂frequencyReferenceMeasure, 0 < 1 + t := by
  rw [ae_iff]
  have hzero : frequencyReferenceMeasure (Set.Iic (-1 : ℝ)) = 0 := by
    unfold frequencyReferenceMeasure referenceMeasure
    rw [← Measure.sum_coe_finset (Finset.range 160), Measure.sum_apply, tsum_fintype]
    · apply Finset.sum_eq_zero
      intro j hj
      rw [Measure.smul_apply]
      · rw [Measure.restrict_apply measurableSet_Iic]
        have hempty : Set.Ico (referenceCellLeft (1 / 2) j)
            (referenceCellRight (1 / 2) j) ∩ Set.Iic (-1 : ℝ) = ∅ := by
          ext t
          simp only [Set.mem_inter_iff, Set.mem_Ico, Set.mem_Iic,
            Set.mem_empty_iff_false, iff_false, not_and]
          intro ht hbad
          have hleft : (0 : ℝ) ≤ (j : ℝ) := by positivity
          have : 0 < 1 + t := by
            dsimp [referenceCellLeft] at ht
            linarith
          linarith
        rw [← Set.inter_comm, hempty, measure_empty, smul_zero]
    · exact measurableSet_Iic
  have hset : {t : ℝ | ¬ 0 < 1 + t} = Set.Iic (-1 : ℝ) := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_Iic]
    constructor <;> intro h <;> linarith
  rw [hset]
  exact hzero
end
end Li2Lean.P0.ConfigSegment


namespace Li2Lean.P0.ConfigSegment
noncomputable section
lemma integrable_log_one_frequency_prod_snd :
    Integrable (fun p : ℝ × ℝ => Real.log (1 + p.2))
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) := by
  unfold frequencyReferenceMeasure referenceMeasure
  rw [← Measure.sum_coe_finset (Finset.range 160), Measure.prod_sum,
    Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  have hj : Integrable (fun x : ℝ => Real.log (1 + x))
      (volume.restrict (Set.Ico (referenceCellLeft (1 / 2) ij.2)
        (referenceCellRight (1 / 2) ij.2))) :=
    frequency_log_one_cell_integrable ij.2 (Finset.mem_range.mp ij.2.property)
  exact ((hj.comp_snd (volume.restrict (Set.Ico
      (referenceCellLeft (1 / 2) ij.1)
      (referenceCellRight (1 / 2) ij.1)))).smul_measure ENNReal.ofReal_ne_top).smul_measure
      ENNReal.ofReal_ne_top
end
end Li2Lean.P0.ConfigSegment

namespace Li2Lean.P0
noncomputable section
open ConfigSegment

theorem p0RegularizedFrequencyKernel_frequencyReference_integrable :
    Integrable (fun p : ℝ × ℝ => p0RegularizedFrequencyKernel p.1 p.2)
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) := by
  letI : SFinite frequencyReferenceMeasure := by
    unfold frequencyReferenceMeasure referenceMeasure
    rw [← Measure.sum_coe_finset (Finset.range 160)]
    letI : ∀ n : Finset.range 160,
        IsFiniteMeasure (ENNReal.ofReal (referenceDensity ConfigData.frequencyMassUnits n) •
          volume.restrict (Set.Ico (referenceCellLeft (1 / 2) n)
            (referenceCellRight (1 / 2) n))) := by
      intro n
      constructor
      rw [Measure.smul_apply, Measure.restrict_apply_univ]
      exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ico_lt_top
    exact sfinite_sum_of_countable _
  have hlog : Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) :=
    integrable_log_referenceMeasure_prod (1 / 2) 160 ConfigData.frequencyMassUnits
  have h1 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.1))
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) :=
    integrable_log_one_frequency_prod
  have h2 : Integrable (fun p : ℝ × ℝ => Real.log (1 + p.2))
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) :=
    integrable_log_one_frequency_prod_snd
  have hbase : Integrable (fun p : ℝ × ℝ =>
      Real.log (1 + p.1) + Real.log (1 + p.2) - Real.log |p.1 - p.2|)
      (frequencyReferenceMeasure.prod frequencyReferenceMeasure) := h1.add h2 |>.sub hlog
  have hdiag : (frequencyReferenceMeasure.prod frequencyReferenceMeasure)
      (Set.diagonal ℝ) = 0 := by
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards with t
    have hset : Prod.mk t ⁻¹' Set.diagonal ℝ = {t} := by
      ext s
      simp [Set.diagonal, eq_comm]
    simp [hset, frequencyReferenceMeasure_singleton]
  have hne : ∀ᵐ p : ℝ × ℝ ∂(frequencyReferenceMeasure.prod frequencyReferenceMeasure),
      p.1 ≠ p.2 := by
    rw [ae_iff]
    have hset : {p : ℝ × ℝ | ¬ p.1 ≠ p.2} = Set.diagonal ℝ := by
      ext p
      simp [Set.diagonal]
    rw [hset]
    exact hdiag
  have hp1 : ∀ᵐ p : ℝ × ℝ ∂(frequencyReferenceMeasure.prod frequencyReferenceMeasure),
      0 < 1 + p.1 :=
    L6Admissible.ae_fst_of (ν := frequencyReferenceMeasure) frequencyReferenceMeasure_ae_pos
  have hp2 : ∀ᵐ p : ℝ × ℝ ∂(frequencyReferenceMeasure.prod frequencyReferenceMeasure),
      0 < 1 + p.2 :=
    L6Admissible.ae_snd_of (μ := frequencyReferenceMeasure) frequencyReferenceMeasure_ae_pos
  refine hbase.congr ?_
  filter_upwards [hne, hp1, hp2] with p hne hp1 hp2
  have h1ne : (1 + p.1) ≠ 0 := ne_of_gt hp1
  have h2ne : (1 + p.2) ≠ 0 := ne_of_gt hp2
  have hdiff : |p.1 - p.2| ≠ 0 := abs_ne_zero.mpr (sub_ne_zero.mpr hne)
  simp only [p0RegularizedFrequencyKernel, if_neg hne]
  rw [Real.log_div (mul_ne_zero h1ne h2ne) hdiff, Real.log_mul h1ne h2ne]

end
end Li2Lean.P0

namespace Li2Lean.P0.ConfigSegment
noncomputable section
lemma frequencyReferenceMeasure_sfinite : SFinite frequencyReferenceMeasure := by
  unfold frequencyReferenceMeasure referenceMeasure
  rw [← Measure.sum_coe_finset (Finset.range 160)]
  letI : ∀ n : Finset.range 160,
      IsFiniteMeasure (ENNReal.ofReal (referenceDensity ConfigData.frequencyMassUnits n) •
        volume.restrict (Set.Ico (referenceCellLeft (1 / 2) n)
          (referenceCellRight (1 / 2) n))) := by
    intro n
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    exact ENNReal.mul_lt_top ENNReal.ofReal_lt_top measure_Ico_lt_top
  exact sfinite_sum_of_countable _
end
end Li2Lean.P0.ConfigSegment
