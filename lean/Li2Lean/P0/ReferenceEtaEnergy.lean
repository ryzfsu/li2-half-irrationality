/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferencePackaging
import Li2Lean.P0.ReferenceAtomless
import Li2Lean.Kit.LogRectangle

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment ConfigContourMeasure

/-- The real logarithmic kernel is absolutely integrable on every finite
product of literal reference cells, including self-cells and shared endpoints. -/
theorem integrable_log_referenceMeasure_prod (start : ℝ) (count : ℕ)
    (units : List ℕ) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((referenceMeasure start count units).prod
        (referenceMeasure start count units)) := by
  unfold referenceMeasure
  rw [← Measure.sum_coe_finset (Finset.range count), Measure.prod_sum,
    Measure.sum_fintype, Fintype.sum_prod_type]
  apply integrable_finsetSum_measure.mpr
  intro ij hij
  apply integrable_finsetSum_measure.mpr
  intro ji hji
  have hbase := LogSegment.integrable_log_abs_sub_rectangle
    (a := referenceCellLeft start (ij : ℕ))
    (b := referenceCellRight start (ij : ℕ))
    (c := referenceCellLeft start (ji : ℕ))
    (d := referenceCellRight start (ji : ℕ))
    (referenceCellLeft_le_right start (ji : ℕ))
  rw [Measure.prod_smul_left, Measure.prod_smul_right]
  exact (hbase.smul_measure ENNReal.ofReal_ne_top).smul_measure
    ENNReal.ofReal_ne_top

/-- The pinned C-A component has an honest finite logarithmic self-energy. -/
theorem integrable_log_kappa0_prod :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      (kappa0.prod kappa0) := by
  exact integrable_log_referenceMeasure_prod (1 / 4) 32 ConfigData.pinnedMassUnits

/-- After mapping both variables to the real axis in ℂ, the literal C-A
component has a genuine Li2 logarithmic-kernel integrability proof. -/
theorem integrable_li2LogKernel_kappa0_prod :
    Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((Measure.map Complex.ofReal kappa0).prod
        (Measure.map Complex.ofReal kappa0)) := by
  letI : ∀ i : (Finset.range 32), IsFiniteMeasure
      (ENNReal.ofReal (referenceDensity ConfigData.pinnedMassUnits (i : ℕ)) •
        volume.restrict (Set.Ico (referenceCellLeft (1 / 4) (i : ℕ))
          (referenceCellRight (1 / 4) (i : ℕ)))) := by
    intro i
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact measure_Ico_lt_top
  letI : SFinite kappa0 := by
    unfold kappa0 ConfigSegment.pinnedReferenceMeasure ConfigSegment.referenceMeasure
    rw [← Measure.sum_coe_finset (Finset.range 32)]
    exact sfinite_sum_of_countable _
  rw [Measure.map_prod_map kappa0 kappa0 Complex.measurable_ofReal
    Complex.measurable_ofReal]
  have hmeas : Measurable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) := by
    unfold li2LogKernel
    exact (Real.measurable_log.comp
      (by fun_prop : Measurable fun x : ℂ × ℂ => ‖x.1 - x.2‖)).neg
  apply (integrable_map_measure hmeas.aestronglyMeasurable
    ((Complex.measurable_ofReal.comp measurable_fst).prodMk
      (Complex.measurable_ofReal.comp measurable_snd)).aemeasurable).2
  have h := integrable_log_kappa0_prod
  have hneg := h.neg
  simpa only [Function.comp_apply, Prod.map_apply] using hneg.congr (by
    filter_upwards [] with p
    change -Real.log |p.1 - p.2| =
      -Real.log ‖(p.1 : ℂ) - (p.2 : ℂ)‖
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs])

/-- The companion product expands into the four literal C-A/contour products.
This is the exact measure identity used to isolate the remaining contour
product API obligation. -/
theorem eta0_prod_expand :
    eta0.prod eta0 =
      (Measure.map Complex.ofReal kappa0).prod (Measure.map Complex.ofReal kappa0) +
      (Measure.map Complex.ofReal kappa0).prod nu0 +
      nu0.prod (Measure.map Complex.ofReal kappa0) + nu0.prod nu0 := by
  letI : ∀ i : (Finset.range 32), IsFiniteMeasure
      (ENNReal.ofReal (referenceDensity ConfigData.pinnedMassUnits (i : ℕ)) •
        volume.restrict (Set.Ico (referenceCellLeft (1 / 4) (i : ℕ))
          (referenceCellRight (1 / 4) (i : ℕ)))) := by
    intro i
    constructor
    rw [Measure.smul_apply, Measure.restrict_apply_univ]
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    exact measure_Ico_lt_top
  letI : SFinite kappa0 := by
    unfold kappa0 ConfigSegment.pinnedReferenceMeasure ConfigSegment.referenceMeasure
    rw [← Measure.sum_coe_finset (Finset.range 32)]
    exact sfinite_sum_of_countable _
  letI : SFinite nu0 := by
    unfold nu0 ConfigContourMeasure.contourReferenceMeasure
    letI : IsFiniteMeasure ConfigContourMeasure.contourParamMeasure := by
      constructor
      rw [ConfigContourMeasure.contourParamMeasure_univ]
      exact ENNReal.ofReal_lt_top
    infer_instance
  unfold eta0 p0CompanionMeasure
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  ac_rfl

/-- The literal companion is atomless by the direct κ/ν singleton proof. -/
theorem eta0_singleton_literal (z : ℂ) : eta0 {z} = 0 := by
  change p0CompanionMeasure kappa0 nu0 {z} = 0
  unfold kappa0 nu0
  exact eta0_singleton z

end
end Li2Lean.P0.ReferencePackaging
