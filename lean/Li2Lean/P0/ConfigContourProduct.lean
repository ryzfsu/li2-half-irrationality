/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourSelfPotential
import Li2Lean.P0.ConfigContourDiagonalAbel
import Li2Lean.P0.ConfigContourAbelPOC
import Li2Lean.P0.ConfigContourKernel
import Li2Lean.P0.FrequencyRegularity
import Mathlib.MeasureTheory.Group.Prod
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Integral.IntegrableOn

open MeasureTheory
open scoped BigOperators Interval

namespace Li2Lean.P0.ConfigContourProduct

noncomputable section

open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourDiagonalAbel
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourAbelPOC
open Li2Lean.P0.FrequencyRegularity

private theorem continuous_circleZeta : Continuous circleZeta := by
  unfold circleZeta
  fun_prop

private def diagAbs (d : ℝ) : ℝ :=
  |diagonalLogKernel d 0|

private def diagWindow : Set ℝ := Set.Icc (-(2 * Real.pi)) (2 * Real.pi)

private theorem circleZeta_add_two_pi (d : ℝ) :
    circleZeta (d + 2 * Real.pi) = circleZeta d := by
  unfold circleZeta
  rw [show (Complex.I : ℂ) * ((d + 2 * Real.pi : ℝ) : ℂ) =
      (Complex.I * (d : ℂ)) + (2 * (Real.pi : ℂ) * Complex.I) by
        push_cast; ring]
  rw [Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]

private theorem diagonalLogKernel_periodic (d : ℝ) :
    diagonalLogKernel (d + 2 * Real.pi) 0 = diagonalLogKernel d 0 := by
  unfold diagonalLogKernel
  rw [circleZeta_add_two_pi]

private theorem diagAbs_integrable_window' :
    IntervalIntegrable diagAbs volume (-(2 * Real.pi)) (2 * Real.pi) := by
  have hpos : IntervalIntegrable diagAbs volume 0 (2 * Real.pi) := by
    change IntervalIntegrable (fun x => |diagonalLogKernel x 0|) volume 0 (2 * Real.pi)
    exact (diagonalLogKernel_intervalIntegrable 0).norm
  have hneg0 : IntervalIntegrable diagAbs volume (-(2 * Real.pi)) 0 := by
    have hshift := hpos.comp_add_right (2 * Real.pi)
    have heq : (fun x : ℝ => diagAbs (x + 2 * Real.pi)) = diagAbs := by
      funext x
      simp only [diagAbs, diagonalLogKernel_periodic]
    simpa [heq] using hshift
  exact hneg0.trans hpos

private theorem diagAbs_integrable_window :
    IntegrableOn diagAbs diagWindow volume := by
  change Integrable diagAbs (volume.restrict diagWindow)
  exact (intervalIntegrable_iff_integrableOn_Icc_of_le (by linarith [Real.two_pi_pos])).mp
    diagAbs_integrable_window'

private theorem window_const_integrable :
    IntegrableOn (fun _ : ℝ => (1 : ℝ)) (Set.Icc (0 : ℝ) (2 * Real.pi)) volume := by
  apply integrableOn_const
  · exact (measure_Icc_lt_top.ne)
  · simp

private theorem diag_product_integrable :
    IntegrableOn (fun p : ℝ × ℝ => diagAbs p.2)
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ diagWindow)
      (volume.prod volume) := by
  rw [IntegrableOn, ← Measure.prod_restrict]
  exact (diagAbs_integrable_window.comp_snd (volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))))

private theorem diag_product_global_integrable :
    Integrable ((Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ diagWindow).indicator
      (fun p : ℝ × ℝ => diagAbs p.2)) (volume.prod volume) := by
  exact diag_product_integrable.integrable_indicator
    (measurableSet_Icc.prod measurableSet_Icc)

private def diagMajor (p : ℝ × ℝ) : ℝ :=
  (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ diagWindow).indicator
    (fun q : ℝ × ℝ => diagAbs q.2) p

private def subSwap (p : ℝ × ℝ) : ℝ × ℝ := (p.2, p.1 - p.2)

private theorem diagMajor_integrable :
    Integrable diagMajor (volume.prod volume) := by
  exact diag_product_global_integrable

private theorem diagMajor_subSwap_integrable :
    Integrable (diagMajor ∘ subSwap) (volume.prod volume) := by
  have hmp : MeasurePreserving subSwap (volume.prod volume) (volume.prod volume) := by
    change MeasurePreserving (fun z : ℝ × ℝ => (z.2, z.1 - z.2))
      (volume.prod volume) (volume.prod volume)
    exact measurePreserving_prod_sub_swap volume volume
  have hi := hmp.integrable_comp diagMajor_integrable.aestronglyMeasurable
  exact hi.mpr diagMajor_integrable

private theorem correction_norm_bounds (u v : ℝ) :
    1 - contourRatio ≤
        ‖(1 : ℂ) - (contourRatio : ℂ) / (phase u * phase v)‖ ∧
      ‖(1 : ℂ) - (contourRatio : ℂ) / (phase u * phase v)‖ ≤
        1 + contourRatio := by
  let z : ℂ := (contourRatio : ℂ) / (phase u * phase v)
  have hz : ‖z‖ = contourRatio := by
    dsimp [z]
    rw [norm_div, norm_mul, norm_phase, norm_phase, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg,
      div_one]
  have hupper : ‖(1 : ℂ) - z‖ ≤ 1 + contourRatio := by
    calc
      ‖(1 : ℂ) - z‖ ≤ ‖(1 : ℂ)‖ + ‖z‖ := norm_sub_le _ _
      _ = 1 + contourRatio := by rw [norm_one, hz]
  have hlower : 1 - contourRatio ≤ ‖(1 : ℂ) - z‖ := by
    have htriangle : (1 : ℝ) ≤ ‖(1 - z : ℂ)‖ + ‖z‖ := by
      have := norm_add_le (1 - z : ℂ) z
      convert this using 1 <;> rw [sub_add_cancel]
      simp
    rw [hz] at htriangle
    linarith
  exact ⟨by simpa [z] using hlower, by simpa [z] using hupper⟩

private theorem correction_log_abs_le (u v : ℝ) :
    |Real.log ‖(1 : ℂ) - (contourRatio : ℂ) / (phase u * phase v)‖| ≤
      |Real.log (1 - contourRatio)| + Real.log 2 := by
  have hq0 : 0 ≤ contourRatio := contourRatio_nonneg
  have hq1 : contourRatio < 1 := contourRatio_lt_one
  have ha : 0 < 1 - contourRatio := by linarith
  have hx : 0 < ‖(1 : ℂ) - (contourRatio : ℂ) /
      (phase u * phase v)‖ := norm_pos_iff.mpr (correction_ne_zero u v)
  have hb : ‖(1 : ℂ) - (contourRatio : ℂ) /
      (phase u * phase v)‖ ≤ 2 := by
    have h := (correction_norm_bounds u v).2
    linarith
  have hlow := Real.log_le_log ha (correction_norm_bounds u v).1
  have hupp := Real.log_le_log hx hb
  apply abs_le.mpr
  constructor
  · linarith [neg_abs_le (Real.log (1 - contourRatio)), Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]
  · linarith [abs_nonneg (Real.log (1 - contourRatio)), Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 2)]

private theorem diagonal_norm_difference_eq (u v : ℝ) :
    ‖circleZeta (u - v) - circleZeta 0‖ = ‖phase u - phase v‖ := by
  have hfac : circleZeta (u - v) - circleZeta 0 =
      circleZeta (-v) * (circleZeta u - circleZeta v) := by
    calc
      circleZeta (u - v) - circleZeta 0 =
          circleZeta (-v) * circleZeta u - circleZeta (-v) * circleZeta v := by
            have h1 : circleZeta (-v) * circleZeta u = circleZeta (u - v) := by
              rw [circleZeta_mul]
              congr 1
              ring
            have h2 : circleZeta (-v) * circleZeta v = circleZeta 0 := by
              rw [circleZeta_mul]
              congr 1
              ring
            rw [h1, h2]
      _ = circleZeta (-v) * (circleZeta u - circleZeta v) := by ring
  rw [hfac, norm_mul]
  have hv : ‖circleZeta (-v)‖ = 1 := by
    simp [circleZeta, Complex.norm_exp]
  rw [hv, one_mul, circleZeta_eq_phase, circleZeta_eq_phase]

private theorem diagonal_log_abs_eq (u v : ℝ) :
    |Real.log ‖phase u - phase v‖| =
      |diagonalLogKernel (u - v) 0| := by
  unfold diagonalLogKernel
  rw [diagonal_norm_difference_eq]

private theorem contour_kernel_abs_bound (u v : ℝ) :
    |contourLogDistanceKernel (u, v)| ≤
      diagAbs (u - v) +
        (|Real.log contourScale| + |Real.log (1 - contourRatio)| + Real.log 2) := by
  by_cases hphase : phase u = phase v
  · have hdist : Li2Lean.p0EllipsePoint 1 u =
        Li2Lean.p0EllipsePoint 1 v := by
      have hf := ellipse_difference_factorization u v
      have hz : phase u - phase v = 0 := sub_eq_zero.mpr hphase
      rw [hz] at hf
      have hf' : Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v = 0 := by
        simpa using hf
      exact sub_eq_zero.mp hf'
    simp [contourLogDistanceKernel, hdist, diagAbs]
    positivity
  · have hsplit := ellipse_log_distance u v hphase
    have hdiag := diagonal_log_abs_eq u v
    have hcorr := correction_log_abs_le u v
    unfold contourLogDistanceKernel
    rw [hsplit]
    have habs :
        |Real.log contourScale + Real.log ‖phase u - phase v‖ +
            Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| ≤
          |Real.log contourScale| + |Real.log ‖phase u - phase v‖| +
            |Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| := by
      calc
        _ ≤ |Real.log contourScale + Real.log ‖phase u - phase v‖| +
            |Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| :=
          abs_add_le _ _
        _ ≤ (|Real.log contourScale| + |Real.log ‖phase u - phase v‖|) +
            |Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by ring
    rw [hdiag] at habs
    have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
    have hfinal :
        |Real.log contourScale + Real.log ‖phase u - phase v‖ +
            Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| ≤
          |Real.log contourScale| + |diagonalLogKernel (u - v) 0| +
            (|Real.log (1 - contourRatio)| + Real.log 2) := by
      calc
        _ ≤ |Real.log contourScale| + |diagonalLogKernel (u - v) 0| +
            |Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| := habs
        _ ≤ |Real.log contourScale| + |diagonalLogKernel (u - v) 0| +
            (|Real.log (1 - contourRatio)| + Real.log 2) := by
          gcongr
    change |Real.log contourScale + Real.log ‖phase u - phase v‖ +
        Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖| ≤
      |diagonalLogKernel (u - v) 0| +
        (|Real.log contourScale| + |Real.log (1 - contourRatio)| + Real.log 2)
    convert hfinal using 1 <;> ring

private def contourBound : ℝ :=
  |Real.log contourScale| + |Real.log (1 - contourRatio)| + Real.log 2

private theorem contour_bound_nonneg : 0 ≤ contourBound := by
  unfold contourBound
  positivity

private theorem contour_const_integrable :
    IntegrableOn (fun _ : ℝ × ℝ => contourBound)
      contourParameterSquare (volume.prod volume) := by
  unfold contourParameterSquare
  apply integrableOn_const
  ·
    have hfin : IsFiniteMeasure
        ((volume.prod volume).restrict
          (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi))) := by
      rw [← Measure.prod_restrict]
      infer_instance
    have hset : (volume.prod volume)
        (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)) ≠ ⊤ :=
      isFiniteMeasure_restrict.mp hfin
    exact hset
  · finiteness

private theorem contour_const_global_integrable :
    Integrable (contourParameterSquare.indicator
      (fun _ : ℝ × ℝ => contourBound)) (volume.prod volume) := by
  exact contour_const_integrable.integrable_indicator
    (measurableSet_Icc.prod measurableSet_Icc)

private theorem contour_kernel_measurable :
    Measurable contourLogDistanceKernel := by
  unfold contourLogDistanceKernel
  apply Real.measurable_log.comp
  apply Measurable.norm
  apply Measurable.sub
  · exact ((continuous_ellipsePoint 1).comp continuous_fst).measurable
  · exact ((continuous_ellipsePoint 1).comp continuous_snd).measurable

private theorem contour_major_restrict_integrable :
    Integrable
      (fun p : ℝ × ℝ => (diagMajor ∘ subSwap) p +
        contourParameterSquare.indicator (fun _ : ℝ × ℝ => contourBound) p)
      ((volume.prod volume).restrict contourParameterSquare) := by
  have hg : Integrable
      (fun p : ℝ × ℝ => (diagMajor ∘ subSwap) p +
        contourParameterSquare.indicator (fun _ : ℝ × ℝ => contourBound) p)
      (volume.prod volume) :=
    diagMajor_subSwap_integrable.add contour_const_global_integrable
  exact hg.mono_measure Measure.restrict_le_self

theorem contourLogDistanceKernel_integrable :
    Integrable contourLogDistanceKernel
      ((volume.prod volume).restrict contourParameterSquare) := by
  apply contour_major_restrict_integrable.mono'
  · exact contour_kernel_measurable.aestronglyMeasurable.mono_measure
      Measure.restrict_le_self
  have hsq : MeasurableSet contourParameterSquare := by
    unfold contourParameterSquare
    exact measurableSet_Icc.prod measurableSet_Icc
  filter_upwards [ae_restrict_mem hsq] with p hp
  have hbound := contour_kernel_abs_bound p.1 p.2
  have hu : p.1 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := hp.1
  have hv : p.2 ∈ Set.Icc (0 : ℝ) (2 * Real.pi) := hp.2
  have hpi : 0 < 2 * Real.pi := Real.two_pi_pos
  have hd : p.1 - p.2 ∈ diagWindow := by
    rw [diagWindow]
    constructor
    · linarith [hu.1, hv.2]
    · linarith [hu.2, hv.1]
  have hprod : subSwap p ∈
      (Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ diagWindow) := by
    exact ⟨hv, hd⟩
  have hdiag : diagMajor (subSwap p) = diagAbs (p.1 - p.2) := by
    unfold diagMajor
    rw [Set.indicator_of_mem hprod]
    rfl
  have hconst : contourParameterSquare.indicator
      (fun _ : ℝ × ℝ => contourBound) p = contourBound := by
    simp [Set.indicator_of_mem, hp]
  change ‖contourLogDistanceKernel p‖ ≤
      diagMajor (subSwap p) +
        contourParameterSquare.indicator (fun _ : ℝ × ℝ => contourBound) p
  rw [Real.norm_eq_abs, hdiag, hconst]
  exact hbound

private theorem ellipse_eq_of_eq {u v : ℝ}
    (h : Li2Lean.p0EllipsePoint 1 u = Li2Lean.p0EllipsePoint 1 v) :
    circleZeta u = circleZeta v := by
  have hf := ellipse_difference_factorization u v
  have hz : (contourScale : ℂ) * (phase u - phase v) *
      (1 - (contourRatio : ℂ) / (phase u * phase v)) = 0 := by
    rw [← hf, sub_eq_zero.mpr h]
  have hc : (contourScale : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt contourScale_pos)
  have hcorr : 1 - (contourRatio : ℂ) / (phase u * phase v) ≠ 0 :=
    correction_ne_zero u v
  have hphase : phase u - phase v = 0 := by
    rcases mul_eq_zero.mp hz with hcd | hcorr'
    · exact (mul_eq_zero.mp hcd).resolve_left hc
    · exact False.elim (hcorr hcorr')
  have hp : phase u = phase v := sub_eq_zero.mp hphase
  simpa [phase, circleZeta, mul_comm] using hp

theorem contourPointCollisionSet_subset_phase :
    contourPointCollisionSet ⊆
      {p : ℝ × ℝ | circleZeta p.1 = circleZeta p.2} := by
  intro p hp
  exact ellipse_eq_of_eq hp

theorem contourPointCollisionSet_measurable :
    MeasurableSet contourPointCollisionSet := by
  unfold contourPointCollisionSet
  exact measurableSet_eq_fun
    ((continuous_ellipsePoint 1).comp continuous_fst).measurable
    ((continuous_ellipsePoint 1).comp continuous_snd).measurable

theorem contourParameterSquare_measurable :
    MeasurableSet contourParameterSquare := by
  exact (measurableSet_Icc.prod measurableSet_Icc)

theorem contour_collision_measure_zero :
    (volume.prod volume)
      (contourPointCollisionSet ∩ contourParameterSquare) = 0 := by
  let phaseSet : Set (ℝ × ℝ) := {p : ℝ × ℝ | circleZeta p.1 = circleZeta p.2}
  have hphase_zero : (volume.prod volume) phaseSet = 0 := by
    apply Measure.measure_prod_null_of_ae_null
      (measurableSet_eq_fun
        ((continuous_circleZeta.comp continuous_fst)).measurable
        ((continuous_circleZeta.comp continuous_snd)).measurable)
    filter_upwards with u
    change volume {v : ℝ | circleZeta u = circleZeta v} = 0
    have hs : {v : ℝ | circleZeta u = circleZeta v} =
        {v : ℝ | circleZeta v = circleZeta u} := by
      ext v
      exact eq_comm
    rw [hs]
    exact collision_set_measure_zero u
  apply measure_mono_null
  · intro p hp
    exact contourPointCollisionSet_subset_phase hp.1
  · simpa [phaseSet] using hphase_zero

end

end Li2Lean.P0.ConfigContourProduct
