/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorCover

open MeasureTheory Filter Metric MeromorphicOn
open scoped Topology

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- A logarithmic truncation with its genuine finite value at collisions. -/
def truncatedLogNorm (ε : ℝ) (v : ℂ) : ℝ := Real.log (max ε ‖v‖)

theorem continuous_truncatedLogNorm {ε : ℝ} (hε : 0 < ε) :
    Continuous (truncatedLogNorm ε) := by
  unfold truncatedLogNorm
  exact (continuous_const.max continuous_norm).log
    (fun v => ne_of_gt (lt_of_lt_of_le hε (le_max_left _ _)))

/-- Jensen's formula gives the lower mean inequality at a nonzero center. -/
theorem log_norm_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R : ℝ}
    (hR : 0 < R) (hf : AnalyticOnNhd ℂ f (closedBall c |R|)) (hfc : f c ≠ 0) :
    Real.log ‖f c‖ ≤ Real.circleAverage (fun u => Real.log ‖f u‖) c R := by
  rw [hf.circleAverage_log_norm hR.ne' hfc]
  apply le_add_of_nonneg_left
  apply finsum_nonneg
  intro u
  by_cases hu : u ∈ closedBall c |R|
  · by_cases huc : u = c
    · subst u
      rw [hf.divisor_apply (by simp), (hf c (by simp)).analyticOrderAt_eq_zero.mpr hfc]
      simp
    · apply mul_nonneg
      · exact_mod_cast hf.divisor_nonneg u
      · apply Real.log_nonneg
        have hnorm : 0 < ‖c - u‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (Ne.symm huc))
        rw [← div_eq_mul_inv, le_div_iff₀ hnorm, one_mul]
        simpa only [mem_closedBall, dist_eq_norm', abs_of_pos hR] using hu
  · simp [hu]

/-- Truncated Jensen remains valid when the center itself is a zero.
The nonzero-center branch removes only discrete circle zeros before comparing logs. -/
theorem truncatedLogNorm_le_circleAverage {f : ℂ → ℂ} {c : ℂ} {R ε : ℝ}
    (hR : 0 < R) (hε : 0 < ε)
    (hf : AnalyticOnNhd ℂ f (closedBall c |R|)) :
    truncatedLogNorm ε (f c) ≤
      Real.circleAverage (fun u => truncatedLogNorm ε (f u)) c R := by
  have hci : CircleIntegrable (fun u => truncatedLogNorm ε (f u)) c R :=
    ((continuous_truncatedLogNorm hε).comp_continuousOn
      (hf.continuousOn.mono sphere_subset_closedBall)).circleIntegrable'
  have hconst : Real.log ε ≤
      Real.circleAverage (fun u => truncatedLogNorm ε (f u)) c R := by
    rw [← Real.circleAverage_const (Real.log ε) c R]
    apply Real.circleAverage_mono (circleIntegrable_const _ _ _) hci
    intro u _
    exact Real.log_le_log hε (le_max_left _ _)
  by_cases hsmall : ‖f c‖ ≤ ε
  · simpa only [truncatedLogNorm, max_eq_left hsmall] using hconst
  · have hnorm : 0 < ‖f c‖ := hε.trans (lt_of_not_ge hsmall)
    have hfc : f c ≠ 0 := norm_pos_iff.mp hnorm
    have hnonzero : ∀ᶠ u in codiscreteWithin (closedBall c |R|), f u ≠ 0 := by
      apply (hf.eqOn_zero_or_eventually_ne_zero_of_preconnected
        (convex_closedBall c |R|).isPreconnected).resolve_left
      intro heq
      exact hfc (heq (by simp))
    have hnonzero' := codiscreteWithin_mono sphere_subset_closedBall hnonzero
    let g : ℂ → ℝ := fun u => if f u = 0 then Real.log ε else Real.log ‖f u‖
    have hgeq : (fun u => Real.log ‖f u‖) =ᶠ[codiscreteWithin (sphere c |R|)] g := by
      filter_upwards [hnonzero'] with u hu
      simp only [g, if_neg hu]
    have hgi : CircleIntegrable g c R :=
      CircleIntegrable.congr_codiscreteWithin hgeq
        ((hf.mono sphere_subset_closedBall).meromorphicOn.circleIntegrable_log_norm)
    calc
      truncatedLogNorm ε (f c) = Real.log ‖f c‖ := by
        simp only [truncatedLogNorm, max_eq_right (le_of_not_ge hsmall)]
      _ ≤ Real.circleAverage (fun u => Real.log ‖f u‖) c R :=
        log_norm_le_circleAverage hR hf hfc
      _ = Real.circleAverage g c R :=
        Real.circleAverage_congr_codiscreteWithin hgeq hR.ne'
      _ ≤ Real.circleAverage (fun u => truncatedLogNorm ε (f u)) c R := by
        apply Real.circleAverage_mono hgi hci
        intro u _
        by_cases hu : f u = 0
        · simp only [g, if_pos hu]
          exact Real.log_le_log hε (le_max_left _ _)
        · simp only [g, if_neg hu]
          exact Real.log_le_log (norm_pos_iff.mpr hu) (le_max_right _ _)

/-- The fixed actual lift is analytic on each smaller closed disk. -/
theorem analyticOnNhd_interiorDiskMap_closedBall {z : ℂ} (hz : z ∈ ellipseInterior)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    AnalyticOnNhd ℂ (interiorDiskMap z) (closedBall 0 |R|) := by
  apply (analyticOnNhd_interiorDiskMap hz).mono
  intro u hu
  simp only [mem_closedBall, dist_zero_right, abs_of_nonneg hR] at hu
  exact mem_ball_zero_iff.mpr (hu.trans_lt hR1)

/-- The complex mean on every smaller circle is the original source point. -/
theorem circleAverage_interiorDiskMap {z : ℂ} (hz : z ∈ ellipseInterior)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    Real.circleAverage (interiorDiskMap z) 0 R = z := by
  have ha := analyticOnNhd_interiorDiskMap_closedBall hz hR hR1
  rw [circleAverage_of_differentiable_on_off_countable (s := (∅ : Set ℂ))
    Set.countable_empty ha.continuousOn
    (fun u hu => (ha u (ball_subset_closedBall hu.1)).differentiableAt),
    interiorDiskMap_zero hz]

/-- A uniform genuine truncated logarithmic Jensen bound for all source points. -/
theorem truncatedLogNorm_interiorDiskMap {z x : ℂ} (hz : z ∈ ellipseInterior)
    {R ε : ℝ} (hR : 0 < R) (hR1 : R < 1) (hε : 0 < ε) :
    truncatedLogNorm ε (z - x) ≤
      Real.circleAverage (fun u => truncatedLogNorm ε (interiorDiskMap z u - x)) 0 R := by
  have ha := (analyticOnNhd_interiorDiskMap_closedBall hz hR.le hR1).sub
    (analyticOnNhd_const (v := x))
  simpa only [Pi.sub_apply, interiorDiskMap_zero hz] using truncatedLogNorm_le_circleAverage hR hε ha

/-- The finite-radius log mean is exact for every source outside the full interior. -/
theorem log_norm_circleAverage_interiorDiskMap_of_notMem {z x : ℂ}
    (hz : z ∈ ellipseInterior) (hx : x ∉ ellipseInterior)
    {R : ℝ} (hR : 0 ≤ R) (hR1 : R < 1) :
    Real.circleAverage (fun u => Real.log ‖interiorDiskMap z u - x‖) 0 R =
      Real.log ‖z - x‖ := by
  have ha := (analyticOnNhd_interiorDiskMap_closedBall hz hR hR1).sub
    (analyticOnNhd_const (v := x))
  change AnalyticOnNhd ℂ (fun u => interiorDiskMap z u - x) (closedBall 0 |R|) at ha
  have hno : ∀ u ∈ closedBall 0 |R|, interiorDiskMap z u - x ≠ 0 := by
    intro u hu
    have hu' : ‖u‖ < 1 := by
      have h := hu
      simp only [mem_closedBall, dist_zero_right, abs_of_nonneg hR] at h
      exact h.trans_lt hR1
    intro heq
    exact hx (sub_eq_zero.mp heq ▸ interiorDiskMap_mem_interior hz hu')
  simpa only [interiorDiskMap_zero hz] using ha.circleAverage_log_norm_of_ne_zero hno

end
end Li2Lean.P0.TubeInterior
