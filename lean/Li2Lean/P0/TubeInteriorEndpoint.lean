/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorSweep
import Li2Lean.P0.TubeInteriorFactorization

open MeasureTheory ProbabilityTheory
open scoped NNReal

namespace Li2Lean.P0.TubeInterior

noncomputable section

theorem ellipseLevel_eq_zero_of_mem_Gamma {z : ℂ} (hz : z ∈ Gamma) :
    ellipseLevel z = 0 := by
  obtain ⟨u, rfl⟩ := hz
  exact ellipseLevel_gammaPoint u

theorem interiorPreimage_norm_cases_of_mem_Gamma {z : ℂ} (hz : z ∈ Gamma) :
    ‖interiorPreimage z‖ = 1 ∨ ‖interiorPreimage z‖ = annulusRatio := by
  let w : ℂ := interiorPreimage z
  change ‖w‖ = 1 ∨ ‖w‖ = annulusRatio
  have hw : w ≠ 0 := interiorPreimage_ne_zero z
  have hlevel : ellipseLevel (joukowski w) = 0 := by
    rw [joukowski_interiorPreimage]
    exact ellipseLevel_eq_zero_of_mem_Gamma hz
  have hfact := ellipseLevel_joukowski_factorization w hw
  have hprod : (1 - Complex.normSq w) *
      (coeffC ^ 2 * Complex.normSq w - coeffD ^ 2) = 0 := by
    have hzero : ((1 - Complex.normSq w) *
        (coeffC ^ 2 * Complex.normSq w - coeffD ^ 2)) *
        (w.re ^ 2 / semiMajor ^ 2 + w.im ^ 2 / semiMinor ^ 2) = 0 := by
      rw [← hfact, hlevel]
      ring
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (ellipse_weight_pos hw))
  rcases mul_eq_zero.mp hprod with hleft | hright
  · left
    rw [Complex.normSq_eq_norm_sq] at hleft
    nlinarith [norm_nonneg w]
  · right
    rw [coeffD_eq_ratio_mul_coeffC] at hright
    rw [Complex.normSq_eq_norm_sq] at hright
    have hc : 0 < coeffC ^ 2 := sq_pos_of_pos coeffC_pos
    have hr : 0 < annulusRatio := annulusRatio_pos
    have hsquare : ‖w‖ ^ 2 = annulusRatio ^ 2 := by
      nlinarith [hright]
    nlinarith [hsquare, norm_nonneg w]

theorem interiorSweep_eq_dirac_of_stripScale_zero {z : ℂ}
    (hscale : stripScale z = 0) :
    interiorSweep z = Measure.dirac (stripBoundaryPoint (stripLocation z)) := by
  unfold interiorSweep
  simp [hscale, ProbabilityTheory.cauchyMeasure_zero_scale]

theorem stripBoundaryPoint_stripLocation_of_mem_Gamma {z : ℂ}
    (hz : z ∈ Gamma) :
    stripBoundaryPoint (stripLocation z) = z := by
  let w : ℂ := interiorPreimage z
  have hw : w ≠ 0 := interiorPreimage_ne_zero z
  have hwj : joukowski w = z := by
    exact joukowski_interiorPreimage z
  have hcases := interiorPreimage_norm_cases_of_mem_Gamma hz
  rcases hcases with hunit | hinner
  · have hdepth : preimageDepth z = 0 := by
      unfold preimageDepth
      rw [show interiorPreimage z = w from rfl, hunit, Real.log_one]
      norm_num
    have hangle : stripAngle z = 0 := by
      unfold stripAngle
      rw [hdepth]
      ring
    have hscale : stripScale z = 0 := by
      unfold stripScale
      rw [hangle, Real.sin_zero, mul_zero, Real.toNNReal_zero]
    have hloc : stripLocation z =
        Real.exp (Real.pi * w.arg / annulusWidth) := by
      unfold stripLocation
      rw [hangle, Real.cos_zero, mul_one]
    have hlocpos : 0 < stripLocation z := by
      rw [hloc]
      exact Real.exp_pos _
    have hlogloc : Real.log |stripLocation z| =
        Real.pi * w.arg / annulusWidth := by
      rw [abs_of_pos hlocpos, hloc, Real.log_exp]
    have hargmap : w = Complex.exp (Complex.I * (w.arg : ℂ)) := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rw [hunit] at h
      simpa only [Complex.ofReal_one, one_mul, mul_comm] using h.symm
    have hlogloc' : Real.log (stripLocation z) =
        Real.pi * w.arg / annulusWidth := by
      simpa only [abs_of_pos hlocpos] using hlogloc
    have hpoint : stripBoundaryPoint (stripLocation z) =
        gammaPoint w.arg := by
      unfold stripBoundaryPoint
      rw [if_pos hlocpos.le, abs_of_pos hlocpos, hlogloc']
      congr 1
      field_simp [Real.pi_ne_zero, annulusWidth_pos.ne']
    calc
      stripBoundaryPoint (stripLocation z) = gammaPoint w.arg := hpoint
      _ = joukowski (Complex.exp (Complex.I * (w.arg : ℂ))) :=
        (joukowski_unit_circle_eq_gammaPoint w.arg).symm
      _ = joukowski w := congrArg joukowski hargmap.symm
      _ = z := hwj
  · have hdepth : preimageDepth z = annulusWidth := by
      unfold preimageDepth
      rw [show interiorPreimage z = w from rfl, hinner]
      unfold annulusWidth
      ring
    have hangle : stripAngle z = Real.pi := by
      unfold stripAngle
      rw [hdepth]
      field_simp [annulusWidth_pos.ne']
    have hscale : stripScale z = 0 := by
      unfold stripScale
      rw [hangle, Real.sin_pi, mul_zero, Real.toNNReal_zero]
    have hloc : stripLocation z =
        -Real.exp (Real.pi * w.arg / annulusWidth) := by
      unfold stripLocation
      rw [hangle, Real.cos_pi]
      ring
    have hlocneg : stripLocation z < 0 := by
      rw [hloc]
      exact neg_lt_zero.mpr (Real.exp_pos _)
    have hlogloc : Real.log |stripLocation z| =
        Real.pi * w.arg / annulusWidth := by
      rw [abs_of_neg hlocneg, hloc, neg_neg, Real.log_exp]
    have hlogloc' : Real.log (-stripLocation z) =
        Real.pi * w.arg / annulusWidth := by
      simpa only [abs_of_neg hlocneg] using hlogloc
    have hargmap : w = (annulusRatio : ℂ) *
        Complex.exp (Complex.I * (w.arg : ℂ)) := by
      have h := Complex.norm_mul_exp_arg_mul_I w
      rw [hinner] at h
      simpa only [Complex.ofReal_mul, mul_assoc, Complex.ofReal_one, one_mul,
        mul_comm] using h.symm
    have hpoint : stripBoundaryPoint (stripLocation z) =
        gammaPoint (-w.arg) := by
      unfold stripBoundaryPoint
      rw [if_neg (not_le_of_gt hlocneg), abs_of_neg hlocneg, hlogloc']
      congr 1
      field_simp [Real.pi_ne_zero, annulusWidth_pos.ne']
    calc
      stripBoundaryPoint (stripLocation z) = gammaPoint (-w.arg) := hpoint
      _ = joukowski ((annulusRatio : ℂ) *
          Complex.exp (Complex.I * (w.arg : ℂ))) :=
        (joukowski_inner_circle_eq_gammaPoint w.arg).symm
      _ = joukowski w := congrArg joukowski hargmap.symm
      _ = z := hwj

theorem interiorSweep_eq_dirac_of_mem_Gamma {z : ℂ} (hz : z ∈ Gamma) :
    interiorSweep z = Measure.dirac z := by
  have hscale : stripScale z = 0 := by
    rcases interiorPreimage_norm_cases_of_mem_Gamma hz with hunit | hinner
    · unfold stripScale
      have hdepth : preimageDepth z = 0 := by
        unfold preimageDepth
        rw [hunit, Real.log_one]
        norm_num
      have hangle : stripAngle z = 0 := by
        unfold stripAngle
        rw [hdepth]
        ring
      rw [hangle, Real.sin_zero, mul_zero, Real.toNNReal_zero]
    · unfold stripScale
      have hdepth : preimageDepth z = annulusWidth := by
        unfold preimageDepth
        rw [hinner]
        unfold annulusWidth
        ring
      have hangle : stripAngle z = Real.pi := by
        unfold stripAngle
        rw [hdepth]
        field_simp [annulusWidth_pos.ne']
      rw [hangle, Real.sin_pi, mul_zero, Real.toNNReal_zero]
  calc
    interiorSweep z = Measure.dirac (stripBoundaryPoint (stripLocation z)) :=
      interiorSweep_eq_dirac_of_stripScale_zero hscale
    _ = Measure.dirac z := congrArg Measure.dirac
      (stripBoundaryPoint_stripLocation_of_mem_Gamma hz)


end
end Li2Lean.P0.TubeInterior
