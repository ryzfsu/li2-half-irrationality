/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourAnalytic
import Li2Lean.P0.ConfigFejerLog
import Li2Lean.DiagonalLogClassicalProbe
import Mathlib.Analysis.SpecialFunctions.Integrability.Log
import Mathlib.MeasureTheory.Topology

open MeasureTheory Filter Set
open scoped BigOperators Topology Interval

namespace Li2Lean.P0.ConfigContourAbelPOC

noncomputable section

open ConfigContourAnalytic ConfigContourKernel ConfigContourReference ConfigFejerLog

theorem circleZeta_eq_phase (u : ℝ) :
    circleZeta u = phase u := by
  unfold circleZeta phase
  congr 1
  ring

theorem phase_sub (u v : ℝ) :
    phase (u - v) = phase (-v) * phase u := by
  unfold phase
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_neg_conj (u : ℝ) :
    phase (-u) = (starRingEnd ℂ) (phase u) := by
  unfold phase
  rw [← Complex.exp_conj]
  congr 1
  simp

theorem circleZeta_norm (u : ℝ) : ‖circleZeta u‖ = 1 := by
  simp [circleZeta, Complex.norm_exp]

theorem circleZeta_sub_norm_eq (u v : ℝ) :
    ‖circleZeta u - circleZeta v‖ =
      ‖1 - circleZeta (-(u - v))‖ := by
  have hmul : circleZeta u * circleZeta (-(u - v)) = circleZeta v := by
    rw [circleZeta_mul]
    congr 1
    ring
  have hfactor : circleZeta u * (1 - circleZeta (-(u - v))) =
      circleZeta u - circleZeta v := by
    rw [mul_sub, mul_one, hmul]
  calc
    ‖circleZeta u - circleZeta v‖ =
        ‖circleZeta u * (1 - circleZeta (-(u - v)))‖ := by
      rw [hfactor]
    _ = ‖1 - circleZeta (-(u - v))‖ := by
      rw [norm_mul, circleZeta_norm, one_mul]

theorem radial_norm_sq_identity {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(1 : ℂ) - (r : ℂ) * z‖ ^ 2 =
      (1 - r) ^ 2 + r * ‖(1 : ℂ) - z‖ ^ 2 := by
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_sub]
  have hzsq : z.re ^ 2 + z.im ^ 2 = 1 := by
    have hz' : ‖z‖ ^ 2 = (1 : ℝ) := by rw [hz]; norm_num
    rw [← Complex.normSq_eq_norm_sq] at hz'
    simpa [Complex.normSq_apply, pow_two] using hz'
  rw [← Complex.normSq_eq_norm_sq (1 - z), Complex.normSq_sub]
  simp [Complex.normSq_apply, Complex.mul_re, Complex.mul_im]
  nlinarith

theorem radial_norm_upper {r : ℝ} (hr : 0 ≤ r) (hr1 : r ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(1 : ℂ) - (r : ℂ) * z‖ ≤ 2 := by
  have h := norm_sub_le (1 : ℂ) ((r : ℂ) * z)
  rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg hr, hz, mul_one] at h
  linarith

theorem radial_norm_lower_half {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r ≤ 1)
    (z : ℂ) (hz : ‖z‖ = 1) :
    ‖(1 : ℂ) - (r : ℂ) * z‖ ≥ ‖(1 : ℂ) - z‖ / 2 := by
  have hr0 : 0 ≤ r := by linarith
  have hsq : (‖(1 : ℂ) - z‖ / 2) ^ 2 ≤
      ‖(1 : ℂ) - (r : ℂ) * z‖ ^ 2 := by
    rw [radial_norm_sq_identity hr0 hr1 z hz]
    nlinarith [sq_nonneg (1 - r), sq_nonneg ‖(1 - z : ℂ)‖]
  exact le_of_sq_le_sq hsq (norm_nonneg _)

theorem diagonalAbelKernel_abs_le {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    {u v : ℝ} (hneq : circleZeta u ≠ circleZeta v) :
    |diagonalAbelKernel r u v| ≤
      |diagonalLogKernel u v| + Real.log 2 := by
  let z : ℂ := circleZeta (-(u - v))
  let x : ℝ := ‖(1 : ℂ) - z‖
  let y : ℝ := ‖(1 : ℂ) - (r : ℂ) * z‖
  have hz : ‖z‖ = 1 := by
    dsimp [z]
    exact circleZeta_norm _
  have hx : 0 < x := by
    dsimp [x, z]
    rw [← circleZeta_sub_norm_eq]
    exact norm_pos_iff.mpr (sub_ne_zero.mpr hneq)
  have hynz : (1 : ℂ) - (r : ℂ) * z ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg hr0, hz, mul_one] at hn
    linarith
  have hy : 0 < y := by
    dsimp [y]
    exact norm_pos_iff.mpr hynz
  have hyupper : y ≤ 2 := by
    dsimp [y]
    exact radial_norm_upper hr0 hr1.le z hz
  have hlogupper : Real.log y ≤ Real.log 2 :=
    Real.log_le_log hy hyupper
  have hlogx : Real.log x = diagonalLogKernel u v := by
    change Real.log ‖1 - circleZeta (-(u - v))‖ =
      Real.log ‖circleZeta u - circleZeta v‖
    rw [circleZeta_sub_norm_eq]
  have hlow : -(abs (Real.log x) + Real.log 2) ≤ Real.log y := by
    by_cases hrs : r ≤ 1 / 2
    · have hylow : (1 / 2 : ℝ) ≤ y := by
        dsimp [y]
        have h := norm_sub_norm_le (1 : ℂ) ((r : ℂ) * z)
        rw [norm_one, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg hr0, hz, mul_one] at h
        linarith
      have hloghalf : Real.log (1 / 2 : ℝ) ≤ Real.log y :=
        Real.log_le_log (by norm_num) hylow
      have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
      rw [hhalf] at hloghalf
      have habs : 0 ≤ |Real.log x| := abs_nonneg _
      linarith
    · have hrs' : 1 / 2 ≤ r := le_of_not_ge hrs
      have hylow : x / 2 ≤ y := by
        dsimp [x, y]
        exact radial_norm_lower_half hrs' hr1.le z hz
      have hloglow : Real.log (x / 2) ≤ Real.log y :=
        Real.log_le_log (div_pos hx (by norm_num)) hylow
      rw [Real.log_div (ne_of_gt hx) (by norm_num)] at hloglow
      have hneg : -|Real.log x| ≤ Real.log x := neg_abs_le _
      linarith
  have habs : |Real.log y| ≤ |Real.log x| + Real.log 2 := by
    rw [abs_le]
    constructor <;> linarith [hlogupper, hlow, abs_nonneg (Real.log x)]
  calc
    |diagonalAbelKernel r u v| = |Real.log y| := by
      rfl
    _ ≤ |Real.log x| + Real.log 2 := habs
    _ = |diagonalLogKernel u v| + Real.log 2 := by rw [hlogx]

theorem diagonalAbelKernel_continuous {r : ℝ} (hr : ‖(r : ℂ)‖ < 1)
    (v : ℝ) :
    Continuous (fun u : ℝ => diagonalAbelKernel r u v) := by
  have hlog := ConfigFejerLog.continuous_log_norm (a := (r : ℂ)) hr
  have hcomp : Continuous (fun u : ℝ =>
      Real.log ‖1 - (r : ℂ) * phase (v - u)‖) :=
    hlog.comp (continuous_const.sub continuous_id)
  apply hcomp.congr
  intro u
  unfold diagonalAbelKernel
  rw [circleZeta_eq_phase]
  congr 3
  ring

theorem diagonalAbelKernel_intervalIntegrable {r : ℝ}
    (hr : ‖(r : ℂ)‖ < 1) (v : ℝ) :
    IntervalIntegrable (fun u : ℝ => diagonalAbelKernel r u v)
      volume (0 : ℝ) (2 * Real.pi) := by
  exact (diagonalAbelKernel_continuous hr v).intervalIntegrable _ _

theorem diagonalAbelKernel_tendsto {u v : ℝ}
    (hneq : circleZeta u ≠ circleZeta v) :
    Tendsto (fun r : ℝ => diagonalAbelKernel r u v)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (diagonalLogKernel u v)) := by
  have hdiff : ‖circleZeta u - circleZeta v‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (sub_ne_zero.mpr hneq)
  have hfac : ‖1 - circleZeta (-(u - v))‖ ≠ 0 := by
    rw [← circleZeta_sub_norm_eq]
    exact hdiff
  have hid : Tendsto (fun r : ℝ => r) (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (1 : ℝ)) := tendsto_id.mono_left nhdsWithin_le_nhds
  have hco : Tendsto (fun r : ℝ => (r : ℂ))
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (1 : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hid
  have hmul : Tendsto (fun r : ℝ => (r : ℂ) * circleZeta (-(u - v)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds ((1 : ℂ) * circleZeta (-(u - v)))) :=
    hco.mul tendsto_const_nhds
  have harg : Tendsto (fun r : ℝ =>
      (1 : ℂ) - (r : ℂ) * circleZeta (-(u - v)))
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds ((1 : ℂ) - (1 : ℂ) * circleZeta (-(u - v)))) :=
    tendsto_const_nhds.sub hmul
  have hnorm := continuous_norm.continuousAt.tendsto.comp harg
  have hlog := hnorm.log (by simpa using hfac)
  have htarget : diagonalLogKernel u v =
      Real.log ‖(1 : ℂ) - circleZeta (-(u - v))‖ := by
    unfold diagonalLogKernel
    simpa using congrArg Real.log (circleZeta_sub_norm_eq u v)
  rw [htarget]
  simpa [diagonalAbelKernel] using hlog

theorem contourDensity_diagonalAbel_integral {r : ℝ}
    (hr : ‖(r : ℂ)‖ < 1) (v : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * diagonalAbelKernel r u v) =
      -(2 * Real.pi) *
        contourLogPolynomial ((r : ℂ) * phase (-v)) := by
  have hparam : ‖((r : ℂ) * phase (-v))‖ < 1 := by
    simpa only [norm_mul, norm_phase, mul_one] using hr
  have hkernel (u : ℝ) : diagonalAbelKernel r u v =
      Real.log ‖1 - ((r : ℂ) * phase (-v)) * phase u‖ := by
    unfold diagonalAbelKernel
    rw [circleZeta_eq_phase, phase_neg_conj]
    have hconj :
        (1 : ℂ) - (r : ℂ) * (starRingEnd ℂ) (phase (u - v)) =
          (starRingEnd ℂ) ((1 : ℂ) - (r : ℂ) * phase (u - v)) := by
      simp
    rw [hconj, Complex.norm_conj, phase_sub]
    congr 3
    ring
  have hfun :
      (fun u : ℝ => contourDensity u * diagonalAbelKernel r u v) =
        (fun u : ℝ => contourDensity u *
          Real.log ‖1 - ((r : ℂ) * phase (-v)) * phase u‖) := by
    funext u
    rw [hkernel]
  rw [hfun]
  exact integral_contourDensity_log_norm hparam

private theorem collision_countable (v : ℝ) :
    ({u : ℝ | circleZeta u = circleZeta v}).Countable := by
  have hsub : {u : ℝ | circleZeta u = circleZeta v} ⊆
      (fun n : ℤ => v + (n : ℝ) * (2 * Real.pi)) '' (Set.univ : Set ℤ) := by
    intro u hu
    have hexp : Complex.exp (Complex.I * (u : ℂ)) =
        Complex.exp (Complex.I * (v : ℂ)) := hu
    obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
    have him := congrArg Complex.im hn
    have hu' : u = v + (n : ℝ) * (2 * Real.pi) := by
      simpa [Complex.mul_re, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im] using him
    exact ⟨n, by simp, hu'.symm⟩
  have himage :
      ((fun n : ℤ => v + (n : ℝ) * (2 * Real.pi)) '' (Set.univ : Set ℤ)).Countable := by
    simpa only [Set.image_univ] using
      Set.countable_range (fun n : ℤ => v + (n : ℝ) * (2 * Real.pi))
  exact himage.mono hsub

private theorem circleZeta_ne_ae (v : ℝ) :
    ∀ᵐ u ∂volume, circleZeta u ≠ circleZeta v := by
  have hc := collision_countable v
  simpa only [ae_iff, Classical.not_not] using hc.measure_zero volume

/-- Abel convergence against any continuous real weight.  The majorant is
obtained from the radial two-sided estimate, while the collision set is
removed only as a null set. -/
theorem diagonalAbel_weighted_limit (g : ℝ → ℝ) (hg : Continuous g) (v : ℝ) :
    Tendsto
      (fun r : ℝ => ∫ u in (0 : ℝ)..(2 * Real.pi),
        diagonalAbelKernel r u v * g u)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (∫ u in (0 : ℝ)..(2 * Real.pi),
        diagonalLogKernel u v * g u)) := by
  have hr_event : ∀ᶠ r : ℝ in nhdsWithin (1 : ℝ) (Set.Iio 1),
      0 ≤ r ∧ r < 1 := by
    filter_upwards [self_mem_nhdsWithin,
      mem_nhdsWithin_of_mem_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1))] with r hr hr0
    exact ⟨le_of_lt hr0, hr⟩
  apply intervalIntegral.tendsto_integral_filter_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (l := nhdsWithin (1 : ℝ) (Set.Iio 1))
    (F := fun r : ℝ => fun u : ℝ => diagonalAbelKernel r u v * g u)
    (f := fun u : ℝ => diagonalLogKernel u v * g u)
    (bound := fun u : ℝ => (|diagonalLogKernel u v| + Real.log 2) * |g u|)
  · filter_upwards [hr_event] with r ⟨hr0, hr1⟩
    have hrnorm : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    exact (((diagonalAbelKernel_continuous hrnorm v).mul hg).aestronglyMeasurable.restrict)
  · filter_upwards [hr_event] with r ⟨hr0, hr1⟩
    filter_upwards [circleZeta_ne_ae v] with u hu
    intro huI
    have hle := diagonalAbelKernel_abs_le hr0 hr1 hu
    rw [norm_mul, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right hle (abs_nonneg _)
  · have hdiag := DiagonalLogClassicalProbe.diagonalLogKernel_intervalIntegrable v
    have hdiag' : IntervalIntegrable
        (fun u : ℝ => |diagonalLogKernel u v|)
        volume (0 : ℝ) (2 * Real.pi) := by
      simpa only [Real.norm_eq_abs] using hdiag.norm
    have hbase : IntervalIntegrable
        (fun u : ℝ => |diagonalLogKernel u v| + Real.log 2)
        volume (0 : ℝ) (2 * Real.pi) := by
      exact hdiag'.add intervalIntegrable_const
    exact hbase.mul_continuousOn hg.abs.continuousOn
  · filter_upwards [circleZeta_ne_ae v] with u hu
    intro huI
    exact (diagonalAbelKernel_tendsto hu).mul tendsto_const_nhds

theorem cosine_limit_exchange (n : ℕ) (v : ℝ) :
    Tendsto (fun r : ℝ => diagonalAbelFourierCoefficient r n v)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (diagonalFourierCoefficient n v)) := by
    simpa [diagonalAbelFourierCoefficient, diagonalFourierCoefficient] using
    diagonalAbel_weighted_limit
      (fun u : ℝ => Real.cos ((n : ℝ) * u))
      (Real.continuous_cos.comp (continuous_const.mul continuous_id)) v

theorem sine_limit_exchange (n : ℕ) (v : ℝ) :
    Tendsto (fun r : ℝ => diagonalAbelSineCoefficient r n v)
      (nhdsWithin (1 : ℝ) (Set.Iio 1))
      (nhds (diagonalSineCoefficient n v)) := by
    simpa [diagonalAbelSineCoefficient, diagonalSineCoefficient] using
    diagonalAbel_weighted_limit
      (fun u : ℝ => Real.sin ((n : ℝ) * u))
      (Real.continuous_sin.comp (continuous_const.mul continuous_id)) v

theorem diagonalAbelCertificate : DiagonalAbelCertificate where
  abel_intervalIntegrable := by
    intro r hr0 hr1 v
    have hrnorm : ‖(r : ℂ)‖ < 1 := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hr0]
      exact hr1
    exact diagonalAbelKernel_intervalIntegrable hrnorm v
  pointwise_limit_away := fun u v => diagonalAbelKernel_tendsto
  cosine_limit_exchange := cosine_limit_exchange
  sine_limit_exchange := sine_limit_exchange

end

end Li2Lean.P0.ConfigContourAbelPOC
