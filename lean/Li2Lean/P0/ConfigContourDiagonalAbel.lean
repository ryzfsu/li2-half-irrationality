/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourAnalytic
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.SpecialFunctions.Integrability.Log

open MeasureTheory
open scoped Interval
open Filter

namespace Li2Lean.P0.ConfigContourDiagonalAbel

noncomputable section

open Li2Lean.P0.ConfigContourAnalytic

/-! The collision locus of the circle parameterization is countable.  This is
the measure-zero input needed when the pointwise Abel limit is passed through
an interval integral. -/

theorem collision_subset_affine (v : ℝ) :
    {u : ℝ | circleZeta u = circleZeta v} ⊆
      (fun n : ℤ => v + (n : ℝ) * (2 * Real.pi)) '' (Set.univ : Set ℤ) := by
  intro u hu
  have hexp : Complex.exp (Complex.I * (u : ℂ)) =
      Complex.exp (Complex.I * (v : ℂ)) := hu
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  refine ⟨n, Set.mem_univ _, ?_⟩
  have him := congrArg Complex.im hn
  dsimp at him
  norm_num at him
  simpa [mul_add, add_mul, sub_eq_add_neg, mul_assoc] using him.symm

theorem collision_set_measure_zero (v : ℝ) :
    volume {u : ℝ | circleZeta u = circleZeta v} = 0 := by
  apply measure_mono_null (collision_subset_affine v)
  apply Set.Countable.measure_zero
  simpa [Set.image_univ] using
    (Set.countable_range (fun n : ℤ => v + (n : ℝ) * (2 * Real.pi)))

theorem diagonalLogKernel_eq_log_two_sin (u v : ℝ) :
    diagonalLogKernel u v =
      Real.log ‖(2 : ℝ) * Real.sin ((u - v) / 2)‖ := by
  have hfac : circleZeta u - circleZeta v =
      circleZeta v * (circleZeta (u - v) - 1) := by
    calc
      circleZeta u - circleZeta v =
          circleZeta (v + (u - v)) - circleZeta v := by
            congr 1
            ring
      _ = circleZeta v * circleZeta (u - v) - circleZeta v := by
            rw [circleZeta_mul]
      _ = circleZeta v * (circleZeta (u - v) - 1) := by ring
  rw [diagonalLogKernel, hfac, norm_mul]
  have hvnorm : ‖circleZeta v‖ = 1 := by
    simp [circleZeta, Complex.norm_exp]
  rw [hvnorm, one_mul]
  rw [show circleZeta (u - v) =
      Complex.exp (Complex.I * ((u - v : ℝ) : ℂ)) by rfl]
  rw [Complex.norm_exp_I_mul_ofReal_sub_one]

/-- The diagonal chord logarithm is integrable despite its collision point. -/
theorem diagonalLogKernel_intervalIntegrable (v : ℝ) :
    IntervalIntegrable (fun u => diagonalLogKernel u v) volume 0 (2 * Real.pi) := by
  have hcast : AnalyticOnNhd ℝ (fun u : ℝ => (u : ℂ)) Set.univ := by
    exact Complex.ofRealCLM.analyticOnNhd _
  have hlin : AnalyticOnNhd ℝ (fun u : ℝ => (Complex.I : ℂ) * (u : ℂ)) Set.univ := by
    exact analyticOnNhd_const.mul hcast
  have hexp : AnalyticOnNhd ℝ (fun u : ℝ => Complex.exp
      ((Complex.I : ℂ) * (u : ℂ))) Set.univ := by
    exact analyticOnNhd_cexp.restrictScalars.comp hlin
      (Set.mapsTo_univ _ _)
  have ha : AnalyticOnNhd ℝ (fun u : ℝ => circleZeta u - circleZeta v) Set.univ := by
    change AnalyticOnNhd ℝ
      ((fun u : ℝ => Complex.exp (Complex.I * (u : ℂ))) -
        (fun _ : ℝ => Complex.exp (Complex.I * (v : ℂ)))) Set.univ
    exact hexp.sub analyticOnNhd_const
  have hm : MeromorphicOn (fun u : ℝ => circleZeta u - circleZeta v)
      [[(0 : ℝ), 2 * Real.pi]] := by
    intro u hu
    exact (ha u (Set.mem_univ _)).meromorphicAt
  have hi := hm.intervalIntegrable_log_norm
  simpa [diagonalLogKernel, circleZeta] using hi

/-- The regularized logarithm has no zero inside the disk. -/
theorem diagonalAbel_nonzero {r u v : ℝ} (hr : |r| < 1) :
    1 - (r : ℂ) * circleZeta (-(u - v)) ≠ 0 := by
  intro h
  have hmul : (r : ℂ) * circleZeta (-(u - v)) = 1 := (sub_eq_zero.mp h).symm
  have hz : ‖circleZeta (-(u - v))‖ = 1 := by
    simp [circleZeta, Complex.norm_exp]
  have hnorm := congrArg norm hmul
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, hz, mul_one] at hnorm
  have hrabs : |r| = 1 := by simpa using hnorm
  linarith

/-- The Abel kernel is continuous and hence integrable for every subunit radius. -/
theorem diagonalAbelKernel_intervalIntegrable {r : ℝ} (hr : |r| < 1) (v : ℝ) :
    IntervalIntegrable (fun u => diagonalAbelKernel r u v) volume 0 (2 * Real.pi) := by
  have hc : Continuous (fun u : ℝ =>
      (1 : ℂ) - (r : ℂ) * circleZeta (-(u - v))) := by
    unfold circleZeta
    fun_prop
  have hn (u : ℝ) :
      (1 : ℂ) - (r : ℂ) * circleZeta (-(u - v)) ≠ 0 := diagonalAbel_nonzero hr
  have hlog : Continuous (fun u : ℝ =>
      Real.log ‖(1 : ℂ) - (r : ℂ) * circleZeta (-(u - v))‖) := by
    exact (continuous_norm.comp hc).log (fun u => norm_ne_zero_iff.mpr (hn u))
  exact (hlog.congr fun u => by rfl).intervalIntegrable _ _

/-- A distinct pair of circle phases makes the limiting Abel factor nonzero. -/
theorem diagonalAbel_limit_factor_ne {u v : ℝ}
    (hphase : circleZeta u ≠ circleZeta v) :
    1 - circleZeta (-(u - v)) ≠ 0 := by
  intro h
  have hz : circleZeta (-(u - v)) = (circleZeta u)⁻¹ * circleZeta v := by
    calc
      circleZeta (-(u - v)) = Complex.exp
          (-((Complex.I : ℂ) * (u : ℂ)) + (Complex.I : ℂ) * (v : ℂ)) := by
        dsimp [circleZeta]
        congr 1
        push_cast
        ring
      _ = Complex.exp (-((Complex.I : ℂ) * (u : ℂ))) *
          Complex.exp ((Complex.I : ℂ) * (v : ℂ)) := Complex.exp_add _ _
      _ = (circleZeta u)⁻¹ * circleZeta v := by
        simp [circleZeta, Complex.exp_neg]
  rw [hz] at h
  have h' : (circleZeta u)⁻¹ * circleZeta v = 1 := (sub_eq_zero.mp h).symm
  have hphaseEq : circleZeta u = circleZeta v := by
    calc
      circleZeta u = circleZeta u * 1 := (mul_one _).symm
      _ = circleZeta u * ((circleZeta u)⁻¹ * circleZeta v) := by rw [h']
      _ = circleZeta v := by simp [mul_assoc, circleZeta_ne_zero]
  exact hphase hphaseEq

/-- Off the diagonal, the Abel kernel converges to the logarithmic kernel. -/
theorem diagonalAbelKernel_tendsto {u v : ℝ}
    (hphase : circleZeta u ≠ circleZeta v) :
    Tendsto (fun r : ℝ => diagonalAbelKernel r u v)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (diagonalLogKernel u v)) := by
  let z := circleZeta (-(u - v))
  have hz : 1 - z ≠ 0 := by simpa [z] using diagonalAbel_limit_factor_ne hphase
  have hlim : Tendsto (fun r : ℝ => (1 : ℂ) - (r : ℂ) * z)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (1 - z)) := by
    have hcast : Tendsto (fun r : ℝ => (r : ℂ))
        (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds (1 : ℂ)) :=
      Complex.continuous_ofReal.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
    simpa using tendsto_const_nhds.sub (hcast.mul tendsto_const_nhds)
  have hnorm : Tendsto (fun r : ℝ => ‖(1 : ℂ) - (r : ℂ) * z‖)
      (nhdsWithin (1 : ℝ) (Set.Iio 1)) (nhds ‖1 - z‖) :=
    (continuous_norm.continuousAt.tendsto.comp hlim)
  have hpos : 0 < ‖1 - z‖ := norm_pos_iff.mpr hz
  have hlog := (Real.continuousAt_log hpos.ne').tendsto.comp hnorm
  have htarget : diagonalLogKernel u v = Real.log ‖1 - z‖ := by
    have hprod : circleZeta u * z = circleZeta v := by
      dsimp [z, circleZeta]
      rw [← Complex.exp_add]
      congr 1
      push_cast
      ring
    have hfac : circleZeta u - circleZeta v = circleZeta u * (1 - z) := by
      rw [← hprod]
      ring
    rw [diagonalLogKernel, hfac, norm_mul]
    have hunit : ‖circleZeta u‖ = 1 := by simp [circleZeta, Complex.norm_exp]
    rw [hunit, one_mul]
  simpa [Function.comp_def, diagonalAbelKernel, z, htarget] using hlog

/-! The analytic part of the certificate is now discharged.  The only inputs
left for a full certificate are the two coefficient-level limit exchanges;
keeping those as arguments prevents an unproved integral/sum interchange from
being hidden in the contour identity. -/

theorem diagonalAbelCertificate_of_coefficient_exchanges
    (hcos : ∀ n : ℕ, ∀ v : ℝ,
      Tendsto (fun r : ℝ => diagonalAbelFourierCoefficient r n v)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (diagonalFourierCoefficient n v)))
    (hsin : ∀ n : ℕ, ∀ v : ℝ,
      Tendsto (fun r : ℝ => diagonalAbelSineCoefficient r n v)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (diagonalSineCoefficient n v))) :
    DiagonalAbelCertificate := by
  refine ⟨?_, ?_, hcos, hsin⟩
  · intro r hr0 hr1 v
    apply diagonalAbelKernel_intervalIntegrable
    simpa [abs_of_nonneg hr0] using hr1
  · intro u v hphase
    exact diagonalAbelKernel_tendsto hphase

end

end Li2Lean.P0.ConfigContourDiagonalAbel
