/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourFinite
import Li2Lean.Kit.ContourKit

open scoped BigOperators
open MeasureTheory
open Filter

namespace Li2Lean.P0.ConfigContourAnalytic

noncomputable section

def circleZeta (u : ℝ) : ℂ := Complex.exp (Complex.I * (u : ℂ))

def jMap (xi c q : ℝ) (u : ℝ) : ℂ :=
  ContourKit.joukowski (xi : ℂ) (c : ℂ) (c * q : ℂ) (circleZeta u)

theorem circleZeta_ne_zero (u : ℝ) : circleZeta u ≠ 0 := by
  simp [circleZeta]

theorem circleZeta_mul (u v : ℝ) :
    circleZeta u * circleZeta v = circleZeta (u + v) := by
  dsimp [circleZeta]
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem circleZeta_neg (u : ℝ) : circleZeta (-u) = (circleZeta u)⁻¹ := by
  simp [circleZeta, Complex.exp_neg]

theorem jMap_sub_factorization (xi c q u v : ℝ) :
    jMap xi c q u - jMap xi c q v =
      (c : ℂ) * (circleZeta u - circleZeta v) *
        (1 - (q : ℂ) * (circleZeta (-(u + v)))) := by
  unfold jMap ContourKit.joukowski
  have hu := circleZeta_ne_zero u
  have hv := circleZeta_ne_zero v
  have huv : circleZeta u * circleZeta v ≠ 0 := mul_ne_zero hu hv
  have hzneg : circleZeta (-(u + v)) =
      (circleZeta u * circleZeta v)⁻¹ := by
    rw [circleZeta_neg, circleZeta_mul]
  rw [hzneg]
  field_simp [hu, hv, huv]
  ring

private theorem q_circleZeta_norm_lt_one (q theta : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    ‖(q : ℂ) * circleZeta (-theta)‖ < 1 := by
  rw [norm_mul]
  have hunit : ‖circleZeta (-theta)‖ = 1 := by
    simp [circleZeta, Complex.norm_exp]
  rw [hunit, mul_one]
  exact hq

private theorem q_circleZeta_factor_ne_zero (q theta : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    1 - (q : ℂ) * circleZeta (-theta) ≠ 0 := by
  intro hzero
  have hone : (1 : ℂ) = (q : ℂ) * circleZeta (-theta) :=
    sub_eq_zero.mp hzero
  have hnorm : (1 : ℝ) = ‖(q : ℂ) * circleZeta (-theta)‖ := by
    simpa using congrArg norm hone
  linarith [q_circleZeta_norm_lt_one q theta hq]

theorem logNorm_jMap_sub (xi c q u v : ℝ) (hc : 0 < c)
    (hq : ‖(q : ℂ)‖ < 1)
    (hneq : circleZeta u ≠ circleZeta v) :
    Real.log ‖jMap xi c q u - jMap xi c q v‖ =
      Real.log c + Real.log ‖circleZeta u - circleZeta v‖ +
        Real.log ‖1 - (q : ℂ) * circleZeta (-(u + v))‖ := by
  have hfac := jMap_sub_factorization xi c q u v
  have hcne : (c : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hc)
  have hdiff : circleZeta u - circleZeta v ≠ 0 := sub_ne_zero.mpr hneq
  have hqfac : 1 - (q : ℂ) * circleZeta (-(u + v)) ≠ 0 := by
    exact q_circleZeta_factor_ne_zero q (u + v) hq
  rw [hfac, norm_mul, norm_mul]
  have hcnorm : ‖(c : ℂ)‖ = c := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc]
  rw [hcnorm]
  rw [mul_assoc]
  rw [Real.log_mul (ne_of_gt hc)
    (mul_ne_zero (norm_ne_zero_iff.mpr hdiff)
      (norm_ne_zero_iff.mpr hqfac))]
  rw [Real.log_mul (norm_ne_zero_iff.mpr hdiff)
    (norm_ne_zero_iff.mpr hqfac)]
  ring

theorem logNorm_one_sub_q_exp_neg (q theta : ℝ) (hq : ‖(q : ℂ)‖ < 1) :
    Real.log ‖1 - (q : ℂ) * circleZeta (-theta)‖ =
      -∑' n : ℕ, ((q : ℝ) ^ (n + 1) * Real.cos ((n + 1) * theta) / (n + 1)) := by
  let z : ℂ := (q : ℂ) * circleZeta (-theta)
  have hz : ‖z‖ < 1 := by
    dsimp [z]
    have hunit : ‖circleZeta (-theta)‖ = 1 := by
      simp [circleZeta, Complex.norm_exp]
    rw [norm_mul, hunit, mul_one]
    exact hq
  have hs := Complex.hasSum_taylorSeries_neg_log' hz
  have hsr := Complex.hasSum_re hs
  have heq : (-Complex.log (1 - z)).re = -Real.log ‖1 - z‖ := by
    rw [Complex.neg_re, Complex.log_re]
  have hlog : Real.log ‖1 - z‖ = -(-Complex.log (1 - z)).re := by
    linarith [heq]
  rw [hlog, ← hsr.tsum_eq]
  congr 1
  apply tsum_congr
  intro n
  dsimp [z, circleZeta]
  rw [mul_pow, ← Complex.exp_nat_mul]
  have hden : (↑n + 1 : ℂ) = ((n + 1 : ℕ) : ℝ) := by
    push_cast
    norm_num
  have harg : (↑(n + 1) : ℂ) * (Complex.I * (↑(-theta) : ℂ)) =
      ((-((n + 1 : ℕ) : ℝ) * theta : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hexp :
      Complex.exp ((↑(n + 1) : ℂ) * (Complex.I * (↑(-theta) : ℂ))) =
        (Real.cos (((n + 1 : ℕ) : ℝ) * theta) : ℂ) -
          Complex.I * (Real.sin (((n + 1 : ℕ) : ℝ) * theta) : ℂ) := by
    rw [harg, Complex.exp_ofReal_mul_I]
    have hneg : -((n + 1 : ℕ) : ℝ) * theta =
        -(((n + 1 : ℕ) : ℝ) * theta) := by ring
    rw [hneg, Real.cos_neg, Real.sin_neg]
    simp [Complex.ofReal_neg, mul_comm]
    noncomm_ring
  rw [hden, Complex.div_ofReal_re, hexp]
  rw [Complex.mul_re]
  have hqpow_re : (((q : ℂ) ^ (n + 1)).re) = q ^ (n + 1) := by
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
  have hqpow_im : (((q : ℂ) ^ (n + 1)).im) = 0 := by
    rw [← Complex.ofReal_pow, Complex.ofReal_im]
  rw [hqpow_re, hqpow_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    mul_zero, sub_zero, zero_mul, neg_zero]
  rw [Complex.sub_re, Complex.mul_re]
  simp
  have harg3 : ((n : ℂ) + 1) * (theta : ℂ) =
      (((n : ℝ) + 1) * theta : ℝ) := by
    push_cast
    ring
  rw [harg3, Complex.cos_ofReal_re, Complex.sin_ofReal_im]
  simp

/-!
The two kernels below separate the smooth external Joukowski factor from the
singular circle difference.  The Abel series is pointwise and unconditional
for `‖q‖ < 1`; exchanging it with an interval integral is recorded separately
so that the diagonal singularity cannot be hidden in a formal `∑`/`∫` swap.
-/

def externalLogKernel (q u v : ℝ) : ℝ :=
  Real.log ‖1 - (q : ℂ) * circleZeta (-(u + v))‖

def diagonalLogKernel (u v : ℝ) : ℝ :=
  Real.log ‖circleZeta u - circleZeta v‖

def diagonalAbelKernel (r u v : ℝ) : ℝ :=
  Real.log ‖1 - (r : ℂ) * circleZeta (-(u - v))‖

def diagonalFourierCoefficient (n : ℕ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * Real.pi),
    diagonalLogKernel u v * Real.cos ((n : ℝ) * u)

def diagonalSineCoefficient (n : ℕ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * Real.pi),
    diagonalLogKernel u v * Real.sin ((n : ℝ) * u)

def diagonalAbelFourierCoefficient (r : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * Real.pi),
    diagonalAbelKernel r u v * Real.cos ((n : ℝ) * u)

def diagonalAbelSineCoefficient (r : ℝ) (n : ℕ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * Real.pi),
    diagonalAbelKernel r u v * Real.sin ((n : ℝ) * u)

theorem externalLogKernel_eq_tsum (q u v : ℝ) (hq : ‖(q : ℂ)‖ < 1) :
    externalLogKernel q u v =
      -∑' n : ℕ, ((q : ℝ) ^ (n + 1) *
        Real.cos ((n + 1) * (u + v)) / (n + 1)) := by
  simpa [externalLogKernel] using logNorm_one_sub_q_exp_neg q (u + v) hq

theorem diagonalAbelKernel_eq_tsum (r u v : ℝ) (hr : ‖(r : ℂ)‖ < 1) :
    diagonalAbelKernel r u v =
      -∑' n : ℕ, ((r : ℝ) ^ (n + 1) *
        Real.cos ((n + 1) * (u - v)) / (n + 1)) := by
  simpa [diagonalAbelKernel] using logNorm_one_sub_q_exp_neg r (u - v) hr

/--
An explicit obligation for the Abel regularization of the diagonal kernel.
The fields assert local integrability for every subunit radius, the almost
everywhere pointwise limit as the radius tends to one from below, and the
two coefficient-level limit exchanges.  No Fourier coefficient value is
assumed here.
-/
structure DiagonalAbelCertificate : Prop where
  abel_intervalIntegrable :
    ∀ r : ℝ, 0 ≤ r → r < 1 → ∀ v : ℝ,
      IntervalIntegrable (fun u => diagonalAbelKernel r u v)
        volume (0 : ℝ) (2 * Real.pi)
  pointwise_limit_away :
    ∀ u v : ℝ, circleZeta u ≠ circleZeta v →
      Tendsto (fun r : ℝ => diagonalAbelKernel r u v)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (diagonalLogKernel u v))
  cosine_limit_exchange :
    ∀ n : ℕ, ∀ v : ℝ,
      Tendsto (fun r : ℝ => diagonalAbelFourierCoefficient r n v)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (diagonalFourierCoefficient n v))
  sine_limit_exchange :
    ∀ n : ℕ, ∀ v : ℝ,
      Tendsto (fun r : ℝ => diagonalAbelSineCoefficient r n v)
        (nhdsWithin (1 : ℝ) (Set.Iio 1))
        (nhds (diagonalSineCoefficient n v))

/--
The remaining positive-frequency diagonal calculation, isolated from the
Abel exchange obligation.  The `n ≥ 1` guard makes the displayed denominator
well-defined and records exactly the coefficient statement needed by the
finite contour Fourier assembly.
-/
structure DiagonalFourierGap : Prop where
  intervalIntegrable :
    ∀ v : ℝ, IntervalIntegrable (fun u => diagonalLogKernel u v)
      volume (0 : ℝ) (2 * Real.pi)
  cosine_coeff :
    ∀ n : ℕ, 1 ≤ n → ∀ v : ℝ,
      diagonalFourierCoefficient n v =
        -(Real.pi / (n : ℝ)) * Real.cos ((n : ℝ) * v)
  sine_coeff :
    ∀ n : ℕ, 1 ≤ n → ∀ v : ℝ,
      diagonalSineCoefficient n v =
        -(Real.pi / (n : ℝ)) * Real.sin ((n : ℝ) * v)

end

end Li2Lean.P0.ConfigContourAnalytic
