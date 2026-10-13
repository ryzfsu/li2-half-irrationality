/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigFejerMass
import Li2Lean.P0.ConfigContourKernel

/-!
# Fourier evaluation of the actual finite Fejer logarithmic potential

The analytic input is Mathlib's convergent logarithm Taylor series on the
open unit disk. Domination and character orthogonality are proved here,
rather than supplied as a correspondence premise.
-/

open MeasureTheory Filter
open scoped BigOperators Topology

namespace Li2Lean.P0.ConfigFejerLog

noncomputable section

open ConfigContourReference ConfigContourKernel ConfigFejerMass

theorem norm_fourierChar (k : ℤ) (u : ℝ) : ‖fourierChar k u‖ = 1 := by
  simp [fourierChar, Complex.norm_exp]

theorem fourierChar_mul (k l : ℤ) (u : ℝ) :
    fourierChar k u * fourierChar l u = fourierChar (k + l) u := by
  unfold fourierChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem phase_pow (n : ℕ) (u : ℝ) : phase u ^ n = fourierChar (n : ℤ) u := by
  unfold phase fourierChar
  rw [← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

def logSeriesTerm (a : ℂ) (k : ℤ) (n : ℕ) (u : ℝ) : ℂ :=
  fourierChar k u * ((a * phase u) ^ n / (n : ℂ))

theorem continuous_logSeriesTerm (a : ℂ) (k : ℤ) (n : ℕ) :
    Continuous (logSeriesTerm a k n) := by
  unfold logSeriesTerm fourierChar phase
  fun_prop

theorem logSeriesTerm_norm_le (a : ℂ) (k : ℤ) (n : ℕ) (u : ℝ) :
    ‖logSeriesTerm a k n u‖ ≤ ‖a‖ ^ n := by
  rcases n.eq_zero_or_pos with rfl | hn
  · simp [logSeriesTerm]
  · have hden : (1 : ℝ) ≤ n := by exact_mod_cast hn
    simp only [logSeriesTerm, norm_mul, norm_fourierChar, one_mul, norm_div,
      norm_pow, norm_phase, mul_one, norm_natCast]
    exact div_le_self (by positivity) hden

theorem integral_logSeriesTerm (a : ℂ) (k : ℤ) (n : ℕ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi), logSeriesTerm a k n u) =
      (a ^ n / (n : ℂ)) *
        (if k + (n : ℤ) = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) := by
  have heq (u : ℝ) : logSeriesTerm a k n u =
      (a ^ n / (n : ℂ)) * fourierChar (k + (n : ℤ)) u := by
    unfold logSeriesTerm
    rw [mul_pow, phase_pow, ← fourierChar_mul]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  congr 1
  simpa only [sub_zero] using integral_fourierChar (k + (n : ℤ)) 0

/-- Termwise integration of the genuine complex log, with a proved geometric
majorant. The multiplier may be any integer character. -/
theorem hasSum_integral_logSeries {a : ℂ} (ha : ‖a‖ < 1) (k : ℤ) :
    HasSum (fun n : ℕ => (a ^ n / (n : ℂ)) *
      (if k + (n : ℤ) = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0))
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        fourierChar k u * (-Complex.log (1 - a * phase u))) := by
  have hseries (u : ℝ) : HasSum (fun n => logSeriesTerm a k n u)
      (fourierChar k u * (-Complex.log (1 - a * phase u))) := by
    apply HasSum.mul_left
    apply Complex.hasSum_taylorSeries_neg_log
    simpa only [norm_mul, norm_phase, mul_one] using ha
  have hdom := intervalIntegral.hasSum_integral_of_dominated_convergence
    (μ := volume) (a := (0 : ℝ)) (b := 2 * Real.pi)
    (F := fun n => logSeriesTerm a k n)
    (f := fun u => fourierChar k u * (-Complex.log (1 - a * phase u)))
    (fun n (_ : ℝ) => ‖a‖ ^ n)
    (fun n => (continuous_logSeriesTerm a k n).aestronglyMeasurable)
    (fun n => ae_of_all _ fun u hu => logSeriesTerm_norm_le a k n u)
    (ae_of_all _ fun u hu => summable_geometric_of_lt_one (norm_nonneg a) ha)
    intervalIntegrable_const
    (ae_of_all _ fun u hu => hseries u)
  simpa only [integral_logSeriesTerm] using hdom

/-- Negative Fourier mode of the analytic logarithm, including mode zero
under the total-field convention `a^0/0=0`. -/
theorem integral_negMode_negLog {a : ℂ} (ha : ‖a‖ < 1) (n : ℕ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fourierChar (-(n : ℤ)) u * (-Complex.log (1 - a * phase u))) =
      (a ^ n / (n : ℂ)) * ((2 * Real.pi : ℝ) : ℂ) := by
  apply (hasSum_integral_logSeries ha (-(n : ℤ))).unique
  have h := hasSum_single (f := fun m : ℕ => (a ^ m / (m : ℂ)) *
      (if -(n : ℤ) + (m : ℤ) = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0)) n
    (fun m hmn => by
      have hne : -(n : ℤ) + (m : ℤ) ≠ 0 := by omega
      simp [hne])
  simpa using h

/-- Positive Fourier modes of the analytic logarithm vanish, including
the zero average. -/
theorem integral_posMode_negLog {a : ℂ} (ha : ‖a‖ < 1) (n : ℕ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fourierChar (n : ℤ) u * (-Complex.log (1 - a * phase u))) = 0 := by
  apply (hasSum_integral_logSeries ha (n : ℤ)).unique
  have hzero (m : ℕ) : (a ^ m / (m : ℂ)) *
      (if (n : ℤ) + (m : ℤ) = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0) = 0 := by
    by_cases hm : m = 0
    · subst m
      simp
    · have hne : (n : ℤ) + (m : ℤ) ≠ 0 := by omega
      simp [hne]
  simpa only [hzero] using (hasSum_zero : HasSum (fun _ : ℕ => (0 : ℂ)) 0)

theorem fourierChar_sub_angle (k : ℤ) (u theta : ℝ) :
    fourierChar k (u - theta) = fourierChar (-k) theta * fourierChar k u := by
  unfold fourierChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

theorem continuous_negLog {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (fun u : ℝ => -Complex.log (1 - a * phase u)) := by
  apply Continuous.neg
  apply continuous_iff_continuousAt.mpr
  intro u
  have hz : ‖-(a * phase u)‖ < 1 := by
    simpa only [norm_neg, norm_mul, norm_phase, mul_one] using ha
  have hp : 1 - a * phase u ∈ Complex.slitPlane := by
    simpa only [sub_eq_add_neg] using Complex.mem_slitPlane_of_norm_lt_one hz
  have hc : Continuous (fun v : ℝ => 1 - a * phase v) := by
    unfold phase
    fun_prop
  exact ContinuousAt.comp (g := Complex.log) (f := fun v : ℝ => 1 - a * phase v)
    (Complex.hasDerivAt_log hp).continuousAt hc.continuousAt

/-- A shifted Fourier mode is evaluated without numerical quadrature. -/
theorem integral_differenceMode_shift {a : ℂ} (ha : ‖a‖ < 1)
    (r s : ℕ) (theta : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
        (-Complex.log (1 - a * phase u))) =
      if r ≤ s then ((2 * Real.pi : ℝ) : ℂ) *
        ((a * phase theta) ^ (s - r) / ((s - r : ℕ) : ℂ)) else 0 := by
  simp_rw [fourierChar_sub_angle, mul_assoc]
  rw [intervalIntegral.integral_const_mul]
  by_cases hrs : r ≤ s
  · rw [ite_eq_left hrs]
    have hk : (r : ℤ) - (s : ℤ) = -((s - r : ℕ) : ℤ) := by omega
    rw [hk, integral_negMode_negLog ha, neg_neg, ← phase_pow]
    rw [mul_pow]
    ring
  · rw [ite_eq_right hrs]
    have hk : (r : ℤ) - (s : ℤ) = ((r - s : ℕ) : ℤ) := by omega
    rw [hk, integral_posMode_negLog ha, mul_zero]

/-- Grouping equal Fourier differences in the finite squared kernel. -/
theorem triangular_sum (N : ℕ) (f : ℕ → ℂ) :
    (∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
      if r ≤ s then f (s - r) else 0) =
      ∑ n ∈ Finset.range N, ((N - n : ℕ) : ℂ) * f n := by
  rw [Finset.sum_comm]
  have hrow (s : ℕ) (hs : s ∈ Finset.range N) :
      (∑ r ∈ Finset.range N, if r ≤ s then f (s - r) else 0) =
        ∑ r ∈ Finset.range (s + 1), f (s - r) := by
    have hsub : Finset.range (s + 1) ⊆ Finset.range N := by
      apply Finset.range_mono
      exact Finset.mem_range.mp hs
    rw [← Finset.sum_subset hsub]
    · apply Finset.sum_congr rfl
      intro r hr
      rw [ite_eq_left (by have := Finset.mem_range.mp hr; omega)]
    · intro r hr hrnot
      rw [ite_eq_right (by
        have : ¬r < s + 1 := by simpa only [Finset.mem_range] using hrnot
        omega)]
  rw [Finset.sum_congr rfl hrow]
  have href (s : ℕ) :
      (∑ r ∈ Finset.range (s + 1), f (s - r)) =
        ∑ r ∈ Finset.range (s + 1), f r := by
    simpa only [Nat.add_sub_cancel] using Finset.sum_range_reflect f (s + 1)
  simp_rw [href]
  rw [Finset.sum_range_diag_flip N (fun n _ => f n)]
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]

def fejerLogPolynomial (a : ℂ) : ℂ :=
  ∑ n ∈ Finset.range 49, (((49 - n : ℕ) : ℂ) / 49) * (a ^ n / (n : ℂ))

/-- The exact complex finite Fejer/log identity on the open disk. -/
theorem integral_fejer48_negLog {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      (fejer48 (u - theta) : ℂ) * (-Complex.log (1 - a * phase u))) =
      ((2 * Real.pi : ℝ) : ℂ) * fejerLogPolynomial (a * phase theta) := by
  let F : ℕ → ℕ → ℝ → ℂ := fun r s u =>
    fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
      (-Complex.log (1 - a * phase u))
  have hF (r s : ℕ) : Continuous (F r s) :=
    ((continuous_fourierChar _).comp (continuous_id.sub continuous_const)).mul
      (continuous_negLog ha)
  have heq (u : ℝ) : (fejer48 (u - theta) : ℂ) *
      (-Complex.log (1 - a * phase u)) =
      (49 : ℂ)⁻¹ * ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49, F r s u := by
    unfold fejer48
    rw [Complex.ofReal_div, exp_sum_norm_sq]
    norm_num only [Complex.ofReal_ofNat]
    simp only [F]
    simp_rw [← Finset.sum_mul]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  have hrow (r : ℕ) : Continuous (fun u => ∑ s ∈ Finset.range 49, F r s u) := by
    apply continuous_finsetSum
    intro s hs
    exact hF r s
  rw [intervalIntegral.integral_finsetSum (fun r hr => (hrow r).intervalIntegrable _ _)]
  simp_rw [intervalIntegral.integral_finsetSum (fun s hs => (hF _ s).intervalIntegrable _ _)]
  simp_rw [F, integral_differenceMode_shift ha]
  rw [triangular_sum 49 (fun n => ((2 * Real.pi : ℝ) : ℂ) *
    ((a * phase theta) ^ n / (n : ℂ)))]
  unfold fejerLogPolynomial
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro n hn
  ring

/-- The real logarithm identity used by the potential checker. -/
theorem integral_fejer48_log_norm {a : ℂ} (ha : ‖a‖ < 1) (theta : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fejer48 (u - theta) * Real.log ‖1 - a * phase u‖) =
      -(2 * Real.pi) * (fejerLogPolynomial (a * phase theta)).re := by
  have hc : Continuous (fun u : ℝ =>
      (fejer48 (u - theta) : ℂ) * (-Complex.log (1 - a * phase u))) :=
    (Complex.continuous_ofReal.comp
      (continuous_fejer48.comp (continuous_id.sub continuous_const))).mul
        (continuous_negLog ha)
  have h := congrArg Complex.reCLM (integral_fejer48_negLog ha theta)
  rw [← Complex.reCLM.intervalIntegral_comp_comm (hc.intervalIntegrable _ _)] at h
  simp only [Complex.reCLM_apply, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.neg_re, Complex.log_re,
    mul_neg, intervalIntegral.integral_neg] at h
  linarith

def contourLogPolynomial (a : ℂ) : ℝ :=
  ∑ j : Fin 64, contourWeight j * (fejerLogPolynomial (a * phase (contourAngle j))).re

theorem continuous_log_norm {a : ℂ} (ha : ‖a‖ < 1) :
    Continuous (fun u : ℝ => Real.log ‖1 - a * phase u‖) := by
  have h := Complex.continuous_re.comp (continuous_negLog ha)
  have heq : (fun u : ℝ => Real.log ‖1 - a * phase u‖) =
      fun u => -(-Complex.log (1 - a * phase u)).re := by
    funext u
    simp only [Complex.neg_re, Complex.log_re, neg_neg]
  rw [heq]
  exact h.neg

/-- Exact finite logarithmic transform of the original 64-weight density.
The weights, Fejer normalization, and midpoint angles are all literal v10 data. -/
theorem integral_contourDensity_log_norm {a : ℂ} (ha : ‖a‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * Real.log ‖1 - a * phase u‖) =
      -(2 * Real.pi) * contourLogPolynomial a := by
  unfold contourDensity
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [mul_assoc, intervalIntegral.integral_const_mul,
      integral_fejer48_log_norm ha]
    unfold contourLogPolynomial
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j hj
    ring
  · intro j hj
    exact ((continuous_const.mul
      (continuous_fejer48.comp (continuous_id.sub continuous_const))).mul
        (continuous_log_norm ha)).intervalIntegrable _ _

def contourMoment (n : ℕ) : ℝ :=
  (1 - (n : ℝ) / 49) * ∑ j : Fin 64,
    contourWeight j * Real.cos ((n : ℝ) * contourAngle j)

theorem phase_pow_re (n : ℕ) (theta : ℝ) :
    (phase theta ^ n).re = Real.cos ((n : ℝ) * theta) := by
  rw [phase_pow]
  unfold fourierChar
  simp only [Int.cast_natCast]
  simpa only [Complex.ofReal_mul, Complex.ofReal_natCast] using
    Complex.exp_ofReal_mul_I_re ((n : ℝ) * theta)

theorem fejerLogPolynomial_ofReal_re (x theta : ℝ) :
    (fejerLogPolynomial ((x : ℂ) * phase theta)).re =
      ∑ n ∈ Finset.range 49,
        (1 - (n : ℝ) / 49) * (x ^ n / (n : ℝ)) *
          Real.cos ((n : ℝ) * theta) := by
  have hterm (n : ℕ) : (((49 - n : ℕ) : ℂ) / 49) *
      (((x : ℂ) * phase theta) ^ n / (n : ℂ)) =
      ((((49 - n : ℕ) : ℝ) / 49 * (x ^ n / (n : ℝ)) : ℝ) : ℂ) *
        phase theta ^ n := by
    push_cast
    rw [mul_pow]
    ring
  unfold fejerLogPolynomial
  simp_rw [hterm]
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  simp only [Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, phase_pow_re]
  have hn49 : n ≤ 49 := by have := Finset.mem_range.mp hn; omega
  rw [Nat.cast_sub hn49]
  push_cast
  ring

/-- The actual cosine moments used in `check_dual.py`, with the Fejer
factor `1-n/49` and no changed weights. -/
theorem contourLogPolynomial_ofReal (x : ℝ) :
    contourLogPolynomial (x : ℂ) =
      ∑ n ∈ Finset.range 49, contourMoment n * (x ^ n / (n : ℝ)) := by
  unfold contourLogPolynomial
  simp_rw [fejerLogPolynomial_ofReal_re, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n hn
  unfold contourMoment
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j hj
  ring

end

end Li2Lean.P0.ConfigFejerLog
