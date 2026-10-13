/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourReference

/-!
# Normalization of the actual v10 Fejer reference

Complex exponential orthogonality evaluates the squared-norm kernel itself.
The final mass theorem therefore concerns the original 64-weight measure,
not a replacement trigonometric density or a supplied normalization premise.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigFejerMass

noncomputable section

open ConfigContourReference

def fourierChar (k : ℤ) (u : ℝ) : ℂ :=
  Complex.exp ((k : ℂ) * (u : ℂ) * Complex.I)

theorem continuous_fourierChar (k : ℤ) : Continuous (fourierChar k) := by
  unfold fourierChar
  fun_prop

/-- Exact orthogonality over one full turn, including any phase shift. -/
theorem integral_fourierChar (k : ℤ) (theta : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi), fourierChar k (u - theta)) =
      if k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
  by_cases hk : k = 0
  · subst k
    simp [fourierChar]
  · rw [ite_eq_right hk]
    have hkC : (k : ℂ) ≠ 0 := by exact_mod_cast hk
    have heq (u : ℝ) : fourierChar k (u - theta) =
        Complex.exp (-((k : ℂ) * (theta : ℂ) * Complex.I)) *
          Complex.exp (((k : ℂ) * Complex.I) * (u : ℂ)) := by
      rw [fourierChar, ← Complex.exp_add]
      congr 1
      push_cast
      ring
    simp_rw [heq]
    rw [intervalIntegral.integral_const_mul,
      integral_exp_mul_complex (mul_ne_zero hkC Complex.I_ne_zero)]
    have hp : Complex.exp (((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ)) = 1 := by
      rw [show ((k : ℂ) * Complex.I) * ((2 * Real.pi : ℝ) : ℂ) =
        (k : ℂ) * (2 * (Real.pi : ℂ) * Complex.I) by push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I k
    rw [hp]
    simp

/-- Expanding a finite squared norm into its exact Fourier differences. -/
theorem exp_sum_norm_sq (N : ℕ) (u : ℝ) :
    ((‖∑ r ∈ Finset.range N,
      Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)‖ ^ 2 : ℝ) : ℂ) =
      ∑ r ∈ Finset.range N, ∑ s ∈ Finset.range N,
        fourierChar ((r : ℤ) - (s : ℤ)) u := by
  have hn (z : ℂ) : ((‖z‖ ^ 2 : ℝ) : ℂ) = z * (starRingEnd ℂ) z := by
    apply Complex.ext
    · simp only [Complex.ofReal_re, Complex.sq_norm, Complex.normSq_apply,
        Complex.mul_re, Complex.conj_re, Complex.conj_im]
      ring
    · simp only [Complex.ofReal_im, Complex.mul_im, Complex.conj_re, Complex.conj_im]
      ring
  rw [hn, map_sum, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  apply Finset.sum_congr rfl
  intro s hs
  rw [← Complex.exp_conj, ← Complex.exp_add]
  unfold fourierChar
  congr 1
  simp only [map_mul, Complex.conj_natCast, Complex.conj_ofReal, Complex.conj_I]
  push_cast
  ring

/-- The normalized Fejer kernel in (5.4) has unit total mass, with no
restriction on its midpoint angle. -/
theorem integral_fejer48 (theta : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi), fejer48 (u - theta)) = 2 * Real.pi := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have heq (u : ℝ) : (fejer48 (u - theta) : ℂ) =
      (49 : ℂ)⁻¹ * ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) := by
    unfold fejer48
    rw [Complex.ofReal_div, exp_sum_norm_sq]
    norm_num only [Complex.ofReal_ofNat]
    ring
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  have hterms (r s : ℕ) : IntervalIntegrable
      (fun u => fourierChar ((r : ℤ) - (s : ℤ)) (u - theta))
      volume 0 (2 * Real.pi) :=
    ((continuous_fourierChar _).comp (continuous_id.sub continuous_const)).intervalIntegrable _ _
  have hrow (r : ℕ) : IntervalIntegrable
      (fun u => ∑ s ∈ Finset.range 49,
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta))
      volume 0 (2 * Real.pi) := by
    apply Continuous.intervalIntegrable
    apply continuous_finsetSum
    intro s hs
    exact (continuous_fourierChar _).comp (continuous_id.sub continuous_const)
  have hexpand :
      (∫ u in (0 : ℝ)..(2 * Real.pi), ∑ r ∈ Finset.range 49,
        ∑ s ∈ Finset.range 49, fourierChar ((r : ℤ) - (s : ℤ)) (u - theta)) =
      ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
        ∫ u in (0 : ℝ)..(2 * Real.pi),
          fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) := by
    rw [intervalIntegral.integral_finsetSum (fun r hr => hrow r)]
    apply Finset.sum_congr rfl
    intro r hr
    exact intervalIntegral.integral_finsetSum (fun s hs => hterms r s)
  rw [hexpand]
  simp_rw [integral_fourierChar]
  simp only [sub_eq_zero, Int.natCast_inj]
  simp
  rw [Finset.sum_congr rfl (fun x hx =>
    ite_eq_left (Finset.mem_range.mp hx))]
  simp

theorem continuous_fejer48 : Continuous fejer48 := by
  unfold fejer48
  fun_prop

/-- The total parameter mass is exactly the sum of the original weights. -/
theorem integral_contourDensity :
    (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u) =
      (2 * Real.pi) * ∑ j : Fin 64, contourWeight j := by
  unfold contourDensity
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_fejer48]
    rw [← Finset.sum_mul]
    ring
  · intro j hj
    apply Continuous.intervalIntegrable
    exact continuous_const.mul (continuous_fejer48.comp (continuous_id.sub continuous_const))

theorem contourWeight_sum :
    (∑ j : Fin 64, contourWeight j) = (267885951940 / 1000000000000 : ℝ) := by
  unfold contourWeight ConfigData.referenceDenominator
  norm_num [Fin.sum_univ_succ, ConfigData.contourMassUnits, List.getD]

/-- Actual `nu_0` mass from Appendix A, in the unchanged `du/(2*pi)`
normalization of (5.4). -/
theorem contourReferenceIntegral_one :
    contourReferenceIntegral (fun _ => 1) =
      (267885951940 / 1000000000000 : ℝ) := by
  unfold contourReferenceIntegral
  simp only [mul_one]
  rw [integral_contourDensity, contourWeight_sum]
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

end

end Li2Lean.P0.ConfigFejerMass
