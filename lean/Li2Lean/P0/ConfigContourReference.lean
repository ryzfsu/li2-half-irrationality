/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigData
import Li2Lean.LayerInterfaces

/-!
# The literal v10 contour reference

The parameter density below is exactly equation (5.4) of docs/6333 and the
Appendix A array in `ConfigData`.  In particular it is the Fejer mixture with
degree 48 and 64 midpoint angles, and it is integrated against `du / (2*pi)`.
The reflection theorem is an analytic leaf of `CAReceipt.contour_reduction`.
No assertion about the Fourier evaluation of the logarithmic integral is
made by defining the integral or proving its symmetry.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigContourReference

noncomputable section

/-- Reversal of the exact 64 midpoint angles in v10 (5.4). -/
def reverseIndex : Fin 64 ≃ Fin 64 where
  toFun j := ⟨63 - j.val, by omega⟩
  invFun j := ⟨63 - j.val, by omega⟩
  left_inv j := by ext; dsimp; omega
  right_inv j := by ext; dsimp; omega

/-- The actual mass of the `j`th Fejer kernel from Appendix A. -/
def contourWeight (j : Fin 64) : ℝ :=
  (ConfigData.contourMassUnits.getD j.val 0 : ℝ) /
    (ConfigData.referenceDenominator : ℝ)

/-- The actual midpoint angle `pi*(2*j+1)/64` from v10 (5.4). -/
def contourAngle (j : Fin 64) : ℝ :=
  Real.pi * (2 * (j.val : ℝ) + 1) / 64

theorem massUnits_reverse : ∀ j : Fin 64,
    ConfigData.contourMassUnits.getD (reverseIndex j).val 0 =
      ConfigData.contourMassUnits.getD j.val 0 := by
  decide +kernel

theorem contourWeight_reverse (j : Fin 64) :
    contourWeight (reverseIndex j) = contourWeight j := by
  unfold contourWeight
  rw [massUnits_reverse]

theorem contourWeight_nonneg (j : Fin 64) : 0 ≤ contourWeight j := by
  unfold contourWeight
  positivity

theorem contourAngle_reverse (j : Fin 64) :
    contourAngle (reverseIndex j) = 2 * Real.pi - contourAngle j := by
  have hj : j.val ≤ 63 := by omega
  simp only [contourAngle, reverseIndex, Equiv.coe_fn_mk]
  rw [Nat.cast_sub hj]
  push_cast
  ring

/-- The literal Fejer kernel `|sum_(r=0)^48 exp(i*r*u)|^2/49`.
This definition retains the nonnegative squared-norm form in v10 (5.4). -/
def fejer48 (u : ℝ) : ℝ :=
  ‖∑ r ∈ Finset.range 49,
      Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)‖ ^ 2 / 49

theorem fejer48_nonneg (u : ℝ) : 0 ≤ fejer48 u := by
  unfold fejer48
  positivity

theorem fejer48_neg (u : ℝ) : fejer48 (-u) = fejer48 u := by
  have hs : (∑ r ∈ Finset.range 49,
      Complex.exp ((r : ℂ) * ((-u : ℝ) : ℂ) * Complex.I)) =
      (starRingEnd ℂ) (∑ r ∈ Finset.range 49,
        Complex.exp ((r : ℂ) * (u : ℂ) * Complex.I)) := by
    rw [map_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [← Complex.exp_conj]
    congr 1
    simp
  unfold fejer48
  rw [hs, Complex.norm_conj]

/-- The density numerator in (5.4); the normalization is in
`contourReferenceIntegral`. -/
def contourDensity (u : ℝ) : ℝ :=
  ∑ j : Fin 64, contourWeight j * fejer48 (u - contourAngle j)

theorem contourDensity_nonneg (u : ℝ) : 0 ≤ contourDensity u := by
  apply Finset.sum_nonneg
  intro j hj
  exact mul_nonneg (contourWeight_nonneg j) (fejer48_nonneg _)

/-- Exact reflection of the original 64-term Fejer mixture; no positivity
or Fourier approximation is a premise. -/
theorem contourDensity_reflect (u : ℝ) :
    contourDensity (2 * Real.pi - u) = contourDensity u := by
  unfold contourDensity
  rw [← Equiv.sum_comp reverseIndex
    (fun j => contourWeight j * fejer48 (2 * Real.pi - u - contourAngle j))]
  apply Finset.sum_congr rfl
  intro j hj
  rw [contourWeight_reverse, contourAngle_reverse]
  congr 1
  rw [show 2 * Real.pi - u - (2 * Real.pi - contourAngle j) =
      -(u - contourAngle j) by ring, fejer48_neg]

/-- Integration against the v10 reference contour measure, parameterized
exactly once with the paper's `du/(2*pi)` normalization. -/
def contourReferenceIntegral (f : ℂ → ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..(2 * Real.pi),
    contourDensity u * f (Li2Lean.p0EllipsePoint 1 u)

/-- The actual logarithmic potential of the Fejer reference (5.4). -/
def contourReferencePotential (z : ℂ) : ℝ :=
  contourReferenceIntegral (fun w => Real.log ‖z - w‖)

theorem ellipse_reflect (u : ℝ) :
    Li2Lean.p0EllipsePoint 1 (2 * Real.pi - u) =
      (starRingEnd ℂ) (Li2Lean.p0EllipsePoint 1 u) := by
  simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
    Real.cos_two_pi_sub, Real.sin_two_pi_sub, map_add, map_mul,
    Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.ofReal_neg, neg_mul]

/-- Reflection invariance of the literal v10 contour integral. -/
theorem contourReferenceIntegral_conj (f : ℂ → ℝ) :
    contourReferenceIntegral (fun w => f ((starRingEnd ℂ) w)) =
      contourReferenceIntegral f := by
  unfold contourReferenceIntegral
  congr 1
  have h := intervalIntegral.integral_comp_sub_left
    (fun u => contourDensity u * f (Li2Lean.p0EllipsePoint 1 u))
    (a := (0 : ℝ)) (b := 2 * Real.pi) (2 * Real.pi)
  simp only [sub_self, sub_zero] at h
  rw [← h]
  apply intervalIntegral.integral_congr
  intro u hu
  change contourDensity u * f ((starRingEnd ℂ) (Li2Lean.p0EllipsePoint 1 u)) =
    contourDensity (2 * Real.pi - u) *
      f (Li2Lean.p0EllipsePoint 1 (2 * Real.pi - u))
  rw [contourDensity_reflect, ellipse_reflect]

/-- Conjugation symmetry of the actual contour logarithmic potential.
This includes points on the contour; reflection is a measure substitution
and does not require removing the diagonal from the statement. -/
theorem contourReferencePotential_conj (z : ℂ) :
    contourReferencePotential ((starRingEnd ℂ) z) =
      contourReferencePotential z := by
  unfold contourReferencePotential
  have hkernel : (fun w : ℂ => Real.log ‖(starRingEnd ℂ) z - w‖) =
      (fun w : ℂ => Real.log ‖z - (starRingEnd ℂ) w‖) := by
    funext w
    have hnorm := Complex.norm_conj (z - (starRingEnd ℂ) w)
    simpa only [map_sub, starRingEnd_self_apply] using congrArg Real.log hnorm
  rw [hkernel]
  exact contourReferenceIntegral_conj (fun w => Real.log ‖z - w‖)

end

end Li2Lean.P0.ConfigContourReference
