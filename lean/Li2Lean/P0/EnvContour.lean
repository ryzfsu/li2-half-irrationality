/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvFreq
import Li2Lean.P0.ContourOffDiag
import Li2Lean.P0.FrequencyLimit

/-!
# The contour form of the source rows

Each source row `C_{a,·}` (`a ∈ I_m`) is the sum of its diagonal part
`log 2 · U_a · [a = j]` and the contour integral
`-(2πi)^{-1} ∮_{mΓ} F(z) / ((z-a)(z-j)) dz` (proved contour identity
`p0ContourIdentityStatement_proved`, paper v13 `eq:p0-contour-q`).  Here the contour part is
rewritten as `∫ φ_a(u) ψ_j(u) dμ(u)` over the parameter measure `μ` of `E`.
-/

open Finset MeasureTheory

namespace Li2Lean.P0.Env

noncomputable section

theorem p0CQ_two_cast_complex (g i j : ℕ) :
    ((p0CQ 2 g i j : ℚ) : ℂ) = p0C g i j := by
  unfold p0CQ p0C p0U p0UQ
  split_ifs with h
  · push_cast; ring
  · push_cast; ring

/-- The diagonal (pinned) part of a source row. -/
def pinPart (g a j : ℕ) : ℂ :=
  if a = j then ((Real.log 2 : ℝ) : ℂ) * p0U g a else 0

/-- The contour part of a source row. -/
def contPart (m a j : ℕ) : ℂ :=
  -p0EllipseIntegral m (fun z => p0Entire (m / 2) z / ((z - (a : ℂ)) * (z - (j : ℂ))))

theorem p0C_split (m : ℕ) (h4 : 4 ∣ m) (a j : ℕ) (ha : a < 2 * m) (hj : j < 2 * m) :
    p0C (m / 2) a j = pinPart (m / 2) a j + contPart m a j := by
  have hm2 : 2 * (m / 2) = m := by omega
  have h := p0ContourIdentityStatement_proved (m / 2) a j (by omega) (by omega)
  rw [h, hm2, add_comm]
  rfl

/-- The contour factor `φ_a(u) = -(2πi)^{-1} F(z(u)) z'(u) / (z(u) - a)`. -/
def phiC (m a : ℕ) (u : ℝ) : ℂ :=
  -((Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ * p0Entire (m / 2) (p0EllipsePoint m u) *
    p0EllipseTangent m u) * (p0EllipsePoint m u - (a : ℂ))⁻¹

/-- The column factor `ψ_j(u) = 1/(z(u) - j)`. -/
def psiC (m j : ℕ) (u : ℝ) : ℂ := (p0EllipsePoint m u - (j : ℂ))⁻¹

theorem ellipse_sub_ne (m : ℕ) (hm : 0 < m) (a : ℕ) (ha : a ≤ 2 * m) (u : ℝ) :
    p0EllipsePoint m u - (a : ℂ) ≠ 0 := by
  have h := FrequencyRegularity.ellipsePoint_ne_real m hm u (a : ℝ) (by positivity)
    (by exact_mod_cast ha)
  intro h0
  apply h
  have := sub_eq_zero.mp h0
  rw [this]; push_cast; rfl

theorem continuous_phiC (m : ℕ) (hm : 0 < m) (a : ℕ) (ha : a ≤ 2 * m) :
    Continuous (phiC m a) := by
  unfold phiC
  apply Continuous.mul
  · exact ((continuous_const.mul ((FrequencyRegularity.continuous_entire _).comp
      (FrequencyRegularity.continuous_ellipsePoint m))).mul
      (FrequencyRegularity.continuous_ellipseTangent m)).neg
  · exact ((FrequencyRegularity.continuous_ellipsePoint m).sub continuous_const).inv₀
      (ellipse_sub_ne m hm a ha)

theorem continuous_psiC (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j ≤ 2 * m) :
    Continuous (psiC m j) :=
  ((FrequencyRegularity.continuous_ellipsePoint m).sub continuous_const).inv₀
    (ellipse_sub_ne m hm j hj)

theorem integrable_phiC_psiC (m : ℕ) (hm : 0 < m) (a j : ℕ) (ha : a ≤ 2 * m)
    (hj : j ≤ 2 * m) :
    Integrable (fun u => phiC m a u * psiC m j u) contourParameterMeasure :=
  ((continuous_phiC m hm a ha).mul (continuous_psiC m hm j hj)).integrableOn_Icc

theorem contPart_eq_integral (m : ℕ) (hm : 0 < m) (a j : ℕ) (ha : a ≤ 2 * m)
    (hj : j ≤ 2 * m) :
    contPart m a j = ∫ u, phiC m a u * psiC m j u ∂contourParameterMeasure := by
  unfold contPart p0EllipseIntegral contourParameterMeasure
  rw [intervalIntegral.integral_of_le (by positivity), ← integral_Icc_eq_integral_Ioc,
    ← integral_const_mul, ← integral_neg]
  apply integral_congr_ae
  filter_upwards [] with u
  have h1 := ellipse_sub_ne m hm a ha u
  have h2 := ellipse_sub_ne m hm j hj u
  simp only [phiC, psiC]
  field_simp

end

end Li2Lean.P0.Env
