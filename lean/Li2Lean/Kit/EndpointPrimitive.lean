/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Analysis.SpecialFunctions.Log.Monotone

/-!
Generic endpoint bounds for logarithmic primitives.

The value `Real.log 0 = 0` is only a totalized computational convention.  The
theorems below use the continuous extension of `x * log x` at zero and never
differentiate the logarithm at the endpoint.  They are intended for endpoint
cells in the C-A row checker and for later contour/energy certificates.
-/

namespace ContourKit

noncomputable section

open Set

/-- The totalized endpoint primitive `x (log x - 1)`. -/
def endpointPrimitive (x : ℝ) : ℝ := x * (Real.log x - 1)

@[simp] theorem endpointPrimitive_zero : endpointPrimitive 0 = 0 := by
  simp [endpointPrimitive]

/-- `x log x` is antitone up to `exp (-1)`, including its continuous value at 0. -/
theorem mulLog_antitone_Icc_expNegOne :
    AntitoneOn (fun x : ℝ => x * Real.log x) (Icc 0 (Real.exp (-1))) := by
  exact Real.mul_log_strictAntiOn.antitoneOn

/-- The C-A primitive is antitone on every interval `[0,h]` with `h ≤ exp(-1)`.

The proof separates the `x log x` part from the linear `-x` part, so no
derivative or logarithm value at zero is used. -/
theorem endpointPrimitive_antitone_Icc {h : ℝ}
    (hh : h ≤ Real.exp (-1)) :
    AntitoneOn endpointPrimitive (Icc 0 h) := by
  intro x hx y hy hxy
  have hx' : x ∈ Icc (0 : ℝ) (Real.exp (-1)) :=
    ⟨hx.1, hx.2.trans hh⟩
  have hy' : y ∈ Icc (0 : ℝ) (Real.exp (-1)) :=
    ⟨hy.1, hy.2.trans hh⟩
  have hlog : y * Real.log y ≤ x * Real.log x :=
    mulLog_antitone_Icc_expNegOne hx' hy' hxy
  dsimp [endpointPrimitive]
  nlinarith

/-- Endpoint lower bound for an endpoint cell.  In particular, every
`x ∈ [0,h]` has `F(h) ≤ F(x)`, where `F(x)=x(log x-1)`. -/
theorem endpointPrimitive_lower_bound {h x : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ Real.exp (-1))
    (hx0 : 0 ≤ x) (hxh : x ≤ h) :
    endpointPrimitive h ≤ endpointPrimitive x := by
  exact endpointPrimitive_antitone_Icc hh ⟨hx0, hxh⟩ ⟨hh0, le_rfl⟩ hxh

/-- The corresponding endpoint bound for `x log x`; this is the singular
piece used when a cell touches a segment endpoint. -/
theorem mulLog_endpoint_lower_bound {h x : ℝ}
    (hh0 : 0 ≤ h) (hh : h ≤ Real.exp (-1))
    (hx0 : 0 ≤ x) (hxh : x ≤ h) :
    h * Real.log h ≤ x * Real.log x := by
  exact mulLog_antitone_Icc_expNegOne ⟨hx0, hxh.trans hh⟩
    ⟨hh0, hh⟩ hxh

/-- Sign-aware multiplication preserves a lower bound for a nonnegative
coefficient.  This is convenient when the singular piece has a known sign. -/
theorem mul_nonneg_coeff_lower_bound {c a b : ℝ}
    (hc : 0 ≤ c) (hab : a ≤ b) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left hab hc

/-- Sign-aware multiplication reverses a lower bound for a nonpositive
coefficient. -/
theorem mul_nonpos_coeff_lower_bound {c a b : ℝ}
    (hc : c ≤ 0) (hab : a ≤ b) : c * b ≤ c * a := by
  exact mul_le_mul_of_nonpos_left hab hc

/-- Rational version of sign-aware multiplication for checker data. -/
theorem rat_mul_nonneg_coeff_lower_bound {c a b : ℚ}
    (hc : 0 ≤ c) (hab : a ≤ b) : c * a ≤ c * b :=
  mul_le_mul_of_nonneg_left hab hc

/-- Rational version of sign-aware multiplication for a nonpositive
coefficient. -/
theorem rat_mul_nonpos_coeff_reverses {c a b : ℚ}
    (hc : c ≤ 0) (hab : a ≤ b) : c * b ≤ c * a :=
  mul_le_mul_of_nonpos_left hab hc

/-- A rational nonnegative coefficient can multiply real analytic bounds. -/
theorem real_rat_mul_nonneg_coeff_lower_bound {c : ℚ} {a b : ℝ}
    (hc : 0 ≤ c) (hab : a ≤ b) : (c : ℝ) * a ≤ (c : ℝ) * b :=
  mul_le_mul_of_nonneg_left hab (by exact_mod_cast hc)

/-- A rational nonpositive coefficient reverses real analytic bounds. -/
theorem real_rat_mul_nonpos_coeff_reverses {c : ℚ} {a b : ℝ}
    (hc : c ≤ 0) (hab : a ≤ b) : (c : ℝ) * b ≤ (c : ℝ) * a :=
  mul_le_mul_of_nonpos_left hab (by exact_mod_cast hc)

end

end ContourKit
