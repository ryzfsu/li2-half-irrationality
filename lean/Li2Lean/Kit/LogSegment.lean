/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory

namespace Li2Lean.LogSegment

noncomputable section

/-- The real primitive used by v10 C-A for every real reference cell.
The totalized logarithm gives the required endpoint convention `F 0 = 0`. -/
def primitive (v : ℝ) : ℝ := v * (Real.log |v| - 1)

@[simp] theorem primitive_zero : primitive 0 = 0 := by simp [primitive]

theorem primitive_eq (v : ℝ) : primitive v = v * Real.log v - v := by
  simp only [primitive, Real.log_abs]
  ring

/-- This continuity includes the logarithmic singularity at a cell endpoint. -/
theorem continuous_primitive : Continuous primitive := by
  simp_rw [funext primitive_eq]
  exact Real.continuous_mul_log.sub continuous_id

/-- The derivative is only claimed away from the singular endpoint. -/
theorem hasDerivAt_primitive {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt primitive (Real.log |v|) v := by
  simp_rw [funext primitive_eq]
  simpa using! (Real.hasDerivAt_mul_log hv).sub (hasDerivAt_id v)

/-- Exact segment potential, valid inside, outside, and at both endpoints.
This is the C-A `F` endpoint-difference rule of docs/6333, section 5. -/
theorem integral_log_abs_sub (x a b : ℝ) :
    (∫ y in a..b, Real.log |x - y|) =
      primitive (x - a) - primitive (x - b) := by
  simp_rw [Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_left Real.log x, integral_log]
  simp only [primitive_eq]
  ring

/-- Reflected segment potential, including its zero endpoint convention. -/
theorem integral_log_add (t a b : ℝ) :
    (∫ y in a..b, Real.log (t + y)) =
      primitive (t + b) - primitive (t + a) := by
  rw [intervalIntegral.integral_comp_add_left Real.log t, integral_log]
  simp only [primitive_eq]
  ring

/-- Absolute logarithms remain integrable even when the cell contains `x`. -/
theorem intervalIntegrable_log_abs_sub (x a b : ℝ) :
    IntervalIntegrable (fun y => Real.log |x - y|) volume a b := by
  simpa only [Real.log_abs, sub_sub_cancel] using
    (intervalIntegral.intervalIntegrable_log' (a := x - a) (b := x - b)).comp_sub_left x

/-- Half-open and closed cell conventions have the same logarithmic potential. -/
theorem integral_Ico_log_abs_sub (x : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ y in Set.Ico a b, Real.log |x - y|) =
      primitive (x - a) - primitive (x - b) := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le hab, integral_log_abs_sub]

/-- Integrability for the literal half-open cell measure in v10. -/
theorem integrableOn_Ico_log_abs_sub (x : ℝ) {a b : ℝ} (hab : a ≤ b) :
    IntegrableOn (fun y => Real.log |x - y|) (Set.Ico a b) volume :=
  (intervalIntegrable_iff_integrableOn_Ico_of_le hab).mp
    (intervalIntegrable_log_abs_sub x a b)

/-- Derivative of the exact segment potential away from its two endpoints. -/
theorem hasDerivAt_integral_log_abs_sub {x a b : ℝ}
    (ha : x ≠ a) (hb : x ≠ b) :
    HasDerivAt (fun z => ∫ y in a..b, Real.log |z - y|)
      (Real.log |x - a| - Real.log |x - b|) x := by
  have hleft := (hasDerivAt_primitive (sub_ne_zero.mpr ha)).comp x
    ((hasDerivAt_id x).sub_const a)
  have hright := (hasDerivAt_primitive (sub_ne_zero.mpr hb)).comp x
    ((hasDerivAt_id x).sub_const b)
  simpa only [one_mul, mul_one, integral_log_abs_sub] using! hleft.sub hright

/-- Continuity of the actual integral potential, including all cell endpoints. -/
theorem continuous_integral_log_abs_sub (a b : ℝ) :
    Continuous (fun x => ∫ y in a..b, Real.log |x - y|) := by
  simp_rw [integral_log_abs_sub]
  exact (continuous_primitive.comp (continuous_id.sub continuous_const)).sub
    (continuous_primitive.comp (continuous_id.sub continuous_const))

/-- Derivative of a reflected real cell, on the entire positive-frequency tail. -/
theorem hasDerivAt_integral_log_add {t a b : ℝ}
    (ha : t + a ≠ 0) (hb : t + b ≠ 0) :
    HasDerivAt (fun z => ∫ y in a..b, Real.log (z + y))
      (Real.log (t + b) - Real.log (t + a)) t := by
  have hleft := (hasDerivAt_primitive hb).comp t
    ((hasDerivAt_id t).add_const b)
  have hright := (hasDerivAt_primitive ha).comp t
    ((hasDerivAt_id t).add_const a)
  simpa only [one_mul, mul_one, Real.log_abs, integral_log_add] using! hleft.sub hright

end

end Li2Lean.LogSegment
