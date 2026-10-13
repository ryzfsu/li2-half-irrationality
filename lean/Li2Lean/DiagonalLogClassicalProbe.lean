/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourAnalytic
import Mathlib.Analysis.SpecialFunctions.Integrability.Log

open MeasureTheory
open Li2Lean.P0.ConfigContourAnalytic

namespace DiagonalLogClassicalProbe

noncomputable section

private theorem circleZeta_eq_circleMap (u : ℝ) :
    circleZeta u = circleMap 0 1 u := by
  unfold circleZeta circleMap
  simp only [zero_add]
  change Complex.exp (Complex.I * (u : ℂ)) =
    (1 : ℂ) * Complex.exp ((u : ℂ) * Complex.I)
  rw [show Complex.I * (u : ℂ) = (u : ℂ) * Complex.I by ring]
  simp

/-- The diagonal logarithmic circle kernel is interval-integrable for every
parameter, including the collision point.  This is inherited directly from
mathlib's meromorphic log-integrability theorem for a circle. -/
theorem diagonalLogKernel_intervalIntegrable (v : ℝ) :
    IntervalIntegrable (fun u => diagonalLogKernel u v) volume 0 (2 * Real.pi) := by
  have h := circleIntegrable_log_norm_sub_const (c := (0 : ℂ))
    (a := circleZeta v) (1 : ℝ)
  rw [circleIntegrable_def] at h
  have h' : IntervalIntegrable
      (fun u => Real.log ‖circleZeta u - circleZeta v‖)
      volume 0 (2 * Real.pi) := by
    convert h using 1
    funext u
    rw [circleZeta_eq_circleMap u]
  exact h'

#print axioms diagonalLogKernel_intervalIntegrable

end
end DiagonalLogClassicalProbe
