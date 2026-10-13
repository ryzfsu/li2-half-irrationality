/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigLogTaylor
import Li2Lean.P0.ConfigAnalytic
import Mathlib.Analysis.Real.Pi.Bounds

namespace Li2Lean.P0.ConfigCstarNumeric

open Li2Lean.P0.ConfigLogTaylor

/-- Six odd rational-series terms enclose the first reduced logarithm
in the v10 `eq:config-cstar` constant. -/
theorem log_eleven_sevenths_upper_v10 :
    Real.log (11 / 7 : ℝ) < (451986 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := 11 / 7) (upper := 451986 / 1000000)
    (by norm_num) 6 (by
      norm_num [logPolynomial, logRemainder, logCoordinate, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

/-- A directed rational-series bound for the range-reduced `log 336`. -/
theorem log_twentyone_sixteenths_upper_v10 :
    Real.log (21 / 16 : ℝ) < (271934 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := 21 / 16) (upper := 271934 / 1000000)
    (by norm_num) 6 (by
      norm_num [logPolynomial, logRemainder, logCoordinate, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

/-- A directed rational-series bound for the range-reduced `log (35/3)`. -/
theorem log_thirtyfive_twentyfourths_upper_v10 :
    Real.log (35 / 24 : ℝ) < (377295 / 1000000 : ℝ) := by
  have h := log_lt_of_rational (q := 35 / 24) (upper := 377295 / 1000000)
    (by norm_num) 6 (by
      norm_num [logPolynomial, logRemainder, logCoordinate, Finset.sum_range_succ])
  norm_num at h ⊢
  exact h

/-- The full literal v10 `eq:config-cstar` numerical inequality. The two
ellipse clearances and all coefficients are unchanged; all transcendental
enclosures are theorems, with no supplied analytic-bound hypotheses. -/
theorem cstar_expression_lt_v10 :
    4 * Real.log (2 * Real.pi) + 9 + (21 / 2 : ℝ) * Real.log 2 +
      Real.log 336 + Real.log (35 / 3 : ℝ) +
      5 / (2 * (751 / 5000 : ℝ)) + 1 / (2 * (1749 / 5000 : ℝ)) <
      (49979 / 1000 : ℝ) := by
  have hpi : Real.pi < (22 / 7 : ℝ) := by
    linarith [Real.pi_lt_d4]
  have hlogpi : Real.log (2 * Real.pi) < Real.log (44 / 7 : ℝ) :=
    Real.log_lt_log (by positivity) (by linarith)
  have h44 : Real.log (44 / 7 : ℝ) =
      2 * Real.log 2 + Real.log (11 / 7 : ℝ) := by
    have heq : (44 / 7 : ℝ) = 2 ^ 2 * (11 / 7) := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h336 : Real.log (336 : ℝ) =
      8 * Real.log 2 + Real.log (21 / 16 : ℝ) := by
    have heq : (336 : ℝ) = 2 ^ 8 * (21 / 16) := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  have h35 : Real.log (35 / 3 : ℝ) =
      3 * Real.log 2 + Real.log (35 / 24 : ℝ) := by
    have heq : (35 / 3 : ℝ) = 2 ^ 3 * (35 / 24) := by norm_num
    rw [heq, Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [h44] at hlogpi
  rw [h336, h35]
  have hlogtwo := Li2Lean.P0.ConfigAnalytic.logTwoEnclosure_v10.2
  have h11 := log_eleven_sevenths_upper_v10
  have h21 := log_twentyone_sixteenths_upper_v10
  have h35' := log_thirtyfive_twentyfourths_upper_v10
  norm_num at *
  linarith

end Li2Lean.P0.ConfigCstarNumeric
