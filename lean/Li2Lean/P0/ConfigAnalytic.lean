/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.P0.ConfigAnalytic

/-- The v10 C-A enclosure for `log 2`, proved from the finite logarithm
series and its geometric remainder (docs/6333, section 5, (5.7)--(5.9)). -/
theorem logTwoEnclosure_v10 :
    (693 / 1000 : ℝ) < Real.log 2 ∧
      Real.log 2 < 6931473 / 10000000 := by
  constructor
  · have hseries := Real.sum_range_le_log_div
      (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 3
    have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ))) = 2 := by norm_num
    rw [hratio] at hseries
    have hfinite : (693 / 1000 : ℝ) <
        2 * (∑ k ∈ Finset.range 3,
          (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * k + 1)) := by
      norm_num [Finset.sum_range_succ]
    nlinarith
  · have hseries := Real.log_div_le_sum_range_add
      (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 8
    have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ))) = 2 := by norm_num
    rw [hratio] at hseries
    have hfinite :
        2 * ((∑ k ∈ Finset.range 8,
          (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * k + 1)) +
          (1 / 3 : ℝ) ^ (2 * 8 + 1) / (1 - (1 / 3 : ℝ) ^ 2)) <
          (6931473 / 10000000 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    nlinarith

end Li2Lean.P0.ConfigAnalytic
