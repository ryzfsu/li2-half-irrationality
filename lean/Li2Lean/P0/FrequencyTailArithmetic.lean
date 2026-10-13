/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.FrequencyTail

namespace Li2Lean.P0.FrequencyTailArithmetic

noncomputable section

/-- The exponential base in the scalar estimate for `b_m` in §7. -/
def geometricTailBase : ℝ := (50000 : ℝ) * (8 / 15 : ℝ) ^ 20

/-- The explicit numerical upper bound for `b_m` in §7. -/
def paperTailBound (m : ℕ) : ℝ :=
  (15 * (m : ℝ) / 1600) * geometricTailBase ^ m

theorem geometricTailBase_lt_quarter : geometricTailBase < 1 / 4 := by
  norm_num [geometricTailBase]

theorem natCast_le_two_pow (m : ℕ) : (m : ℝ) ≤ (2 : ℝ) ^ m := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [Nat.cast_succ, pow_succ]
      have hpow : (1 : ℝ) ≤ (2 : ℝ) ^ m := one_le_pow₀ (by norm_num)
      nlinarith

/-- The exact rational-series constants imply the dyadic allowance in `FrequencyTail`. -/
theorem paperTailBound_le_dyadicBudget (m : ℕ) :
    paperTailBound m ≤ (3 / 320 : ℝ) * (1 / 2 : ℝ) ^ m := by
  have hpow : geometricTailBase ^ m ≤ (1 / 4 : ℝ) ^ m := by
    exact pow_le_pow_left₀ (by norm_num [geometricTailBase])
      (le_of_lt geometricTailBase_lt_quarter) m
  have hsmall : (m : ℝ) * (1 / 4 : ℝ) ^ m ≤ (1 / 2 : ℝ) ^ m := by
    calc
      (m : ℝ) * (1 / 4 : ℝ) ^ m ≤ (2 : ℝ) ^ m * (1 / 4 : ℝ) ^ m :=
        mul_le_mul_of_nonneg_right (natCast_le_two_pow m) (by positivity)
      _ = (1 / 2 : ℝ) ^ m := by rw [← mul_pow]; norm_num
  unfold paperTailBound
  calc
    (15 * (m : ℝ) / 1600) * geometricTailBase ^ m ≤
        (15 * (m : ℝ) / 1600) * (1 / 4 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_left hpow (by positivity)
    _ = (3 / 320 : ℝ) * ((m : ℝ) * (1 / 4 : ℝ) ^ m) := by ring
    _ ≤ (3 / 320 : ℝ) * (1 / 2 : ℝ) ^ m :=
      mul_le_mul_of_nonneg_left hsmall (by norm_num)

theorem paperTailBound_le_replacementTailRatio (m : ℕ) :
    paperTailBound m ≤ Li2Lean.P0.FrequencyTail.replacementTailRatio m := by
  simpa [Li2Lean.P0.FrequencyTail.replacementTailRatio] using
    paperTailBound_le_dyadicBudget m

theorem dyadicBudget_lt_half (m : ℕ) :
    (3 / 320 : ℝ) * (1 / 2 : ℝ) ^ m < 1 / 2 := by
  have hpow := Li2Lean.P0.FrequencyTail.half_pow_le_one m
  calc
    (3 / 320 : ℝ) * (1 / 2 : ℝ) ^ m ≤ 3 / 320 := by
      calc
        (3 / 320 : ℝ) * (1 / 2 : ℝ) ^ m ≤ (3 / 320 : ℝ) * 1 :=
          mul_le_mul_of_nonneg_left hpow (by norm_num)
        _ = 3 / 320 := by ring
    _ < 1 / 2 := by norm_num

theorem paperTailBound_lt_half (m : ℕ) : paperTailBound m < 1 / 2 := by
  exact lt_of_le_of_lt (paperTailBound_le_dyadicBudget m) (dyadicBudget_lt_half m)

/-- Any `b_m` satisfying the displayed scalar estimate is a valid contraction coefficient. -/
theorem scalarTailCoefficient_lt_half {m : ℕ} {b_m : ℝ}
    (hb : b_m ≤ paperTailBound m) : b_m < 1 / 2 :=
  lt_of_le_of_lt hb (paperTailBound_lt_half m)

end

end Li2Lean.P0.FrequencyTailArithmetic
