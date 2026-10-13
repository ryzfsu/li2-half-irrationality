/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.P0.FrequencyTail

noncomputable section

/--
The relative tail allowance in docs/6333 §7, (7.1)--(7.4), after the
replacement and geometric-tail estimates: the finite replacement argument
aims to show `tail <= ratio m * (head + tail)` with this exact constant.
The q-uniform comparison discussed in docs/6406 preserves this q=2 bound.
-/
def replacementTailRatio (m : ℕ) : ℝ := (3 / 320 : ℝ) * (1 / 2 : ℝ) ^ m

/-- Algebraic absorption used after the paper's frequency replacement map. -/
theorem absorbTail {head tail q : ℝ}
    (htail : 0 ≤ tail)
    (hqhalf : q ≤ 1 / 2)
    (hbound : tail ≤ q * (head + tail)) :
    head + tail ≤ (1 + 2 * q) * head := by
  have hrel : (1 - q) * tail ≤ q * head := by nlinarith
  have hhalf : (1 / 2 : ℝ) * tail ≤ (1 - q) * tail := by
    apply mul_le_mul_of_nonneg_right _ htail
    linarith
  have htail' : tail ≤ 2 * q * head := by nlinarith
  calc
    head + tail ≤ head + 2 * q * head := by
      simpa [add_comm] using add_le_add_left htail' head
    _ = (1 + 2 * q) * head := by ring

theorem half_pow_nonneg (m : ℕ) : 0 ≤ (1 / 2 : ℝ) ^ m :=
  pow_nonneg (by norm_num) m

theorem half_pow_le_one (m : ℕ) : (1 / 2 : ℝ) ^ m ≤ 1 := by
  induction m with
  | zero => norm_num
  | succ m ih =>
      rw [pow_succ]
      calc
        (1 / 2 : ℝ) ^ m * (1 / 2 : ℝ) ≤ 1 * (1 / 2 : ℝ) :=
          mul_le_mul_of_nonneg_right ih (by norm_num)
        _ ≤ 1 := by norm_num

theorem replacementTailRatio_nonneg (m : ℕ) : 0 ≤ replacementTailRatio m := by
  unfold replacementTailRatio
  positivity

theorem replacementTailRatio_le_half (m : ℕ) : replacementTailRatio m ≤ 1 / 2 := by
  have hpow := half_pow_le_one m
  unfold replacementTailRatio
  nlinarith [mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 3 / 320)]

/--
The exact coefficient conversion in docs/6333 §7, (7.1): twice the
replacement budget is the displayed `(3/160) 2^{-m}` term, represented in
Lean as `(3/160) * (1/2)^m`.
-/
theorem cutoffFactor_eq (m : ℕ) :
    1 + 2 * replacementTailRatio m =
      1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m := by
  unfold replacementTailRatio
  ring

/-- The final finite-cutoff absorption step of docs/6333 §7, (7.1).
The replacement-map estimate and the pointwise contour-integrand estimate
are separate obligations; this lemma does not assume either is proved. -/
theorem finiteCutoff_absorption {m : ℕ} {head tail : ℝ}
    (htail : 0 ≤ tail)
    (hreplacement : tail ≤ replacementTailRatio m * (head + tail)) :
    head + tail ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * head := by
  rw [← cutoffFactor_eq m]
  exact absorbTail htail (replacementTailRatio_le_half m) hreplacement

end

end Li2Lean.P0.FrequencyTail
