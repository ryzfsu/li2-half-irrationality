/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyLiteralRowENNReal

open scoped BigOperators ENNReal

namespace Li2Lean.P0.FrequencyLimit

noncomputable section

/-- Admissible cutoff heights use the literal first frequency `g + 1`. -/
abbrev PaperFrequencyCutoffHeight (m : ℕ) := {H : ℕ // m / 2 + 1 ≤ H}

/-- The paper's standard cutoff `20m`, packaged with its lower-endpoint proof. -/
def p0FrequencyCutoffHeight (m : ℕ) (hm : 0 < m) : PaperFrequencyCutoffHeight m :=
  ⟨20 * m, by omega⟩

/-- Every coordinate of a truncated tuple lies in the paper interval `(g,H]`. -/
theorem truncatedFrequencyCoordinate_mem_Ioc
    {m : ℕ} (H : PaperFrequencyCutoffHeight m)
    (r : TruncatedFrequencyTuple (m / 2) m H.1) (i : Fin m) :
    (r.1 i).1 ∈ Finset.Ioc (m / 2) H.1 := by
  rw [Finset.mem_Ioc]
  exact ⟨r.2.2 i, Nat.lt_succ_iff.mp (r.1 i).2⟩

/-- The exact multiplicative tail factor in v13's frequency cutoff estimate. -/
def actualFrequencyTailFactor (m : ℕ) : ℝ :=
  1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m

/-- The tail factor is bounded by the exponential of its exact small exponent. -/
theorem actualFrequencyTailFactor_le_exp (m : ℕ) :
    actualFrequencyTailFactor m ≤
      Real.exp ((3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) := by
  have h := Real.add_one_le_exp ((3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m)
  simpa [actualFrequencyTailFactor, add_comm] using h

/-- For every `m`, the tail exponent fits inside the existing `1/3` allowance. -/
theorem actualFrequencyTailExponent_le_one_third (m : ℕ) :
    (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m ≤ 1 / 3 := by
  have hp := FrequencyTail.half_pow_le_one m
  have hmul := mul_le_mul_of_nonneg_left hp
    (by norm_num : (0 : ℝ) ≤ 3 / 160)
  calc
    (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m ≤ 3 / 160 := by
      simpa only [mul_one] using hmul
    _ ≤ 1 / 3 := by norm_num

/-- A uniform form that can be absorbed into the coefficient exponent budget. -/
theorem actualFrequencyTailFactor_le_exp_one_third (m : ℕ) :
    actualFrequencyTailFactor m ≤ Real.exp (1 / 3 : ℝ) := by
  exact (actualFrequencyTailFactor_le_exp m).trans
    (Real.exp_le_exp.mpr (actualFrequencyTailExponent_le_one_third m))

/-- The literal full envelope has the actual paper tail factor at the admissible
cutoff height `20m`; no arbitrary coefficient-tail field is introduced. -/
theorem full_cutoffENN_actual_tail_factor (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    EInfinityENN m h4 ≠ ⊤ ∧
      EInfinityENN m h4 ≤
        ENNReal.ofReal
          (actualFrequencyTailFactor m * E m (p0FrequencyCutoffHeight m hm).1 h4) := by
  simpa [actualFrequencyTailFactor, p0FrequencyCutoffHeight] using
    full_cutoffENN_of_contourFactor m hm h4

/-- The multiplicative cutoff factor consumes at most `1/3` in the final
coefficient exponent once the finite cutoff envelope is bounded. -/
theorem actualFrequencyTailFactor_mul_exp_le (m : ℕ) (B : ℝ) :
    actualFrequencyTailFactor m * Real.exp B ≤ Real.exp (B + 1 / 3) := by
  calc
    actualFrequencyTailFactor m * Real.exp B ≤
        Real.exp (1 / 3 : ℝ) * Real.exp B :=
      mul_le_mul_of_nonneg_right (actualFrequencyTailFactor_le_exp_one_third m)
        (Real.exp_nonneg B)
    _ = Real.exp (B + 1 / 3) := by rw [← Real.exp_add]; congr 1; ring

end

end Li2Lean.P0.FrequencyLimit

#print axioms Li2Lean.P0.FrequencyLimit.truncatedFrequencyCoordinate_mem_Ioc
#print axioms Li2Lean.P0.FrequencyLimit.actualFrequencyTailFactor_le_exp
#print axioms Li2Lean.P0.FrequencyLimit.actualFrequencyTailExponent_le_one_third
#print axioms Li2Lean.P0.FrequencyLimit.actualFrequencyTailFactor_le_exp_one_third
#print axioms Li2Lean.P0.FrequencyLimit.full_cutoffENN_actual_tail_factor
#print axioms Li2Lean.P0.FrequencyLimit.actualFrequencyTailFactor_mul_exp_le
