/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FinalEnvelopeWiring

/-- Solution for the comparator challenge. -/
theorem li2_half_irrational :
    Irrational (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
  simpa [Li2Lean.li2InvValue] using
    Li2Lean.li2_half_irrational_unconditional
