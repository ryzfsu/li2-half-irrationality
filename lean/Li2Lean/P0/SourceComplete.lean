/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SourceBank
import Li2Lean.P0.SourceMellin

namespace Li2Lean

/-! This conjunction records the unconditional leaves currently closed in the
    v10 source section: the complete Mellin statement and the derivative-bank
    identity at order zero. It does not assert the open all-orders bank lemma. -/
theorem sourceSectionLeavesProved :
    sourceMellinStatement ∧
      (∀ a : ℝ, ∀ i j : ℕ,
        sourceDgM 0 i j a =
          sourceB a 0 i j + sourceLog a * sourceC a 0 i j -
            sourceBeta a * sourceA a 0 i j) := by
  constructor
  · exact sourceMellinStatement_proved
  · intro a i j
    exact sourceBank_zero a i j

#print axioms sourceSectionLeavesProved
#print axioms sourceMellinStatement_proved
#print axioms sourceDg_zero
#print axioms sourceBank_zero

end Li2Lean
