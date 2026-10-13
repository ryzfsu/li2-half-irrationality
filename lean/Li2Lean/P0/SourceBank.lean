/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Source

namespace Li2Lean

noncomputable section

/-! The zero-order specialization is a complete unconditional leaf of the
    parameter derivative-bank identity. It compares the exact source
    definitions at every base and every pair of indices. -/

theorem sourceDg_zero (f : ℝ → ℝ) (a : ℝ) :
    sourceDg 0 f a = f a := by
  simp [sourceDg]

/-- The literal derivative-bank identity at derivative order zero. -/
theorem sourceBank_zero (a : ℝ) (i j : ℕ) :
    sourceDgM 0 i j a =
      sourceB a 0 i j + sourceLog a * sourceC a 0 i j -
        sourceBeta a * sourceA a 0 i j := by
  rw [sourceDgM, sourceDg_zero]
  by_cases hij : i = j
  · subst j
    simp [sourceM, sourceB, sourceBdiag, sourceC, sourceA, sourceU,
      sourceQ, sourceB0, sourceB0ij, sourceC0, sourceA0]
  · simp [sourceM, sourceB, sourceC, sourceA, sourceU,
      sourceT, sourceQ, sourceT0, sourceB0ij, sourceC0,
      sourceA0, hij]

end

end Li2Lean
