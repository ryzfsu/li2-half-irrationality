/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ControlledResidue

namespace Li2Lean.P0.ControlledResidue

theorem residueOf_eq_ratCast (q : ℚ) (hcop : Nat.Coprime q.den 83) :
    residueOf q hcop = (q : F83) := by
  unfold residueOf
  rw [Rat.cast_def, div_eq_mul_inv]

#print axioms residueOf_eq_ratCast

end Li2Lean.P0.ControlledResidue
