/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.ActualSourceBlock8

namespace Li2Lean.P0.SeedLiteral

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

@[simp] theorem actualSeed_row33 (c : Fin 64) :
    actualSeedEntry (33 : Fin 64) c = (((aTable[33]!)[c.val]! : Nat) : F83) := by
  fin_cases c
  all_goals rw [actualSeedEntry_bottom_formula _ _ (by decide)]
  all_goals apply ZMod.val_injective 83
  all_goals decide +kernel

#print axioms actualSeed_row33

end Li2Lean.P0.SeedLiteral
