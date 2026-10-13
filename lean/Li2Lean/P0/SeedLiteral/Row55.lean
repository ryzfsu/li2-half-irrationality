/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.Factors
namespace Li2Lean.P0.SeedLiteral

set_option maxRecDepth 1000000
set_option maxHeartbeats 5000000 in
theorem p0_row55 (j : Fin 64) :
    aMat (55 : Fin 64) j = (lMat * uMat) (55 : Fin 64) j := by
  fin_cases j <;> decide +kernel
end Li2Lean.P0.SeedLiteral
