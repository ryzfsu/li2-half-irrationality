/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.NonvanishingScaledLucas

namespace Li2Lean

noncomputable section

theorem l4_a2_fixed_tower_of_scaledLucas :
    ∀ F : P0Family, P0A2NonvanishingStatement F :=
  fun F => P0.ScaledLucas.p0A2_nonvanishing F

end

end Li2Lean
