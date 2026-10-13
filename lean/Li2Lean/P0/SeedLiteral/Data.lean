/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
namespace Li2Lean.P0.SeedLiteral

open Matrix

instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

abbrev F83 := ZMod 83
abbrev Mat64 := Matrix (Fin 64) (Fin 64) F83
end Li2Lean.P0.SeedLiteral
