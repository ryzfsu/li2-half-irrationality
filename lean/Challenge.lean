/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
Comparator challenge: Li₂(1/2) is irrational.
Mathlib-only statement, no project imports, no premises. The proof is `sorry` by design;
the comparator checks that the root-namespace `li2_half_irrational` in `Solution.lean` has exactly this type and uses only
`propext`, `Quot.sound`, `Classical.choice`.
Li₂(1/2) = ∑_{k ≥ 1} 2^{-k} / k² = ∑_{k ≥ 0} (1/2)^(k+1) / (k+1)².
-/

theorem li2_half_irrational :
    Irrational (∑' k : ℕ, ((2 : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
  sorry
