/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean

/--
The exact real series in the all-n target. This is the definition used in
docs/6404, §1 and docs/6406, §2 (L0).
-/
noncomputable def li2InvValue (n : ℤ) : ℝ :=
  ∑' k : ℕ, ((n : ℝ)⁻¹) ^ (k + 1) / ((k : ℝ) + 1) ^ 2

/--
The unconditional theorem target from docs/6408, §1. It remains a proposition
in S0 and is not asserted as proved.
-/
noncomputable def li2InvIrrationalStatement : Prop :=
  ∀ n : ℤ, n ≠ 0 → Irrational (li2InvValue n)

end Li2Lean
