/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Bridges
import Li2Lean.L1

namespace Li2Lean

/--
The all-n target follows from the eight range-specific bridge statements in
docs/6404 §1. The bridge is explicit, so this conditional theorem makes no
unconditional all-n claim.
-/
theorem li2_inv_irrational_of_bridges (bridges : Li2Bridges)
    (n : ℤ) (hn : n ≠ 0) : Irrational (li2InvValue n) := by
  by_cases hposOne : n = 1
  · subst n
    exact bridges.pos_one
  by_cases hnegOne : n = -1
  · subst n
    exact bridges.neg_one
  by_cases hposTwo : n = 2
  · subst n
    rcases bridges.pos_two with ⟨certificate⟩
    exact l1_endpoint_criterion (li2InvValue (2 : ℤ)) certificate
  by_cases hnegTwo : n = -2
  · subst n
    exact bridges.neg_two
  by_cases hposMiddle : (3 : ℤ) ≤ n ∧ n ≤ 11
  · exact bridges.pos_middle n hposMiddle.1 hposMiddle.2 hn
  by_cases hnegMiddle : (-7 : ℤ) ≤ n ∧ n ≤ -3
  · exact bridges.neg_middle n hnegMiddle.1 hnegMiddle.2 hn
  by_cases hposTail : (12 : ℤ) ≤ n
  · exact bridges.pos_tail n hposTail hn
  by_cases hnegTail : n ≤ (-8 : ℤ)
  · exact bridges.neg_tail n hnegTail hn
  · omega

/--
The `n = 2` instance of the same conditional target, corresponding to
docs/6404 §1 and docs/6333 §1.
-/
theorem li2_half_irrational_of_bridges (bridges : Li2Bridges) :
    Irrational (li2InvValue (2 : ℤ)) :=
  let ⟨certificate⟩ := bridges.pos_two
  l1_endpoint_criterion (li2InvValue (2 : ℤ)) certificate

end Li2Lean
