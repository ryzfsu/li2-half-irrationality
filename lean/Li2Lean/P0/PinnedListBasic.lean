/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
open scoped BigOperators
namespace Li2Lean.P0.PinnedListBasic
noncomputable section
def evalL (x : ℝ) : List ℚ → ℝ
  | [] => 0
  | c :: p => (c : ℝ) + x * evalL x p

theorem evalL_map (x : ℝ) (c : ℚ) (p : List ℚ) :
    evalL x (p.map (c * ·)) = (c : ℝ) * evalL x p := by
  induction p with
  | nil => simp [evalL]
  | cons a p ih => simp [evalL, ih]; ring

theorem evalL_sum (x : ℝ) (p : List ℚ) :
    evalL x p = ∑ k ∈ Finset.range p.length, (p.getD k 0 : ℝ) * x ^ k := by
  induction p with
  | nil => simp [evalL]
  | cons a p ih =>
    simp only [List.length_cons, Finset.sum_range_succ', List.getD_cons_zero,
      List.getD_cons_succ, pow_zero, mul_one, evalL, ih]
    rw [Finset.mul_sum]
    conv_rhs => rw [add_comm]
    congr 1
    apply Finset.sum_congr rfl
    intro k hk
    rw [pow_succ]
    ring
end
end Li2Lean.P0.PinnedListBasic
