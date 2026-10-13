/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.LogRectangle
import Li2Lean.P0.CA.Pinned.LogEval

namespace Li2Lean.P0.ConfigRectangleBounds
open Li2Lean.P0.CA.Pinned Li2Lean.LogSegment
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def HI (q : ℚ) : QI :=
  if q = 0 then QI.pt 0 else
    QI.sub (QI.smul (q^2/2) (logI |q|)) (QI.pt (3*q^2/4))

theorem HI_sound (q : ℚ) : (HI q).Contains (secondPrimitive (q : ℝ)) := by
  unfold HI
  split_ifs with hq
  · subst q; simpa using QI.mem_pt (0 : ℚ)
  · have h := QI.mem_sub (QI.mem_smul (q^2/2) (logI_sound (abs_pos.mpr hq)))
      (QI.mem_pt (3*q^2/4))
    convert h using 1 <;> push_cast <;> simp only [secondPrimitive] <;> ring

def sumIdx : ℕ → (ℕ → QI) → QI
  | 0, _ => QI.pt 0
  | n+1, f => QI.add (sumIdx n f) (f n)

theorem sumIdx_sound {n : ℕ} {f : ℕ → QI} {r : ℕ → ℝ}
    (h : ∀ j < n, (f j).Contains (r j)) :
    (sumIdx n f).Contains (∑ j ∈ Finset.range n, r j) := by
  induction n with
  | zero => simpa [sumIdx] using QI.mem_pt (0 : ℚ)
  | succ n ih =>
    rw [sumIdx, Finset.sum_range_succ]
    exact QI.mem_add (ih (fun j hj => h j (by omega))) (h n (by omega))

end Li2Lean.P0.ConfigRectangleBounds
