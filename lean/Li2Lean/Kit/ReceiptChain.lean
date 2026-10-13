/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Data.Rat.Init

/-!
Pure rational receipt data and exact finite-cover proofs for Appendix A, C-A.
This module intentionally has no real analysis dependency. The declarations
retain their existing names and exact statements; real coverage and analytic
Taylor soundness remain in `Li2Lean.Agents.F_L8.Types`.
-/

namespace Li2Lean.F_L8

/--
One exact rational row in the directed cell tables of docs/6333, §5 C-A.
The `lower` field is input data; this structure does not assert that a
transcendental potential lies above it.
-/
structure ReceiptCell where
  lo : ℚ
  hi : ℚ
  lower : ℚ
  deriving DecidableEq, Repr

/-- Exact adjacency and positive width for a nonempty finite rational cover. -/
inductive ExactChain : List ReceiptCell → ℚ → ℚ → Prop
  | one (c : ReceiptCell) (left right : ℚ)
      (hleft : c.lo = left) (hright : c.hi = right) (hwidth : c.lo ≤ c.hi) :
      ExactChain [c] left right
  | more (c d : ReceiptCell) (rest : List ReceiptCell) (left right : ℚ)
      (hleft : c.lo = left) (hadj : c.hi = d.lo) (hwidth : c.lo ≤ c.hi)
      (htail : ExactChain (d :: rest) d.lo right) :
      ExactChain (c :: d :: rest) left right

/-- Recursive specification retained for comparison with the original definition. -/
def ExactChainSpec : List ReceiptCell → ℚ → ℚ → Prop
  | [], _, _ => False
  | [c], a, b => c.lo = a ∧ c.hi = b ∧ c.lo ≤ c.hi
  | c :: d :: rest, a, b =>
      c.lo = a ∧ c.hi = d.lo ∧ c.lo ≤ c.hi ∧ ExactChainSpec (d :: rest) d.lo b

theorem exactChain_iff_spec {cells : List ReceiptCell} {left right : ℚ} :
    ExactChain cells left right ↔ ExactChainSpec cells left right := by
  induction cells generalizing left right with
  | nil =>
      constructor
      · intro h
        cases h
      · simp [ExactChainSpec]
  | cons c rest ih =>
      cases rest with
      | nil =>
          constructor
          · intro h
            cases h with
            | one _ _ _ hleft hright hwidth =>
                simpa [ExactChainSpec] using And.intro hleft (And.intro hright hwidth)
          · intro h
            simp only [ExactChainSpec] at h
            rcases h with ⟨hleft, hright, hwidth⟩
            exact ExactChain.one c left right hleft hright hwidth
      | cons d tail =>
          constructor
          · intro h
            cases h with
            | more _ _ _ _ _ hleft hadj hwidth htail =>
                simpa [ExactChainSpec] using
                  And.intro hleft (And.intro hadj (And.intro hwidth (ih.mp htail)))
          · intro h
            simp only [ExactChainSpec] at h
            rcases h with ⟨hleft, hadj, hwidth, htail⟩
            exact ExactChain.more c d tail left right hleft hadj hwidth
              (ih.mpr htail)

theorem exactChain_headLo {c : ReceiptCell} {rest : List ReceiptCell}
    {left right : ℚ} (h : ExactChain (c :: rest) left right) : c.lo = left := by
  cases h <;> assumption

/-- Concatenating adjacent checked chains preserves the exact cover. -/
theorem exactChain_append {xs ys : List ReceiptCell} {left mid right : ℚ}
    (hne : ys ≠ []) (hx : ExactChain xs left mid)
    (hy : ExactChain ys mid right) : ExactChain (xs ++ ys) left right := by
  induction hx with
  | one c left mid hleft hmid hwidth =>
      cases ys with
      | nil => exact False.elim (hne rfl)
      | cons d ysRest =>
          have hd := exactChain_headLo hy
          apply ExactChain.more c d ysRest left right hleft ?_ hwidth ?_
          · calc
              c.hi = mid := hmid
              _ = d.lo := hd.symm
          · rw [hd]
            exact hy
  | more c d rest left mid hleft hadj hwidth htail ih =>
      simpa only [List.cons_append] using
        (ExactChain.more c d (rest ++ ys) left right hleft hadj hwidth (ih hy))

/-- Every checked chain is nonempty, without unfolding any certificate data. -/
theorem exactChain_ne_nil {cells : List ReceiptCell} {left right : ℚ}
    (h : ExactChain cells left right) : cells ≠ [] := by
  cases h <;> simp

/-- Compose checked shards without expanding a shard to prove nonemptiness. -/
theorem exactChain_join {xs ys : List ReceiptCell} {left mid right : ℚ}
    (hx : ExactChain xs left mid) (hy : ExactChain ys mid right) :
    ExactChain (xs ++ ys) left right :=
  exactChain_append (exactChain_ne_nil hy) hx hy

end Li2Lean.F_L8
