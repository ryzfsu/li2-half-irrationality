/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.ReceiptChain
import Li2Lean.Kit.IntervalChecker

namespace Li2Lean.F_L8

open ContourKit

/--
The constant Taylor model attached to a C-A row. Its zero remainder makes the
analytic obligation explicit: the target function must be at least `lower` on
the whole cell.
-/
def ReceiptCell.model (c : ReceiptCell) (h : c.lo ≤ c.hi) : TaylorCell :=
  { domain := ⟨c.lo, c.hi, h⟩
    center := (c.lo + c.hi) / 2
    coefficients := [c.lower]
    remainder := 0 }

/-- The rational checker accepts the exact cell lower bound. -/
theorem ReceiptCell.model_checked (c : ReceiptCell) (h : c.lo ≤ c.hi) :
    checkTaylorCell c.lower (c.model h) = true := by
  simp [checkTaylorCell, ReceiptCell.model, TaylorCell.polynomialRange,
    intervalHorner, QInterval.point, QInterval.add, QInterval.mul,
    QInterval.radius, shift]

/--
The one-sided Taylor remainder obligation for the constant model of a C-A row.
This is exactly the cellwise analytic bound still to be proved from the
potential formulas in docs/6333, §5 C-A (5.1), (5.5), and (5.6).
-/
def ReceiptCell.modelRemainderValid (f : ℝ → ℝ) (c : ReceiptCell)
    (h : c.lo ≤ c.hi) : Prop :=
  TaylorLowerRemainderValid f (c.model h)

/-- The interval checker turns a supplied row remainder proof into its bound. -/
theorem ReceiptCell.sound (c : ReceiptCell) (h : c.lo ≤ c.hi)
    {f : ℝ → ℝ} (hrem : c.modelRemainderValid f h) {x : ℝ}
    (hxlo : (c.lo : ℝ) ≤ x) (hxhi : x ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ f x := by
  exact checkTaylorCell_lower_sound (c.model_checked h) hrem ⟨hxlo, hxhi⟩

/-- An exact rational cell chain covers every real point between its endpoints. -/
theorem exactChain_covers {cells : List ReceiptCell} {a b : ℚ}
    (hchain : ExactChain cells a b) :
    ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
      ∃ c, c ∈ cells ∧ c.lo ≤ c.hi ∧ (c.lo : ℝ) ≤ x ∧ x ≤ (c.hi : ℝ) := by
  induction hchain with
  | one c a b hleft hright hwidth =>
      intro x hax hxb
      rw [← hleft] at hax
      rw [← hright] at hxb
      exact ⟨c, by simp, hwidth, hax, hxb⟩
  | more c d rest a b hleft hadj hwidth htail ih =>
      intro x hax hxb
      by_cases hx : x ≤ (c.hi : ℝ)
      · rw [← hleft] at hax
        exact ⟨c, by simp, hwidth, hax, hx⟩
      · have hnext : (d.lo : ℝ) ≤ x := by
          rw [← hadj]
          exact le_of_lt (lt_of_not_ge hx)
        obtain ⟨e, hem, hwidth', helo, hehi⟩ := ih x hnext hxb
        exact ⟨e, by simp [hem], hwidth', helo, hehi⟩

/-- Sound lower-bound selection across a checked chain with per-cell remainders. -/
theorem exactChain_sound {cells : List ReceiptCell} {a b : ℚ} {f : ℝ → ℝ}
    (hchain : ExactChain cells a b)
    (hrem : ∀ c, c ∈ cells → ∀ hwidth : c.lo ≤ c.hi,
      c.modelRemainderValid f hwidth)
    {x : ℝ} (hax : (a : ℝ) ≤ x) (hxb : x ≤ (b : ℝ)) :
    ∃ c, c ∈ cells ∧ (c.lower : ℝ) ≤ f x := by
  obtain ⟨c, hem, hwidth, hlo, hhi⟩ := exactChain_covers hchain x hax hxb
  exact ⟨c, hem, c.sound hwidth (hrem c hem hwidth) hlo hhi⟩

end Li2Lean.F_L8
