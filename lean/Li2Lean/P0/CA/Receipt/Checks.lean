/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.ReceiptChain
import Mathlib.Tactic.Ring
import Mathlib.Algebra.Order.Ring.Rat

/-!
# Rational checkers for the C-A 397/200 slack receipt

All checkers below are computable Booleans over `ℚ`. Each has a soundness
theorem; the generated data shards evaluate them with `decide +kernel`.

* `chainCheck cells left right` certifies `ExactChain cells left right`.
* `penaltyMass h a cells` is the exact rational mass
  `∑ (hi - lo) * max (h - (lower - a)) 0` of the spent row floors below the
  threshold `h`; it is the rational value of the step majorant used for the
  C-A penalties.
* `floorCheck b cells` certifies `b ≤ lower` for every row.
* `endpointCheck r b cells` certifies `b ≤ lower` for every row whose right
  endpoint is at least `r`.
-/

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.F_L8

/-- The contour C-A threshold `h_eta = -1673/500` of the slack receipt. -/
def hEtaQ : ℚ := -1673 / 500

/-- The frequency C-A threshold `h_mu = 71/25`. -/
def hMuQ : ℚ := 71 / 25

/-- Contour row allowance. -/
def contourAllowance : ℚ := 1 / 2000

/-- Pinned and frequency row allowance. -/
def realAllowance : ℚ := 1 / 10000

/-- Exact spent pinned penalty mass. -/
def pinnedPenaltyQ : ℚ := 1719970838541 / 20480000000000

/-- Exact spent finite-frequency penalty mass. -/
def frequencyPenaltyQ : ℚ := 38169112950419 / 409600000000000

/-- Boolean exact-chain checker. -/
def chainCheck : List ReceiptCell → ℚ → ℚ → Bool
  | [], _, _ => false
  | [c], left, right =>
      decide (c.lo = left) && decide (c.hi = right) && decide (c.lo ≤ c.hi)
  | c :: d :: rest, left, right =>
      decide (c.lo = left) && decide (c.hi = d.lo) && decide (c.lo ≤ c.hi) &&
        chainCheck (d :: rest) d.lo right

theorem chainCheck_sound :
    ∀ {cells : List ReceiptCell} {left right : ℚ},
      chainCheck cells left right = true → ExactChain cells left right
  | [], _, _, h => by simp [chainCheck] at h
  | [c], left, right, h => by
      simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ExactChain.one c left right h.1.1 h.1.2 h.2
  | c :: d :: rest, left, right, h => by
      simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      exact ExactChain.more c d rest left right h.1.1.1 h.1.1.2 h.1.2
        (chainCheck_sound h.2)

/-- Exact rational penalty mass of the spent row floors below `h`. -/
def penaltyMass (h a : ℚ) : List ReceiptCell → ℚ
  | [] => 0
  | c :: rest => (c.hi - c.lo) * max (h - (c.lower - a)) 0 + penaltyMass h a rest

theorem penaltyMass_append (h a : ℚ) (xs ys : List ReceiptCell) :
    penaltyMass h a (xs ++ ys) = penaltyMass h a xs + penaltyMass h a ys := by
  induction xs with
  | nil => rw [List.nil_append]; simp only [penaltyMass]; ring
  | cons c xs ih =>
      simp only [List.cons_append, penaltyMass, ih]
      ring

/-- Every row lower bound is at least `b`. -/
def floorCheck (b : ℚ) : List ReceiptCell → Bool
  | [] => true
  | c :: rest => decide (b ≤ c.lower) && floorCheck b rest

theorem floorCheck_sound {b : ℚ} :
    ∀ {cells : List ReceiptCell}, floorCheck b cells = true →
      ∀ c ∈ cells, b ≤ c.lower
  | [], _ => by simp
  | c :: rest, h => by
      simp only [floorCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      intro d hd
      rcases List.mem_cons.mp hd with rfl | hd
      · exact h.1
      · exact floorCheck_sound h.2 d hd

theorem floorCheck_complete {b : ℚ} :
    ∀ {cells : List ReceiptCell}, (∀ c ∈ cells, b ≤ c.lower) →
      floorCheck b cells = true
  | [], _ => rfl
  | c :: rest, h => by
      simp only [floorCheck, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨h c (by simp), floorCheck_complete fun d hd => h d (by simp [hd])⟩

theorem floorCheck_append (b : ℚ) (xs ys : List ReceiptCell) :
    floorCheck b (xs ++ ys) = (floorCheck b xs && floorCheck b ys) := by
  induction xs with
  | nil => simp [floorCheck]
  | cons c xs ih => simp [floorCheck, ih, Bool.and_assoc]

/-- Every row reaching the right endpoint `r` has lower bound at least `b`. -/
def endpointCheck (r b : ℚ) : List ReceiptCell → Bool
  | [] => true
  | c :: rest => (!decide (r ≤ c.hi) || decide (b ≤ c.lower)) && endpointCheck r b rest

theorem endpointCheck_sound {r b : ℚ} :
    ∀ {cells : List ReceiptCell}, endpointCheck r b cells = true →
      ∀ c ∈ cells, r ≤ c.hi → b ≤ c.lower
  | [], _ => by simp
  | c :: rest, h => by
      simp only [endpointCheck, Bool.and_eq_true, Bool.or_eq_true,
        Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq] at h
      intro d hd hr
      rcases List.mem_cons.mp hd with rfl | hd
      · rcases h.1 with h1 | h1
        · exact absurd hr h1
        · exact h1
      · exact endpointCheck_sound h.2 d hd hr

theorem endpointCheck_append (r b : ℚ) (xs ys : List ReceiptCell) :
    endpointCheck r b (xs ++ ys) =
      (endpointCheck r b xs && endpointCheck r b ys) := by
  induction xs with
  | nil => simp [endpointCheck]
  | cons c xs ih => simp [endpointCheck, ih, Bool.and_assoc]

end Li2Lean.P0.CA.Receipt
