/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
Generic exact interval arithmetic and Taylor-model checking over `ℚ`.

The arithmetic checker is executable as a Boolean and intended for finite
kernel-checked reflection (`decide` or `norm_num`). Analytic facts identifying
a function with a Taylor polynomial plus a bounded remainder remain ordinary
Lean theorems; the checker never treats them as trusted input. The API contains
no Li₂-specific constants or formulas.
-/

namespace ContourKit

/-- A closed rational interval, with well-formedness carried by construction. -/
structure QInterval where
  lo : ℚ
  hi : ℚ
  ordered : lo ≤ hi
  deriving DecidableEq, Repr

namespace QInterval

/-- Real membership in a rational interval. -/
def Contains (I : QInterval) (x : ℝ) : Prop :=
  (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

/-- The point interval at a rational. -/
def point (q : ℚ) : QInterval := ⟨q, q, le_rfl⟩

/-- The sum of two intervals. -/
def add (I J : QInterval) : QInterval :=
  ⟨I.lo + J.lo, I.hi + J.hi, add_le_add I.ordered J.ordered⟩

/-- The negation of an interval. -/
def neg (I : QInterval) : QInterval :=
  ⟨-I.hi, -I.lo, neg_le_neg I.ordered⟩

/-- The difference of two intervals. -/
def sub (I J : QInterval) : QInterval := add I (neg J)

/-- A rational absolute bound for every point in the interval. -/
def radius (I : QInterval) : ℚ := max |I.lo| |I.hi|

lemma radius_nonneg (I : QInterval) : 0 ≤ I.radius :=
  le_trans (abs_nonneg _) (le_max_left _ _)

/-- A conservative product enclosure. Its symmetric form keeps proofs small. -/
def mul (I J : QInterval) : QInterval :=
  ⟨-(I.radius * J.radius), I.radius * J.radius, by
    have hI := radius_nonneg I
    have hJ := radius_nonneg J
    have h := mul_nonneg hI hJ
    linarith⟩

lemma mem_point (q : ℚ) : (point q).Contains (q : ℝ) := by
  simp [Contains, point]

lemma mem_add {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (add I J).Contains (x + y) := by
  simp only [Contains, add, Rat.cast_add] at *
  constructor <;> linarith

lemma mem_neg {I : QInterval} {x : ℝ}
    (hx : I.Contains x) : (neg I).Contains (-x) := by
  simp only [Contains, neg, Rat.cast_neg] at *
  constructor <;> linarith

lemma mem_sub {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (sub I J).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using mem_add hx (mem_neg hy)

lemma mem_abs_le_radius {I : QInterval} {x : ℝ}
    (hx : I.Contains x) : |x| ≤ (I.radius : ℝ) := by
  have hloQ : |I.lo| ≤ I.radius := le_max_left _ _
  have hhiQ : |I.hi| ≤ I.radius := le_max_right _ _
  have hlo : |(I.lo : ℝ)| ≤ (I.radius : ℝ) := by exact_mod_cast hloQ
  have hhi : |(I.hi : ℝ)| ≤ (I.radius : ℝ) := by exact_mod_cast hhiQ
  apply abs_le.mpr
  constructor
  · exact le_trans (abs_le.mp hlo).1 hx.1
  · exact le_trans hx.2 (abs_le.mp hhi).2

lemma mem_mul {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (mul I J).Contains (x * y) := by
  have hI : 0 ≤ (I.radius : ℝ) := by exact_mod_cast radius_nonneg I
  have hJ : 0 ≤ (J.radius : ℝ) := by exact_mod_cast radius_nonneg J
  have hx' := mem_abs_le_radius hx
  have hy' := mem_abs_le_radius hy
  have habs : |x * y| ≤ (I.radius : ℝ) * (J.radius : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hx' hy' (abs_nonneg y) hI
  have hbounds := abs_le.mp habs
  constructor
  · simp only [mul, Rat.cast_neg, Rat.cast_mul]
    change -((I.radius : ℝ) * (J.radius : ℝ)) ≤ x * y
    exact hbounds.1
  · simp only [mul, Rat.cast_mul]
    change x * y ≤ (I.radius : ℝ) * (J.radius : ℝ)
    exact hbounds.2

end QInterval

/-- Horner evaluation of a coefficient list in ascending order. -/
def horner : List ℚ → ℝ → ℝ
  | [], _ => 0
  | a :: as, x => (a : ℝ) + x * horner as x

/-- Interval Horner evaluation of the same coefficient list. -/
def intervalHorner : List ℚ → QInterval → QInterval
  | [], _ => QInterval.point 0
  | a :: as, I => QInterval.add (QInterval.point a)
      (QInterval.mul I (intervalHorner as I))

theorem intervalHorner_sound (coefficients : List ℚ) (I : QInterval)
    {x : ℝ} (hx : I.Contains x) :
    (intervalHorner coefficients I).Contains (horner coefficients x) := by
  induction coefficients with
  | nil =>
      simpa [intervalHorner, horner] using QInterval.mem_point (0 : ℚ)
  | cons a coefficients ih =>
      have hpoint := QInterval.mem_point a
      have hmul := QInterval.mem_mul hx ih
      simpa only [intervalHorner, horner] using QInterval.mem_add hpoint hmul

/-- Translate an interval by a rational center. -/
def shift (I : QInterval) (center : ℚ) : QInterval :=
  ⟨I.lo - center, I.hi - center, by linarith [I.ordered]⟩

lemma mem_shift {I : QInterval} {center : ℚ} {x : ℝ}
    (hx : I.Contains x) : (shift I center).Contains (x - center) := by
  simp only [QInterval.Contains, shift, Rat.cast_sub] at *
  constructor <;> linarith

/-- A Taylor-model cell. All stored numerical data are exact rationals. -/
structure TaylorCell where
  domain : QInterval
  center : ℚ
  coefficients : List ℚ
  remainder : ℚ
  deriving DecidableEq, Repr

/-- The interval enclosure of the cell's Taylor polynomial. -/
def TaylorCell.polynomialRange (C : TaylorCell) : QInterval :=
  intervalHorner C.coefficients (shift C.domain C.center)

/--
The exact rational part of the cell check. The lower endpoint of the polynomial
range minus the supplied Taylor error must dominate the requested global lower
bound.
-/
def checkTaylorCell (lower : ℚ) (C : TaylorCell) : Bool :=
  decide (0 ≤ C.remainder ∧ lower ≤ C.polynomialRange.lo - C.remainder)

/-- The analytic remainder obligation attached to a Taylor model. -/
def TaylorRemainderValid (f : ℝ → ℝ) (C : TaylorCell) : Prop :=
  ∀ x : ℝ, C.domain.Contains x →
    |f x - horner C.coefficients (x - C.center)| ≤ (C.remainder : ℝ)

/-- A one-sided Taylor remainder bound, sufficient for lower certificates. -/
def TaylorLowerRemainderValid (f : ℝ → ℝ) (C : TaylorCell) : Prop :=
  ∀ x : ℝ, C.domain.Contains x →
    -(C.remainder : ℝ) ≤ f x - horner C.coefficients (x - C.center)

theorem checkTaylorCell_spec {lower : ℚ} {C : TaylorCell}
    (h : checkTaylorCell lower C = true) :
    0 ≤ C.remainder ∧ lower ≤ C.polynomialRange.lo - C.remainder := by
  exact of_decide_eq_true h

/-- Soundness of one rationally checked Taylor cell. -/
theorem checkTaylorCell_sound {f : ℝ → ℝ} {lower : ℚ} {C : TaylorCell}
    (hcheck : checkTaylorCell lower C = true)
    (hrem : TaylorRemainderValid f C) {x : ℝ}
    (hx : C.domain.Contains x) : (lower : ℝ) ≤ f x := by
  obtain ⟨_, hmargin⟩ := checkTaylorCell_spec hcheck
  have hpoly := intervalHorner_sound C.coefficients
    (shift C.domain C.center) (mem_shift hx)
  have hremx := hrem x hx
  have hmarginR : (lower : ℝ) ≤ (C.polynomialRange.lo : ℝ) - C.remainder := by
    exact_mod_cast hmargin
  have hTaylor :
      (C.polynomialRange.lo : ℝ) ≤ horner C.coefficients (x - C.center) :=
    hpoly.1
  have hError :
      -(C.remainder : ℝ) ≤ f x - horner C.coefficients (x - C.center) :=
    (abs_le.mp hremx).1
  linarith

/-- Lower-bound soundness needs only the directed (lower) Taylor remainder. -/
theorem checkTaylorCell_lower_sound {f : ℝ → ℝ} {lower : ℚ} {C : TaylorCell}
    (hcheck : checkTaylorCell lower C = true)
    (hrem : TaylorLowerRemainderValid f C) {x : ℝ}
    (hx : C.domain.Contains x) : (lower : ℝ) ≤ f x := by
  obtain ⟨_, hmargin⟩ := checkTaylorCell_spec hcheck
  have hpoly := intervalHorner_sound C.coefficients
    (shift C.domain C.center) (mem_shift hx)
  have hremx := hrem x hx
  have hmarginR : (lower : ℝ) ≤ (C.polynomialRange.lo : ℝ) - C.remainder := by
    exact_mod_cast hmargin
  have hTaylor :
      (C.polynomialRange.lo : ℝ) ≤ horner C.coefficients (x - C.center) :=
    hpoly.1
  linarith

/-- A nonempty chain of rational cells with exactly matching adjacent ends. -/
inductive TaylorChain : ℚ → ℚ → Type
  | single (cell : TaylorCell) : TaylorChain cell.domain.lo cell.domain.hi
  | cons (cell : TaylorCell) {right : ℚ}
      (tail : TaylorChain cell.domain.hi right) : TaylorChain cell.domain.lo right

namespace TaylorChain

def Cells {left right : ℚ} (chain : TaylorChain left right) : List TaylorCell :=
  match chain with
  | .single C => [C]
  | .cons C tail => C :: Cells (left := C.domain.hi) (right := right) tail

def Checked {left right : ℚ} (chain : TaylorChain left right) (lower : ℚ) : Prop :=
  match chain with
  | .single C => checkTaylorCell lower C = true
  | .cons C tail => checkTaylorCell lower C = true ∧
      Checked (left := C.domain.hi) (right := right) tail lower

def RemaindersValid {left right : ℚ} (chain : TaylorChain left right) (f : ℝ → ℝ) : Prop :=
  match chain with
  | .single C => TaylorRemainderValid f C
  | .cons C tail => TaylorRemainderValid f C ∧
      RemaindersValid (left := C.domain.hi) (right := right) tail f

def LowerRemaindersValid {left right : ℚ} (chain : TaylorChain left right) (f : ℝ → ℝ) : Prop :=
  match chain with
  | .single C => TaylorLowerRemainderValid f C
  | .cons C tail => TaylorLowerRemainderValid f C ∧
      LowerRemaindersValid (left := C.domain.hi) (right := right) tail f

/-- Exact endpoint matching in a chain gives a closed cover of its range. -/
theorem covers {left right : ℚ} (chain : TaylorChain left right) {x : ℝ}
    (hleft : (left : ℝ) ≤ x) (hright : x ≤ (right : ℝ)) :
    ∃ C, C ∈ chain.Cells ∧ C.domain.Contains x := by
  induction chain with
  | single C =>
      exact ⟨C, by change C ∈ [C]; simp, ⟨hleft, hright⟩⟩
  | @cons C right tail ih =>
      by_cases hx : x ≤ (C.domain.hi : ℝ)
      · exact ⟨C, by change C ∈ C :: TaylorChain.Cells tail; exact List.mem_cons_self,
          ⟨hleft, hx⟩⟩
      · have hx' : (C.domain.hi : ℝ) ≤ x := le_of_lt (lt_of_not_ge hx)
        obtain ⟨D, hD, hDx⟩ := ih hx' hright
        exact ⟨D, by
          change D ∈ C :: TaylorChain.Cells tail
          exact List.mem_cons_of_mem C hD, hDx⟩

/-- A checked chain and its Taylor remainder proofs imply the global bound. -/
theorem sound {left right : ℚ} (chain : TaylorChain left right) {f : ℝ → ℝ} {lower : ℚ}
    (hcheck : chain.Checked lower) (hrem : chain.RemaindersValid f)
    {x : ℝ} (hleft : (left : ℝ) ≤ x) (hright : x ≤ (right : ℝ)) :
    (lower : ℝ) ≤ f x := by
  induction chain with
  | single D =>
      change checkTaylorCell lower D = true at hcheck
      change TaylorRemainderValid f D at hrem
      have hcheckD : checkTaylorCell lower D = true := hcheck
      have hremD : TaylorRemainderValid f D := hrem
      exact checkTaylorCell_sound hcheckD hremD ⟨hleft, hright⟩
  | @cons D right tail ih =>
      change checkTaylorCell lower D = true ∧
        TaylorChain.Checked (left := D.domain.hi) (right := right) tail lower at hcheck
      change TaylorRemainderValid f D ∧
        TaylorChain.RemaindersValid (left := D.domain.hi) (right := right) tail f at hrem
      by_cases hx : x ≤ (D.domain.hi : ℝ)
      · exact checkTaylorCell_sound hcheck.1 hrem.1 ⟨hleft, hx⟩
      · have hx' : (D.domain.hi : ℝ) ≤ x := le_of_lt (lt_of_not_ge hx)
        exact ih hcheck.2 hrem.2 hx' hright

/-- A checked chain with directed Taylor remainders proves a lower bound. -/
theorem lower_sound {left right : ℚ} (chain : TaylorChain left right) {f : ℝ → ℝ} {lower : ℚ}
    (hcheck : chain.Checked lower) (hrem : chain.LowerRemaindersValid f)
    {x : ℝ} (hleft : (left : ℝ) ≤ x) (hright : x ≤ (right : ℝ)) :
    (lower : ℝ) ≤ f x := by
  induction chain with
  | single D =>
      change checkTaylorCell lower D = true at hcheck
      change TaylorLowerRemainderValid f D at hrem
      exact checkTaylorCell_lower_sound hcheck hrem ⟨hleft, hright⟩
  | @cons D right tail ih =>
      change checkTaylorCell lower D = true ∧
        TaylorChain.Checked (left := D.domain.hi) (right := right) tail lower at hcheck
      change TaylorLowerRemainderValid f D ∧
        TaylorChain.LowerRemaindersValid (left := D.domain.hi) (right := right) tail f at hrem
      by_cases hx : x ≤ (D.domain.hi : ℝ)
      · exact checkTaylorCell_lower_sound hcheck.1 hrem.1 ⟨hleft, hx⟩
      · have hx' : (D.domain.hi : ℝ) ≤ x := le_of_lt (lt_of_not_ge hx)
        exact ih hcheck.2 hrem.2 hx' hright

end TaylorChain

/-- A small closed reflection example for the rational checker. -/
example : checkTaylorCell (-1)
    { domain := ⟨0, 1, by norm_num⟩
      center := 0
      coefficients := [0, 1]
      remainder := 0 } = true := by
  norm_num [checkTaylorCell, TaylorCell.polynomialRange, intervalHorner,
    horner, QInterval.point, QInterval.add, QInterval.mul, QInterval.radius, shift]

end ContourKit
