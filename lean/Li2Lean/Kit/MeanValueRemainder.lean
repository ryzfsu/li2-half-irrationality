/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.IntervalChecker

/-
General rational allowance checker and mean-value soundness for C-A style
cells. The numerical row and its allowance are data only: soundness still
requires proving the center lower bound and a derivative bound for the actual
analytic function. The derivative bound is converted to a Lipschitz estimate
inside Lean using Mathlib's mean-value theorem on a convex interval.

This interface is useful for docs/6333, section 5 C-A and for future contour
and energy certificates that approximate a function by a center value on a
cell.
-/

namespace ContourKit

/-- The rational midpoint used by a constant Taylor model on a cell. -/
def rationalCellCenter (lo hi : ℚ) : ℚ := (lo + hi) / 2

/-- Half the width of a rational cell; this has the same units as its domain. -/
def rationalCellHalfWidth (lo hi : ℚ) : ℚ := (hi - lo) / 2

/-- Check that a rational Lipschitz bound fits within a row's allowance. -/
def checkMeanValueAllowance (lo hi allowance slope : ℚ) : Bool :=
  decide (lo ≤ hi ∧ 0 ≤ allowance ∧ 0 ≤ slope ∧
    slope * rationalCellHalfWidth lo hi ≤ allowance)

theorem checkMeanValueAllowance_spec {lo hi allowance slope : ℚ}
    (h : checkMeanValueAllowance lo hi allowance slope = true) :
    lo ≤ hi ∧ 0 ≤ allowance ∧ 0 ≤ slope ∧
      slope * rationalCellHalfWidth lo hi ≤ allowance := by
  exact of_decide_eq_true h

theorem rationalCellCenter_mem {lo hi : ℚ} (h : lo ≤ hi) :
    lo ≤ rationalCellCenter lo hi ∧ rationalCellCenter lo hi ≤ hi := by
  constructor <;> dsimp [rationalCellCenter] <;> linarith

theorem rationalCellHalfWidth_nonneg {lo hi : ℚ} (h : lo ≤ hi) :
    0 ≤ rationalCellHalfWidth lo hi := by
  dsimp [rationalCellHalfWidth]
  positivity

theorem abs_sub_center_le_halfWidth {lo hi : ℚ} (hlohi : lo ≤ hi)
    {x : ℝ} (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    |x - (rationalCellCenter lo hi : ℝ)| ≤
      (rationalCellHalfWidth lo hi : ℝ) := by
  have hcenter := rationalCellCenter_mem hlohi
  have hcenterLo : (lo : ℝ) ≤ (rationalCellCenter lo hi : ℝ) := by
    exact_mod_cast hcenter.1
  have hcenterHi : (rationalCellCenter lo hi : ℝ) ≤ (hi : ℝ) := by
    exact_mod_cast hcenter.2
  have hmid : (rationalCellCenter lo hi : ℝ) =
      ((lo : ℝ) + (hi : ℝ)) / 2 := by
    simp [rationalCellCenter]
  have hrad : (rationalCellHalfWidth lo hi : ℝ) =
      ((hi : ℝ) - (lo : ℝ)) / 2 := by
    simp [rationalCellHalfWidth]
  rw [abs_le, hmid, hrad]
  constructor <;> nlinarith

/--
Mean-value soundness for one rational row. If `lower` is a lower bound at
the cell midpoint, and the absolute derivative is at most `slope` throughout
the cell, then the function is at least `lower - allowance` everywhere,
provided the exact rational checker verifies `slope * halfWidth ≤ allowance`.
The allowance is a value error (function units), not a derivative bound
(function units per domain unit).
-/
theorem meanValueAllowance_row_sound {lo hi lower allowance slope : ℚ}
    (hcheck : checkMeanValueAllowance lo hi allowance slope = true)
    {f : ℝ → ℝ}
    (hcenter : (lower : ℝ) ≤ f (rationalCellCenter lo hi : ℝ))
    (hdiff : ∀ y ∈ Set.Icc (lo : ℝ) (hi : ℝ), DifferentiableAt ℝ f y)
    (hderiv : ∀ y ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      |deriv f y| ≤ (slope : ℝ))
    {x : ℝ} (hxlo : (lo : ℝ) ≤ x) (hxhi : x ≤ (hi : ℝ)) :
    (lower : ℝ) - (allowance : ℝ) ≤ f x := by
  obtain ⟨hlohi, hallownonneg, hslope, hbudget⟩ :=
    checkMeanValueAllowance_spec hcheck
  have hxmem : x ∈ Set.Icc (lo : ℝ) (hi : ℝ) := ⟨hxlo, hxhi⟩
  have hcenterRat := rationalCellCenter_mem hlohi
  have hcenterMem : (rationalCellCenter lo hi : ℝ) ∈
      Set.Icc (lo : ℝ) (hi : ℝ) := by
    change (lo : ℝ) ≤ (rationalCellCenter lo hi : ℝ) ∧
      (rationalCellCenter lo hi : ℝ) ≤ (hi : ℝ)
    exact ⟨by exact_mod_cast hcenterRat.1, by exact_mod_cast hcenterRat.2⟩
  have hdist := abs_sub_center_le_halfWidth hlohi hxlo hxhi
  have hslopeR : (0 : ℝ) ≤ (slope : ℝ) := by exact_mod_cast hslope
  have hbudgetR : (slope : ℝ) * (rationalCellHalfWidth lo hi : ℝ) ≤
      (allowance : ℝ) := by exact_mod_cast hbudget
  have hLip : |f x - f (rationalCellCenter lo hi : ℝ)| ≤
      (slope : ℝ) * |x - (rationalCellCenter lo hi : ℝ)| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (lo : ℝ) (hi : ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun y hy => hdiff y hy)
        (fun y hy => by simpa only [Real.norm_eq_abs] using hderiv y hy)
        hcenterMem hxmem
  have hLipRadius : |f x - f (rationalCellCenter lo hi : ℝ)| ≤
      (slope : ℝ) * (rationalCellHalfWidth lo hi : ℝ) :=
    le_trans hLip (mul_le_mul_of_nonneg_left hdist hslopeR)
  have hLipLower := (abs_le.mp hLipRadius).1
  have hbound : (lower : ℝ) - (allowance : ℝ) ≤
      f (rationalCellCenter lo hi : ℝ) -
        (slope : ℝ) * (rationalCellHalfWidth lo hi : ℝ) := by
    have hbudgetLower : (lower : ℝ) - (allowance : ℝ) ≤
        (lower : ℝ) - (slope : ℝ) * (rationalCellHalfWidth lo hi : ℝ) := by
      linarith
    linarith
  calc
    (lower : ℝ) - (allowance : ℝ) ≤
        f (rationalCellCenter lo hi : ℝ) -
          (slope : ℝ) * (rationalCellHalfWidth lo hi : ℝ) := hbound
    _ ≤ f x := by linarith

/-- The corresponding one-sided Taylor remainder statement for the constant
polynomial centered at the midpoint. -/
theorem meanValueAllowance_taylorRemainder {lo hi lower allowance slope : ℚ}
    (hcheck : checkMeanValueAllowance lo hi allowance slope = true)
    {f : ℝ → ℝ}
    (hcenter : (lower : ℝ) ≤ f (rationalCellCenter lo hi : ℝ))
    (hdiff : ∀ y ∈ Set.Icc (lo : ℝ) (hi : ℝ), DifferentiableAt ℝ f y)
    (hderiv : ∀ y ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      |deriv f y| ≤ (slope : ℝ)) :
    TaylorLowerRemainderValid f
      { domain := ⟨lo, hi, (checkMeanValueAllowance_spec hcheck).1⟩
        center := rationalCellCenter lo hi
        coefficients := [lower]
        remainder := allowance } := by
  intro x hx
  have h := meanValueAllowance_row_sound hcheck hcenter hdiff hderiv hx.1 hx.2
  change -(allowance : ℝ) ≤ f x -
    horner [lower] (x - (rationalCellCenter lo hi : ℝ))
  simp only [horner, mul_zero, add_zero]
  linarith

end ContourKit

