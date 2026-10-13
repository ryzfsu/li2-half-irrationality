/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.LayerInterfaces

/-
# Rational tangent coordinates for C-A cells

This is the E2 coordinate toolkit for the contour rows in docs/6333, section 5
and Appendix A. The Weierstrass substitution uses t = tan (u/2). At a
rational parameter t, the sine and cosine values are exact rationals. The
angle-cell map is deliberately an interface: a caller supplies the
correspondence between its paper angle endpoints and the two mapped endpoints;
this file does not silently replace the paper's angular cells.

The formulas are elementary trigonometry, proved in the kernel from Mathlib's
arctangent identities. No numerical approximation or external certificate
enters these lemmas.
-/

open Set

namespace Li2Lean
namespace ContourKit

noncomputable section

/-- Weierstrass sine coordinate, valued exactly in Q. -/
def weierstrassSin (t : ℚ) : ℚ := 2 * t / (1 + t ^ 2)

/-- Weierstrass cosine coordinate, valued exactly in Q. -/
def weierstrassCos (t : ℚ) : ℚ := (1 - t ^ 2) / (1 + t ^ 2)

/-- The denominator in the two rational Weierstrass coordinates is positive. -/
theorem weierstrass_den_pos (t : ℚ) : 0 < 1 + t ^ 2 := by
  positivity

/-- Exact sine formula at the rational tangent parameter t = tan (u/2). -/
theorem sin_two_arctan_rat (t : ℚ) :
    Real.sin (2 * Real.arctan (t : ℝ)) = (weierstrassSin t : ℝ) := by
  rw [Real.sin_two_mul, Real.sin_arctan, Real.cos_arctan]
  have hsqrt : (0 : ℝ) < Real.sqrt (1 + (t : ℝ) ^ 2) := by positivity
  have hsqrtne : Real.sqrt (1 + (t : ℝ) ^ 2) ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt (1 + (t : ℝ) ^ 2)) ^ 2 = 1 + (t : ℝ) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  unfold weierstrassSin
  push_cast
  field_simp [hsqrtne]
  rw [hsqrt_sq]

/-- Exact cosine formula at the rational tangent parameter t = tan (u/2). -/
theorem cos_two_arctan_rat (t : ℚ) :
    Real.cos (2 * Real.arctan (t : ℝ)) = (weierstrassCos t : ℝ) := by
  rw [Real.cos_two_mul, Real.cos_arctan]
  have hsqrt : (0 : ℝ) < Real.sqrt (1 + (t : ℝ) ^ 2) := by positivity
  have hsqrtne : Real.sqrt (1 + (t : ℝ) ^ 2) ≠ 0 := ne_of_gt hsqrt
  have hsqrt_sq : (Real.sqrt (1 + (t : ℝ) ^ 2)) ^ 2 = 1 + (t : ℝ) ^ 2 := by
    rw [Real.sq_sqrt]
    positivity
  unfold weierstrassCos
  push_cast
  field_simp [hsqrtne]
  rw [hsqrt_sq]
  ring

/-- The tangent-half-angle map at a Weierstrass endpoint recovers its parameter. -/
theorem tan_half_two_arctan_rat (t : ℚ) :
    Real.tan ((2 * Real.arctan (t : ℝ)) / 2) = (t : ℝ) := by
  convert Real.tan_arctan (t : ℝ) using 1
  ring

/-- The rational parameterization lies on the unit circle. -/
theorem weierstrass_circle (t : ℚ) :
    (weierstrassCos t : ℝ) ^ 2 + (weierstrassSin t : ℝ) ^ 2 = 1 := by
  unfold weierstrassCos weierstrassSin
  push_cast
  field_simp [ne_of_gt (weierstrass_den_pos t)]
  ring_nf

/-- A rational parameter interval used by a C-A row checker. -/
structure RationalTangentCell where
  lo : ℚ
  hi : ℚ
  lo_le_hi : lo ≤ hi

namespace RationalTangentCell

/-- The angular image of a rational tangent cell. -/
def angle (c : RationalTangentCell) : Set ℝ :=
  Set.Icc (2 * Real.arctan (c.lo : ℝ)) (2 * Real.arctan (c.hi : ℝ))

theorem angle_nonempty (c : RationalTangentCell) : (c.angle).Nonempty := by
  refine ⟨2 * Real.arctan (c.lo : ℝ), ?_⟩
  constructor
  · rfl
  · exact mul_le_mul_of_nonneg_left
      (Real.arctan_mono (by exact_mod_cast c.lo_le_hi)) (by norm_num)

theorem angle_left_mem (c : RationalTangentCell) :
    2 * Real.arctan (c.lo : ℝ) ∈ c.angle := by
  constructor
  · rfl
  · exact mul_le_mul_of_nonneg_left
      (Real.arctan_mono (by exact_mod_cast c.lo_le_hi)) (by norm_num)

theorem angle_right_mem (c : RationalTangentCell) :
    2 * Real.arctan (c.hi : ℝ) ∈ c.angle := by
  constructor
  · exact mul_le_mul_of_nonneg_left
      (Real.arctan_mono (by exact_mod_cast c.lo_le_hi)) (by norm_num)
  · rfl

/-
Every angle in the mapped cell has tangent-half-angle between the parameters.
The endpoint correspondence is the part that a concrete paper cell must provide.
-/
theorem tan_half_mem {c : RationalTangentCell} {u : ℝ} (hu : u ∈ c.angle)
    (hu_range : u / 2 ∈ Set.Ioo (-(Real.pi / 2)) (Real.pi / 2)) :
    (c.lo : ℝ) ≤ Real.tan (u / 2) ∧
      Real.tan (u / 2) ≤ (c.hi : ℝ) := by
  have hleft : 2 * Real.arctan (c.lo : ℝ) ≤ u := hu.1
  have hright : u ≤ 2 * Real.arctan (c.hi : ℝ) := hu.2
  have hleft' : Real.arctan (c.lo : ℝ) ≤ u / 2 := by linarith
  have hright' : u / 2 ≤ Real.arctan (c.hi : ℝ) := by linarith
  constructor
  · rw [← Real.tan_arctan (c.lo : ℝ)]
    exact Real.strictMonoOn_tan.monotoneOn
      (Real.arctan_mem_Ioo _) hu_range hleft'
  · rw [← Real.tan_arctan (c.hi : ℝ)]
    exact Real.strictMonoOn_tan.monotoneOn
      hu_range (Real.arctan_mem_Ioo _) hright'

end RationalTangentCell

/-
Explicit endpoint correspondence for a paper angular cell.

The equalities are fields rather than hidden assumptions: a concrete C-A
checker must prove them from its own cell data.
-/
structure RationalTangentCellMapping where
  tangentCell : RationalTangentCell
  paperLeft : ℝ
  paperRight : ℝ
  paperLeft_eq : paperLeft = (2 : ℝ) * Real.arctan (tangentCell.lo : ℝ)
  paperRight_eq : paperRight = (2 : ℝ) * Real.arctan (tangentCell.hi : ℝ)
  paperLeft_le_right : paperLeft ≤ paperRight

/-
The mapped interval is exactly the paper interval once the endpoint fields
of RationalTangentCellMapping are discharged.
-/
theorem rationalTangentCellMapping_interval_eq (M : RationalTangentCellMapping) :
    Set.Icc M.paperLeft M.paperRight =
      RationalTangentCell.angle M.tangentCell := by
  rw [M.paperLeft_eq, M.paperRight_eq]
  rfl


end
end ContourKit

namespace P0

noncomputable section

/-
The point on the v10 ellipse obtained from a rational tangent parameter.
-/
def p0EllipsePointTanQ (m : ℕ) (t : ℚ) : ℂ :=
  Complex.ofReal (m : ℝ) *
    (Complex.ofReal (((11281 : ℚ) / 10000 +
      (12783 : ℚ) / 10000 * ContourKit.weierstrassCos t : ℚ) : ℝ) +
      Complex.I * Complex.ofReal ((((229 : ℚ) / 200) *
        ContourKit.weierstrassSin t : ℚ) : ℝ))

/-
The paper ellipse parameter agrees exactly with the rational point at
u = 2*arctan t.
-/
theorem p0EllipsePoint_two_arctan_rat (m : ℕ) (t : ℚ) :
    Li2Lean.p0EllipsePoint m (2 * Real.arctan (t : ℝ)) =
      p0EllipsePointTanQ m t := by
  unfold Li2Lean.p0EllipsePoint p0EllipsePointTanQ
  rw [ContourKit.cos_two_arctan_rat, ContourKit.sin_two_arctan_rat]
  norm_num

end
end P0
end Li2Lean
