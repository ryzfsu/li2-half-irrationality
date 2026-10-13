/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CAWetaEndpoint
import Li2Lean.P0.CAInteriorContourPotential
import Li2Lean.P0.ConfigSlackSemanticIdentity
import Li2Lean.P0.ConfigPrimitiveEnclosure
import Li2Lean.Agents.F_L8.MeanValueSlackAdapter
import Li2Lean.Kit.MeanValueRemainder

set_option maxRecDepth 100000

/-!
# Singular-residual interface for the first pinned C-A row

The first pinned row starts just to the right of the endpoint `1/4`.  The
derivative of the endpoint primitive is large there, so the proof keeps the
term `cSing * F (x - 1/4)` exact and applies a mean-value estimate only to the
remaining smooth field.  This module proves that reduction; the center and
residual derivative bounds are supplied by the source-locked evaluator.
-/

open MeasureTheory
open ContourKit
open Li2Lean.LogSegment
open Li2Lean.F_L8
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigPrimitiveEnclosure
open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigFejerLog
open Li2Lean.P0.ConfigInteriorContourPotential

namespace Li2Lean.P0.PinnedResidualRow1

noncomputable section

def singularCoefficient : ℚ := 15624999999 / 15625000000

def smoothPinnedResidual (x : ℝ) : ℝ :=
  pinnedWeta x - (singularCoefficient : ℝ) * primitive (x - 1 / 4)

theorem pinnedWeta_eq_singular_add_residual (x : ℝ) :
    pinnedWeta x =
      (singularCoefficient : ℝ) * primitive (x - 1 / 4) +
        smoothPinnedResidual x := by
  unfold smoothPinnedResidual
  ring

/-! This is the source-locked expression consumed by the center certificate.
Every reference component is the literal finite endpoint sum; the contour
term is still the actual potential at this stage. -/

theorem smoothPinnedResidual_explicit (x : ℝ) :
    smoothPinnedResidual x =
      (primitive (x - 1 / 4) - primitive (x - 5 / 4) +
        (primitive x - primitive (x - 2))) -
      (x * Real.log 2 +
        (primitive (x + 1 / 2) - primitive x) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
      2 * ((∑ j ∈ Finset.range 32,
          referenceDensity ConfigData.pinnedMassUnits j *
            (primitive (x - referenceCellLeft (1 / 4) j) -
              primitive (x - referenceCellRight (1 / 4) j))) +
        contourReferencePotential (x : ℂ)) -
      (∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits j *
          (primitive (x + referenceCellRight (1 / 2) j) -
            primitive (x + referenceCellLeft (1 / 2) j))) -
      (singularCoefficient : ℝ) * primitive (x - 1 / 4) := by
  unfold smoothPinnedResidual
  change Config.Weta actualReference (x : ℂ) -
      (singularCoefficient : ℝ) * primitive (x - 1 / 4) = _
  rw [ConfigSlackSemanticIdentity.actualWeta_ofReal_eq_endpoints]


/-! The endpoint primitive is ordered on the first row even though its
derivative is not bounded uniformly at the vertex itself. -/

theorem singular_lower_on_row
    {x : ℝ} (hxlo : (2049 / 8192 : ℝ) ≤ x)
    (hxhi : x ≤ (1025 / 4096 : ℝ)) :
    (singularCoefficient : ℝ) *
        primitive ((1025 / 4096 : ℝ) - 1 / 4) ≤
      (singularCoefficient : ℝ) * primitive (x - 1 / 4) := by
  have hcoeff : 0 ≤ (singularCoefficient : ℝ) := by
    norm_num [singularCoefficient]
  have hvertex : (1 / 4 : ℝ) ≤ x := by linarith
  have hwidth : (1025 / 4096 : ℝ) - (1 / 4 : ℝ) ≤ 1 := by norm_num
  have hmono := segmentPrimitive_radial_mono
    (x := x - 1 / 4)
    (a := (1025 / 4096 : ℝ) - 1 / 4) (by linarith) (by linarith)
    (by norm_num) hwidth
  have hprimitive :
      primitive ((1025 / 4096 : ℝ) - 1 / 4) ≤ primitive (x - 1 / 4) := by
    simp only [primitive,
      abs_of_nonneg (show 0 ≤ (1025 / 4096 : ℝ) - 1 / 4 by norm_num),
      abs_of_nonneg (show 0 ≤ x - 1 / 4 by linarith)]
    linarith
  exact mul_le_mul_of_nonneg_left hprimitive hcoeff

theorem singular_lower_on_row_general
    {x lo hi vertex : ℝ} {coeff : ℚ}
    (hcoeff : 0 ≤ (coeff : ℝ))
    (hvertex : (vertex : ℝ) ≤ lo)
    (hxlo : lo ≤ x) (hxhi : x ≤ hi)
    (hradius : hi - (vertex : ℝ) ≤ 1) :
    (coeff : ℝ) * primitive (hi - (vertex : ℝ)) ≤
      (coeff : ℝ) * primitive (x - (vertex : ℝ)) := by
  have hx : 0 ≤ x - (vertex : ℝ) := by linarith
  have hxa : x - (vertex : ℝ) ≤ hi - (vertex : ℝ) := by linarith
  have ha : 0 ≤ hi - (vertex : ℝ) := by linarith
  by_cases hzero : hi = vertex
  · have hxv : x = vertex := by linarith
    simp [hzero, hxv]
  · have hne : hi - (vertex : ℝ) ≠ 0 := sub_ne_zero.mpr hzero
    have hapos : 0 < hi - (vertex : ℝ) := lt_of_le_of_ne ha (Ne.symm hne)
    have hmono := segmentPrimitive_radial_mono hx hxa hapos hradius
    have hprimitive :
        primitive (hi - (vertex : ℝ)) ≤ primitive (x - (vertex : ℝ)) := by
      simp only [primitive, abs_of_nonneg hx,
        abs_of_nonneg ha]
      linarith
    exact mul_le_mul_of_nonneg_left hprimitive hcoeff

/-!
The theorem below is the semantic hand-off for row 1.  Its premises contain
only the actual smooth residual and its derivative; no interval or potential
value is supplied as an unchecked evaluator field.  Once those two facts are
proved from the finite endpoint/Fejer formulas, the existing receipt model is
closed by pure real analysis.
-/

theorem row1_modelRemainder_of_residual
    {c : Li2Lean.F_L8.ReceiptCell} {allowance slope : ℚ}
    (hc_lo : c.lo = 2049 / 8192)
    (hc_hi : c.hi = 1025 / 4096)
    (hwidth : c.lo ≤ c.hi)
    (hallow : 0 ≤ allowance)
    (hcenter : (c.lower : ℝ) - (allowance : ℝ) ≤
      (singularCoefficient : ℝ) *
          primitive ((1025 / 4096 : ℝ) - 1 / 4) +
        smoothPinnedResidual (rationalCellCenter c.lo c.hi) -
        (slope : ℝ) * (rationalCellHalfWidth c.lo c.hi : ℝ))
    (hcheck : checkMeanValueAllowance c.lo c.hi allowance slope = true)
    (hdiff : ∀ y ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ),
      DifferentiableAt ℝ smoothPinnedResidual y)
    (hderiv : ∀ y ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ),
      |deriv smoothPinnedResidual y| ≤ (slope : ℝ)) :
    (c.afterAllowance allowance).modelRemainderValid pinnedWeta hwidth := by
  have hxrow {x : ℝ} (hx : x ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ)) :
      (1 / 4 : ℝ) ≤ x := by
    rw [hc_lo] at hx
    linarith [hx.1]
  intro x hx
  have hxmem : x ∈ Set.Icc (c.lo : ℝ) (c.hi : ℝ) := hx
  have hcenter_mem :
      (rationalCellCenter c.lo c.hi : ℝ) ∈
        Set.Icc (c.lo : ℝ) (c.hi : ℝ) := by
    have h := rationalCellCenter_mem hwidth
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hdist := abs_sub_center_le_halfWidth hwidth hx.1 hx.2
  have hslope : (0 : ℝ) ≤ (slope : ℝ) := by
    exact_mod_cast (checkMeanValueAllowance_spec hcheck).2.2.1
  have hLip :
      |smoothPinnedResidual x -
          smoothPinnedResidual (rationalCellCenter c.lo c.hi)| ≤
        (slope : ℝ) * |x - (rationalCellCenter c.lo c.hi : ℝ)| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (c.lo : ℝ) (c.hi : ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun y hy => hdiff y hy)
        (fun y hy => by simpa only [Real.norm_eq_abs] using hderiv y hy)
        hcenter_mem hxmem
  have hLip' :
      |smoothPinnedResidual x -
          smoothPinnedResidual (rationalCellCenter c.lo c.hi)| ≤
        (slope : ℝ) * (rationalCellHalfWidth c.lo c.hi : ℝ) :=
    le_trans hLip (mul_le_mul_of_nonneg_left hdist hslope)
  have hresidual :
      smoothPinnedResidual (rationalCellCenter c.lo c.hi) -
          (slope : ℝ) * (rationalCellHalfWidth c.lo c.hi : ℝ) ≤
        smoothPinnedResidual x := by
    linarith [abs_le.mp hLip']
  have hsing := singular_lower_on_row_general
    (coeff := singularCoefficient) (x := x)
    (lo := c.lo) (hi := c.hi) (vertex := (1 / 4 : ℝ))
    (by norm_num [singularCoefficient])
    (by rw [hc_lo]; norm_num)
    hx.1 hx.2 (by rw [hc_hi]; norm_num)
  rw [hc_hi] at hsing
  have htotal : (c.lower : ℝ) - (allowance : ℝ) ≤ pinnedWeta x := by
    rw [pinnedWeta_eq_singular_add_residual]
    linarith [hcenter, hsing, hresidual]
  simp only [Li2Lean.F_L8.ReceiptCell.modelRemainderValid,
    Li2Lean.F_L8.ReceiptCell.model,
    TaylorLowerRemainderValid, horner, Rat.cast_zero, mul_zero, add_zero,
    Li2Lean.F_L8.ReceiptCell.afterAllowance]
  push_cast
  linarith

/-! A source-locked specialization.  The row data are copied from the
Appendix A receipt; only the two analytic residual facts remain as premises.
This makes the hand-off independent of the generic `EvalInput` checker. -/

def row1SourceCell : Li2Lean.F_L8.ReceiptCell :=
  ⟨2049 / 8192, 1025 / 4096, -7464622151 / 2500000000⟩

def row1Allowance : ℚ := 1 / 10000

def row1Slope : ℚ := 121 / 100

theorem row1SourceCell_width : row1SourceCell.lo ≤ row1SourceCell.hi := by
  norm_num [row1SourceCell]

theorem row1SourceCell_matches_data :
    ConfigData.pinnedCellsChunk000[1]'(by
      have h := ConfigData.pinnedCellsChunk000_length
      omega) = row1SourceCell := by
  norm_num [row1SourceCell, ConfigData.pinnedCellsChunk000]

theorem row1_allowance_check :
    checkMeanValueAllowance row1SourceCell.lo row1SourceCell.hi
      row1Allowance row1Slope = true := by
  norm_num [row1SourceCell, row1Allowance, row1Slope,
    checkMeanValueAllowance, rationalCellHalfWidth]

theorem row1_modelRemainder_of_actual_residual
    (hcenter : (row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
      (singularCoefficient : ℝ) *
          primitive ((1025 / 4096 : ℝ) - 1 / 4) +
        smoothPinnedResidual
          (rationalCellCenter row1SourceCell.lo row1SourceCell.hi) -
        (row1Slope : ℝ) *
          (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ))
    (hdiff : ∀ y ∈ Set.Icc (row1SourceCell.lo : ℝ)
        (row1SourceCell.hi : ℝ), DifferentiableAt ℝ smoothPinnedResidual y)
    (hderiv : ∀ y ∈ Set.Icc (row1SourceCell.lo : ℝ)
        (row1SourceCell.hi : ℝ),
      |deriv smoothPinnedResidual y| ≤ (row1Slope : ℝ)) :
    (row1SourceCell.afterAllowance row1Allowance).modelRemainderValid
      pinnedWeta row1SourceCell_width := by
  apply row1_modelRemainder_of_residual
    (c := row1SourceCell) (allowance := row1Allowance)
    (slope := row1Slope) (by rfl) (by rfl) row1SourceCell_width
    (by norm_num [row1Allowance]) hcenter row1_allowance_check hdiff hderiv

end

end Li2Lean.P0.PinnedResidualRow1

#print axioms Li2Lean.P0.PinnedResidualRow1.row1_modelRemainder_of_residual
