/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSlackSemanticIdentity
import Li2Lean.P0.ConfigContourSelfPotential
import Li2Lean.P0.ConfigLogTaylor
import Li2Lean.P0.ConfigPrimitiveEnclosure
import Li2Lean.Agents.F_L8.MeanValueSlackAdapter
import Li2Lean.Kit.MeanValueRemainder

/-!
# A rational cell checker for the three C-A fields

This file is an interface scaffold, not a closed certificate checker.
`rowCheck` is a Boolean calculation on rational data, but `EvalInput` still
accepts arbitrary interval terms and Fejer moments, and the atan check only
checks interval ordering. No theorem currently ties those fields to the
literal `Weta`/`Wmu` evaluators. `rowCheck_sound` is conditional on an explicit
`EvaluatorSoundness` argument; the repository has no instance of that
structure.

Rows meeting a logarithmic endpoint use the `endpoint` branch. Such rows are
not fed to the mean-value theorem: a density jump or the first frequency
cell can make a finite closed-cell derivative bound false.
-/

namespace Li2Lean.P0.ConfigRowCheck

open ContourKit
open Li2Lean.F_L8
open Li2Lean.P0.Config
open Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.ConfigLogTaylor
open Li2Lean.LogSegment
open Li2Lean.P0.ConfigAnalytic
open Li2Lean.P0.ConfigPrimitiveEnclosure

noncomputable section

/-! ## Singular primitive terms

Endpoint cells contain the continuous primitive
F(v) = v * (log |v| - 1). Its derivative is unbounded at v = 0,
so it is kept outside the regular mean-value residual.
-/

structure SingularPrimitive where
  coefficient : ℚ
  vertex : ℚ
  deriving DecidableEq, Repr

def SingularPrimitive.eval (s : SingularPrimitive) (x : ℝ) : ℝ :=
  (s.coefficient : ℝ) * primitive (x - (s.vertex : ℝ))

theorem singularPrimitive_eval_eq (s : SingularPrimitive) (x : ℝ) :
    s.eval x = (s.coefficient : ℝ) * primitive (x - (s.vertex : ℝ)) := rfl

theorem singularPrimitive_lower_left
    {s : SingularPrimitive} {lo hi x : ℝ}
    (hcoeff : 0 ≤ (s.coefficient : ℝ))
    (hvertex : (s.vertex : ℝ) = lo)
    (hlo : lo ≤ x) (hxhi : x ≤ hi)
    (hradius : hi - lo ≤ 1) :
    (s.coefficient : ℝ) * primitive (hi - lo) ≤ s.eval x := by
  have hx : 0 ≤ x - lo := by linarith
  have hlohi : lo ≤ hi := le_trans hlo hxhi
  have hxa : x - lo ≤ hi - lo := by linarith
  have hprimitive : primitive (hi - lo) ≤ primitive (x - lo) := by
    by_cases hz : hi = lo
    · have hxz : x = lo := by linarith
      simp [hz, hxz]
    · have ha : 0 < hi - lo := sub_pos.mpr (lt_of_le_of_ne hlohi (Ne.symm hz))
      have hF := segmentPrimitive_radial_mono hx hxa ha hradius
      simp only [primitive, abs_of_nonneg hx,
        abs_of_nonneg (show 0 ≤ hi - lo by linarith)]
      linarith
  change (s.coefficient : ℝ) * primitive (hi - lo) ≤
    (s.coefficient : ℝ) * primitive (x - (s.vertex : ℝ))
  rw [hvertex]
  exact mul_le_mul_of_nonneg_left hprimitive hcoeff

theorem singularPrimitive_pinned_loss
    {s : SingularPrimitive} {lo hi : ℝ}
    (hcoeff : 0 ≤ (s.coefficient : ℝ))
    (hvertex : (s.vertex : ℝ) = lo)
    (hlo : lo ≤ hi)
    (hradius : hi - lo ≤ (1 / 8192 : ℝ)) :
    -(s.coefficient : ℝ) *
        ((1 : ℝ) + 13 * (6931473 / 10000000 : ℝ)) / 8192 ≤
      s.eval hi := by
  have hwidth : 0 ≤ hi - lo := by linarith
  have hdy := abs_segmentPrimitive_dyadic (v := hi - lo) 13 (by
    rw [abs_of_nonneg hwidth]
    norm_num
    linarith)
  have hbound : |primitive (hi - lo)| ≤
      ((1 : ℝ) + 13 * (6931473 / 10000000 : ℝ)) / 8192 := by
    have hdy' : |(hi - lo) * (Real.log |hi - lo| - 1)| ≤
        ((1 : ℝ) + 13 * (6931473 / 10000000 : ℝ)) / 8192 := by
      convert hdy using 1 <;> norm_num
    simpa [primitive] using hdy'
  have hneg : -(s.coefficient : ℝ) * |primitive (hi - lo)| ≤
      (s.coefficient : ℝ) * primitive (hi - lo) := by
    have habs : -|primitive (hi - lo)| ≤ primitive (hi - lo) := neg_abs_le _
    calc
      -(s.coefficient : ℝ) * |primitive (hi - lo)| =
          (s.coefficient : ℝ) * (-|primitive (hi - lo)|) := by ring
      _ ≤ (s.coefficient : ℝ) * primitive (hi - lo) :=
        mul_le_mul_of_nonneg_left habs hcoeff
  have hvertexEq := singularPrimitive_lower_left hcoeff hvertex hlo (le_rfl)
    (by linarith)
  calc
    -(s.coefficient : ℝ) *
        ((1 : ℝ) + 13 * (6931473 / 10000000 : ℝ)) / 8192 ≤
      -(s.coefficient : ℝ) * |primitive (hi - lo)| := by nlinarith
    _ ≤ (s.coefficient : ℝ) * primitive (hi - lo) := hneg
    _ ≤ s.eval hi := hvertexEq
/-! ## Literal target functions -/

inductive CellKind
  | contourArc
  | pinnedReal
  | frequency
  deriving DecidableEq, Repr

inductive CellRegime
  | regular
  | endpoint
  deriving DecidableEq, Repr

def targetFunction : CellKind → ℝ → ℝ
  | .contourArc => fun u =>
      Config.Weta ConfigReferenceSymmetry.actualReference
        (Li2Lean.p0EllipsePoint 1 (Real.pi * u))
  | .pinnedReal => fun x =>
      Config.Weta ConfigReferenceSymmetry.actualReference (Complex.ofReal x)
  | .frequency => Config.Wmu ConfigReferenceSymmetry.actualReference

/-! ## Rational evaluator inputs -/

structure LogInput where
  n : ℕ
  domain : QInterval
  enclosure : QInterval
  deriving DecidableEq, Repr

def logInputChecked (d : LogInput) : Bool :=
  Li2Lean.P0.ConfigLogTaylor.checkLogInterval d.n d.domain d.enclosure

def allLogInputsChecked : List LogInput → Bool
  | [] => true
  | d :: ds => logInputChecked d && allLogInputsChecked ds

def atanInputChecked (argument enclosure : QInterval) : Bool :=
  decide (argument.lo ≤ argument.hi ∧ enclosure.lo ≤ enclosure.hi)

structure AtanInput where
  argument : QInterval
  enclosure : QInterval
  deriving DecidableEq, Repr

def AtanInput.checked (a : AtanInput) : Bool :=
  atanInputChecked a.argument a.enclosure

def sumIntervals : List QInterval → QInterval
  | [] => QInterval.point 0
  | I :: Is => QInterval.add I (sumIntervals Is)

def sumRationals : List ℚ → ℚ
  | [] => 0
  | q :: qs => q + sumRationals qs

def absSumRationals : List ℚ → ℚ
  | [] => 0
  | q :: qs => |q| + absSumRationals qs

def logInterval : List LogInput → QInterval
  | [] => QInterval.point 0
  | d :: ds => QInterval.add d.enclosure (logInterval ds)

/-!
These operations sum caller-provided rational intervals. Only logarithm
entries are passed through `checkLogInterval`; the atan enclosure and finite
Fejer moments are not yet checked against their analytic/source definitions.
-/
structure EvalInput where
  logs : List LogInput
  atan : AtanInput
  fejerMoments : List ℚ
  centerTerms : List QInterval
  slopeTerms : List QInterval
  endpointTerms : List QInterval
  endpointLog : QInterval
  deriving DecidableEq, Repr

def EvalInput.checked (e : EvalInput) : Bool :=
  allLogInputsChecked e.logs && e.atan.checked

def centerInterval (e : EvalInput) : QInterval :=
  QInterval.add
    (QInterval.add (sumIntervals e.centerTerms) (logInterval e.logs))
    (QInterval.add e.atan.enclosure
      (QInterval.point (sumRationals e.fejerMoments)))

def slopeInterval (e : EvalInput) : QInterval :=
  QInterval.add
    (QInterval.add (sumIntervals e.slopeTerms) (logInterval e.logs))
    (QInterval.add e.atan.enclosure
      (QInterval.point (absSumRationals e.fejerMoments)))

def endpointInterval (e : EvalInput) : QInterval :=
  QInterval.add
    (QInterval.add (sumIntervals e.endpointTerms) (logInterval e.logs))
    (QInterval.add e.atan.enclosure
      (QInterval.point (sumRationals e.fejerMoments)))

def centerLower (e : EvalInput) : ℚ := (centerInterval e).lo

def slopeUpper (e : EvalInput) : ℚ := (slopeInterval e).hi

def endpointLower (e : EvalInput) : ℚ := (endpointInterval e).lo

def endpointLogUpper (e : EvalInput) : ℚ := e.endpointLog.hi

/-! ## Cell data and the executable check -/

structure CellData where
  kind : CellKind
  regime : CellRegime
  lo : ℚ
  hi : ℚ
  floor : ℚ
  allowance : ℚ
  eval : EvalInput
  deriving DecidableEq, Repr

def CellData.receipt (c : CellData) : ReceiptCell :=
  ⟨c.lo, c.hi, c.floor⟩

def regularArithmeticCheck (c : CellData) : Bool :=
  decide (c.lo ≤ c.hi ∧ 0 ≤ c.allowance ∧
    0 ≤ slopeUpper c.eval ∧
    slopeUpper c.eval * rationalCellHalfWidth c.lo c.hi ≤ c.allowance ∧
    (c.floor : ℚ) ≤ centerLower c.eval ∧
    (c.floor : ℚ) - c.allowance ≤
      centerLower c.eval - slopeUpper c.eval *
        rationalCellHalfWidth c.lo c.hi)

def endpointArithmeticCheck (c : CellData) : Bool :=
  decide (c.lo ≤ c.hi ∧ 0 ≤ c.allowance ∧
    0 ≤ endpointLogUpper c.eval ∧
    (c.floor : ℚ) - c.allowance ≤
      endpointLower c.eval - slopeUpper c.eval *
        rationalCellHalfWidth c.lo c.hi *
          (1 + endpointLogUpper c.eval))

/-- The only executable row decision. All fields consumed here are `ℚ`. -/
def rowCheck (c : CellData) : Bool :=
  c.eval.checked &&
    match c.regime with
    | .regular => regularArithmeticCheck c
    | .endpoint => endpointArithmeticCheck c

theorem rowCheck_spec_regular {c : CellData}
    (h : rowCheck c = true) (hr : c.regime = .regular) :
    c.eval.checked = true ∧
      c.lo ≤ c.hi ∧ 0 ≤ c.allowance ∧ 0 ≤ slopeUpper c.eval ∧
      slopeUpper c.eval * rationalCellHalfWidth c.lo c.hi ≤ c.allowance ∧
      (c.floor : ℚ) ≤ centerLower c.eval ∧
      (c.floor : ℚ) - c.allowance ≤
        centerLower c.eval - slopeUpper c.eval *
          rationalCellHalfWidth c.lo c.hi := by
  have hp : c.eval.checked = true ∧ regularArithmeticCheck c = true := by
    simpa [rowCheck, hr] using h
  have ha := of_decide_eq_true hp.2
  exact ⟨hp.1, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2.1,
    ha.2.2.2.2.1, ha.2.2.2.2.2⟩

theorem rowCheck_spec_endpoint {c : CellData}
    (h : rowCheck c = true) (hr : c.regime = .endpoint) :
    c.eval.checked = true ∧
      c.lo ≤ c.hi ∧ 0 ≤ c.allowance ∧ 0 ≤ endpointLogUpper c.eval ∧
      (c.floor : ℚ) - c.allowance ≤
        endpointLower c.eval - slopeUpper c.eval *
          rationalCellHalfWidth c.lo c.hi *
            (1 + endpointLogUpper c.eval) := by
  have hp : c.eval.checked = true ∧ endpointArithmeticCheck c = true := by
    simpa [rowCheck, hr] using h
  have ha := of_decide_eq_true hp.2
  exact ⟨hp.1, ha.1, ha.2.1, ha.2.2.1, ha.2.2.2⟩

/-!
`EvaluatorSoundness` records the missing semantic proof obligations. It is not
instantiated in this module: the centre, regular derivative, and endpoint
modulus facts still have to be derived from the literal Weta/Wmu identities
and from checked evaluator inputs. The contour Fourier obligation remains
explicit.
-/

structure EvaluatorSoundness where
  contourFourier :
    ConfigContourSelfPotential.ContourSelfPotentialFourierObligation
  center_sound : ∀ (k : CellKind) (e : EvalInput) (center : ℚ),
    e.checked = true →
      (centerLower e : ℝ) ≤
        targetFunction k (center : ℝ)
  regular_differentiable : ∀ (k : CellKind) (e : EvalInput)
    (lo hi : ℚ),
    e.checked = true → lo ≤ hi →
    ∀ y ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      DifferentiableAt ℝ (targetFunction k) y
  regular_derivative : ∀ (k : CellKind) (e : EvalInput)
    (lo hi : ℚ),
    e.checked = true → lo ≤ hi →
    ∀ y ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      |deriv (targetFunction k) y| ≤ (slopeUpper e : ℝ)
  endpoint_modulus : ∀ (k : CellKind) (e : EvalInput)
    (lo hi : ℚ),
    e.checked = true → lo ≤ hi →
    ∀ x ∈ Set.Icc (lo : ℝ) (hi : ℝ),
      (endpointLower e : ℝ) - (slopeUpper e : ℝ) *
          (rationalCellHalfWidth lo hi : ℝ) *
            (1 + (endpointLogUpper e : ℝ)) ≤
        targetFunction k x

def midpoint (c : CellData) : ℚ := rationalCellCenter c.lo c.hi

def centerAt (c : CellData) : ℝ := (midpoint c : ℝ)

def CellData.receiptAfterAllowance (c : CellData) : ReceiptCell :=
  c.receipt.afterAllowance c.allowance

private theorem receipt_width {c : CellData} (h : c.lo ≤ c.hi) :
    c.receiptAfterAllowance.lo ≤ c.receiptAfterAllowance.hi := by
  change c.lo ≤ c.hi
  exact h

theorem regular_center_sound (S : EvaluatorSoundness) (c : CellData)
    (hcheck : rowCheck c = true) (hr : c.regime = .regular) :
    (centerLower c.eval : ℝ) ≤ targetFunction c.kind (centerAt c) := by
  have hs := rowCheck_spec_regular hcheck hr
  have h := S.center_sound c.kind c.eval (midpoint c) hs.1
  simpa [centerAt, midpoint] using h

private theorem regular_floor_center_sound (S : EvaluatorSoundness) (c : CellData)
    (hcheck : rowCheck c = true) (hr : c.regime = .regular) :
    (c.floor : ℝ) ≤ targetFunction c.kind (centerAt c) := by
  have hs := rowCheck_spec_regular hcheck hr
  have hc := regular_center_sound S c hcheck hr
  have hf : (c.floor : ℝ) ≤ (centerLower c.eval : ℝ) := by
    exact_mod_cast hs.2.2.2.2.2.1
  exact hf.trans hc

theorem regular_model_sound (S : EvaluatorSoundness) (c : CellData)
    (hcheck : rowCheck c = true) (hr : c.regime = .regular) :
    (c.receiptAfterAllowance).modelRemainderValid
      (targetFunction c.kind) (receipt_width (rowCheck_spec_regular hcheck hr).2.1) := by
  have hs := rowCheck_spec_regular hcheck hr
  have hw : c.receipt.lo ≤ c.receipt.hi := by
    simpa [CellData.receipt] using hs.2.1
  have hallow : ContourKit.checkMeanValueAllowance c.lo c.hi
      c.allowance (slopeUpper c.eval) = true := by
    apply decide_eq_true_eq.mpr
    exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  apply ReceiptCell.modelRemainderValid_afterAllowance
    c.receipt c.allowance (slopeUpper c.eval)
    hw hallow
  · simpa [CellData.receipt, CellData.receiptAfterAllowance, midpoint,
      centerAt] using regular_floor_center_sound S c hcheck hr
  · intro y hy
    exact S.regular_differentiable c.kind c.eval c.lo c.hi
      hs.1 hs.2.1 y hy
  · intro y hy
    exact S.regular_derivative c.kind c.eval c.lo c.hi
      hs.1 hs.2.1 y hy

theorem endpoint_model_sound (S : EvaluatorSoundness) (c : CellData)
    (hcheck : rowCheck c = true) (hr : c.regime = .endpoint) :
    (c.receiptAfterAllowance).modelRemainderValid
      (targetFunction c.kind) (receipt_width (rowCheck_spec_endpoint hcheck hr).2.1) := by
  have hs := rowCheck_spec_endpoint hcheck hr
  intro x hx
  have hmod := S.endpoint_modulus c.kind c.eval c.lo c.hi
    hs.1 hs.2.1 x hx
  have hbudget : (c.floor : ℝ) - (c.allowance : ℝ) ≤
      (endpointLower c.eval : ℝ) - (slopeUpper c.eval : ℝ) *
        (rationalCellHalfWidth c.lo c.hi : ℝ) *
          (1 + (endpointLogUpper c.eval : ℝ)) := by
    exact_mod_cast hs.2.2.2.2
  simp only [ReceiptCell.modelRemainderValid, ReceiptCell.model,
    CellData.receiptAfterAllowance, CellData.receipt,
    TaylorLowerRemainderValid, horner, Rat.cast_zero, mul_zero, add_zero,
    ReceiptCell.afterAllowance] at hx ⊢
  push_cast
  linarith

private theorem rowCheck_width (c : CellData) (hcheck : rowCheck c = true) :
    c.lo ≤ c.hi := by
  cases hr : c.regime with
  | regular => exact (rowCheck_spec_regular hcheck hr).2.1
  | endpoint => exact (rowCheck_spec_endpoint hcheck hr).2.1

/-- Conditional wrapper for all three literal fields. It composes the row's
rational arithmetic with the supplied semantic obligations; it does not
provide or certify an `EvaluatorSoundness` instance. The first frequency row
must be supplied with `regime = endpoint`, never with the finite-slope branch.
-/
theorem rowCheck_sound (S : EvaluatorSoundness) (c : CellData)
    (hcheck : rowCheck c = true) :
    (c.receiptAfterAllowance).modelRemainderValid
      (targetFunction c.kind) (receipt_width (rowCheck_width c hcheck)) := by
  cases hr : c.regime with
  | regular => exact regular_model_sound S c hcheck hr
  | endpoint => exact endpoint_model_sound S c hcheck hr

/-!
## Source-locked replacement interface

`EvaluatorSoundness` above is retained as a legacy conditional wrapper.  It
quantifies over arbitrary `EvalInput` values and therefore has no canonical
inhabitant.  The interface below fixes one source row, its index, its
evaluator data, and its target function.  The bridge fields are the remaining
semantic obligations for this row; they are not inferred from `rowCheck`.
-/

def sourceRowIndex : ℕ := 1

theorem sourceRowIndex_lt_frequency_chunk :
    sourceRowIndex < ConfigData.frequencyCellsChunk000.length := by
  norm_num [sourceRowIndex, ConfigData.frequencyCellsChunk000_length]

def sourceRowRawReceipt : ReceiptCell :=
  ⟨20499 / 40960, 10259 / 20480, 947477683 / 500000000⟩

set_option maxRecDepth 100000 in
theorem sourceRowRawReceipt_matches_data :
    ConfigData.frequencyCellsChunk000[sourceRowIndex]'
        sourceRowIndex_lt_frequency_chunk = sourceRowRawReceipt := by
  norm_num [sourceRowIndex, sourceRowRawReceipt,
    ConfigData.frequencyCellsChunk000]

def sourceRowAllowance : ℚ := 1 / 100

def sourceRowEval : EvalInput :=
  { logs := []
    atan := ⟨QInterval.point 0, QInterval.point 0⟩
    fejerMoments := []
    centerTerms := [QInterval.point (947477683 / 500000000)]
    slopeTerms := [QInterval.point 30]
    endpointTerms := []
    endpointLog := QInterval.point 0 }

def sourceRowSlope : ℚ := slopeUpper sourceRowEval

def sourceRow : CellData :=
  { kind := .frequency
    regime := .regular
    lo := 20499 / 40960
    hi := 10259 / 20480
    floor := 947477683 / 500000000
    allowance := sourceRowAllowance
    eval := sourceRowEval }

theorem sourceRow_receipt_eq_raw : sourceRow.receipt = sourceRowRawReceipt := by
  rfl

theorem sourceRow_check : rowCheck sourceRow = true := by
  norm_num [rowCheck, sourceRow, sourceRowEval, sourceRowAllowance,
    sourceRowRawReceipt, sourceRowSlope, EvalInput.checked,
    AtanInput.checked, atanInputChecked, regularArithmeticCheck,
    centerLower, slopeUpper, centerInterval, slopeInterval, endpointInterval,
    allLogInputsChecked, logInputChecked, sumIntervals, logInterval,
    sumRationals, absSumRationals,
    rationalCellHalfWidth, QInterval.point, QInterval.add]

theorem sourceRow_raw_width : sourceRowRawReceipt.lo ≤ sourceRowRawReceipt.hi := by
  norm_num [sourceRowRawReceipt]

def sourceRowAdjusted : ReceiptCell :=
  sourceRowRawReceipt.afterAllowance sourceRowAllowance

def sourceRowLower : ℚ := sourceRowRawReceipt.lower - sourceRowAllowance

theorem sourceRowAdjusted_lower : sourceRowAdjusted.lower = sourceRowLower := by
  rfl

theorem sourceRowAdjusted_width : sourceRowAdjusted.lo ≤ sourceRowAdjusted.hi := by
  change sourceRowRawReceipt.lo ≤ sourceRowRawReceipt.hi
  exact sourceRow_raw_width

def sourceRowFunction : ℝ → ℝ := targetFunction sourceRow.kind

def sourceRowCenter : ℚ :=
  rationalCellCenter sourceRowRawReceipt.lo sourceRowRawReceipt.hi

def sourceRowHalfWidth : ℚ :=
  rationalCellHalfWidth sourceRowRawReceipt.lo sourceRowRawReceipt.hi

/-!
The first three fields are the evaluator, differentiability, and derivative
residuals for the fixed row.  `original_floor_margin` is stronger: it is the
additional margin needed to prove the raw source receipt, rather than the
receipt with the row allowance spent.  Keeping it explicit prevents the
arithmetic checker from being mistaken for an analytic proof.
-/
structure SourceRowBridge : Prop where
  center_sound :
    (centerLower sourceRow.eval : ℝ) ≤ sourceRowFunction (sourceRowCenter : ℝ)
  regular_differentiable :
    ∀ y ∈ Set.Icc (sourceRowRawReceipt.lo : ℝ)
        (sourceRowRawReceipt.hi : ℝ),
      DifferentiableAt ℝ sourceRowFunction y
  regular_derivative :
    ∀ y ∈ Set.Icc (sourceRowRawReceipt.lo : ℝ)
        (sourceRowRawReceipt.hi : ℝ),
      |deriv sourceRowFunction y| ≤ (sourceRowSlope : ℝ)
  original_floor_margin :
    (sourceRowRawReceipt.lower : ℝ) ≤
      sourceRowFunction (sourceRowCenter : ℝ) -
        (sourceRowSlope : ℝ) * (sourceRowHalfWidth : ℝ)

theorem sourceRowLower_check (B : SourceRowBridge) :
    (sourceRowLower : ℝ) ≤
      sourceRowFunction (sourceRowCenter : ℝ) -
        (sourceRowSlope : ℝ) * (sourceRowHalfWidth : ℝ) := by
  have hs := rowCheck_spec_regular (c := sourceRow) sourceRow_check rfl
  have hbudget :
      (sourceRowLower : ℝ) ≤
        (centerLower sourceRow.eval : ℝ) -
          (sourceRowSlope : ℝ) * (sourceRowHalfWidth : ℝ) := by
    have hbudget' := hs.2.2.2.2.2.2
    have hbudgetQ :
        sourceRowRawReceipt.lower - sourceRowAllowance ≤
          centerLower sourceRow.eval - sourceRowSlope * sourceRowHalfWidth := by
      simpa [sourceRow, sourceRowEval, sourceRowRawReceipt,
      sourceRowAllowance, sourceRowLower, sourceRowSlope, sourceRowHalfWidth,
      centerLower, slopeUpper, centerInterval, slopeInterval,
      sumIntervals, logInterval, sumRationals, absSumRationals,
      QInterval.point, QInterval.add, rationalCellHalfWidth] using hbudget'
    exact_mod_cast hbudgetQ
  have hcenter := B.center_sound
  exact le_trans hbudget (by linarith)

/-!
This is the honest row theorem currently supported by the mean-value
allowance API.  It returns the fixed raw `ReceiptCell` after exactly one
subtraction of `sourceRowAllowance`; no second allowance is hidden in the
statement.
-/
theorem sourceRow_adjusted_modelRemainderValid (B : SourceRowBridge) :
    sourceRowAdjusted.modelRemainderValid sourceRowFunction
      sourceRowAdjusted_width := by
  have hs := rowCheck_spec_regular (c := sourceRow) sourceRow_check rfl
  have hallow :
      checkMeanValueAllowance sourceRowRawReceipt.lo sourceRowRawReceipt.hi
        sourceRowAllowance sourceRowSlope = true := by
    apply decide_eq_true_eq.mpr
    exact ⟨hs.2.1, hs.2.2.1, hs.2.2.2.1, hs.2.2.2.2.1⟩
  have hcenter :
      (sourceRowRawReceipt.lower : ℝ) ≤
        sourceRowFunction (rationalCellCenter
          sourceRowRawReceipt.lo sourceRowRawReceipt.hi : ℝ) := by
    have hc := B.center_sound
    have hcenter_eq :
        centerLower sourceRow.eval = sourceRowRawReceipt.lower := by
      norm_num [sourceRow, sourceRowEval, sourceRowRawReceipt, centerLower,
        centerInterval, sumIntervals, logInterval, sumRationals,
        QInterval.point, QInterval.add]
    rw [hcenter_eq] at hc
    simpa [sourceRowFunction, sourceRowCenter, sourceRow,
      sourceRowRawReceipt] using hc
  have hdiff :
      ∀ y ∈ Set.Icc (sourceRowRawReceipt.lo : ℝ)
          (sourceRowRawReceipt.hi : ℝ),
        DifferentiableAt ℝ sourceRowFunction y :=
    B.regular_differentiable
  have hderiv :
      ∀ y ∈ Set.Icc (sourceRowRawReceipt.lo : ℝ)
          (sourceRowRawReceipt.hi : ℝ),
        |deriv sourceRowFunction y| ≤ (sourceRowSlope : ℝ) :=
    B.regular_derivative
  have hraw := ReceiptCell.modelRemainderValid_afterAllowance
    sourceRowRawReceipt sourceRowAllowance sourceRowSlope
    sourceRow_raw_width hallow hcenter hdiff hderiv
  simpa [sourceRowAdjusted] using hraw

/-!
The raw receipt needs a separate stronger analytic margin.  This theorem does
not derive that margin from `sourceRow_check`: the bridge must prove the
center value is already at least one full Lipschitz half-width above the raw
floor.  Thus a caller cannot silently reuse the allowance twice.
-/
theorem sourceRow_original_modelRemainderValid (B : SourceRowBridge) :
    sourceRowRawReceipt.modelRemainderValid sourceRowFunction
      sourceRow_raw_width := by
  intro x hx
  change (sourceRowRawReceipt.lo : ℝ) ≤ x ∧
    x ≤ (sourceRowRawReceipt.hi : ℝ) at hx
  have hcenter_mem :
      (rationalCellCenter sourceRowRawReceipt.lo sourceRowRawReceipt.hi : ℝ) ∈
        Set.Icc (sourceRowRawReceipt.lo : ℝ)
          (sourceRowRawReceipt.hi : ℝ) := by
    have h := rationalCellCenter_mem sourceRow_raw_width
    exact ⟨by exact_mod_cast h.1, by exact_mod_cast h.2⟩
  have hdist := abs_sub_center_le_halfWidth sourceRow_raw_width hx.1 hx.2
  have hslope : (0 : ℝ) ≤ (sourceRowSlope : ℝ) := by
    have hs := rowCheck_spec_regular (c := sourceRow) sourceRow_check rfl
    simpa [sourceRowSlope, sourceRowEval, slopeUpper, slopeInterval,
      sumIntervals, logInterval, absSumRationals, QInterval.point,
      QInterval.add] using (show 0 ≤ slopeUpper sourceRow.eval from
        hs.2.2.2.1)
  have hLip :
      |sourceRowFunction x -
          sourceRowFunction (rationalCellCenter
            sourceRowRawReceipt.lo sourceRowRawReceipt.hi : ℝ)| ≤
        (sourceRowSlope : ℝ) *
          |x - (rationalCellCenter sourceRowRawReceipt.lo
            sourceRowRawReceipt.hi : ℝ)| := by
    simpa only [Real.norm_eq_abs] using
      (convex_Icc (sourceRowRawReceipt.lo : ℝ)
        (sourceRowRawReceipt.hi : ℝ)).norm_image_sub_le_of_norm_deriv_le
        (fun y hy => B.regular_differentiable y hy)
        (fun y hy => by
          simpa only [Real.norm_eq_abs] using B.regular_derivative y hy)
        hcenter_mem hx
  have hLipRadius :
      |sourceRowFunction x -
          sourceRowFunction (rationalCellCenter
            sourceRowRawReceipt.lo sourceRowRawReceipt.hi : ℝ)| ≤
        (sourceRowSlope : ℝ) * (sourceRowHalfWidth : ℝ) := by
    exact le_trans hLip (mul_le_mul_of_nonneg_left hdist hslope)
  have hlower := (abs_le.mp hLipRadius).1
  have hmargin := B.original_floor_margin
  have hcenter_eq : sourceRowCenter =
      rationalCellCenter sourceRowRawReceipt.lo sourceRowRawReceipt.hi := rfl
  rw [hcenter_eq] at hmargin
  have htarget : (sourceRowRawReceipt.lower : ℝ) ≤ sourceRowFunction x := by
    linarith
  simp only [ReceiptCell.modelRemainderValid, ReceiptCell.model,
    TaylorLowerRemainderValid, horner, Rat.cast_zero, mul_zero, add_zero]
  push_cast
  linarith

end

end Li2Lean.P0.ConfigRowCheck

#print axioms Li2Lean.P0.ConfigRowCheck.rowCheck_sound
#print axioms Li2Lean.P0.ConfigRowCheck.sourceRowLower_check
#print axioms Li2Lean.P0.ConfigRowCheck.sourceRow_adjusted_modelRemainderValid
#print axioms Li2Lean.P0.ConfigRowCheck.sourceRow_original_modelRemainderValid
