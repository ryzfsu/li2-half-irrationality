/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PinnedResidualRow1
import Li2Lean.P0.ConfigLogTaylor
import Li2Lean.Kit.IntervalChecker
import Li2Lean.Kit.TightIntervalChecker

/-!
# Interval/log evaluator for the pinned C-A smooth residual

This module records the reusable evaluator layer for the first pinned segment.
It uses the rational `QInterval` checker and the proved finite atanh remainder
from `ConfigLogTaylor`; no numerical logarithm or contour estimate is accepted
as an unchecked premise.

Attribution: the shape of the positive-log cell and finite interval
composition was informed by the following Apache-2.0 OpenAI Math reference
modules (from the pinned `openai/math` source snapshot):
`BarrierChebyshevLogFormula.lean`, `BarrierLogRatConstants.lean`, and
`ManuscriptBarrierFieldIntervals.lean`.  Their Catalan-specific formulas,
constants, namespaces, and data are not copied here.  In particular, their
Chebyshev quadratic identity and `[1,2]` scaled-log bounds do not apply to the
pinned primitive arguments, which can have either sign and can approach zero.
The Li2 evaluator therefore keeps the source-locked endpoint formulas and
uses only the generic atanh/log and interval-composition pattern.

The final residual theorem below is intentionally a semantic interface: the
finite endpoint, contour, and Fejer bounds must still be proved separately.
-/

namespace Li2Lean.P0.PinnedResidualEvaluator

noncomputable section

open ContourKit
open Li2Lean.LogSegment
open Li2Lean.P0.ConfigLogTaylor
open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigInteriorContourPotential
open Li2Lean.P0.PinnedResidualRow1

/-! ## Positive logarithm cells -/

/-- A rational domain/enclosure pair for a positive real logarithm. -/
structure LogCell where
  degree : ℕ
  domain : QInterval
  enclosure : QInterval
  deriving DecidableEq, Repr

def LogCell.checked (c : LogCell) : Bool :=
  checkLogInterval c.degree c.domain c.enclosure

theorem logCell_sound {c : LogCell} (hcheck : c.checked = true)
    {x : ℝ} (hx : c.domain.Contains x) :
    c.enclosure.Contains (Real.log x) := by
  exact checkLogInterval_sound hcheck hx

/-! ## Primitive cells and finite interval composition -/

/--
An interval for `primitive v = v * (log |v| - 1)`. The log domain is stored
separately because a primitive argument may be negative even though `|v|` is
positive. A caller supplies the sign/absolute-value containment explicitly;
this keeps zero-crossing cells visible instead of silently assuming positivity.
-/
structure PrimitiveLogCell where
  argument : QInterval
  log : LogCell
  deriving DecidableEq, Repr

def PrimitiveLogCell.interval (c : PrimitiveLogCell) : QInterval :=
  QInterval.tightMul c.argument
    (QInterval.sub c.log.enclosure (QInterval.point 1))

def PrimitiveLogCell.checked (c : PrimitiveLogCell) : Bool := c.log.checked

theorem primitiveLogCell_sound {c : PrimitiveLogCell}
    (hcheck : c.checked = true) {v : ℝ}
    (hv : c.argument.Contains v)
    (habs : c.log.domain.Contains |v|) :
    c.interval.Contains (primitive v) := by
  have hlog : c.log.enclosure.Contains (Real.log |v|) :=
    logCell_sound hcheck habs
  have hshift :
      (QInterval.sub c.log.enclosure (QInterval.point 1)).Contains
        (Real.log |v| - 1) :=
    by simpa using QInterval.mem_sub hlog (QInterval.mem_point (1 : ℚ))
  have hmul := QInterval.mem_tightMul hv hshift
  simpa only [PrimitiveLogCell.interval, primitive] using hmul

def sumIntervals : List QInterval → QInterval
  | [] => QInterval.point 0
  | I :: Is => QInterval.add I (sumIntervals Is)

theorem sumIntervals_sound (Is : List QInterval) (xs : List ℝ)
    (h : List.Forall₂ QInterval.Contains Is xs) :
    (sumIntervals Is).Contains xs.sum := by
  induction Is generalizing xs with
  | nil =>
      cases h
      simp [sumIntervals, QInterval.Contains, QInterval.point]
  | cons I Is ih =>
      cases xs with
      | nil => cases h
      | cons x xs =>
          cases h with
          | cons hI hrest =>
              have hs := ih xs hrest
              simpa only [sumIntervals, List.sum_cons] using
                QInterval.mem_add hI hs

def scaleInterval (q : ℚ) (I : QInterval) : QInterval :=
  if hq : 0 ≤ q then
    ⟨q * I.lo, q * I.hi, mul_le_mul_of_nonneg_left I.ordered hq⟩
  else
    ⟨q * I.hi, q * I.lo,
      mul_le_mul_of_nonpos_left I.ordered (le_of_not_ge hq)⟩

theorem mem_scaleInterval {q : ℚ} {I : QInterval} {x : ℝ}
    (hx : I.Contains x) : (scaleInterval q I).Contains (q * x) := by
  by_cases hq0 : 0 ≤ q
  · have hqR : 0 ≤ (q : ℝ) := by exact_mod_cast hq0
    rw [scaleInterval, dif_pos hq0]
    simp only [QInterval.Contains, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hqR,
      mul_le_mul_of_nonneg_left hx.2 hqR⟩
  · have hqQ : q ≤ 0 := le_of_not_ge hq0
    have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast hqQ
    rw [scaleInterval, dif_neg hq0]
    simp only [QInterval.Contains, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hqR,
      mul_le_mul_of_nonpos_left hx.1 hqR⟩

def sumPrimitiveIntervals (cs : List PrimitiveLogCell) : QInterval :=
  sumIntervals (cs.map PrimitiveLogCell.interval)

theorem sumPrimitiveIntervals_sound (cs : List PrimitiveLogCell) (vs : List ℝ)
    (h : List.Forall₂
      (fun c v => c.checked = true ∧ c.argument.Contains v ∧
        c.log.domain.Contains |v|) cs vs) :
    (sumPrimitiveIntervals cs).Contains
      (vs.map primitive).sum := by
  have hmap : List.Forall₂ QInterval.Contains
      (cs.map PrimitiveLogCell.interval) (vs.map primitive) := by
    induction h with
    | nil => exact .nil
    | @cons c v cs vs hc hrest ih =>
        exact .cons (primitiveLogCell_sound hc.1 hc.2.1 hc.2.2) ih
  exact sumIntervals_sound _ _ hmap

structure WeightedPrimitiveDifference where
  coefficient : ℚ
  left : PrimitiveLogCell
  right : PrimitiveLogCell
  deriving DecidableEq, Repr

def WeightedPrimitiveDifference.interval (d : WeightedPrimitiveDifference) :
    QInterval :=
  scaleInterval d.coefficient
    (QInterval.sub d.left.interval d.right.interval)

theorem weightedPrimitiveDifference_sound (d : WeightedPrimitiveDifference)
    {leftValue rightValue : ℝ}
    (hleft : d.left.interval.Contains (primitive leftValue))
    (hright : d.right.interval.Contains (primitive rightValue)) :
    d.interval.Contains
      ((d.coefficient : ℝ) * (primitive leftValue - primitive rightValue)) := by
  have hdiff := QInterval.mem_sub hleft hright
  simpa only [WeightedPrimitiveDifference.interval] using
    (mem_scaleInterval (q := d.coefficient) hdiff)

def sumWeightedPrimitiveDifferences
    (ds : List WeightedPrimitiveDifference) : QInterval :=
  sumIntervals (ds.map WeightedPrimitiveDifference.interval)

theorem sumWeightedPrimitiveDifferences_sound
    (ds : List WeightedPrimitiveDifference) (values : List ℝ)
    (h : List.Forall₂ QInterval.Contains
      (ds.map WeightedPrimitiveDifference.interval) values) :
    (sumWeightedPrimitiveDifferences ds).Contains values.sum :=
  sumIntervals_sound _ _ h

/-! ## Source-locked smooth residual expression -/

def endpointA0 (x : ℝ) : ℝ :=
  primitive (x - 1 / 4) - primitive (x - 5 / 4) +
    (primitive x - primitive (x - 2))

def endpointPhi (x : ℝ) : ℝ :=
  x * Real.log 2 + (primitive (x + 1 / 2) - primitive x) +
    1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)

def pinnedEndpointSum (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 32,
    referenceDensity ConfigData.pinnedMassUnits j *
      (primitive (x - referenceCellLeft (1 / 4) j) -
        primitive (x - referenceCellRight (1 / 4) j))

def frequencyEndpointSum (x : ℝ) : ℝ :=
  ∑ j ∈ Finset.range 160,
    referenceDensity ConfigData.frequencyMassUnits j *
      (primitive (x + referenceCellRight (1 / 2) j) -
        primitive (x + referenceCellLeft (1 / 2) j))

def smoothResidualFormula (x : ℝ) : ℝ :=
  endpointA0 x - endpointPhi x -
    2 * (pinnedEndpointSum x + contourReferencePotential (x : ℂ)) -
    frequencyEndpointSum x -
    (singularCoefficient : ℝ) * primitive (x - 1 / 4)

theorem smoothPinnedResidual_eq_formula (x : ℝ) :
    smoothPinnedResidual x = smoothResidualFormula x := by
  simpa only [smoothResidualFormula, endpointA0, endpointPhi,
    pinnedEndpointSum, frequencyEndpointSum] using
    (smoothPinnedResidual_explicit x)

/-- Component intervals for the exact source-locked residual formula. -/
structure SmoothResidualBounds where
  endpointA0 : QInterval
  endpointPhi : QInterval
  pinnedReference : QInterval
  contour : QInterval
  frequencyReference : QInterval
  singular : QInterval
  deriving DecidableEq, Repr

def SmoothResidualBounds.interval (b : SmoothResidualBounds) : QInterval :=
  QInterval.sub
    (QInterval.sub
      (QInterval.sub b.endpointA0 b.endpointPhi)
      (scaleInterval 2
        (QInterval.add b.pinnedReference b.contour)))
    (QInterval.add b.frequencyReference
      (scaleInterval singularCoefficient b.singular))

theorem smoothResidual_mem_interval (b : SmoothResidualBounds) {x : ℝ}
    (hA0 : b.endpointA0.Contains (endpointA0 x))
    (hphi : b.endpointPhi.Contains (endpointPhi x))
    (hpinned : b.pinnedReference.Contains (pinnedEndpointSum x))
    (hcontour : b.contour.Contains
      (contourReferencePotential (x : ℂ)))
    (hfrequency : b.frequencyReference.Contains (frequencyEndpointSum x))
    (hsingular : b.singular.Contains (primitive (x - 1 / 4))) :
    b.interval.Contains (smoothPinnedResidual x) := by
  have hpc := QInterval.mem_add hpinned hcontour
  have htwo := mem_scaleInterval (q := (2 : ℚ)) hpc
  have ha0phi := QInterval.mem_sub hA0 hphi
  have hleft := QInterval.mem_sub ha0phi htwo
  have hsing := mem_scaleInterval (q := singularCoefficient) hsingular
  have hright := QInterval.mem_add hfrequency hsing
  have htotal := QInterval.mem_sub hleft hright
  rw [smoothPinnedResidual_eq_formula]
  rw [show smoothResidualFormula x =
      endpointA0 x - endpointPhi x -
        2 * (pinnedEndpointSum x + contourReferencePotential (x : ℂ)) -
        (frequencyEndpointSum x +
          (singularCoefficient : ℝ) * primitive (x - 1 / 4)) by
    unfold smoothResidualFormula
    ring]
  exact htotal

/-! ## Exact theorem shape for connecting a bound to row one -/

theorem row1_center_bound_of_interval
    {b : SmoothResidualBounds}
    (hbound : b.interval.Contains
      (smoothPinnedResidual
        (rationalCellCenter row1SourceCell.lo row1SourceCell.hi)))
    (hnumeric :
      (row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
        (singularCoefficient : ℝ) *
            primitive ((1025 / 4096 : ℝ) - 1 / 4) +
          (b.interval.lo : ℝ) -
        (row1Slope : ℝ) *
          (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ)) :
    (row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
      (singularCoefficient : ℝ) *
          primitive ((1025 / 4096 : ℝ) - 1 / 4) +
        smoothPinnedResidual
          (rationalCellCenter row1SourceCell.lo row1SourceCell.hi) -
        (row1Slope : ℚ) *
          (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ) := by
  linarith [hbound.1]

theorem row1_modelRemainder_from_evaluator
    {b : SmoothResidualBounds}
    (hbound : b.interval.Contains
      (smoothPinnedResidual
        (rationalCellCenter row1SourceCell.lo row1SourceCell.hi)))
    (hnumeric :
      (row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
        (singularCoefficient : ℝ) *
            primitive ((1025 / 4096 : ℝ) - 1 / 4) +
          (b.interval.lo : ℝ) -
        (row1Slope : ℝ) *
          (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ))
    (hdiff : ∀ y ∈ Set.Icc (row1SourceCell.lo : ℝ)
        (row1SourceCell.hi : ℝ), DifferentiableAt ℝ smoothPinnedResidual y)
    (hderiv : ∀ y ∈ Set.Icc (row1SourceCell.lo : ℝ)
        (row1SourceCell.hi : ℝ),
      |deriv smoothPinnedResidual y| ≤ (row1Slope : ℝ)) :
    (row1SourceCell.afterAllowance row1Allowance).modelRemainderValid
      ConfigContourSelfPotential.pinnedWeta row1SourceCell_width := by
  apply row1_modelRemainder_of_actual_residual
  · exact row1_center_bound_of_interval hbound hnumeric
  · exact hdiff
  · exact hderiv

theorem row1_modelRemainder_from_component_intervals
    {b : SmoothResidualBounds}
    (hA0 : b.endpointA0.Contains
      (endpointA0 (rationalCellCenter row1SourceCell.lo row1SourceCell.hi)))
    (hphi : b.endpointPhi.Contains
      (endpointPhi (rationalCellCenter row1SourceCell.lo row1SourceCell.hi)))
    (hpinned : b.pinnedReference.Contains
      (pinnedEndpointSum (rationalCellCenter row1SourceCell.lo row1SourceCell.hi)))
    (hcontour : b.contour.Contains
      (contourReferencePotential
        ((rationalCellCenter row1SourceCell.lo row1SourceCell.hi : ℝ) : ℂ)))
    (hfrequency : b.frequencyReference.Contains
      (frequencyEndpointSum (rationalCellCenter row1SourceCell.lo row1SourceCell.hi)))
    (hsingular : b.singular.Contains
      (primitive (rationalCellCenter row1SourceCell.lo row1SourceCell.hi - 1 / 4)))
    (hnumeric :
      (row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
        (singularCoefficient : ℝ) *
            primitive ((1025 / 4096 : ℝ) - 1 / 4) +
          (b.interval.lo : ℝ) -
        (row1Slope : ℝ) *
          (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ))
    (hdiff : ∀ y ∈ Set.Icc (row1SourceCell.lo : ℝ)
        (row1SourceCell.hi : ℝ), DifferentiableAt ℝ smoothPinnedResidual y)
    (hderiv : ∀ y ∈ Set.Icc (row1SourceCell.lo : ℝ)
        (row1SourceCell.hi : ℝ),
      |deriv smoothPinnedResidual y| ≤ (row1Slope : ℝ)) :
    (row1SourceCell.afterAllowance row1Allowance).modelRemainderValid
      ConfigContourSelfPotential.pinnedWeta row1SourceCell_width := by
  apply row1_modelRemainder_from_evaluator
    (hbound := smoothResidual_mem_interval b hA0 hphi hpinned hcontour
      hfrequency hsingular)
    hnumeric hdiff hderiv

end

end Li2Lean.P0.PinnedResidualEvaluator

#print axioms Li2Lean.P0.PinnedResidualEvaluator.logCell_sound
#print axioms Li2Lean.P0.PinnedResidualEvaluator.primitiveLogCell_sound
#print axioms Li2Lean.P0.PinnedResidualEvaluator.sumPrimitiveIntervals_sound
#print axioms Li2Lean.P0.PinnedResidualEvaluator.weightedPrimitiveDifference_sound
#print axioms Li2Lean.P0.PinnedResidualEvaluator.sumWeightedPrimitiveDifferences_sound
#print axioms Li2Lean.P0.PinnedResidualEvaluator.smoothResidual_mem_interval
#print axioms Li2Lean.P0.PinnedResidualEvaluator.row1_center_bound_of_interval
#print axioms Li2Lean.P0.PinnedResidualEvaluator.row1_modelRemainder_from_component_intervals
