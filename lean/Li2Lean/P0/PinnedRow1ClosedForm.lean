/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.PinnedResidualRow1

/-!
# Closed-form arithmetic gates for the first pinned row

This file records the exact midpoint and the positive square-root interval
needed by the interior Joukowski formula.  It deliberately stops before any
claim about the Fejer logarithmic polynomial: the latter still needs a
kernel-checked trigonometric moment enclosure.
-/

open MeasureTheory
open ContourKit
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigInteriorContourPotential
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigFejerLog
open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigSlackSemanticIdentity
open Li2Lean.P0.PinnedResidualRow1
open Li2Lean.LogSegment

namespace Li2Lean.P0.PinnedRow1ClosedForm

noncomputable section

def row1Center : ℚ := rationalCellCenter
  (2049 / 8192) (1025 / 4096)

theorem row1Center_eq : row1Center = 4099 / 16384 := by
  norm_num [row1Center, rationalCellCenter]

def row1MidDiscriminant : ℚ :=
  ((11281 / 10000 : ℚ) - row1Center) ^ 2 -
    4 * (24233 / 20000 : ℚ) ^ 2 * (1333 / 24233 : ℚ)

theorem row1MidDiscriminant_eq :
    row1MidDiscriminant = 46946025073897 / 104857600000000 := by
  norm_num [row1MidDiscriminant, row1Center, rationalCellCenter]

theorem pinnedDiscriminant_center_eq :
    pinnedDiscriminant (row1Center : ℝ) =
      (46946025073897 / 104857600000000 : ℝ) := by
  norm_num [pinnedDiscriminant, row1Center, rationalCellCenter,
    P0ContourLeaf.xi, P0ContourLeaf.alpha, P0ContourLeaf.beta,
    P0ContourLeaf.axisA, P0ContourLeaf.axisB, contourScale,
    contourRatio]

def row1SqrtLo : ℚ := 6691 / 10000
def row1SqrtHi : ℚ := 6692 / 10000

theorem row1SqrtLo_nonneg : (0 : ℝ) ≤ row1SqrtLo := by
  norm_num [row1SqrtLo]

theorem row1SqrtHi_nonneg : (0 : ℝ) ≤ row1SqrtHi := by
  norm_num [row1SqrtHi]

theorem row1_sqrt_bounds :
    (row1SqrtLo : ℝ) ≤ Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) ∧
      Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) ≤ (row1SqrtHi : ℝ) := by
  rw [pinnedDiscriminant_center_eq]
  constructor
  · apply (Real.le_sqrt row1SqrtLo_nonneg (by norm_num)).2
    norm_num [row1SqrtLo]
  · apply (Real.sqrt_le_iff).2
    constructor
    · exact row1SqrtHi_nonneg
    · norm_num [row1SqrtHi]

def row1RootPlusReal : ℝ :=
  ((4099 / 16384 : ℝ) - (11281 / 10000 : ℝ) +
      Real.sqrt (pinnedDiscriminant (row1Center : ℝ))) /
    (2 * (24233 / 20000 : ℝ))

def row1RootMinusReal : ℝ :=
  ((4099 / 16384 : ℝ) - (11281 / 10000 : ℝ) -
      Real.sqrt (pinnedDiscriminant (row1Center : ℝ))) /
    (2 * (24233 / 20000 : ℝ))

theorem row1Root_den_pos :
    0 < 2 * (24233 / 20000 : ℝ) := by norm_num

theorem row1RootPlus_interval :
    (-87 / 1000 : ℝ) ≤ row1RootPlusReal ∧
      row1RootPlusReal ≤ (-86 / 1000 : ℝ) := by
  unfold row1RootPlusReal
  rw [pinnedDiscriminant_center_eq]
  have hs :
      (6691 / 10000 : ℝ) ≤ Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) ∧
        Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) ≤ (6692 / 10000 : ℝ) := by
    simpa only [row1SqrtLo, row1SqrtHi, Rat.cast_div, Rat.cast_ofNat] using
      row1_sqrt_bounds
  rw [pinnedDiscriminant_center_eq] at hs
  have hden : 2 * (24233 / 20000 : ℝ) = 24233 / 10000 := by norm_num
  rw [hden]
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 24233 / 10000)).2
    nlinarith [hs.1, hs.2]
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24233 / 10000)).2
    nlinarith [hs.1, hs.2]

theorem row1RootMinus_interval :
    (-640 / 1000 : ℝ) ≤ row1RootMinusReal ∧
      row1RootMinusReal ≤ (-637 / 1000 : ℝ) := by
  unfold row1RootMinusReal
  rw [pinnedDiscriminant_center_eq]
  have hs :
      (6691 / 10000 : ℝ) ≤ Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) ∧
        Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) ≤ (6692 / 10000 : ℝ) := by
    simpa only [row1SqrtLo, row1SqrtHi, Rat.cast_div, Rat.cast_ofNat] using
      row1_sqrt_bounds
  rw [pinnedDiscriminant_center_eq] at hs
  have hden : 2 * (24233 / 20000 : ℝ) = 24233 / 10000 := by norm_num
  rw [hden]
  constructor
  · apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 24233 / 10000)).2
    nlinarith [hs.1, hs.2]
  · apply (div_le_iff₀ (by norm_num : (0 : ℝ) < 24233 / 10000)).2
    nlinarith [hs.1, hs.2]

theorem pinnedRootPlus_center_eq :
    pinnedRootPlus (row1Center : ℝ) = (row1RootPlusReal : ℂ) := by
  have hd : 0 ≤ pinnedDiscriminant (row1Center : ℝ) := by
    rw [pinnedDiscriminant_center_eq]
    norm_num
  have hsqrt :
      Complex.sqrt (pinnedDiscriminant (row1Center : ℝ) : ℂ) =
        (Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) : ℂ) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  unfold pinnedRootPlus row1RootPlusReal
  rw [hsqrt]
  norm_num [row1Center, rationalCellCenter, P0ContourLeaf.xi,
    P0ContourLeaf.alpha, P0ContourLeaf.axisA, P0ContourLeaf.axisB]

theorem pinnedRootMinus_center_eq :
    pinnedRootMinus (row1Center : ℝ) = (row1RootMinusReal : ℂ) := by
  have hd : 0 ≤ pinnedDiscriminant (row1Center : ℝ) := by
    rw [pinnedDiscriminant_center_eq]
    norm_num
  have hsqrt :
      Complex.sqrt (pinnedDiscriminant (row1Center : ℝ) : ℂ) =
        (Real.sqrt (pinnedDiscriminant (row1Center : ℝ)) : ℂ) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  unfold pinnedRootMinus row1RootMinusReal
  rw [hsqrt]
  norm_num [row1Center, rationalCellCenter, P0ContourLeaf.xi,
    P0ContourLeaf.alpha, P0ContourLeaf.axisA, P0ContourLeaf.axisB]

def row1ContourPolynomial (r : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 49,
    ConfigFejerLog.contourMoment n * (r ^ n / (n : ℝ))

def row1ContourClosed : ℝ :=
  (267885951940 / 1000000000000 : ℝ) *
      Real.log ConfigContourKernel.contourScale -
    row1ContourPolynomial row1RootPlusReal -
    row1ContourPolynomial row1RootMinusReal

def row1CenterClosedForm : ℝ :=
    (primitive ((row1Center : ℝ) - 1 / 4) -
      primitive ((row1Center : ℝ) - 5 / 4) +
      (primitive (row1Center : ℝ) - primitive ((row1Center : ℝ) - 2))) -
    ((row1Center : ℝ) * Real.log 2 +
      (primitive ((row1Center : ℝ) + 1 / 2) -
        primitive (row1Center : ℝ)) +
      1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
    2 * ((∑ j ∈ Finset.range 32,
      referenceDensity ConfigData.pinnedMassUnits j *
        (primitive ((row1Center : ℝ) - referenceCellLeft (1 / 4) j) -
          primitive ((row1Center : ℝ) - referenceCellRight (1 / 4) j))) +
      row1ContourClosed) -
    (∑ j ∈ Finset.range 160,
      referenceDensity ConfigData.frequencyMassUnits j *
        (primitive ((row1Center : ℝ) + referenceCellRight (1 / 2) j) -
          primitive ((row1Center : ℝ) + referenceCellLeft (1 / 2) j))) -
    (singularCoefficient : ℝ) * primitive ((row1Center : ℝ) - 1 / 4)

theorem smoothPinnedResidual_center_eq_closedForm :
    smoothPinnedResidual (row1Center : ℝ) = row1CenterClosedForm := by
  rw [smoothPinnedResidual_explicit]
  have hcont := contourReferencePotential_pinned_interval
    (x := (row1Center : ℝ)) (by
      norm_num [row1Center, rationalCellCenter]) (by
      norm_num [row1Center, rationalCellCenter])
  rw [hcont, pinnedRootPlus_center_eq, pinnedRootMinus_center_eq]
  have hpoly (r : ℝ) :
      contourLogPolynomial ((starRingEnd ℂ) (r : ℂ)) =
        row1ContourPolynomial r := by
    rw [show (starRingEnd ℂ) (r : ℂ) = (r : ℂ) by simp,
      contourLogPolynomial_ofReal]
    exact rfl
  rw [hpoly, hpoly]
  simp only [row1CenterClosedForm, row1ContourClosed]

theorem row1Center_lower_obligation_equiv :
    ((row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
      (singularCoefficient : ℝ) *
          primitive ((1025 / 4096 : ℝ) - 1 / 4) +
        smoothPinnedResidual (row1Center : ℝ) -
      (row1Slope : ℝ) *
        (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ)) ↔
    ((row1SourceCell.lower : ℝ) - (row1Allowance : ℝ) ≤
      (singularCoefficient : ℝ) *
          primitive ((1025 / 4096 : ℝ) - 1 / 4) +
        row1CenterClosedForm -
      (row1Slope : ℝ) *
        (rationalCellHalfWidth row1SourceCell.lo row1SourceCell.hi : ℝ)) := by
  rw [smoothPinnedResidual_center_eq_closedForm]

theorem row1_discriminant_pos {x : ℝ}
    (hxlo : (2049 / 8192 : ℝ) ≤ x)
    (hxhi : x ≤ (1025 / 4096 : ℝ)) :
    0 < pinnedDiscriminant x := by
  unfold pinnedDiscriminant
  norm_num [P0ContourLeaf.xi, P0ContourLeaf.alpha,
    P0ContourLeaf.beta, P0ContourLeaf.axisA, P0ContourLeaf.axisB,
    contourScale, contourRatio] at *
  nlinarith [sq_nonneg (x - (1025 / 4096 : ℝ))]

/-! The root pair has a real polynomial power-sum recurrence.  This is the
source-locked algebra used below to avoid differentiating the two square-root
branches separately. -/

def row1PairPowerSum (x : ℝ) : ℕ → ℝ
  | 0 => 2
  | 1 => (x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ)
  | n + 2 =>
      ((x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ)) *
          row1PairPowerSum x (n + 1) -
        (1333 / 24233 : ℝ) * row1PairPowerSum x n

theorem row1PairPowerSum_zero (x : ℝ) :
    row1PairPowerSum x 0 = 2 := rfl

theorem row1PairPowerSum_one (x : ℝ) :
    row1PairPowerSum x 1 =
      (x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ) := rfl

theorem row1PairPowerSum_recurrence (x : ℝ) (n : ℕ) :
    row1PairPowerSum x (n + 2) =
      ((x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ)) *
          row1PairPowerSum x (n + 1) -
        (1333 / 24233 : ℝ) * row1PairPowerSum x n := rfl

theorem row1PairPowerSum_root_identity (x : ℝ) :
    ∀ n : ℕ,
      pinnedRootPlus x ^ n + pinnedRootMinus x ^ n =
        (row1PairPowerSum x n : ℂ) := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      norm_num [row1PairPowerSum]
  | one =>
      have hs := pinnedRoots_sum x
      simp only [pow_one]
      change pinnedRootPlus x + pinnedRootMinus x =
        (((x - (11281 / 10000 : ℝ)) /
          (24233 / 20000 : ℝ) : ℝ) : ℂ)
      norm_num [P0ContourLeaf.xi, P0ContourLeaf.alpha,
        P0ContourLeaf.axisA, P0ContourLeaf.axisB] at hs
      simpa using hs
  | more n h₀ h₁ =>
      have hs := pinnedRoots_sum x
      have hp := pinnedRoots_product x
      have hrec :
          pinnedRootPlus x ^ (n + 2) + pinnedRootMinus x ^ (n + 2) =
            (pinnedRootPlus x + pinnedRootMinus x) *
                (pinnedRootPlus x ^ (n + 1) + pinnedRootMinus x ^ (n + 1)) -
              (pinnedRootPlus x * pinnedRootMinus x) *
                (pinnedRootPlus x ^ n + pinnedRootMinus x ^ n) := by
        rw [show n + 2 = (n + 1) + 1 by omega, pow_succ, pow_succ]
        rw [pow_succ, pow_succ]
        ring
      calc
        pinnedRootPlus x ^ (n + 2) + pinnedRootMinus x ^ (n + 2) = _ := hrec
        _ = ((x - (11281 / 10000 : ℝ)) /
              (24233 / 20000 : ℝ) : ℂ) *
              (row1PairPowerSum x (n + 1) : ℂ) -
            ((1333 / 24233 : ℝ) : ℂ) *
              (row1PairPowerSum x n : ℂ) := by
          rw [hs, hp, h₁, h₀]
          norm_num [P0ContourLeaf.xi, P0ContourLeaf.alpha,
            P0ContourLeaf.beta, P0ContourLeaf.axisA, P0ContourLeaf.axisB,
            contourScale, contourRatio]
        _ = (row1PairPowerSum x (n + 2) : ℂ) := by
          rw [row1PairPowerSum]
          push_cast
          ring

theorem row1PairPowerSum_real_part (x : ℝ) (n : ℕ) :
    (pinnedRootPlus x ^ n + pinnedRootMinus x ^ n).re =
      row1PairPowerSum x n := by
  rw [row1PairPowerSum_root_identity]
  simp

def row1PairPowerSumDeriv (x : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / (24233 / 20000 : ℝ)
  | n + 2 =>
      (1 / (24233 / 20000 : ℝ)) * row1PairPowerSum x (n + 1) +
        ((x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ)) *
          row1PairPowerSumDeriv x (n + 1) -
        (1333 / 24233 : ℝ) * row1PairPowerSumDeriv x n

theorem row1PairPowerSumDeriv_zero (x : ℝ) :
    row1PairPowerSumDeriv x 0 = 0 := rfl

theorem row1PairPowerSumDeriv_one (x : ℝ) :
    row1PairPowerSumDeriv x 1 = 1 / (24233 / 20000 : ℝ) := rfl

theorem row1PairPowerSumDeriv_recurrence (x : ℝ) (n : ℕ) :
    row1PairPowerSumDeriv x (n + 2) =
      (1 / (24233 / 20000 : ℝ)) * row1PairPowerSum x (n + 1) +
        ((x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ)) *
          row1PairPowerSumDeriv x (n + 1) -
        (1333 / 24233 : ℝ) * row1PairPowerSumDeriv x n := rfl

theorem row1PairPowerSum_hasDerivAt (x : ℝ) :
    ∀ n : ℕ, HasDerivAt (fun y : ℝ => row1PairPowerSum y n)
      (row1PairPowerSumDeriv x n) x := by
  intro n
  induction n using Nat.twoStepInduction with
  | zero =>
      simpa [row1PairPowerSum, row1PairPowerSumDeriv] using
        (hasDerivAt_const x (2 : ℝ))
  | one =>
      have htrace : HasDerivAt
          (fun y : ℝ => (y - (11281 / 10000 : ℝ)) /
            (24233 / 20000 : ℝ))
          (1 / (24233 / 20000 : ℝ)) x := by
        convert ((hasDerivAt_id x).sub_const (11281 / 10000 : ℝ)).div_const
          (24233 / 20000 : ℝ) using 1
        ext y
        simp only [id_eq]
      simpa [row1PairPowerSum, row1PairPowerSumDeriv] using htrace
  | more n h₀ h₁ =>
      have htrace : HasDerivAt
          (fun y : ℝ => (y - (11281 / 10000 : ℝ)) /
            (24233 / 20000 : ℝ))
          (1 / (24233 / 20000 : ℝ)) x := by
        convert ((hasDerivAt_id x).sub_const (11281 / 10000 : ℝ)).div_const
          (24233 / 20000 : ℝ) using 1
        ext y
        simp only [id_eq]
      have hprod := htrace.mul h₁
      have hratio := h₀.const_mul (1333 / 24233 : ℝ)
      convert hprod.sub hratio using 1
      · ext y
        rfl
      · rfl

def row1RootPlusAt (x : ℝ) : ℝ :=
  ((x - (11281 / 10000 : ℝ)) +
      Real.sqrt (pinnedDiscriminant x)) / (2 * (24233 / 20000 : ℝ))

def row1RootMinusAt (x : ℝ) : ℝ :=
  ((x - (11281 / 10000 : ℝ)) -
      Real.sqrt (pinnedDiscriminant x)) / (2 * (24233 / 20000 : ℝ))

theorem pinnedRootPlus_eq_row1RootPlusAt {x : ℝ}
    (hxlo : (2049 / 8192 : ℝ) ≤ x)
    (hxhi : x ≤ (1025 / 4096 : ℝ)) :
    pinnedRootPlus x = (row1RootPlusAt x : ℂ) := by
  have hd : 0 ≤ pinnedDiscriminant x := (row1_discriminant_pos hxlo hxhi).le
  have hsqrt :
      Complex.sqrt (pinnedDiscriminant x : ℂ) =
        (Real.sqrt (pinnedDiscriminant x) : ℂ) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  unfold pinnedRootPlus row1RootPlusAt
  rw [hsqrt]
  norm_num [P0ContourLeaf.xi, P0ContourLeaf.alpha,
    P0ContourLeaf.axisA, P0ContourLeaf.axisB]

theorem pinnedRootMinus_eq_row1RootMinusAt {x : ℝ}
    (hxlo : (2049 / 8192 : ℝ) ≤ x)
    (hxhi : x ≤ (1025 / 4096 : ℝ)) :
    pinnedRootMinus x = (row1RootMinusAt x : ℂ) := by
  have hd : 0 ≤ pinnedDiscriminant x := (row1_discriminant_pos hxlo hxhi).le
  have hsqrt :
      Complex.sqrt (pinnedDiscriminant x : ℂ) =
        (Real.sqrt (pinnedDiscriminant x) : ℂ) := by
    rw [Complex.sqrt_eq_real_add_ite]
    simp [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hd]
  unfold pinnedRootMinus row1RootMinusAt
  rw [hsqrt]
  norm_num [P0ContourLeaf.xi, P0ContourLeaf.alpha,
    P0ContourLeaf.axisA, P0ContourLeaf.axisB]

theorem row1RootPairPowerSum_identity {x : ℝ}
    (hxlo : (2049 / 8192 : ℝ) ≤ x)
    (hxhi : x ≤ (1025 / 4096 : ℝ)) (n : ℕ) :
    row1RootPlusAt x ^ n + row1RootMinusAt x ^ n =
      row1PairPowerSum x n := by
  have h := row1PairPowerSum_root_identity x n
  rw [pinnedRootPlus_eq_row1RootPlusAt hxlo hxhi,
    pinnedRootMinus_eq_row1RootMinusAt hxlo hxhi] at h
  have hr := congrArg Complex.re h
  simp only [Complex.add_re, ← Complex.ofReal_pow, Complex.ofReal_re] at hr
  exact hr

def row1ContourPairByPowerSum (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 49,
    contourMoment n * (row1PairPowerSum x n / (n : ℝ))

def row1ContourPairDerivative (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 49,
    contourMoment n * (row1PairPowerSumDeriv x n / (n : ℝ))

theorem row1ContourPolynomial_pair_eq_powerSum {x : ℝ}
    (hxlo : (2049 / 8192 : ℝ) ≤ x)
    (hxhi : x ≤ (1025 / 4096 : ℝ)) :
    row1ContourPolynomial (row1RootPlusAt x) +
        row1ContourPolynomial (row1RootMinusAt x) =
      row1ContourPairByPowerSum x := by
  unfold row1ContourPolynomial row1ContourPairByPowerSum
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  calc
    contourMoment n * (row1RootPlusAt x ^ n / (n : ℝ)) +
        contourMoment n * (row1RootMinusAt x ^ n / (n : ℝ)) =
      contourMoment n *
        ((row1RootPlusAt x ^ n + row1RootMinusAt x ^ n) / (n : ℝ)) := by ring
    _ = contourMoment n * (row1PairPowerSum x n / (n : ℝ)) := by
      rw [row1RootPairPowerSum_identity hxlo hxhi]

theorem row1ContourPairByPowerSum_hasDerivAt (x : ℝ) :
    HasDerivAt row1ContourPairByPowerSum
      (row1ContourPairDerivative x) x := by
  unfold row1ContourPairByPowerSum row1ContourPairDerivative
  apply HasDerivAt.fun_sum
  intro n hn
  exact ((row1PairPowerSum_hasDerivAt x n).div_const (n : ℝ)).const_mul
    (contourMoment n)

end

end Li2Lean.P0.PinnedRow1ClosedForm

#print axioms Li2Lean.P0.PinnedRow1ClosedForm.row1_sqrt_bounds
