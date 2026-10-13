/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigQLogDecomposition
import Li2Lean.P0.ConfigContourPotentialActual
import Li2Lean.P0.CA.Pinned.ContourPolynomial
import Li2Lean.P0.ConfigPinnedTail

/-!
# Finite components of the literal reference logarithmic energy

The contour self-energy is integrated from the proved Fourier identity.
The pinned--contour term is integrated from the actual real power-sum
polynomial. Every coefficient in its integrated polynomial is rational.
-/

open MeasureTheory
open scoped BigOperators

set_option autoImplicit false

namespace Li2Lean.P0.ActualReferenceQLogFormula

noncomputable section

open ConfigSegment ConfigReferenceSymmetry ConfigContourReference
open ConfigContourSelfPotential ConfigContourKernel ConfigFejerMass
open ConfigContourExternalFourier ConfigFejerLog

/-- Continuous functions are integrable against every finite cell reference. -/
theorem integrable_reference_of_continuous {f : ℝ → ℝ} (hf : Continuous f)
    (start : ℝ) (count : ℕ) (units : List ℕ) :
    Integrable f (referenceMeasure start count units) := by
  unfold referenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (hf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).smul_measure
    ENNReal.ofReal_ne_top

/-- The complete reference is supported on its literal cell interval. -/
theorem ae_mem_reference_interval (start : ℝ) (count : ℕ) (units : List ℕ) :
    ∀ᵐ x ∂referenceMeasure start count units,
      x ∈ Set.Icc start (start + (count : ℝ) / 32) := by
  unfold referenceMeasure
  rw [ae_finsetSum_measure_iff]
  intro j hj
  apply Measure.ae_smul_measure
  filter_upwards [ae_restrict_mem measurableSet_Ico] with x hx
  have hjc : j + 1 ≤ count := Finset.mem_range.mp hj
  have hjcR : (j : ℝ) + 1 ≤ (count : ℝ) := by exact_mod_cast hjc
  dsimp [referenceCellLeft, referenceCellRight] at hx
  constructor
  · exact le_trans (le_add_of_nonneg_right (by positivity)) hx.1
  · push_cast at hx
    linarith [hx.2]

/-- Continuous reference integrals are finite sums of true cell integrals. -/
theorem integral_reference_of_continuous {f : ℝ → ℝ} (hf : Continuous f)
    (start : ℝ) (count : ℕ) (units : List ℕ) :
    (∫ x, f x ∂referenceMeasure start count units) =
      ∑ j ∈ Finset.range count, referenceDensity units j *
        (∫ x in referenceCellLeft start j..referenceCellRight start j, f x) := by
  unfold referenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_measure, ENNReal.toReal_ofReal (referenceDensity_nonneg units j),
      integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (referenceCellLeft_le_right start j)]
    rfl
  · intro j hj
    exact (hf.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self).smul_measure
      ENNReal.ofReal_ne_top

/-- Source-locked contour self-energy, with the exact Fourier moments. -/
theorem contour_self_energy_eq_fourier :
    contourReferenceIntegral contourReferencePotential = contourSelfEnergyFourier := by
  have hterm (n : ℕ) : Continuous (fun u : ℝ => contourDensity u *
      (((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
        (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) := by
    apply ConfigContourFormula.continuous_contourDensity.mul
    fun_prop
  have hconst : Continuous (fun u : ℝ => contourDensity u *
      (contourMass * Real.log contourScale)) :=
    ConfigContourFormula.continuous_contourDensity.mul continuous_const
  have hsum : Continuous (fun u : ℝ => ∑ n ∈ Finset.range 48,
      contourDensity u *
        (((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
          (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) := by
    apply continuous_finsetSum
    intro n hn
    exact hterm n
  unfold contourReferenceIntegral
  change (2 * Real.pi)⁻¹ *
    (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u * contourSelfPotential u) = _
  simp_rw [ConfigContourPotentialActual.contourSelfPotential_eq_fourier,
    contourSelfPotentialFourier, mul_sub, Finset.mul_sum]
  rw [intervalIntegral.integral_sub (hconst.intervalIntegrable _ _)
      (hsum.intervalIntegrable _ _),
    intervalIntegral.integral_mul_const, integral_contourDensity,
    ← contourMass_eq_source,
    intervalIntegral.integral_finsetSum (fun n hn => (hterm n).intervalIntegrable _ _)]
  have hmoment (n : ℕ) :
      (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u *
        Real.cos ((n + 1 : ℝ) * u)) =
        2 * Real.pi * contourFourierMoment (n + 1) := by
    have h := externalFourierCoefficient_eq_actual_moment_succ n 0
    simpa [externalFourierCoefficient] using h
  have hcell (n : ℕ) :
      (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u *
        (((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
          (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) =
      (2 * Real.pi) * ((1 + contourRatio ^ (n + 1)) *
        contourFourierMoment (n + 1) ^ 2 / (n + 1 : ℝ)) := by
    rw [show (fun u : ℝ => contourDensity u *
          (((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
            (n + 1 : ℝ)) * Real.cos ((n + 1 : ℝ) * u))) =
        fun u => ((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
          (n + 1 : ℝ)) * (contourDensity u * Real.cos ((n + 1 : ℝ) * u)) by
          funext u; ring,
      intervalIntegral.integral_const_mul, hmoment]
    ring
  simp_rw [hcell]
  rw [← Finset.mul_sum]
  unfold contourSelfEnergyFourier
  have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  field_simp

/-! ## Rational polynomial integration for the pinned interaction -/

open Polynomial

/-- The trace of the two Joukowski preimages, over the rational coefficient field. -/
def pairTraceQ : Polynomial ℚ := C (20000 / 24233) * (X - C (11281 / 10000))

/-- Exact Newton recurrence for the real powers of both pinned preimages. -/
def pairPolyQ : ℕ → Polynomial ℚ
  | 0 => C 2
  | 1 => pairTraceQ
  | n + 2 => pairTraceQ * pairPolyQ (n + 1) - C (1333 / 24233) * pairPolyQ n

/-- Rational endpoint integration of a polynomial. -/
def polyIntegralQ (p : Polynomial ℚ) (a b : ℚ) : ℚ :=
  ∑ k ∈ Finset.range (p.natDegree + 1),
    p.coeff k * (b ^ (k + 1) - a ^ (k + 1)) / (k + 1 : ℚ)

def referenceDensityQ (units : List ℕ) (j : ℕ) : ℚ :=
  32 * (units.getD j 0 : ℚ) / (ConfigData.referenceDenominator : ℚ)

def referenceCellLeftQ (start : ℚ) (j : ℕ) : ℚ := start + (j : ℚ) / 32
def referenceCellRightQ (start : ℚ) (j : ℕ) : ℚ := start + (j + 1 : ℚ) / 32

def referencePolyIntegralQ (start : ℚ) (count : ℕ) (units : List ℕ)
    (p : Polynomial ℚ) : ℚ :=
  ∑ j ∈ Finset.range count, referenceDensityQ units j *
    polyIntegralQ p (referenceCellLeftQ start j) (referenceCellRightQ start j)

/-- Integrated power sum against the unchanged pinned mass array. -/
def pinnedPowerIntegralQ (n : ℕ) : ℚ :=
  referencePolyIntegralQ (1 / 4) 32 ConfigData.pinnedMassUnits (pairPolyQ n)

theorem aeval_pairTraceQ (x : ℝ) :
    aeval x pairTraceQ = (x - (11281 / 10000 : ℝ)) / (24233 / 20000 : ℝ) := by
  simp [pairTraceQ]
  ring

theorem aeval_pairPolyQ (x : ℝ) (n : ℕ) :
    aeval x (pairPolyQ n) = PinnedRow1ClosedForm.row1PairPowerSum x n := by
  induction n using Nat.twoStepInduction with
  | zero => simp [pairPolyQ, PinnedRow1ClosedForm.row1PairPowerSum]
  | one => simpa [pairPolyQ, PinnedRow1ClosedForm.row1PairPowerSum] using aeval_pairTraceQ x
  | more n h0 h1 =>
      simp only [pairPolyQ, map_sub, map_mul, Polynomial.aeval_C,
        aeval_pairTraceQ, h0, h1, PinnedRow1ClosedForm.row1PairPowerSum]
      norm_num

theorem intervalIntegral_aeval_eq_polyIntegralQ (p : Polynomial ℚ) (a b : ℚ) :
    (∫ x in (a : ℝ)..(b : ℝ), aeval x p) = (polyIntegralQ p a b : ℝ) := by
  simp_rw [Polynomial.aeval_eq_sum_range, Algebra.smul_def]
  rw [intervalIntegral.integral_finsetSum]
  · simp_rw [intervalIntegral.integral_const_mul, integral_pow]
    unfold polyIntegralQ
    push_cast
    simp [mul_div_assoc]
  · intro k hk
    exact (continuous_const.mul (continuous_id.pow k)).intervalIntegrable _ _

theorem integral_reference_aeval_eq (p : Polynomial ℚ) (start : ℚ) (count : ℕ)
    (units : List ℕ) :
    (∫ x, aeval x p ∂referenceMeasure (start : ℝ) count units) =
      (referencePolyIntegralQ start count units p : ℝ) := by
  rw [integral_reference_of_continuous p.continuous_aeval]
  have hleft (j : ℕ) : referenceCellLeft (start : ℝ) j =
      (referenceCellLeftQ start j : ℝ) := by simp [referenceCellLeft, referenceCellLeftQ]
  have hright (j : ℕ) : referenceCellRight (start : ℝ) j =
      (referenceCellRightQ start j : ℝ) := by
    simp [referenceCellRight, referenceCellRightQ]
  simp_rw [hleft, hright, intervalIntegral_aeval_eq_polyIntegralQ]
  unfold referencePolyIntegralQ referenceDensityQ referenceDensity
  push_cast
  rfl

theorem pinnedPowerIntegralQ_eq (n : ℕ) :
    (∫ x, PinnedRow1ClosedForm.row1PairPowerSum x n ∂pinnedReferenceMeasure) =
      (pinnedPowerIntegralQ n : ℝ) := by
  simp_rw [← aeval_pairPolyQ]
  simpa only [Rat.cast_div, Rat.cast_one, Rat.cast_ofNat,
    pinnedReferenceMeasure, pinnedPowerIntegralQ] using
    integral_reference_aeval_eq (pairPolyQ n) (1 / 4) 32 ConfigData.pinnedMassUnits

theorem integral_pinned_const (r : ℝ) :
    (∫ x, r ∂pinnedReferenceMeasure) = ConfigPinnedTail.pinnedMass * r := by
  unfold pinnedReferenceMeasure
  rw [integral_reference_of_continuous continuous_const]
  have hwidth (j : ℕ) :
      referenceCellRight (1 / 4) j - referenceCellLeft (1 / 4) j = (1 / 32 : ℝ) := by
    simp only [referenceCellLeft, referenceCellRight, Nat.cast_add, Nat.cast_one]
    ring
  simp_rw [intervalIntegral.integral_const, smul_eq_mul, hwidth]
  rw [← Finset.sum_mul, ConfigPinnedTail.pinnedReferenceDensity_sum]
  ring

/-- Finite expression for the pinned--contour energy. Its integrated
power-sum coefficients are exact rational numbers. -/
def pinnedContourFinite : ℝ :=
  ConfigPinnedTail.pinnedMass * contourMass * Real.log contourScale -
    ∑ n ∈ Finset.range 49, contourMoment n *
      ((pinnedPowerIntegralQ n : ℝ) / (n : ℝ))

theorem contourMoment_eq_fourierMoment {n : ℕ} (hn : n ≤ 48) :
    contourMoment n = contourFourierMoment n := by
  simp only [contourMoment, contourFourierMoment, K48Coeff, ite_eq_left hn]

/-- Checker indexing of the finite pinned interaction. -/
theorem pinnedContourFinite_eq_sum48 :
    pinnedContourFinite =
      ConfigPinnedTail.pinnedMass * contourMass * Real.log contourScale -
        ∑ n ∈ Finset.range 48, contourFourierMoment (n + 1) *
          ((pinnedPowerIntegralQ (n + 1) : ℝ) / (n + 1 : ℝ)) := by
  unfold pinnedContourFinite
  have h := Finset.sum_range_succ'
    (fun n => contourMoment n * ((pinnedPowerIntegralQ n : ℝ) / (n : ℝ))) 48
  simp only [Nat.cast_zero, div_zero, mul_zero, add_zero] at h
  rw [h]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  have hm := contourMoment_eq_fourierMoment
    (n := n + 1) (by have := Finset.mem_range.mp hn; omega)
  simp only [hm, Nat.cast_add, Nat.cast_one]

theorem pinned_contour_eq_finite :
    (∫ x, contourReferencePotential (x : ℂ) ∂pinnedReferenceMeasure) =
      pinnedContourFinite := by
  let E : ℝ → ℝ := fun x => contourMass * Real.log contourScale -
    ∑ n ∈ Finset.range 49, contourMoment n * (aeval x (pairPolyQ n) / (n : ℝ))
  have hsum : Continuous (fun x : ℝ =>
      ∑ n ∈ Finset.range 49, contourMoment n *
        (aeval x (pairPolyQ n) / (n : ℝ))) := by
    apply continuous_finsetSum
    intro n hn
    exact ((pairPolyQ n).continuous_aeval.div_const (n : ℝ)).const_mul _
  have hE : (fun x : ℝ => contourReferencePotential (x : ℂ)) =ᵐ[pinnedReferenceMeasure] E := by
    filter_upwards [ae_mem_reference_interval (1 / 4) 32 ConfigData.pinnedMassUnits] with x hx
    have hxlo : (1 / 4 : ℝ) ≤ x := hx.1
    have hxhi : x ≤ (5 / 4 : ℝ) := by norm_num at hx; exact hx.2
    rw [CA.Pinned.contourPotential_eq_poly x hxlo hxhi]
    dsimp [E, CA.Pinned.contourQ]
    simp_rw [aeval_pairPolyQ]
    rfl
  rw [integral_congr_ae hE]
  dsimp [E]
  have hconstI : Integrable (fun _ : ℝ => contourMass * Real.log contourScale)
      pinnedReferenceMeasure :=
    integrable_reference_of_continuous continuous_const (1 / 4) 32 ConfigData.pinnedMassUnits
  have hsumI : Integrable (fun x : ℝ =>
      ∑ n ∈ Finset.range 49, contourMoment n *
        (aeval x (pairPolyQ n) / (n : ℝ))) pinnedReferenceMeasure :=
    integrable_reference_of_continuous hsum (1 / 4) 32 ConfigData.pinnedMassUnits
  rw [integral_sub hconstI hsumI,
    integral_pinned_const,
    integral_finsetSum]
  · simp_rw [integral_const_mul, integral_div, aeval_pairPolyQ, pinnedPowerIntegralQ_eq]
    unfold pinnedContourFinite
    ring
  · intro n hn
    exact integrable_reference_of_continuous
      (((pairPolyQ n).continuous_aeval.div_const (n : ℝ)).const_mul _)
      (1 / 4) 32 ConfigData.pinnedMassUnits

end

end Li2Lean.P0.ActualReferenceQLogFormula

#print axioms Li2Lean.P0.ActualReferenceQLogFormula.contour_self_energy_eq_fourier
#print axioms Li2Lean.P0.ActualReferenceQLogFormula.pinnedPowerIntegralQ_eq
#print axioms Li2Lean.P0.ActualReferenceQLogFormula.pinned_contour_eq_finite
