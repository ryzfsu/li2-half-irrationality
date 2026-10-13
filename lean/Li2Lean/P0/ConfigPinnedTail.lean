/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigRealTail

open MeasureTheory

namespace Li2Lean.P0.ConfigPinnedTail

noncomputable section

open Li2Lean.LogSegment Li2Lean.P0.ConfigSegment Li2Lean.P0.ConfigRealTail

/-- The exact pinned reference mass recorded in v10 C-A. -/
def pinnedMass : ℝ := 732114048060 / 1000000000000

/-- The reflected positive-cell logarithm estimate. -/
theorem log_add_difference_le {a b t : ℝ} (ha : 0 < t + a) (hb : 0 < t + b) :
    Real.log (t + b) - Real.log (t + a) ≤ (b - a) / (t + a) := by
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have heq : (t + b) / (t + a) - 1 = (b - a) / (t + a) := by
    field_simp
    ring
  rwa [heq] at h

/-- The normalized density sum has the exact mass from the original C-A data. -/
theorem pinnedReferenceDensity_sum :
    (∑ j ∈ Finset.range 32, referenceDensity ConfigData.pinnedMassUnits j) =
      32 * pinnedMass := by
  have hq :
      (∑ j ∈ Finset.range 32,
        (32 : ℚ) * (ConfigData.pinnedMassUnits.getD j 0 : ℚ) /
          (ConfigData.referenceDenominator : ℚ)) =
        32 * (732114048060 / 1000000000000 : ℚ) := by decide +kernel
  unfold referenceDensity pinnedMass
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at hreal
  exact hreal

theorem start_le_referenceCellLeft (start : ℝ) (j : ℕ) :
    start ≤ referenceCellLeft start j := by
  unfold referenceCellLeft
  exact le_add_of_nonneg_right (by positivity)

/-- The `F` primitive is odd, including the convention at zero. -/
theorem primitive_neg (x : ℝ) : primitive (-x) = -primitive x := by
  simp only [primitive, abs_neg, neg_mul]

/-- The actual reference measure on the reflected negative real axis has
an exact endpoint formula, without differentiation under an integral. -/
theorem referenceNegativePotential_eq_endpoints (start t : ℝ) (count : ℕ) (units : List ℕ) :
    (∫ y, Real.log |(-t) - y| ∂referenceMeasure start count units) =
      ∑ j ∈ Finset.range count, referenceDensity units j *
        (primitive (t + referenceCellRight start j) -
          primitive (t + referenceCellLeft start j)) := by
  rw [referencePotential_eq_endpoints]
  apply Finset.sum_congr rfl
  intro j hj
  have hl : -t - referenceCellLeft start j = -(t + referenceCellLeft start j) := by ring
  have hr : -t - referenceCellRight start j = -(t + referenceCellRight start j) := by ring
  rw [hl, hr, primitive_neg, primitive_neg]
  ring

/-- Derivative of the actual pinned reference evaluated at `-t`. -/
theorem pinnedReferenceNegative_hasDerivAt {t : ℝ} (ht : 0 ≤ t) :
    HasDerivAt (fun s => pinnedReferencePotential (-s))
      (∑ j ∈ Finset.range 32, referenceDensity ConfigData.pinnedMassUnits j *
        (Real.log (t + referenceCellRight (1 / 4) j) -
          Real.log (t + referenceCellLeft (1 / 4) j))) t := by
  unfold pinnedReferencePotential pinnedReferenceMeasure
  simp_rw [referenceNegativePotential_eq_endpoints]
  apply HasDerivAt.fun_sum
  intro j hj
  have hl := start_le_referenceCellLeft (1 / 4) j
  have hr := referenceCellLeft_le_right (1 / 4) j
  simpa only [integral_log_add] using!
    (hasDerivAt_integral_log_add
      (t := t) (a := referenceCellLeft (1 / 4) j) (b := referenceCellRight (1 / 4) j)
      (by linarith) (by linarith)).const_mul
        (referenceDensity ConfigData.pinnedMassUnits j)

/-- The entire pinned contribution to the v10 tail derivative envelope,
with its exact mass and the actual reference density. -/
theorem pinnedReferenceNegative_deriv_le {t : ℝ} (ht : 0 ≤ t) :
    deriv (fun s => pinnedReferencePotential (-s)) t ≤ pinnedMass / (t + 1 / 4) := by
  rw [(pinnedReferenceNegative_hasDerivAt ht).deriv]
  calc
    _ ≤ ∑ j ∈ Finset.range 32, referenceDensity ConfigData.pinnedMassUnits j *
        ((1 / 32 : ℝ) / (t + 1 / 4)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (referenceDensity_nonneg _ _)
      have hl := start_le_referenceCellLeft (1 / 4) j
      have hr := referenceCellLeft_le_right (1 / 4) j
      have ha : 0 < t + referenceCellLeft (1 / 4) j := by linarith
      have hb : 0 < t + referenceCellRight (1 / 4) j := by linarith
      have hcell := log_add_difference_le ha hb
      have hwidth : referenceCellRight (1 / 4) j - referenceCellLeft (1 / 4) j =
          (1 / 32 : ℝ) := by
        simp only [referenceCellRight, referenceCellLeft, Nat.cast_add, Nat.cast_one]
        ring
      rw [hwidth] at hcell
      apply le_trans hcell
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    _ = (32 * pinnedMass) * ((1 / 32 : ℝ) / (t + 1 / 4)) := by
      rw [← Finset.sum_mul, pinnedReferenceDensity_sum]
    _ = pinnedMass / (t + 1 / 4) := by ring

/-- Every real-axis contribution to the literal `Wmu`; only the Fejér
contour-reference potential remains outside this definition. -/
def realTailWithPinned (t : ℝ) : ℝ :=
  realTailPart t - pinnedReferencePotential (-t)

/-- The complete real-reference part of v10 (5.8), with the same construction
and exact masses. The missing contour derivative is explicitly separate. -/
theorem realTailWithPinned_deriv_ge {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    Real.log 2 - 1 / (2 * (t - 1 / 2)) + 3 / (t + 2) -
      2 / (t - 11 / 2) - pinnedMass / (t + 1 / 4) ≤
        deriv realTailWithPinned t := by
  have ht0 : 0 ≤ t := by linarith
  have ht1 : (1 / 2 : ℝ) < t := by linarith
  have hreal := (((B0_hasDerivAt (by linarith : 0 < t)).sub (psi_hasDerivAt ht1)).sub
    ((frequencyReferencePotential_hasDerivAt ht).const_mul 2))
  have hd : DifferentiableAt ℝ realTailPart t := hreal.differentiableAt
  have hp := pinnedReferenceNegative_hasDerivAt ht0
  have heq : deriv realTailWithPinned t = deriv realTailPart t -
      deriv (fun s => pinnedReferencePotential (-s)) t := by
    exact (hd.hasDerivAt.sub hp.differentiableAt.hasDerivAt).deriv
  rw [heq]
  have hr := realTailPart_deriv_ge ht
  have hpin := pinnedReferenceNegative_deriv_le ht0
  linarith

end

end Li2Lean.P0.ConfigPinnedTail
