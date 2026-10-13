/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.LogSegment
import Li2Lean.P0.Config

open MeasureTheory

namespace Li2Lean.P0.ConfigSegment

noncomputable section

open Li2Lean.LogSegment

/-- C-A reference cell left endpoint. All reference cells have width `1/32`. -/
def referenceCellLeft (start : ℝ) (j : ℕ) : ℝ := start + (j : ℝ) / 32

/-- C-A reference cell right endpoint, with the literal half-open convention. -/
def referenceCellRight (start : ℝ) (j : ℕ) : ℝ := start + ((j + 1 : ℕ) : ℝ) / 32

/-- The actual density: the stored mass divided by the exact width `1/32`. -/
def referenceDensity (units : List ℕ) (j : ℕ) : ℝ :=
  32 * (units.getD j 0 : ℝ) / (ConfigData.referenceDenominator : ℝ)

/-- Piecewise-uniform reference measure of C-A, built from the actual mass units. -/
def referenceMeasure (start : ℝ) (count : ℕ) (units : List ℕ) : Measure ℝ :=
  ∑ j ∈ Finset.range count,
    ENNReal.ofReal (referenceDensity units j) •
      volume.restrict (Set.Ico (referenceCellLeft start j) (referenceCellRight start j))

/-- The actual 32-cell pinned reference from v10 Appendix A. -/
def pinnedReferenceMeasure : Measure ℝ :=
  referenceMeasure (1 / 4) 32 ConfigData.pinnedMassUnits

/-- The actual 160-cell frequency reference from v10 Appendix A. -/
def frequencyReferenceMeasure : Measure ℝ :=
  referenceMeasure (1 / 2) 160 ConfigData.frequencyMassUnits

/-- Pinned real-axis potential of the actual reference measure. -/
def pinnedReferencePotential (x : ℝ) : ℝ :=
  ∫ y, Real.log |x - y| ∂pinnedReferenceMeasure

/-- Frequency potential of the actual reference measure. -/
def frequencyReferencePotential (x : ℝ) : ℝ :=
  ∫ y, Real.log |x - y| ∂frequencyReferenceMeasure

/-- Pinned complex potential used in the literal `Weta` reference. -/
def pinnedReferenceComplexPotential (z : ℂ) : ℝ :=
  ∫ y, Real.log ‖z - (y : ℂ)‖ ∂pinnedReferenceMeasure

/-- Frequency complex potential; reflection is obtained by evaluation at `-z`. -/
def frequencyReferenceComplexPotential (z : ℂ) : ℝ :=
  ∫ y, Real.log ‖z - (y : ℂ)‖ ∂frequencyReferenceMeasure

/-- The endpoint arrays are exactly the cells used by the reference measure. -/
theorem pinnedReferenceEdges_exact :
    (List.range 33).map (fun j => (1 / 4 : ℚ) + (j : ℚ) / 32) =
      ConfigData.pinnedReferenceEdges := by decide +kernel

/-- The endpoint arrays are exactly the cells used by the frequency measure. -/
theorem frequencyReferenceEdges_exact :
    (List.range 161).map (fun j => (1 / 2 : ℚ) + (j : ℚ) / 32) =
      ConfigData.frequencyReferenceEdges := by decide +kernel

theorem referenceCellLeft_le_right (start : ℝ) (j : ℕ) :
    referenceCellLeft start j ≤ referenceCellRight start j := by
  simp only [referenceCellLeft, referenceCellRight, Nat.cast_add, Nat.cast_one]
  linarith

theorem referenceDensity_nonneg (units : List ℕ) (j : ℕ) :
    0 ≤ referenceDensity units j := by
  unfold referenceDensity ConfigData.referenceDenominator
  positivity

/-- Actual log-kernel integrability for all real evaluation points, including
all reference endpoints. No separation or regularity premise is needed. -/
theorem integrable_log_referenceMeasure (start : ℝ) (count : ℕ)
    (units : List ℕ) (x : ℝ) :
    Integrable (fun y => Real.log |x - y|) (referenceMeasure start count units) := by
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (integrableOn_Ico_log_abs_sub x (referenceCellLeft_le_right start j)).smul_measure
    ENNReal.ofReal_ne_top

/-- Exact semantic correspondence between the true reference integral and
its finite `x log |x|` formula. The equation is valid at every cell endpoint. -/
theorem referencePotential_eq_endpoints (start : ℝ) (count : ℕ)
    (units : List ℕ) (x : ℝ) :
    (∫ y, Real.log |x - y| ∂referenceMeasure start count units) =
      ∑ j ∈ Finset.range count, referenceDensity units j *
        (primitive (x - referenceCellLeft start j) -
          primitive (x - referenceCellRight start j)) := by
  unfold referenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_measure, ENNReal.toReal_ofReal (referenceDensity_nonneg units j),
      integral_Ico_log_abs_sub x (referenceCellLeft_le_right start j)]
    rfl
  · intro j hj
    exact (integrableOn_Ico_log_abs_sub x (referenceCellLeft_le_right start j)).smul_measure
      ENNReal.ofReal_ne_top

/-- C-A pinned potential in the literal 32-cell reference, with no analytic premise. -/
theorem pinnedReferencePotential_eq_endpoints (x : ℝ) :
    pinnedReferencePotential x =
      ∑ j ∈ Finset.range 32, referenceDensity ConfigData.pinnedMassUnits j *
        (primitive (x - referenceCellLeft (1 / 4) j) -
          primitive (x - referenceCellRight (1 / 4) j)) :=
  referencePotential_eq_endpoints (1 / 4) 32 ConfigData.pinnedMassUnits x

/-- C-A frequency potential in the literal 160-cell reference, with no analytic premise. -/
theorem frequencyReferencePotential_eq_endpoints (x : ℝ) :
    frequencyReferencePotential x =
      ∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j *
        (primitive (x - referenceCellLeft (1 / 2) j) -
          primitive (x - referenceCellRight (1 / 2) j)) :=
  referencePotential_eq_endpoints (1 / 2) 160 ConfigData.frequencyMassUnits x

/-- A real evaluation of the complex pinned potential is the real formula. -/
theorem pinnedReferenceComplexPotential_ofReal (x : ℝ) :
    pinnedReferenceComplexPotential (x : ℂ) = pinnedReferencePotential x := by
  simp only [pinnedReferenceComplexPotential, pinnedReferencePotential,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- A real evaluation of the complex frequency potential is the real formula. -/
theorem frequencyReferenceComplexPotential_ofReal (x : ℝ) :
    frequencyReferenceComplexPotential (x : ℂ) = frequencyReferencePotential x := by
  simp only [frequencyReferenceComplexPotential, frequencyReferencePotential,
    ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Real reference measures give conjugation-invariant complex potentials. -/
theorem pinnedReferenceComplexPotential_conj (z : ℂ) :
    pinnedReferenceComplexPotential (starRingEnd ℂ z) =
      pinnedReferenceComplexPotential z := by
  unfold pinnedReferenceComplexPotential
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  rw [show starRingEnd ℂ z - (y : ℂ) = starRingEnd ℂ (z - (y : ℂ)) by simp]
  exact Complex.norm_conj _

/-- The reflected frequency potential inherits the same conjugation symmetry. -/
theorem frequencyReferenceComplexPotential_conj (z : ℂ) :
    frequencyReferenceComplexPotential (starRingEnd ℂ z) =
      frequencyReferenceComplexPotential z := by
  unfold frequencyReferenceComplexPotential
  apply integral_congr_ae
  filter_upwards [] with y
  congr 1
  rw [show starRingEnd ℂ z - (y : ℂ) = starRingEnd ℂ (z - (y : ℂ)) by simp]
  exact Complex.norm_conj _

/-- The literal v10 `A0` integral has the closed C-A formula at every real point,
including all four segment endpoints. -/
theorem A0_ofReal_eq_endpoints (x : ℝ) :
    Config.A0 (x : ℂ) =
      primitive (x - 1 / 4) - primitive (x - 5 / 4) +
        (primitive x - primitive (x - 2)) := by
  simp only [Config.A0, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
    integral_log_abs_sub, sub_zero]

/-- The literal v10 frequency field `B0` in endpoint form. -/
theorem B0_eq_endpoints (t : ℝ) :
    Config.B0 t =
      primitive (t + 5 / 4) - primitive (t + 1 / 4) +
        (primitive (t + 2) - primitive t) := by
  simp only [Config.B0, integral_log_add, add_zero]

/-- The literal v10 `phi` integral in endpoint form, including the zero-segment endpoints. -/
theorem phi_ofReal_eq_endpoints (x : ℝ) :
    Config.phi (x : ℂ) =
      x * Real.log 2 + (primitive (x + 1 / 2) - primitive x) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) := by
  simp only [Config.phi, Complex.ofReal_re, ← Complex.ofReal_add, Complex.norm_real,
    Real.norm_eq_abs, Real.log_abs, integral_log_add, add_zero]


/-- Differentiation of the actual reference integral is reduced to the finite
endpoint formula. Only the finitely many genuine singular endpoints are excluded. -/
theorem hasDerivAt_referencePotential {start x : ℝ} {count : ℕ} {units : List ℕ}
    (hleft : ∀ j ∈ Finset.range count, x ≠ referenceCellLeft start j)
    (hright : ∀ j ∈ Finset.range count, x ≠ referenceCellRight start j) :
    HasDerivAt (fun z => ∫ y, Real.log |z - y| ∂referenceMeasure start count units)
      (∑ j ∈ Finset.range count, referenceDensity units j *
        (Real.log |x - referenceCellLeft start j| -
          Real.log |x - referenceCellRight start j|)) x := by
  simp_rw [referencePotential_eq_endpoints]
  apply HasDerivAt.fun_sum
  intro j hj
  simpa only [integral_log_abs_sub] using!
    (hasDerivAt_integral_log_abs_sub (hleft j hj) (hright j hj)).const_mul
      (referenceDensity units j)

/-- The actual reference potential remains continuous at density discontinuities. -/
theorem continuous_referencePotential (start : ℝ) (count : ℕ) (units : List ℕ) :
    Continuous (fun x => ∫ y, Real.log |x - y| ∂referenceMeasure start count units) := by
  simp_rw [referencePotential_eq_endpoints]
  apply continuous_finsetSum
  intro j hj
  exact ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
    (continuous_primitive.comp (continuous_id.sub continuous_const))).const_mul _

/-- The closed form is directly reusable by cell checkers for the actual integral. -/
theorem referencePotential_lower_of_endpoint_sum {start x lower : ℝ} {count : ℕ}
    {units : List ℕ}
    (h : lower ≤ ∑ j ∈ Finset.range count, referenceDensity units j *
      (primitive (x - referenceCellLeft start j) -
        primitive (x - referenceCellRight start j))) :
    lower ≤ ∫ y, Real.log |x - y| ∂referenceMeasure start count units := by
  rwa [referencePotential_eq_endpoints]

end

end Li2Lean.P0.ConfigSegment
