/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSegment
import Li2Lean.P0.ConfigReferenceSymmetry
import Li2Lean.Kit.LogRectangle

open MeasureTheory

namespace Li2Lean.P0.ConfigQLogSegments

noncomputable section

open Li2Lean.P0.ConfigSegment
open Li2Lean.LogSegment

/-- The exact cell-pair endpoint expression for the logarithmic kernel. -/
def rectangleLogValue (a b c d : ℝ) : ℝ :=
  secondPrimitive (b - c) - secondPrimitive (a - c) -
    secondPrimitive (b - d) + secondPrimitive (a - d)

/-- The literal potential of a finite piecewise-uniform reference measure. -/
def referencePotential (start : ℝ) (count : ℕ) (units : List ℕ) (x : ℝ) : ℝ :=
  ∫ y, Real.log |x - y| ∂referenceMeasure start count units

/-- The reflected logarithmic potential of a positive-axis reference. -/
def referencePlusPotential (start : ℝ) (count : ℕ) (units : List ℕ) (x : ℝ) : ℝ :=
  ∫ y, Real.log |x + y| ∂referenceMeasure start count units

/-- The exact endpoint expression for a sum-kernel rectangle. -/
def rectangleLogAddValue (a b c d : ℝ) : ℝ :=
  secondPrimitive (b + d) - secondPrimitive (a + d) -
    secondPrimitive (b + c) + secondPrimitive (a + c)

private lemma primitive_neg (x : ℝ) : primitive (-x) = -primitive x := by
  simp [primitive, abs_neg]

/-- The reflected potential has an exact endpoint form at every real point. -/
theorem referencePlusPotential_eq_endpoints (start : ℝ) (count : ℕ)
    (units : List ℕ) (x : ℝ) :
    referencePlusPotential start count units x =
      ∑ j ∈ Finset.range count, referenceDensity units j *
        (primitive (x + referenceCellRight start j) -
          primitive (x + referenceCellLeft start j)) := by
  have hfun : (fun y : ℝ => Real.log |x + y|) =
      fun y => Real.log |(-x) - y| := by
    funext y
    congr 1
    rw [show x + y = -((-x) - y) by ring, abs_neg]
  unfold referencePlusPotential
  rw [hfun]
  rw [referencePotential_eq_endpoints start count units (-x)]
  apply Finset.sum_congr rfl
  intro j hj
  have hleft : -x - referenceCellLeft start j = -(x + referenceCellLeft start j) := by ring
  have hright : -x - referenceCellRight start j = -(x + referenceCellRight start j) := by ring
  rw [hleft, hright, primitive_neg, primitive_neg]
  ring

private lemma continuous_cellPlusPrimitive (leftStart rightStart : ℝ) (units : List ℕ)
    (i j : ℕ) :
    Integrable (fun x : ℝ => referenceDensity units j *
      (primitive (x + referenceCellRight rightStart j) -
        primitive (x + referenceCellLeft rightStart j)))
      (volume.restrict (Set.Ico (referenceCellLeft leftStart i)
        (referenceCellRight leftStart i))) := by
  have hcont : Continuous (fun x : ℝ => referenceDensity units j *
      (primitive (x + referenceCellRight rightStart j) -
        primitive (x + referenceCellLeft rightStart j))) :=
    continuous_const.mul
      ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
        (continuous_primitive.comp (continuous_id.add continuous_const)))
  exact hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

private lemma integral_cell_plus_endpoint_difference
    (leftStart rightStart : ℝ) (i j : ℕ) :
    (∫ x in Set.Ico (referenceCellLeft leftStart i)
        (referenceCellRight leftStart i),
      primitive (x + referenceCellRight rightStart j) -
        primitive (x + referenceCellLeft rightStart j)) =
      rectangleLogAddValue (referenceCellLeft leftStart i)
        (referenceCellRight leftStart i) (referenceCellLeft rightStart j)
        (referenceCellRight rightStart j) := by
  have hi : referenceCellLeft leftStart i ≤ referenceCellRight leftStart i :=
    referenceCellLeft_le_right leftStart i
  have hright : Integrable
      (fun x : ℝ => primitive (x + referenceCellRight rightStart j))
      (volume.restrict (Set.Ico (referenceCellLeft leftStart i)
        (referenceCellRight leftStart i))) :=
    (continuous_primitive.comp (continuous_id.add continuous_const)).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  have hleft : Integrable
      (fun x : ℝ => primitive (x + referenceCellLeft rightStart j))
      (volume.restrict (Set.Ico (referenceCellLeft leftStart i)
        (referenceCellRight leftStart i))) :=
    (continuous_primitive.comp (continuous_id.add continuous_const)).integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self
  rw [integral_sub hright hleft,
    integral_Ico_primitive_add _ hi, integral_Ico_primitive_add _ hi]
  simp [rectangleLogAddValue]
  ring

/-- Integrating the actual reflected potential of one cell reference against
another cell reference reduces to an exact finite rectangle sum. -/
theorem referenceCrossPlusEnergy_eq_rectangleSum
    (leftStart : ℝ) (leftCount : ℕ) (leftUnits : List ℕ)
    (rightStart : ℝ) (rightCount : ℕ) (rightUnits : List ℕ) :
    (∫ x, referencePlusPotential rightStart rightCount rightUnits x
      ∂referenceMeasure leftStart leftCount leftUnits) =
      ∑ i ∈ Finset.range leftCount, ∑ j ∈ Finset.range rightCount,
        referenceDensity leftUnits i * referenceDensity rightUnits j *
          rectangleLogAddValue
            (referenceCellLeft leftStart i) (referenceCellRight leftStart i)
            (referenceCellLeft rightStart j) (referenceCellRight rightStart j) := by
  have hPotentialContinuous :
      Continuous (fun x : ℝ =>
        ∑ j ∈ Finset.range rightCount,
          referenceDensity rightUnits j *
            (primitive (x + referenceCellRight rightStart j) -
              primitive (x + referenceCellLeft rightStart j))) := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul
      ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
        (continuous_primitive.comp (continuous_id.add continuous_const)))
  have hPotentialIntegrable :
      Integrable (fun x : ℝ => referencePlusPotential rightStart rightCount rightUnits x)
        (referenceMeasure leftStart leftCount leftUnits) := by
    rw [show (fun x : ℝ => referencePlusPotential rightStart rightCount rightUnits x) =
      fun x => ∑ j ∈ Finset.range rightCount,
        referenceDensity rightUnits j *
          (primitive (x + referenceCellRight rightStart j) -
            primitive (x + referenceCellLeft rightStart j)) by
        funext x
        exact referencePlusPotential_eq_endpoints rightStart rightCount rightUnits x]
    unfold referenceMeasure
    apply integrable_finsetSum_measure.mpr
    intro i hi
    exact hPotentialContinuous.integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self |>.smul_measure ENNReal.ofReal_ne_top
  rw [show (fun x : ℝ => referencePlusPotential rightStart rightCount rightUnits x) =
    fun x => ∑ j ∈ Finset.range rightCount,
      referenceDensity rightUnits j *
        (primitive (x + referenceCellRight rightStart j) -
          primitive (x + referenceCellLeft rightStart j)) by
      funext x
      exact referencePlusPotential_eq_endpoints rightStart rightCount rightUnits x]
  unfold referenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (referenceDensity_nonneg leftUnits i),
      integral_finsetSum]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul,
        integral_cell_plus_endpoint_difference leftStart rightStart i j]
      dsimp [rectangleLogAddValue]
      ring
    · intro j hj
      exact continuous_cellPlusPrimitive leftStart rightStart rightUnits i j
  · intro i hi
    exact hPotentialContinuous.integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self |>.smul_measure ENNReal.ofReal_ne_top

private lemma continuous_cellPrimitive (start : ℝ) (units : List ℕ)
    (i j : ℕ) :
    Integrable (fun x : ℝ =>
      referenceDensity units j *
        (primitive (x - referenceCellLeft start j) -
          primitive (x - referenceCellRight start j)))
      (volume.restrict (Set.Ico (referenceCellLeft start i)
        (referenceCellRight start i))) := by
  have hcont : Continuous (fun x : ℝ =>
      referenceDensity units j *
        (primitive (x - referenceCellLeft start j) -
          primitive (x - referenceCellRight start j))) :=
    continuous_const.mul
      ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
        (continuous_primitive.comp (continuous_id.sub continuous_const)))
  exact hcont.integrableOn_Icc.mono_set Set.Ico_subset_Icc_self

/-- Integrating one endpoint difference over another reference cell gives
the exact second-primitive rectangle value. -/
private lemma integral_cell_endpoint_difference (start : ℝ) (i j : ℕ) :
    (∫ x in Set.Ico (referenceCellLeft start i)
        (referenceCellRight start i),
      primitive (x - referenceCellLeft start j) -
        primitive (x - referenceCellRight start j)) =
      rectangleLogValue (referenceCellLeft start i)
        (referenceCellRight start i) (referenceCellLeft start j)
        (referenceCellRight start j) := by
  have hi : referenceCellLeft start i ≤ referenceCellRight start i :=
    referenceCellLeft_le_right start i
  have hleft : Integrable
      (fun x : ℝ => primitive (x - referenceCellLeft start j))
      (volume.restrict (Set.Ico (referenceCellLeft start i)
        (referenceCellRight start i))) :=
    (continuous_primitive.comp
      (continuous_id.sub continuous_const)).integrableOn_Icc.mono_set
        Set.Ico_subset_Icc_self
  have hright : Integrable
      (fun x : ℝ => primitive (x - referenceCellRight start j))
      (volume.restrict (Set.Ico (referenceCellLeft start i)
        (referenceCellRight start i))) :=
    (continuous_primitive.comp
      (continuous_id.sub continuous_const)).integrableOn_Icc.mono_set
        Set.Ico_subset_Icc_self
  rw [integral_sub hleft hright]
  rw [integral_Ico_primitive_sub _ hi, integral_Ico_primitive_sub _ hi]
  simp [rectangleLogValue]
  ring

/-- The actual self-potential integral of any piecewise-uniform reference is
the finite sum of exact rectangle logarithmic energies. -/
theorem referenceSelfEnergy_eq_rectangleSum (start : ℝ) (count : ℕ)
    (units : List ℕ) :
    (∫ x, referencePotential start count units x
      ∂referenceMeasure start count units) =
      ∑ i ∈ Finset.range count, ∑ j ∈ Finset.range count,
        referenceDensity units i * referenceDensity units j *
          rectangleLogValue
            (referenceCellLeft start i) (referenceCellRight start i)
            (referenceCellLeft start j) (referenceCellRight start j) := by
  have hPotentialContinuous :
      Continuous (fun x : ℝ =>
        ∑ j ∈ Finset.range count,
          referenceDensity units j *
            (primitive (x - referenceCellLeft start j) -
              primitive (x - referenceCellRight start j))) := by
    apply continuous_finsetSum
    intro j hj
    exact continuous_const.mul
      ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
        (continuous_primitive.comp (continuous_id.sub continuous_const)))
  have hPotentialIntegrable :
      Integrable (fun x : ℝ => referencePotential start count units x)
        (referenceMeasure start count units) := by
    rw [show (fun x : ℝ => referencePotential start count units x) =
      fun x => ∑ j ∈ Finset.range count,
        referenceDensity units j *
          (primitive (x - referenceCellLeft start j) -
            primitive (x - referenceCellRight start j)) by
        funext x
        exact referencePotential_eq_endpoints start count units x]
    unfold referenceMeasure
    apply integrable_finsetSum_measure.mpr
    intro i hi
    exact hPotentialContinuous.integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self |>.smul_measure ENNReal.ofReal_ne_top
  rw [show (fun x : ℝ => referencePotential start count units x) =
    fun x => ∑ j ∈ Finset.range count,
      referenceDensity units j *
        (primitive (x - referenceCellLeft start j) -
          primitive (x - referenceCellRight start j)) by
      funext x
      exact referencePotential_eq_endpoints start count units x]
  unfold referenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro i hi
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (referenceDensity_nonneg units i)]
    rw [integral_finsetSum]
    simp only [smul_eq_mul]
    rw [Finset.mul_sum]
    · apply Finset.sum_congr rfl
      intro j hj
      rw [integral_const_mul, integral_cell_endpoint_difference]
      dsimp [rectangleLogValue]
      ring
    · intro j hj
      exact continuous_cellPrimitive start units i j
  · intro i hi
    exact hPotentialContinuous.integrableOn_Icc.mono_set
      Set.Ico_subset_Icc_self |>.smul_measure ENNReal.ofReal_ne_top

/-! ### Literal v10 specializations

These are semantic identities for the actual Appendix A arrays. They do not
introduce numerical bounds; the finite sums are the objects consumed by the
rational logarithm certificate layer.
-/

theorem pinnedSelfEnergy_eq_rectangleSum :
    (∫ x, ConfigSegment.pinnedReferencePotential x
      ∂ConfigSegment.pinnedReferenceMeasure) =
      ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 32,
        referenceDensity ConfigData.pinnedMassUnits i *
          referenceDensity ConfigData.pinnedMassUnits j *
          rectangleLogValue
            (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
            (referenceCellLeft (1 / 4) j) (referenceCellRight (1 / 4) j) := by
  simpa only [referencePotential, pinnedReferencePotential,
    pinnedReferenceMeasure] using
    (referenceSelfEnergy_eq_rectangleSum (1 / 4) 32
      ConfigData.pinnedMassUnits)

theorem frequencySelfEnergy_eq_rectangleSum :
    (∫ x, ConfigSegment.frequencyReferencePotential x
      ∂ConfigSegment.frequencyReferenceMeasure) =
      ∑ i ∈ Finset.range 160, ∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits i *
          referenceDensity ConfigData.frequencyMassUnits j *
          rectangleLogValue
            (referenceCellLeft (1 / 2) i) (referenceCellRight (1 / 2) i)
            (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j) := by
  simpa only [referencePotential, frequencyReferencePotential,
    frequencyReferenceMeasure] using
    (referenceSelfEnergy_eq_rectangleSum (1 / 2) 160
      ConfigData.frequencyMassUnits)

theorem pinnedFrequencyPlusEnergy_eq_rectangleSum :
    (∫ x, referencePlusPotential (1 / 2) 160 ConfigData.frequencyMassUnits x
      ∂ConfigSegment.pinnedReferenceMeasure) =
      ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.pinnedMassUnits i *
          referenceDensity ConfigData.frequencyMassUnits j *
          rectangleLogAddValue
            (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
            (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j) := by
  simpa only [pinnedReferenceMeasure] using
    (referenceCrossPlusEnergy_eq_rectangleSum
      (1 / 4) 32 ConfigData.pinnedMassUnits
      (1 / 2) 160 ConfigData.frequencyMassUnits)

theorem reflectedFrequencyPotential_ofReal (x : ℝ) :
    Li2Lean.P0.ConfigReferenceSymmetry.reflectedFrequencyPotential
        (Complex.ofReal x) =
      referencePlusPotential (1 / 2) 160 ConfigData.frequencyMassUnits x := by
  rw [Li2Lean.P0.ConfigReferenceSymmetry.reflectedFrequencyPotential_eq_mixed]
  unfold referencePlusPotential
  apply integral_congr_ae
  filter_upwards [] with t
  simp only [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]

theorem pinnedReflectedFrequencyEnergy_eq_rectangleSum :
    (∫ x, Li2Lean.P0.ConfigReferenceSymmetry.reflectedFrequencyPotential
        (Complex.ofReal x) ∂ConfigSegment.pinnedReferenceMeasure) =
      ∑ i ∈ Finset.range 32, ∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.pinnedMassUnits i *
          referenceDensity ConfigData.frequencyMassUnits j *
          rectangleLogAddValue
            (referenceCellLeft (1 / 4) i) (referenceCellRight (1 / 4) i)
            (referenceCellLeft (1 / 2) j) (referenceCellRight (1 / 2) j) := by
  calc
    _ = ∫ x, referencePlusPotential (1 / 2) 160
          ConfigData.frequencyMassUnits x
          ∂ConfigSegment.pinnedReferenceMeasure := by
      apply integral_congr_ae
      filter_upwards [] with x
      exact reflectedFrequencyPotential_ofReal x
    _ = _ := pinnedFrequencyPlusEnergy_eq_rectangleSum

end

end Li2Lean.P0.ConfigQLogSegments

#print axioms Li2Lean.P0.ConfigQLogSegments.referenceSelfEnergy_eq_rectangleSum
#print axioms Li2Lean.P0.ConfigQLogSegments.referenceCrossPlusEnergy_eq_rectangleSum
#print axioms Li2Lean.P0.ConfigQLogSegments.pinnedSelfEnergy_eq_rectangleSum
#print axioms Li2Lean.P0.ConfigQLogSegments.frequencySelfEnergy_eq_rectangleSum
#print axioms Li2Lean.P0.ConfigQLogSegments.pinnedReflectedFrequencyEnergy_eq_rectangleSum
