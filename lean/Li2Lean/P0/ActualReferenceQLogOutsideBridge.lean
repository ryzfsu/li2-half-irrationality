/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceQLogOutside
import Li2Lean.P0.ActualReferenceQLogOutsideCheck

/-!
# The exterior primitive and its rational endpoint checker agree

The calculus leaf uses the original finite Fejer moments. The independent
checker uses the equivalent degree-48 moments and shifts the index by one.
The statements here reconcile those definitions and connect the checker
directly to the literal frequency/contour interaction.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ActualReferenceQLogOutsideBridge

noncomputable section

open ConfigContourReference ConfigContourKernel ConfigContourFormula ConfigSegment
open ActualReferenceQLogOutside

theorem outsideCoefficient_eq_bR {n : ℕ} (hn : n < 48) :
    outsideCoefficient (n + 1) = CA.Contour.bR n := by
  have hn' : n + 1 ≤ 48 := by omega
  simp only [outsideCoefficient, CA.Contour.bR, ConfigFejerLog.contourMoment,
    ConfigContourSelfPotential.contourFourierMoment,
    ConfigContourSelfPotential.K48Coeff, ite_eq_left hn', Nat.cast_add, Nat.cast_one]

theorem outsideLogPrimitive_eq_checker {t : ℝ} (ht : 1 / 2 ≤ t) :
    outsideLogPrimitive (outsideRadius t) = ActualReferenceQLogOutsideCheck.logPrimitive t := by
  rw [outsideLogPrimitive_eq ht]
  simp only [ActualReferenceQLogOutsideCheck.logPrimitive, outsideProduct, mul_assoc]

theorem outsidePowerPrimitive_eq_checker (n : ℕ) (t : ℝ) :
    outsidePowerPrimitive (n + 1) (outsideRadius t) =
      ActualReferenceQLogOutsideCheck.powerPrimitive n t := by
  cases n with
  | zero =>
      simpa only [ActualReferenceQLogOutsideCheck.powerPrimitive, outsideParameter] using
        outsidePowerPrimitive_one_eq (outsideRadius t)
  | succ k =>
      simpa only [ActualReferenceQLogOutsideCheck.powerPrimitive, outsideParameter] using
        outsidePowerPrimitive_add_two_eq k (outsideRadius t)

theorem outsideContourPrimitive_eq_checker {t : ℝ} (ht : 1 / 2 ≤ t) :
    outsideContourPrimitive t = ActualReferenceQLogOutsideCheck.primitive t := by
  have hmass : (ActualReferenceQLogOutsideCheck.mq : ℝ) =
      (267885951940 / 1000000000000 : ℝ) := by
    norm_num [ActualReferenceQLogOutsideCheck.mq]
  rw [outsideContourPrimitive_eq_sum48, ActualReferenceQLogOutsideCheck.primitive,
    hmass, outsideLogPrimitive_eq_checker ht]
  congr 1
  apply Finset.sum_congr rfl
  intro n hn
  rw [outsideCoefficient_eq_bR (Finset.mem_range.mp hn), outsidePowerPrimitive_eq_checker]

theorem integral_contourReferencePotential_neg_eq_checker {a b : ℝ}
    (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, contourReferencePotential (-(t : ℂ))) =
      ActualReferenceQLogOutsideCheck.primitive b -
        ActualReferenceQLogOutsideCheck.primitive a := by
  rw [integral_contourReferencePotential_neg ha hab,
    outsideContourPrimitive_eq_checker (ha.trans hab), outsideContourPrimitive_eq_checker ha]

theorem integral_contourReferencePotential_neg_frequency_eq_checker :
    (∫ t, contourReferencePotential (-(t : ℂ)) ∂frequencyReferenceMeasure) =
      ∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j *
        (ActualReferenceQLogOutsideCheck.primitive (referenceCellRight (1 / 2) j) -
          ActualReferenceQLogOutsideCheck.primitive (referenceCellLeft (1 / 2) j)) := by
  rw [integral_contourReferencePotential_neg_frequency]
  apply Finset.sum_congr rfl
  intro j hj
  have ha := frequencyCell_left_ge_half j
  have hb := ha.trans (referenceCellLeft_le_right (1 / 2) j)
  rw [outsideContourPrimitive_eq_checker hb, outsideContourPrimitive_eq_checker ha]

theorem primitiveI_mem_outside {t : ℚ} (ht : 1 / 2 ≤ t) :
    (ActualReferenceQLogOutsideCheck.primitiveI t).mem (outsideContourPrimitive (t : ℝ)) := by
  have htR : (1 / 2 : ℝ) ≤ (t : ℝ) := CA.Frequency.half_le_cast ht
  rw [outsideContourPrimitive_eq_checker htR]
  exact ActualReferenceQLogOutsideCheck.primitiveI_mem ht

end

end Li2Lean.P0.ActualReferenceQLogOutsideBridge
