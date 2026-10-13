/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyLimit
import Li2Lean.P0.FrequencyEllipseCutoff
import Li2Lean.P0.ContourFrequencyFactor

open MeasureTheory Filter Topology

namespace Li2Lean.P0.FrequencyLimit

noncomputable section

open FrequencyCutoff FrequencyFinite FrequencyLeaf

/-- The direct literal `contourQMinor...` bridge for the target row
`m = 32`.  The tuple positivity and all right-minor pole conditions remain
explicit; the latter are discharged only for the actual scaled ellipse. -/
theorem contourQMinorFrequencyProduct_m32_ellipse
    (S : Finset ℕ) (hSI : S ⊆ Iset 32)
    (R : Fin 32 → ℕ) (hR : StrictMono R)
    (hRg : ∀ i, 16 < R i) (u : Fin (32 - S.card) → ℝ) :
    contourQMinorFrequencyProduct S (by norm_num) hSI R hR
        (fun z => p0EllipsePoint 32 (u z)) =
      contourQMinorFrequencyIndependentFactor S (by norm_num) hSI
          (fun z => p0EllipsePoint 32 (u z)) *
        frequencyFactor 32 16 S
          ((Finset.univ : Finset (Fin 32)).image R) (32 - S.card)
          (fun z => p0EllipsePoint 32 (u z)) := by
  have hRpos : ∀ i, 0 < R i := fun i =>
    lt_of_le_of_lt (Nat.zero_le _) (hRg i)
  have hZ := Li2Lean.P0.p0EllipsePoint_avoids_contourQRightColumns
    (by norm_num) (by norm_num) S hSI u
  exact Li2Lean.P0.contourQMinorFrequencyProduct_eq_fixedFactor_mul_frequencyFactor
    (hm := by norm_num) (h4 := by norm_num) S hSI R hR hRpos
    (fun z => p0EllipsePoint 32 (u z)) hZ

/-- The literal contour-Q sum factors through the actual qfactor bridge on the
scaled ellipse. No abstract `QFactorIdentity` is assumed: each tuple uses
the concrete `contourQValue_eq_frequencyFactor_ellipse` theorem. -/
theorem finiteQSum_eq_contourFactor_mul_frequencyZ {m H : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) :
    finiteQSum m H hm4 S hSI (fun i => p0EllipsePoint m (u i)) =
      contourQFrequencyIndependentFactor S hm4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        frequencyZ m H S (m - S.card)
          (fun i => p0EllipsePoint m (u i)) := by
  classical
  unfold finiteQSum
  rw [FrequencyCutoff.sum_cutoffTuples]
  calc
    (∑ r : TruncatedTuple (m / 2) m H,
        contourQValue S hm4 hSI (forgetCutoff r).val
          (forgetCutoff r).property.1
          (fun i => p0EllipsePoint m (u i))) =
      contourQFrequencyIndependentFactor S hm4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        ∑ r : TruncatedTuple (m / 2) m H,
          frequencyFactor m (m / 2) S
            (tupleSet (forgetCutoff r)) (m - S.card)
            (fun i => p0EllipsePoint m (u i)) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      exact Li2Lean.P0.contourQValue_eq_frequencyFactor_ellipse hm hm4 S hSI
        (forgetCutoff r).val (forgetCutoff r).property.1
        (forgetCutoff r).property.2 u
    _ = contourQFrequencyIndependentFactor S hm4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        frequencyZ m H S (m - S.card)
          (fun i => p0EllipsePoint m (u i)) := by
      congr 1
      unfold frequencyZ finiteZ finiteFamily
      exact (FrequencyCutoff.sum_powersetCard_eq_sum_truncated
        (A := ℝ) (m / 2) m H
        (fun R => frequencyFactor m (m / 2) S R (m - S.card)
          (fun i => p0EllipsePoint m (u i)))).symm

/-- The concrete qfactor bridge transfers the frequency cutoff to every finite
contour-Q row. Its only geometric side condition is the actual ellipse
non-pole proof supplied by the qfactor module. -/
theorem finiteQSum_cutoff_of_contourFactor {m H : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hH : 20 * m ≤ H)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (u : Fin (m - S.card) → ℝ) :
    finiteQSum m H hm4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        finiteQSum m (20 * m) hm4 S hSI
          (fun i => p0EllipsePoint m (u i)) := by
  have hSI' : S ⊆ FrequencyLeaf.I_m m := by
    rw [← Li2Lean.P0.Iset_eq_frequency_I_m hm hm4]
    exact hSI
  have hcut := FrequencyFinite.frequencyZ_p0Ellipse_cutoff hm hm4 hH S hSI' u
  have hZ := Li2Lean.P0.p0EllipsePoint_avoids_contourQRightColumns
    hm hm4 S hSI u
  have hfactor_nonneg :
      0 ≤ contourQFrequencyIndependentFactor S hm4 hSI
        (fun i => p0EllipsePoint m (u i)) := by
    have hfixed := contourQFixedFactor_nonneg S hSI
      (fun i => p0EllipsePoint m (u i))
    have hden := contourQRightFixedDenominator_pos S hm4 hSI
      (fun i => p0EllipsePoint m (u i)) hZ
    unfold contourQFrequencyIndependentFactor
    positivity
  calc
    finiteQSum m H hm4 S hSI (fun i => p0EllipsePoint m (u i)) =
        contourQFrequencyIndependentFactor S hm4 hSI
            (fun i => p0EllipsePoint m (u i)) *
          frequencyZ m H S (m - S.card)
            (fun i => p0EllipsePoint m (u i)) :=
      finiteQSum_eq_contourFactor_mul_frequencyZ hm hm4 S hSI u
    _ ≤ contourQFrequencyIndependentFactor S hm4 hSI
          (fun i => p0EllipsePoint m (u i)) *
        ((1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
          frequencyZ m (20 * m) S (m - S.card)
            (fun i => p0EllipsePoint m (u i))) :=
      mul_le_mul_of_nonneg_left hcut hfactor_nonneg
    _ = (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        finiteQSum m (20 * m) hm4 S hSI
          (fun i => p0EllipsePoint m (u i)) := by
      rw [finiteQSum_eq_contourFactor_mul_frequencyZ hm hm4 S hSI u]
      ring

/-- The concrete qfactor bridge closes the ENNReal monotone passage for the
literal envelope, with no infinite summability premise. -/
theorem full_cutoffENN_of_contourFactor (m : ℕ) (hm : 0 < m)
    (hm4 : 4 ∣ m) :
    EInfinityENN m hm4 ≠ ⊤ ∧
      EInfinityENN m hm4 ≤
        ENNReal.ofReal
          ((1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) hm4) := by
  apply full_cutoffENN_of_Q_bounds m hm hm4
  intro H hH S hSI u
  exact finiteQSum_cutoff_of_contourFactor hm hm4 hH S hSI u

/-- The literal target row at `m = 32`, retained as a direct instance of the
general bridge so downstream row certificates need no abstract factor input. -/
theorem finiteQSum_cutoff_m32 {H : ℕ} (hH : 640 ≤ H)
    (S : Finset ℕ) (hSI : S ⊆ Iset 32)
    (u : Fin (32 - S.card) → ℝ) :
    finiteQSum 32 H (by norm_num) S hSI
        (fun i => p0EllipsePoint 32 (u i)) ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ (32 : ℕ)) *
        finiteQSum 32 640 (by norm_num) S hSI
          (fun i => p0EllipsePoint 32 (u i)) := by
  apply finiteQSum_cutoff_of_contourFactor (m := 32) (H := H)
    (by norm_num) (by norm_num)
  norm_num at hH ⊢
  exact hH

theorem full_cutoffENN_m32 :
    EInfinityENN 32 (by norm_num) ≠ ⊤ ∧
      EInfinityENN 32 (by norm_num) ≤
        ENNReal.ofReal
          ((1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ (32 : ℕ)) *
            E 32 640 (by norm_num)) := by
  simpa using (full_cutoffENN_of_contourFactor (m := 32)
    (by norm_num) (by norm_num))

end

end Li2Lean.P0.FrequencyLimit
