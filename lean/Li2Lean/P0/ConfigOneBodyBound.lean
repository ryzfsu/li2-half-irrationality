/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigLiteralWeight
import Li2Lean.P0.FrequencyCutoff
import Li2Lean.P0.P0CoefficientStep
import Li2Lean.P0.FrequencyLimit
import Li2Lean.P0.FrequencyHeadCount

open MeasureTheory

namespace Li2Lean.P0.Config

open Li2Lean.P0
open Li2Lean.P0.FrequencyCutoff

theorem tupleSet_sort_eq_of_strictMono {g m : ℕ}
    (r : IncreasingTuple g m) :
    (tupleSet r).sort (· ≤ ·) = List.ofFn r.val := by
  have hset : (List.ofFn r.val).toFinset = tupleSet r := by
    ext x
    simp [tupleSet]
  have hnodup : (List.ofFn r.val).Nodup := by
    apply List.nodup_ofFn.mpr
    exact r.property.1.injective
  have hsorted : (List.ofFn r.val).SortedLE := by
    exact List.sortedLE_ofFn_iff.mpr r.property.1.monotone
  rw [← hset]
  exact (List.toFinset_sort (· ≤ ·) hnodup).2 hsorted.pairwise

theorem orderedElem_tupleSet {g m : ℕ}
    (r : IncreasingTuple g m) (i : Fin m) :
    orderedElem (tupleSet r) (Fin.cast (tupleSet_card r).symm i) = r.val i := by
  classical
  let h := tupleSet_card r
  have hsort := tupleSet_sort_eq_of_strictMono r
  let sorted := (tupleSet r).sort (· ≤ ·)
  have hlen : sorted.length = m := by
    dsimp [sorted]
    rw [Finset.length_sort, tupleSet_card]
  have hi : i.val < sorted.length := by
    simp [hlen]
  have hsorti :
      (tupleSet r).orderEmbOfFin h i = r.val i := by
    rw [Finset.orderEmbOfFin_apply]
    simp [hsort]
  change (tupleSet r).orderIsoOfFin rfl (Fin.cast h.symm i) = r.val i
  have hdef : (tupleSet r).orderIsoOfFin rfl (Fin.cast h.symm i) =
      (tupleSet r).orderEmbOfFin h i := by
    rfl
  exact hdef.trans hsorti

noncomputable def mkTupleConfiguration {m : ℕ} (hm8 : 8 ≤ m)
    (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) :
    FiniteConfiguration :=
  { m := m
    m_ge_eight := hm8
    four_dvd_m := h4
    pinned := S
    frequency := tupleSet r
    pinned_subset := by
      rw [Iset_eq_paper_interval m h4] at hSI
      simpa [pinnedUniverse] using hSI
    frequency_lower := by
      intro a ha
      rcases (mem_tupleSet r a).mp ha with ⟨i, rfl⟩
      exact r.property.2 i
    frequency_card := tupleSet_card r
    contourCount := m - S.card
    contour := fun i => baseEllipse (u i)
    contour_mem := by intro i; exact ⟨u i, rfl⟩
    mass_balance := by
      have hScard : S.card ≤ m := by
        rw [← Iset_card m]
        exact Finset.card_le_card hSI
      omega }

def tupleScaledContourPoint (C : FiniteConfiguration)
    (i : Fin C.contourCount) : ℂ :=
  Complex.ofReal (C.m : ℝ) * C.contour i

theorem mkTupleConfiguration_scaledContourPoint {m : ℕ}
    (hm8 : 8 ≤ m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingTuple (m / 2) m) (u : Fin (m - S.card) → ℝ)
    (i : Fin (m - S.card)) :
    tupleScaledContourPoint (mkTupleConfiguration hm8 h4 S hSI r u) i =
      p0EllipsePoint m (u i) := by
  simp [tupleScaledContourPoint, mkTupleConfiguration, baseEllipse, p0EllipsePoint]

theorem literalConfigQWeight_mkTuple_eq {m : ℕ}
    (hm8 : 8 ≤ m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) :
    literalConfigQWeight (mkTupleConfiguration hm8 h4 S hSI r u) =
      contourQValue S h4 hSI r.val r.property.1 (fun i => p0EllipsePoint m (u i)) := by
  have heq := literalConfigQWeight_eq_contourQValue_of_baseEllipse
    (mkTupleConfiguration hm8 h4 S hSI r u)
    (fun i => u i) (fun i => rfl)
  simpa [mkTupleConfiguration, orderedElem_tupleSet] using heq

theorem contourQValue_le_exp_of_configFinalBound
    {alpha : ℝ} (hfinal : ConfigFinalBoundLiteral alpha) {m : ℕ}
    (hm8 : 8 ≤ m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) :
    contourQValue S h4 hSI r.val r.property.1 (fun i => p0EllipsePoint m (u i)) ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) +
        Config.cStar * (m : ℝ) + 300 + 1 / 3) := by
  rw [← literalConfigQWeight_mkTuple_eq hm8 h4 S hSI r u]
  exact Li2Lean.P0.literalConfigQWeight_le_exp_of_final_bound hfinal rfl

theorem envelopeTerm_le_exp_of_configFinalBound
    {alpha : ℝ} (hfinal : ConfigFinalBoundLiteral alpha) {m : ℕ}
    (hm8 : 8 ≤ m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) :
    FrequencyLimit.envelopeTerm m h4 S hSI r (fun i => u i) ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) +
        Config.cStar * (m : ℝ) + 300 + 1 / 3) *
      ∏ i : Fin (m - S.card), contourArcDensity m (u i) := by
  unfold FrequencyLimit.envelopeTerm
  exact mul_le_mul_of_nonneg_right
    (contourQValue_le_exp_of_configFinalBound hfinal hm8 h4 S hSI r u)
    (by unfold contourArcDensity; positivity)

theorem finiteQSum_le_exp_mul_card_of_configFinalBound
    {alpha : ℝ} (hfinal : ConfigFinalBoundLiteral alpha) {m H : ℕ}
    (hm8 : 8 ≤ m) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (u : Fin (m - S.card) → ℝ) :
    FrequencyLimit.finiteQSum m H h4 S hSI
        (fun i => p0EllipsePoint m (u i)) ≤
      ((FrequencyCutoff.cutoffTuples (m / 2) m H).card : ℝ) *
        Real.exp (-alpha * (m : ℝ) ^ 2 +
          10 * (m : ℝ) * Real.log (m : ℝ) +
          Config.cStar * (m : ℝ) + 300 + 1 / 3) := by
  unfold FrequencyLimit.finiteQSum
  have hterm : ∀ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
      contourQValue S h4 hSI r.val r.property.1
          (fun i => p0EllipsePoint m (u i)) ≤
        Real.exp (-alpha * (m : ℝ) ^ 2 +
          10 * (m : ℝ) * Real.log (m : ℝ) +
          Config.cStar * (m : ℝ) + 300 + 1 / 3) := by
    intro r hr
    exact contourQValue_le_exp_of_configFinalBound hfinal hm8 h4 S hSI
      r u
  calc
    (∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
        contourQValue S h4 hSI r.val r.property.1
          (fun i => p0EllipsePoint m (u i))) ≤
        ∑ _r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
          Real.exp (-alpha * (m : ℝ) ^ 2 +
            10 * (m : ℝ) * Real.log (m : ℝ) +
            Config.cStar * (m : ℝ) + 300 + 1 / 3) := by
      exact Finset.sum_le_sum (fun r hr => hterm r hr)
    _ = ((FrequencyCutoff.cutoffTuples (m / 2) m H).card : ℝ) *
        Real.exp (-alpha * (m : ℝ) ^ 2 +
          10 * (m : ℝ) * Real.log (m : ℝ) +
          Config.cStar * (m : ℝ) + 300 + 1 / 3) := by
      simp [nsmul_eq_mul]

theorem cutoffTuples_card_eq_choose {g m H : ℕ} :
    (FrequencyCutoff.cutoffTuples g m H).card =
      Nat.choose (Finset.Ioc g H).card m := by
  have himage := FrequencyCutoff.image_tupleSet_cutoff g m H
  have hinj := FrequencyCutoff.tupleSet_injective g m
  calc
    (FrequencyCutoff.cutoffTuples g m H).card =
        ((FrequencyCutoff.cutoffTuples g m H).image FrequencyCutoff.tupleSet).card := by
      exact (Finset.card_image_of_injective _ hinj).symm
    _ = ((Finset.Ioc g H).powersetCard m).card := by rw [himage]
    _ = Nat.choose (Finset.Ioc g H).card m := by
      rw [Finset.card_powersetCard]

theorem cutoffTuples_card_eq_frequencyHead_choose {m : ℕ} :
    (FrequencyCutoff.cutoffTuples (m / 2) m (20 * m)).card =
      Nat.choose (Li2Lean.P0.FrequencyHeadCount.frequencyHeadUniverse m).card m := by
  simpa [Li2Lean.P0.FrequencyHeadCount.frequencyHeadUniverse] using
    (cutoffTuples_card_eq_choose (g := m / 2) (m := m) (H := 20 * m))

theorem integrable_envelopeTerm
    {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingTuple (m / 2) m) :
    Integrable (fun u : Fin (m - S.card) → ℝ =>
      FrequencyLimit.envelopeTerm m h4 S hSI r u)
      (ContourKit.productMeasure Li2Lean.P0.contourParameterMeasure) := by
  exact FrequencyRegularity.integrable_parameter
    (FrequencyLimit.continuous_envelopeTerm m (by omega) h4 S hSI r)

end Li2Lean.P0.Config

#print axioms Li2Lean.P0.Config.tupleSet_sort_eq_of_strictMono
#print axioms Li2Lean.P0.Config.orderedElem_tupleSet
#print axioms Li2Lean.P0.Config.mkTupleConfiguration
#print axioms Li2Lean.P0.Config.literalConfigQWeight_mkTuple_eq
#print axioms Li2Lean.P0.Config.contourQValue_le_exp_of_configFinalBound
#print axioms Li2Lean.P0.Config.envelopeTerm_le_exp_of_configFinalBound
#print axioms Li2Lean.P0.Config.finiteQSum_le_exp_mul_card_of_configFinalBound
#print axioms Li2Lean.P0.Config.cutoffTuples_card_eq_choose
#print axioms Li2Lean.P0.Config.cutoffTuples_card_eq_frequencyHead_choose
#print axioms Li2Lean.P0.Config.integrable_envelopeTerm
