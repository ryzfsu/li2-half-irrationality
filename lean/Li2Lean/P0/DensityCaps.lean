/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceClosure

open MeasureTheory Set
open scoped ENNReal

namespace Li2Lean.P0.ReferencePackaging
noncomputable section
open ConfigSegment

private lemma finset_restrict_cells_eq
    (F : Finset ℕ) (cell : ℕ → Set ℝ)
    (hdisj : (F : Set ℕ).Pairwise (Function.onFun Disjoint (cell)))
    (hmeas : ∀ j, MeasurableSet (cell j)) :
    (∑ j ∈ F, volume.restrict (cell j)) =
      volume.restrict (⋃ j ∈ F, cell j) := by
  symm
  rw [Measure.restrict_biUnion_finset hdisj hmeas]
  ext t ht
  rw [Measure.finsetSum_apply, Measure.sum_apply _ ht]
  rw [tsum_fintype]
  exact Finset.sum_coe_sort F (fun j : ℕ => volume.restrict (cell j) t)

private lemma reference_cells_pairwise_disjoint
    (start : ℝ) (F : Finset ℕ) :
    (F : Set ℕ).Pairwise (Function.onFun Disjoint
      (fun j => Set.Ico (referenceCellLeft start j) (referenceCellRight start j))) := by
  intro i hi j hj hij
  change Disjoint (Set.Ico (referenceCellLeft start i) (referenceCellRight start i))
    (Set.Ico (referenceCellLeft start j) (referenceCellRight start j))
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  rcases lt_or_gt_of_ne hij with hlt | hgt
  · have hn : i + 1 ≤ j := Nat.succ_le_of_lt hlt
    have hc : ((i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast hn
    dsimp [referenceCellRight, referenceCellLeft] at hxi hxj
    push_cast at hxi hxj hc
    have hxi' := hxi.2
    have hxj' := hxj.1
    linarith
  · have hn : j + 1 ≤ i := Nat.succ_le_of_lt hgt
    have hc : ((j + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast hn
    dsimp [referenceCellRight, referenceCellLeft] at hxi hxj
    push_cast at hxi hxj hc
    have hxi' := hxi.1
    have hxj' := hxj.2
    linarith


private lemma reference_cells_union_pinned_subset :
    (⋃ j ∈ (Finset.range 32 : Finset ℕ),
      Set.Ico (referenceCellLeft (1 / 4 : ℝ) j) (referenceCellRight (1 / 4 : ℝ) j)) ⊆
      Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) := by
  rintro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  obtain ⟨hjrange, hx⟩ := hj
  rcases hx with ⟨hxleft, hxright⟩
  have hjlt : j < 32 := Finset.mem_range.mp hjrange
  constructor
  · dsimp [referenceCellLeft] at hxleft ⊢
    have hc : (0 : ℝ) ≤ (j : ℝ) := by positivity
    linarith
  · dsimp [referenceCellRight] at hxright ⊢
    have hc : ((j + 1 : ℕ) : ℝ) ≤ 32 := by exact_mod_cast (by omega : j + 1 ≤ 32)
    linarith

private lemma reference_cells_union_frequency_subset :
    (⋃ j ∈ (Finset.range 160 : Finset ℕ),
      Set.Ico (referenceCellLeft (1 / 2 : ℝ) j) (referenceCellRight (1 / 2 : ℝ) j)) ⊆
      Set.Ici (1 / 2 : ℝ) := by
  rintro x hx
  simp only [Set.mem_iUnion] at hx
  obtain ⟨j, hj⟩ := hx
  obtain ⟨hjrange, hx⟩ := hj
  dsimp [referenceCellLeft] at hx
  change (1 / 2 : ℝ) ≤ x
  have hc : (0 : ℝ) ≤ (j : ℝ) := by positivity
  linarith [hx.1]

private lemma weighted_cells_le_union
    (start : ℝ) (F : Finset ℕ) (units : List ℕ)
    (hcap : ∀ j ∈ F, referenceDensity units j ≤ 1) :
    (∑ j ∈ F, ENNReal.ofReal (referenceDensity units j) •
      volume.restrict (Set.Ico (referenceCellLeft start j) (referenceCellRight start j))) ≤
      volume.restrict (⋃ j ∈ F,
        Set.Ico (referenceCellLeft start j) (referenceCellRight start j)) := by
  have hdisj : (F : Set ℕ).Pairwise (Function.onFun Disjoint
      (fun j => Set.Ico (referenceCellLeft start j) (referenceCellRight start j))) :=
    reference_cells_pairwise_disjoint start F
  have hsum := finset_restrict_cells_eq F
      (fun j => Set.Ico (referenceCellLeft start j) (referenceCellRight start j)) hdisj
      (fun j => measurableSet_Ico)
  rw [Measure.le_iff]
  intro s hs
  rw [Measure.finsetSum_apply]
  rw [← hsum]
  rw [Measure.finsetSum_apply]
  apply Finset.sum_le_sum
  intro j hj
  rw [Measure.smul_apply, Measure.restrict_apply hs]
  have hcoef : ENNReal.ofReal (referenceDensity units j) ≤ 1 := by
    exact ENNReal.ofReal_le_one.mpr (hcap j hj)
  have hnonneg : 0 ≤ volume (s ∩ Ico (referenceCellLeft start j) (referenceCellRight start j)) := bot_le
  simpa using
    (smul_le_smul hcoef (le_refl _) bot_le hnonneg)

 theorem pinnedReferenceMeasure_le_volume_restrict :
    pinnedReferenceMeasure ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) := by
  unfold pinnedReferenceMeasure
  apply le_trans (weighted_cells_le_union (1 / 4) (Finset.range 32)
    ConfigData.pinnedMassUnits (by
      intro j hj
      exact pinned_density_cap j (Finset.mem_range.mp hj)))
  exact Measure.restrict_mono reference_cells_union_pinned_subset le_rfl

theorem frequencyReferenceMeasure_le_volume_restrict :
    frequencyReferenceMeasure ≤ volume.restrict (Set.Ici (1 / 2 : ℝ)) := by
  unfold frequencyReferenceMeasure
  apply le_trans (weighted_cells_le_union (1 / 2) (Finset.range 160)
    ConfigData.frequencyMassUnits (by
      intro j hj
      exact frequency_density_cap j (Finset.mem_range.mp hj)))
  exact Measure.restrict_mono reference_cells_union_frequency_subset le_rfl

end
end Li2Lean.P0.ReferencePackaging
