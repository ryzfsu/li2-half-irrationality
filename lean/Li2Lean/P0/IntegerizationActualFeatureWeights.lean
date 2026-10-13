/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationProofs
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Prod
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Tactic

namespace Li2Lean.P0.Integerization
open Finset

/-- Exact source feature support. Label 0 is the ubiquitous feature,
label 1 is supported on I, and label 2 is supported on J. -/
def p0FeatureAllowed (h : ℕ) (f : ℕ × Fin 3) : Prop :=
  (f.2 = 1 → h ≤ f.1 ∧ f.1 < 5*h) ∧ (f.2 = 2 → f.1 < 8*h)

def p0LowestFeatures (h : ℕ) : Finset (ℕ × Fin 3) :=
  (range h ×ˢ {0, 2}) ∪ (Ico h (3*h) ×ˢ univ)

theorem p0LowestFeatures_disjoint (h : ℕ) :
    Disjoint (range h ×ˢ ({0,2} : Finset (Fin 3)))
      (Ico h (3*h) ×ˢ (univ : Finset (Fin 3))) := by
  apply Finset.disjoint_left.mpr
  intro f ha hb
  have ha' := (Finset.mem_product.mp ha).1
  have hb' := (Finset.mem_product.mp hb).1
  simp only [mem_range, mem_Ico] at ha' hb'
  omega

theorem p0LowestFeatures_card (h : ℕ) :
    (p0LowestFeatures h).card = 8*h := by
  rw [p0LowestFeatures, card_union_of_disjoint (p0LowestFeatures_disjoint h)]
  simp
  omega

theorem p0LowestFeatures_mem_iff (h : ℕ) (f : ℕ × Fin 3) :
    f ∈ p0LowestFeatures h ↔ p0FeatureAllowed h f ∧ f.1 < 3*h := by
  rcases f with ⟨k,t⟩
  fin_cases t <;> simp [p0LowestFeatures, p0FeatureAllowed] <;> omega

/-- A finite set of the required size cannot beat a set consisting of all
admissible features below a fixed weight threshold. -/
theorem sum_ge_lowest_of_equal_card
    {α : Type*} [DecidableEq α] (S T : Finset α) (w : α → ℕ) (b : ℕ)
    (hcard : S.card = T.card)
    (hT : ∀ x ∈ T, w x ≤ b)
    (hS : ∀ x ∈ S, x ∉ T → b ≤ w x) :
    (∑ x ∈ T, w x) ≤ ∑ x ∈ S, w x := by
  have hc : (T \ S).card = (S \ T).card :=
    (Finset.card_sdiff_eq_card_sdiff_iff).mpr hcard.symm
  have hlo : (∑ x ∈ T \ S, w x) ≤ (T \ S).card * b := by
    calc
      _ ≤ ∑ _x ∈ T \ S, b := Finset.sum_le_sum fun x hx => hT x (mem_sdiff.mp hx).1
      _ = _ := by simp
  have hhi : (S \ T).card * b ≤ ∑ x ∈ S \ T, w x := by
    calc
      _ = ∑ _x ∈ S \ T, b := by simp
      _ ≤ _ := Finset.sum_le_sum fun x hx =>
        hS x (mem_sdiff.mp hx).1 (mem_sdiff.mp hx).2
  have hsplitS : (∑ x ∈ S \ T, w x) + (∑ x ∈ S ∩ T, w x) =
      ∑ x ∈ S, w x := by
    rw [← Finset.sum_union (Finset.disjoint_sdiff_inter S T), Finset.sdiff_union_inter]
  have hsplitT : (∑ x ∈ T \ S, w x) + (∑ x ∈ S ∩ T, w x) =
      ∑ x ∈ T, w x := by
    rw [Finset.inter_comm S T, ← Finset.sum_union (Finset.disjoint_sdiff_inter T S),
      Finset.sdiff_union_inter]
  rw [hc] at hlo
  omega

theorem p0LowestFeatures_weight (h : ℕ) :
    (∑ f ∈ p0LowestFeatures h, f.1) =
      2 * (∑ k ∈ range h, k) + 3 * (∑ k ∈ Ico h (3*h), k) := by
  rw [p0LowestFeatures, Finset.sum_union (p0LowestFeatures_disjoint h)]
  simp only [Finset.sum_product]
  simp [Finset.mul_sum, Nat.mul_comm]

theorem p0_actual_feature_weight_lower_bound
    (h : ℕ) (p : Fin (8*h) → ℕ × Fin 3)
    (hp : Function.Injective p) (ha : ∀ j, p0FeatureAllowed h (p j)) :
    2 * (∑ k ∈ range h, k) + 3 * (∑ k ∈ Ico h (3*h), k) ≤
      ∑ j, (p j).1 := by
  let S := Finset.univ.image p
  have hcard : S.card = (p0LowestFeatures h).card := by
    rw [p0LowestFeatures_card]
    simp [S, Finset.card_image_of_injective _ hp]
  have hle := sum_ge_lowest_of_equal_card S (p0LowestFeatures h) Prod.fst (3*h)
    hcard
    (fun x hx => (p0LowestFeatures_mem_iff h x |>.mp hx).2.le)
    (by
      intro x hx hnot
      obtain ⟨j, _, rfl⟩ := Finset.mem_image.mp hx
      have hn : ¬ (p j).1 < 3*h := by
        intro hlt
        exact hnot ((p0LowestFeatures_mem_iff h (p j)).mpr ⟨ha j, hlt⟩)
      omega)
  rw [p0LowestFeatures_weight] at hle
  simpa only [S, Finset.sum_image (fun _ _ _ _ he => hp he)] using hle

/-- The paper's exact sufficient exponent for every admissible selection. -/
theorem p0_actual_feature_exponent_lower_bound
    (h : ℕ) (p : Fin (8*h) → ℕ × Fin 3)
    (hp : Function.Injective p) (ha : ∀ j, p0FeatureAllowed h (p j)) :
    13*h^2-4*h ≤ ∑ j, (p j).1 := by
  rw [← p0_feature_exponent]
  exact p0_actual_feature_weight_lower_bound h p hp ha

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0LowestFeatures_card
#print axioms Li2Lean.P0.Integerization.p0LowestFeatures_mem_iff
#print axioms Li2Lean.P0.Integerization.p0_actual_feature_exponent_lower_bound

