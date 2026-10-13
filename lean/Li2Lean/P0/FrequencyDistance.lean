/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyLeaf

open Finset

namespace Li2Lean.P0.FrequencyLeaf

noncomputable section

/-- Distinct positive integers have product at least the factorial of their count. -/
lemma factorial_card_le_prod (T : Finset ℕ) (hT : ∀ u ∈ T, 0 < u) :
    T.card.factorial ≤ ∏ u ∈ T, u := by
  induction T using Finset.induction_on_max with
  | empty => simp
  | @insert a T hmax ih =>
      have ha : a ∉ T := by
        intro ha
        exact (lt_irrefl a) (hmax a ha)
      have hT' : ∀ u ∈ T, 0 < u := by
        intro u hu
        exact hT u (mem_insert_of_mem hu)
      have hsub : insert a T ⊆ Icc 1 a := by
        intro u hu
        rcases mem_insert.mp hu with h | hu
        · rw [h]
          exact mem_Icc.mpr ⟨hT a (mem_insert_self a T), le_rfl⟩
        · exact mem_Icc.mpr ⟨hT' u hu, (hmax u hu).le⟩
      have hcount : T.card + 1 ≤ a := by
        have hc := card_le_card hsub
        simpa [ha, Nat.card_Icc] using hc
      rw [card_insert_of_notMem ha, Nat.factorial_succ, prod_insert ha]
      exact Nat.mul_le_mul hcount (ih hT')

/-- The balanced factorial product is the smallest product with fixed total index. -/
lemma balanced_factorial_le (a b : ℕ) :
    ((a + b) / 2).factorial * (a + b - (a + b) / 2).factorial ≤
      a.factorial * b.factorial := by
  let n := a + b
  have hc := Nat.choose_le_middle a n
  have hmid : n / 2 ≤ n := Nat.div_le_self n 2
  have hapos : 0 < n.choose (n / 2) := Nat.choose_pos hmid
  apply Nat.le_of_mul_le_mul_left (c := n.choose (n / 2)) ?_ hapos
  calc
    n.choose (n / 2) * (((a + b) / 2).factorial *
        (a + b - (a + b) / 2).factorial) = n.factorial := by
      simpa [n, Nat.mul_assoc] using Nat.choose_mul_factorial_mul_factorial hmid
    _ = n.choose a * (a.factorial * b.factorial) := by
      symm
      simpa [n, Nat.mul_assoc] using
        Nat.choose_mul_factorial_mul_factorial (show a ≤ n by omega)
    _ ≤ n.choose (n / 2) * (a.factorial * b.factorial) :=
      Nat.mul_le_mul_right _ hc

/-- Exact integer-distance separation: each positive distance occurs at most twice. -/
theorem distance_product_factorial (T : Finset ℕ) (s : ℕ) (hs : s ∉ T) :
    (T.card / 2).factorial * (T.card - T.card / 2).factorial ≤
      ∏ u ∈ T, Nat.dist s u := by
  let L := T.filter (fun u => u < s)
  let H := T.filter (fun u => ¬u < s)
  have hL : ∀ u ∈ L, u < s := by
    intro u hu
    exact (mem_filter.mp hu).2
  have hH : ∀ u ∈ H, s < u := by
    intro u hu
    have huT := (mem_filter.mp hu).1
    have hunot := (mem_filter.mp hu).2
    have hne : u ≠ s := by
      intro h
      subst u
      exact hs huT
    omega
  have hinjL : Set.InjOn (fun u => s - u) (↑L : Set ℕ) := by
    intro u hu v hv huv
    dsimp only at huv
    have := hL u hu
    have := hL v hv
    omega
  have hinjH : Set.InjOn (fun u => u - s) (↑H : Set ℕ) := by
    intro u hu v hv huv
    dsimp only at huv
    have := hH u hu
    have := hH v hv
    omega
  have hprodL : L.card.factorial ≤ ∏ u ∈ L, Nat.dist s u := by
    have hl := factorial_card_le_prod (L.image (fun u => s - u)) (by
      intro v hv
      rcases mem_image.mp hv with ⟨u, hu, rfl⟩
      exact Nat.sub_pos_of_lt (hL u hu))
    rw [card_image_iff.mpr hinjL, prod_image hinjL] at hl
    convert hl using 1
    apply prod_congr rfl
    intro u hu
    exact Nat.dist_eq_sub_of_le_right (hL u hu).le
  have hprodH : H.card.factorial ≤ ∏ u ∈ H, Nat.dist s u := by
    have hh := factorial_card_le_prod (H.image (fun u => u - s)) (by
      intro v hv
      rcases mem_image.mp hv with ⟨u, hu, rfl⟩
      exact Nat.sub_pos_of_lt (hH u hu))
    rw [card_image_iff.mpr hinjH, prod_image hinjH] at hh
    convert hh using 1
    apply prod_congr rfl
    intro u hu
    exact Nat.dist_eq_sub_of_le (hH u hu).le
  have hcard : L.card + H.card = T.card := by
    exact card_filter_add_card_filter_not (s := T) _
  calc
    (T.card / 2).factorial * (T.card - T.card / 2).factorial ≤
        L.card.factorial * H.card.factorial := by
      simpa [hcard] using balanced_factorial_le L.card H.card
    _ ≤ (∏ u ∈ L, Nat.dist s u) * ∏ u ∈ H, Nat.dist s u :=
      Nat.mul_le_mul hprodL hprodH
    _ = ∏ u ∈ T, Nat.dist s u := prod_filter_mul_prod_filter_not _ _ _

lemma nat_dist_cast_real (s u : ℕ) :
    (Nat.dist s u : ℝ) = |(s : ℝ) - u| := by
  rcases le_total s u with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h, abs_of_nonpos]
    · ring
    · exact sub_nonpos.mpr (Nat.cast_le.mpr h)
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h, abs_of_nonneg]
    exact sub_nonneg.mpr (Nat.cast_le.mpr h)

/-- The denominator-distance bound in v10 `sec-frequency-tail.tex`, with
the exact `d_m` and the actual set after deleting the largest frequency. -/
theorem separationFloor_le_distance_product {m : ℕ} (hm4 : 4 ∣ m)
    (T : Finset ℕ) (hcard : T.card = m - 1) (s : ℕ) (hs : s ∉ T) :
    (separationFloor m : ℝ) ≤ ∏ u ∈ T, |(s : ℝ) - u| := by
  have hb := distance_product_factorial T s hs
  have hhalf : m - 1 - (m - 1) / 2 = m / 2 := by omega
  rw [hcard, hhalf] at hb
  have hbR : (separationFloor m : ℝ) ≤
      ((∏ u ∈ T, Nat.dist s u : ℕ) : ℝ) := by
    exact_mod_cast hb
  simpa [Nat.cast_prod, nat_dist_cast_real] using hbR

end

end Li2Lean.P0.FrequencyLeaf
