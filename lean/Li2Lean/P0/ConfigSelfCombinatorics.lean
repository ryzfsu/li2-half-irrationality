/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSelfStirling
import Mathlib.Data.Nat.Dist

open Finset

namespace Li2Lean.P0.Config.SelfCells

noncomputable section

/-- A nonnegative sequence with uniformly bounded initial sums has the
same bound on every finite selection of indices, without a range premise. -/
lemma sum_le_of_range_bound (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hB : ∀ N, ∑ n ∈ range N, f n ≤ B)
    (D : Finset ℕ) : ∑ n ∈ D, f n ≤ B := by
  have hsub : D ⊆ range (D.sup id + 1) := by
    intro n hn
    simp only [mem_range]
    have h := le_sup (f := id) hn
    dsimp only [id_eq] at h
    omega
  exact (sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => hf n)).trans
    (hB (D.sup id + 1))

/-- The lower-side distance map is injective, so each positive lattice
distance occurs at most once on that side. -/
lemma lower_distance_sum_le (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hB : ∀ N, ∑ n ∈ range N, f n ≤ B)
    (D : Finset ℕ) (i : ℕ) :
    ∑ j ∈ D.filter (fun j => j < i), f (i - j - 1) ≤ B := by
  let L := D.filter (fun j => j < i)
  have hinj : Set.InjOn (fun j => i - j - 1) (↑L : Set ℕ) := by
    intro j hj k hk h
    have hj' := (mem_filter.mp hj).2
    have hk' := (mem_filter.mp hk).2
    dsimp only at h
    omega
  calc
    _ = ∑ d ∈ L.image (fun j => i - j - 1), f d := (sum_image hinj).symm
    _ ≤ B := sum_le_of_range_bound f B hf hB _

/-- The upper-side distance map is injective, with no maximum-frequency
or diameter restriction on the selected lattice sites. -/
lemma upper_distance_sum_le (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hB : ∀ N, ∑ n ∈ range N, f n ≤ B)
    (D : Finset ℕ) (i : ℕ) :
    ∑ j ∈ D.filter (fun j => i < j), f (j - i - 1) ≤ B := by
  let H := D.filter (fun j => i < j)
  have hinj : Set.InjOn (fun j => j - i - 1) (↑H : Set ℕ) := by
    intro j hj k hk h
    have hj' := (mem_filter.mp hj).2
    have hk' := (mem_filter.mp hk).2
    dsimp only at h
    omega
  calc
    _ = ∑ d ∈ H.image (fun j => j - i - 1), f d := (sum_image hinj).symm
    _ ≤ B := sum_le_of_range_bound f B hf hB _

/-- At most two other lattice sites have any fixed positive distance. -/
theorem distance_row_sum_le (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hB : ∀ N, ∑ n ∈ range N, f n ≤ B)
    (D : Finset ℕ) (i : ℕ) :
    (∑ j ∈ D, if i = j then 0 else f (Nat.dist i j - 1)) ≤ 2 * B := by
  have hsplit :
      (∑ j ∈ D, if i = j then 0 else f (Nat.dist i j - 1)) =
        (∑ j ∈ D.filter (fun j => j < i), f (i - j - 1)) +
          (∑ j ∈ D.filter (fun j => i < j), f (j - i - 1)) := by
    rw [sum_filter, sum_filter, ← sum_add_distrib]
    apply sum_congr rfl
    intro j hj
    rcases lt_trichotomy j i with h | h | h
    · simp only [ne_of_gt h, ite_false, h, ite_true, not_lt.mpr h.le,
        Nat.dist_eq_sub_of_le_right h.le, add_zero]
    · subst j
      simp
    · simp only [ne_of_lt h, ite_false, h, ite_true, not_lt.mpr h.le,
        Nat.dist_eq_sub_of_le h.le, zero_add]
  rw [hsplit]
  have hL := lower_distance_sum_le f B hf hB D i
  have hH := upper_distance_sum_le f B hf hB D i
  linarith

/-- The finite all-lattice two-sided error bound required by v10
`eq:config-self`, independently of the number or range of lattice sites. -/
theorem distance_double_sum_le (f : ℕ → ℝ) (B : ℝ)
    (hf : ∀ n, 0 ≤ f n) (hB : ∀ N, ∑ n ∈ range N, f n ≤ B)
    (D : Finset ℕ) :
    (∑ i ∈ D, ∑ j ∈ D, if i = j then 0 else f (Nat.dist i j - 1)) ≤
      (D.card : ℝ) * (2 * B) := by
  calc
    _ ≤ ∑ _i ∈ D, (2 * B) := by
      apply sum_le_sum
      intro i hi
      exact distance_row_sum_le f B hf hB D i
    _ = _ := by simp

end

end Li2Lean.P0.Config.SelfCells
