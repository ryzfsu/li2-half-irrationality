/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Residue counting for the moving-prime assignment bounds

`p0ResCnt p N v` counts `i < N` with `i % p = v`.  It has the closed form
`N / p + [v < N % p]`, and a sum over `i < N` of a function of the base-`p`
digits `(i % p, i / p)` regroups by residue.  These are the exact counting
identities behind the copy counts `c_I(v)`, `c_J(v)` of v13.
-/

namespace Li2Lean.P0.Integerization

open Finset

/-- Number of `i < N` in the residue class `v` modulo `p`. -/
def p0ResCnt (p N v : ℕ) : ℕ := ((range N).filter (fun i => i % p = v)).card

theorem p0ResCnt_eq {p N v : ℕ} (hp : 0 < p) (hv : v < p) :
    p0ResCnt p N v = N / p + if v < N % p then 1 else 0 := by
  have h := Nat.count_modEq_card (b := N) hp v
  rw [Nat.count_eq_card_filter_range, Nat.mod_eq_of_lt hv] at h
  rw [← h]
  unfold p0ResCnt
  congr 1
  apply Finset.filter_congr
  intro i _
  simp [Nat.ModEq, Nat.mod_eq_of_lt hv]

theorem p0ResCnt_succ (p N v : ℕ) :
    p0ResCnt p (N + 1) v = p0ResCnt p N v + if N % p = v then 1 else 0 := by
  unfold p0ResCnt
  rw [Finset.range_add_one, Finset.filter_insert]
  split
  · rw [Finset.card_insert_of_notMem]
    simp
  · simp

theorem p0ResCnt_self {p N : ℕ} (hp : 0 < p) :
    p0ResCnt p N (N % p) = N / p := by
  rw [p0ResCnt_eq hp (Nat.mod_lt N hp)]
  simp

theorem p0ResCnt_mono (p : ℕ) {N N' : ℕ} (h : N ≤ N') (v : ℕ) :
    p0ResCnt p N v ≤ p0ResCnt p N' v := by
  unfold p0ResCnt
  apply Finset.card_le_card
  intro i hi
  simp only [Finset.mem_filter, Finset.mem_range] at hi ⊢
  exact ⟨lt_of_lt_of_le hi.1 h, hi.2⟩

/-- Regroup a sum over `i < N` by residue and digit. -/
theorem p0_sum_range_digits {p : ℕ} (hp : 0 < p) (F : ℕ → ℕ → ℤ) (N : ℕ) :
    ∑ i ∈ range N, F (i % p) (i / p) =
      ∑ v ∈ range p, ∑ d ∈ range (p0ResCnt p N v), F v d := by
  induction N with
  | zero => simp [p0ResCnt]
  | succ N ih =>
    rw [Finset.sum_range_succ, ih]
    have hstep : ∀ v ∈ range p,
        ∑ d ∈ range (p0ResCnt p (N + 1) v), F v d =
          ∑ d ∈ range (p0ResCnt p N v), F v d +
            if v = N % p then F v (N / p) else 0 := by
      intro v _
      rw [p0ResCnt_succ]
      by_cases hv : v = N % p
      · subst hv
        simp only [↓reduceIte, Finset.sum_range_succ, p0ResCnt_self hp]
      · have hv' : ¬ N % p = v := fun h => hv h.symm
        simp [hv, hv']
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib]
    congr 1
    rw [Finset.sum_ite_eq' (range p) (N % p) (fun v => F v (N / p))]
    simp [Nat.mod_lt N hp]

/-- Regroup a sum over a window `[a, a + n)` by residue and digit. -/
theorem p0_sum_window_digits {p : ℕ} (hp : 0 < p) (F : ℕ → ℕ → ℤ) (a n : ℕ) :
    ∑ x ∈ range n, F ((a + x) % p) ((a + x) / p) =
      ∑ v ∈ range p, ∑ d ∈ Ico (p0ResCnt p a v) (p0ResCnt p (a + n) v), F v d := by
  have h1 := p0_sum_range_digits hp F (a + n)
  have h2 := p0_sum_range_digits hp F a
  rw [Finset.sum_range_add] at h1
  have hsub : ∀ v ∈ range p,
      ∑ d ∈ Ico (p0ResCnt p a v) (p0ResCnt p (a + n) v), F v d =
        ∑ d ∈ range (p0ResCnt p (a + n) v), F v d -
          ∑ d ∈ range (p0ResCnt p a v), F v d := by
    intro v _
    exact Finset.sum_Ico_eq_sub _ (p0ResCnt_mono p (Nat.le_add_right a n) v)
  rw [Finset.sum_congr rfl hsub, Finset.sum_sub_distrib, ← h1, ← h2]
  ring

/-- Count form of the window regrouping. -/
theorem p0_card_window_res {p : ℕ} (hp : 0 < p) (a n v : ℕ) (hv : v < p) :
    (((range n).filter (fun x => (a + x) % p = v)).card : ℤ) =
      (p0ResCnt p (a + n) v : ℤ) - p0ResCnt p a v := by
  have h := p0_sum_window_digits hp (fun w _ => if w = v then (1 : ℤ) else 0) a n

  rw [Finset.card_filter]
  push_cast
  rw [h, Finset.sum_eq_single v]
  · simp only [↓reduceIte, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul, mul_one]
    rw [Nat.cast_sub (p0ResCnt_mono p (Nat.le_add_right a n) v)]
  · intro w _ hw
    simp [hw]
  · intro hvp
    exact absurd (Finset.mem_range.mpr hv) hvp

end Li2Lean.P0.Integerization
