/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.Bound

/-!
# Second-order lower Taylor bound for the contour closed form

On the open upper half-parameter interval `(0, π)` the closed form is twice
differentiable with `|W2| ≤ 2200`, hence
`Wform θ ≥ Wform θ0 + W1 θ0 (θ - θ0) - 1100 (θ - θ0)^2`.
-/

namespace Li2Lean.P0.CA.Contour

noncomputable section

theorem sin_ne_zero_of_mem {x : ℝ} (hx : x ∈ Set.Ioo 0 Real.pi) : Real.sin x ≠ 0 :=
  (Real.sin_pos_of_pos_of_lt_pi hx.1 hx.2).ne'

theorem W1_lipschitz {x y : ℝ} (hx : x ∈ Set.Ioo 0 Real.pi) (hy : y ∈ Set.Ioo 0 Real.pi) :
    |W1 x - W1 y| ≤ 2200 * |x - y| := by
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le (f := W1) (f' := W2) (C := 2200)
    (s := Set.Ioo 0 Real.pi)
    (fun z hz => (hasDerivAt_W1 (sin_ne_zero_of_mem hz)).hasDerivWithinAt)
    (fun z _ => by simpa only [Real.norm_eq_abs] using W2_abs_le)
    (convex_Ioo 0 Real.pi) hy hx
  simpa only [Real.norm_eq_abs] using h

theorem taylor_lower {θ θ0 : ℝ} (h : θ ∈ Set.Ioo 0 Real.pi) (h0 : θ0 ∈ Set.Ioo 0 Real.pi) :
    Wform θ0 + W1 θ0 * (θ - θ0) - 1100 * (θ - θ0) ^ 2 ≤ Wform θ := by
  set g : ℝ → ℝ := fun x => Wform x - Wform θ0 - W1 θ0 * (x - θ0) + 1100 * (x - θ0) ^ 2
    with hg
  set g' : ℝ → ℝ := fun x => W1 x - W1 θ0 + 2200 * (x - θ0) with hg'
  have hderiv : ∀ x ∈ Set.Ioo 0 Real.pi, HasDerivAt g (g' x) x := by
    intro x hx
    have h1 := hasDerivAt_Wform (sin_ne_zero_of_mem hx)
    have h2 := ((hasDerivAt_id x).sub_const θ0).const_mul (W1 θ0)
    have h3 := (((hasDerivAt_id x).sub_const θ0).pow 2).const_mul (1100 : ℝ)
    have h := ((h1.sub_const (Wform θ0)).sub h2).add h3
    refine h.congr_deriv ?_
    simp only [hg', id]
    push_cast
    ring
  have hsub : ∀ {a b : ℝ}, a ∈ Set.Ioo 0 Real.pi → b ∈ Set.Ioo 0 Real.pi →
      Set.Icc a b ⊆ Set.Ioo 0 Real.pi := by
    intro a b ha hb x hx
    exact ⟨lt_of_lt_of_le ha.1 hx.1, lt_of_le_of_lt hx.2 hb.2⟩
  have hg0 : g θ0 = 0 := by simp [hg]
  suffices hgθ : 0 ≤ g θ by simp only [hg] at hgθ; linarith
  rcases le_total θ0 θ with hle | hle
  · have hD := hsub h0 h
    have hmono : MonotoneOn g (Set.Icc θ0 θ) := by
      apply monotoneOn_of_hasDerivWithinAt_nonneg (f' := g') (convex_Icc θ0 θ)
      · intro x hx
        exact (hderiv x (hD hx)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hderiv x (hD (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hL := W1_lipschitz (hD (Set.Ioo_subset_Icc_self hx)) h0
        rw [abs_of_nonneg (by linarith [hx.1] : (0 : ℝ) ≤ x - θ0)] at hL
        simp only [hg']
        linarith [neg_abs_le (W1 x - W1 θ0)]
    have := hmono ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    linarith
  · have hD := hsub h h0
    have hanti : AntitoneOn g (Set.Icc θ θ0) := by
      apply antitoneOn_of_hasDerivWithinAt_nonpos (f' := g') (convex_Icc θ θ0)
      · intro x hx
        exact (hderiv x (hD hx)).continuousAt.continuousWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        exact (hderiv x (hD (Set.Ioo_subset_Icc_self hx))).hasDerivWithinAt
      · intro x hx
        rw [interior_Icc] at hx
        have hL := W1_lipschitz (hD (Set.Ioo_subset_Icc_self hx)) h0
        rw [abs_of_nonpos (by linarith [hx.2] : x - θ0 ≤ 0)] at hL
        simp only [hg']
        linarith [le_abs_self (W1 x - W1 θ0)]
    have := hanti ⟨le_rfl, hle⟩ ⟨hle, le_rfl⟩ hle
    linarith

end

end Li2Lean.P0.CA.Contour
