/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# S08 combinatorial identities

Finite binomial identities used to identify the formal-series coefficients
of the scaled P0 moments (paper v13, equations p0-formal-t and p0-formal-b).
All statements are exact identities over `ℚ`.
-/

namespace Li2Lean.P0.Integerization.S08

open Finset

/-- Alternating partial sum of a binomial row. -/
theorem alt_partial_sum (n s : ℕ) :
    (∑ q ∈ range (s + 1), (-1 : ℚ) ^ q * ((n + 1).choose q : ℚ)) =
      (-1 : ℚ) ^ s * (n.choose s : ℚ) := by
  induction s with
  | zero => simp
  | succ s ih =>
    rw [sum_range_succ, ih, Nat.choose_succ_succ' n s]
    push_cast
    ring

/-- `C(n,s)/(s+1) = C(n+1,s+1)/(n+1)`. -/
theorem choose_div_succ (n s : ℕ) :
    (n.choose s : ℚ) / (s + 1) = ((n + 1).choose (s + 1) : ℚ) / (n + 1) := by
  have h := Nat.add_one_mul_choose_eq n s
  have hq : ((n : ℚ) + 1) * (n.choose s : ℚ) =
      ((n + 1).choose (s + 1) : ℚ) * ((s : ℚ) + 1) := by
    exact_mod_cast h
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination hq

/-- The two-parameter harmonic-binomial sum. -/
def phi (N G : ℕ) : ℚ :=
  ∑ s ∈ range G, (-1 : ℚ) ^ s / (s + 1) * (N.choose (G - (s + 1)) : ℚ)

/-- The matching harmonic block `1/(N-G+1) + ... + 1/N`. -/
def hs (N G : ℕ) : ℚ :=
  ∑ s ∈ range G, 1 / ((N : ℚ) - G + s + 1)

theorem phi_succ_succ (N G : ℕ) :
    phi (N + 1) (G + 1) = phi N (G + 1) + phi N G := by
  unfold phi
  rw [sum_range_succ, sum_range_succ]
  have hlast : (N + 1).choose (G + 1 - (G + 1)) = N.choose (G + 1 - (G + 1)) := by
    simp
  rw [hlast]
  have hbody : ∀ s ∈ range G,
      (-1 : ℚ) ^ s / (s + 1) * ((N + 1).choose (G + 1 - (s + 1)) : ℚ) =
        (-1 : ℚ) ^ s / (s + 1) * (N.choose (G + 1 - (s + 1)) : ℚ) +
          (-1 : ℚ) ^ s / (s + 1) * (N.choose (G - (s + 1)) : ℚ) := by
    intro s hs
    have hs' : s < G := mem_range.mp hs
    have e : G + 1 - (s + 1) = (G - (s + 1)) + 1 := by omega
    rw [e, Nat.choose_succ_succ']
    push_cast
    ring
  rw [sum_congr rfl hbody, sum_add_distrib]
  ring

theorem phi_diag (N : ℕ) : phi N (N + 1) = 1 / (N + 1) := by
  have halt := alt_partial_sum N (N + 1)
  have hz : (N.choose (N + 1) : ℚ) = 0 := by
    rw [Nat.choose_eq_zero_of_lt (Nat.lt_succ_self N)]
    simp
  rw [hz, mul_zero, sum_range_succ'] at halt
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at halt
  have hsum : ∑ s ∈ range (N + 1),
      (-1 : ℚ) ^ s * ((N + 1).choose (s + 1) : ℚ) = 1 := by
    have hneg : ∑ s ∈ range (N + 1),
        (-1 : ℚ) ^ (s + 1) * ((N + 1).choose (s + 1) : ℚ) =
          -∑ s ∈ range (N + 1), (-1 : ℚ) ^ s * ((N + 1).choose (s + 1) : ℚ) := by
      rw [← sum_neg_distrib]
      apply sum_congr rfl
      intro s _
      ring
    linarith
  unfold phi
  have hterm : ∀ s ∈ range (N + 1),
      (-1 : ℚ) ^ s / (s + 1) * (N.choose (N + 1 - (s + 1)) : ℚ) =
        (-1 : ℚ) ^ s * ((N + 1).choose (s + 1) : ℚ) / (N + 1) := by
    intro s hs
    have hs' : s ≤ N := Nat.lt_succ_iff.mp (mem_range.mp hs)
    have e : N + 1 - (s + 1) = N - s := by omega
    rw [e, Nat.choose_symm hs']
    rw [show (-1 : ℚ) ^ s / (s + 1) * (N.choose s : ℚ) =
        (-1 : ℚ) ^ s * ((N.choose s : ℚ) / (s + 1)) by ring, choose_div_succ]
    ring
  rw [sum_congr rfl hterm, ← sum_div, hsum]

theorem phi_eq (N : ℕ) : ∀ G, G ≤ N → phi N G = (N.choose G : ℚ) * hs N G := by
  induction N with
  | zero =>
    intro G hG
    have : G = 0 := by omega
    subst this
    simp [phi, hs]
  | succ N ih =>
    intro G hG
    rcases G with _ | G
    · simp [phi, hs]
    rw [phi_succ_succ]
    rcases Nat.lt_or_ge G N with hGN | hGN
    · rw [ih (G + 1) hGN, ih G hGN.le]
      set A : ℚ := ∑ s ∈ range G, 1 / ((N : ℚ) - G + s + 1) with hA
      have h1 : hs (N + 1) (G + 1) = A + 1 / ((N : ℚ) + 1) := by
        unfold hs
        rw [sum_range_succ, hA]
        congr 1
        · apply sum_congr rfl
          intro s _
          push_cast
          ring_nf
        · push_cast
          ring_nf
      have h2 : hs N (G + 1) = A + 1 / ((N : ℚ) - G) := by
        unfold hs
        rw [sum_range_succ', hA]
        congr 1
        · apply sum_congr rfl
          intro s _
          push_cast
          ring_nf
        · push_cast
          ring_nf
      have h3 : hs N G = A := by
        unfold hs
        rfl
      rw [h1, h2, h3, Nat.choose_succ_succ' N G]
      have r1 := Nat.choose_succ_right_eq N G
      have hNG : ((N - G : ℕ) : ℚ) = (N : ℚ) - G := by
        rw [Nat.cast_sub hGN.le]
      have r1q : (N.choose (G + 1) : ℚ) * ((G : ℚ) + 1) =
          (N.choose G : ℚ) * ((N : ℚ) - G) := by
        rw [← hNG]
        exact_mod_cast r1
      have hpos : (0 : ℚ) < (N : ℚ) - G := by
        have : (G : ℚ) < N := by exact_mod_cast hGN
        linarith
      have hkey : (N.choose (G + 1) : ℚ) / ((N : ℚ) - G) =
          ((N.choose G : ℚ) + (N.choose (G + 1) : ℚ)) / ((N : ℚ) + 1) := by
        rw [div_eq_div_iff hpos.ne' (by positivity)]
        linear_combination r1q
      push_cast
      linear_combination hkey
    · have hGN' : G = N := by omega
      subst hGN'
      rw [phi_diag, ih G le_rfl]
      simp only [Nat.choose_self, Nat.cast_one, one_mul]
      unfold hs
      rw [sum_range_succ]
      have hb : ∀ s ∈ range G, (1 : ℚ) / (((G + 1 : ℕ) : ℚ) - ((G + 1 : ℕ) : ℚ) + s + 1) =
          1 / ((G : ℚ) - G + s + 1) := by
        intro s _
        push_cast
        ring_nf
      rw [sum_congr rfl hb]
      push_cast
      ring_nf

/-- Harmonic-binomial identity: the `a = 0` coefficient of the first moment. -/
theorem harmonic_binomial (x g : ℕ) :
    (∑ s ∈ range g, (-1 : ℚ) ^ s / (s + 1) * ((x + g).choose (g - (s + 1)) : ℚ)) =
      ((x + g).choose g : ℚ) * ∑ s ∈ range g, ((x : ℚ) + s + 1)⁻¹ := by
  have h := phi_eq (x + g) g (by omega)
  unfold phi hs at h
  rw [h]
  congr 1
  apply sum_congr rfl
  intro s _
  push_cast
  rw [one_div]
  ring_nf

/-- Vandermonde convolution with the zero term separated. -/
theorem vandermonde_shift (x g n : ℕ) :
    ((x + n + g).choose g : ℚ) = ((x + g).choose g : ℚ) +
      ∑ s ∈ range g, (n.choose (s + 1) : ℚ) * ((x + g).choose (g - (s + 1)) : ℚ) := by
  have h := Nat.add_choose_eq n (x + g) g
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
    (fun a b => n.choose a * (x + g).choose b) g, sum_range_succ'] at h
  have e : x + n + g = n + (x + g) := by ring
  rw [e, h]
  push_cast
  simp only [Nat.choose_zero_right, Nat.sub_zero, Nat.cast_one, one_mul]
  ring

end Li2Lean.P0.Integerization.S08

#print axioms Li2Lean.P0.Integerization.S08.alt_partial_sum
#print axioms Li2Lean.P0.Integerization.S08.harmonic_binomial
#print axioms Li2Lean.P0.Integerization.S08.vandermonde_shift
