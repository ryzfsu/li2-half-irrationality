/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationS08Combinatorics

/-!
# S08 formal-series coefficients of the scaled P0 entries

Scalar mirror of the formal pencil entries of `IntegerizationFormalMoments`
over `ℚ[a]`, their expansion in `ℚ[[a]]`, and the exact coefficient
identities of paper v13 (equations p0-formal-t and p0-formal-b), entrywise.

The lower rows are divided by `(a-1)^g`, which is a unit in `ℚ[[a]]`.
The diagonal correction `gam` is defined as the actual diagonal coefficient
divided by `C(k+g,g)`; it is never needed in closed form.
-/

namespace Li2Lean.P0.Integerization.S08

open Finset

noncomputable section

/-- Rational formal power series in the base variable `a`. -/
abbrev QS := PowerSeries ℚ

/-- Coercion of rational polynomials in `a` to formal series. -/
abbrev co : Polynomial ℚ →+* QS := Polynomial.coeToPowerSeries.ringHom

theorem co_X : co Polynomial.X = PowerSeries.X := by
  simp [co, Polynomial.coeToPowerSeries.ringHom_apply]

theorem co_C (q : ℚ) : co (Polynomial.C q) = PowerSeries.C q := by
  simp [co, Polynomial.coeToPowerSeries.ringHom_apply]

theorem coeff_co (p : Polynomial ℚ) (k : ℕ) :
    PowerSeries.coeff k (co p) = p.coeff k := by
  simp [co, Polynomial.coeToPowerSeries.ringHom_apply]

def rho : QS := PowerSeries.mk 1

/-- Inverse of `b = a - 1` in `ℚ[[a]]`. -/
def binv : QS := -rho

def bS : QS := PowerSeries.X - 1

theorem bS_mul_binv : bS * binv = 1 := by
  have h := PowerSeries.mk_one_mul_one_sub_eq_one (S := ℚ)
  unfold bS binv rho
  linear_combination h

/-- `L₁ = Σ a^r / r`. -/
def L1 : QS := PowerSeries.mk fun r => ((r : ℚ))⁻¹

/-- `L₂ = Σ a^r / r^2`. -/
def L2 : QS := PowerSeries.mk fun r => ((r : ℚ)⁻¹) ^ 2

/-- The binomial weight `c_k = C(k+g,g)`. -/
def cw (g k : ℕ) : ℚ := ((k + g).choose g : ℚ)

theorem cw_pos (g k : ℕ) : 0 < cw g k := by
  unfold cw
  exact_mod_cast Nat.choose_pos (by omega)

/-- The harmonic shift `h_x = Σ_{s<g} 1/(x+s+1)`. -/
def hS (g x : ℕ) : ℚ := ∑ s ∈ range g, ((x : ℚ) + s + 1)⁻¹

/-! ### Scalar mirror of the formal entries -/

def uP (g i : ℕ) : Polynomial ℚ :=
  Polynomial.C (Nat.choose (i + g) g : ℚ) * Polynomial.X ^ i

def qP (g s : ℕ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C 1) ^ (g - s) *
    (Polynomial.X ^ s - (Polynomial.X - Polynomial.C 1) ^ s)

def P1 (g i : ℕ) : Polynomial ℚ :=
  ∑ r ∈ range i, uP g (i - (r + 1)) * Polynomial.C ((r + 1 : ℚ)⁻¹)

def P2 (g i : ℕ) : Polynomial ℚ :=
  ∑ r ∈ range i, uP g (i - (r + 1)) * Polynomial.C ((r + 1 : ℚ)⁻¹ ^ 2)

def Q1 (g i : ℕ) : Polynomial ℚ :=
  ∑ s ∈ range g,
    Polynomial.C (((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
      (Nat.choose (i + g) (g - (s + 1)) : ℚ)) * qP g (s + 1)

def Q2 (g i : ℕ) : Polynomial ℚ :=
  ∑ s ∈ Icc 2 g,
    Polynomial.C (((-1 : ℚ) ^ s / (s : ℚ)) * (Nat.choose (i + g) (g - s) : ℚ)) *
      (∑ r ∈ range (s - 1), Polynomial.C ((r + 1 : ℚ)⁻¹) * qP g (r + 1))

def tsP (g i : ℕ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C 1) ^ g * P1 g i + Polynomial.X ^ i * Q1 g i

def bsP (g i : ℕ) : Polynomial ℚ :=
  (Polynomial.X - Polynomial.C 1) ^ g * P2 g i - Polynomial.X ^ i * Q2 g i

def cP (g i j : ℕ) : Polynomial ℚ :=
  if i = j then
    -uP g i * Polynomial.C (∑ s ∈ range g, ((i + s + 1 : ℚ)⁻¹))
  else
    (uP g i - uP g j) * Polynomial.C (((j : ℚ) - (i : ℚ))⁻¹)

def aP (g i j : ℕ) : Polynomial ℚ :=
  if i = j then uP g i else 0

def bP (g i j : ℕ) : Polynomial ℚ :=
  if i = j then bsP g i
  else (tsP g i - tsP g j) * Polynomial.C (((j : ℚ) - (i : ℚ))⁻¹)

/-! ### Series expansions -/

theorem co_bS : co (Polynomial.X - Polynomial.C 1) = bS := by
  rw [map_sub, co_X, co_C, map_one, bS]

theorem co_uP (g i : ℕ) :
    co (uP g i) = PowerSeries.C (cw g i) * PowerSeries.X ^ i := by
  simp only [uP, cw, map_mul, map_pow, co_X, co_C]

theorem binv_qP {g s : ℕ} (hs : s ≤ g) :
    binv ^ g * co (qP g s) = (PowerSeries.X * binv) ^ s - 1 := by
  have hq : co (qP g s) = bS ^ (g - s) * (PowerSeries.X ^ s - bS ^ s) := by
    simp only [qP, map_mul, map_pow, map_sub, co_X, co_C, map_one, bS]
  have hg : binv ^ g = binv ^ (g - s) * binv ^ s := by
    rw [← pow_add]
    congr 1
    omega
  rw [hq, hg]
  calc binv ^ (g - s) * binv ^ s * (bS ^ (g - s) * (PowerSeries.X ^ s - bS ^ s))
      = (bS * binv) ^ (g - s) *
          ((PowerSeries.X * binv) ^ s - (bS * binv) ^ s) := by ring
    _ = (PowerSeries.X * binv) ^ s - 1 := by
        rw [bS_mul_binv]
        simp

/-- The series part of the first moment after division by `b^g`. -/
def Wt (g x : ℕ) : QS :=
  ∑ s ∈ range g,
    PowerSeries.C (((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
      (Nat.choose (x + g) (g - (s + 1)) : ℚ)) *
      ((PowerSeries.X * binv) ^ (s + 1) - 1)

/-- The series part of the second moment after division by `b^g`. -/
def Wb (g x : ℕ) : QS :=
  ∑ s ∈ Icc 2 g,
    PowerSeries.C (((-1 : ℚ) ^ s / (s : ℚ)) * (Nat.choose (x + g) (g - s) : ℚ)) *
      (∑ r ∈ range (s - 1), PowerSeries.C ((r + 1 : ℚ)⁻¹) *
        ((PowerSeries.X * binv) ^ (r + 1) - 1))

theorem ts_series (g x : ℕ) :
    binv ^ g * co (tsP g x) = co (P1 g x) + PowerSeries.X ^ x * Wt g x := by
  have hQ : binv ^ g * co (Q1 g x) = Wt g x := by
    simp only [Q1, Wt, map_sum, map_mul, co_C, mul_sum]
    apply sum_congr rfl
    intro s hs
    have hs' : s + 1 ≤ g := mem_range.mp hs
    rw [← binv_qP hs']
    ring
  rw [tsP, map_add, map_mul, map_mul, map_pow, map_pow, co_bS, co_X]
  calc binv ^ g * (bS ^ g * co (P1 g x) + PowerSeries.X ^ x * co (Q1 g x))
      = (bS * binv) ^ g * co (P1 g x) +
          PowerSeries.X ^ x * (binv ^ g * co (Q1 g x)) := by ring
    _ = _ := by rw [bS_mul_binv, hQ, one_pow, one_mul]

theorem bs_series (g x : ℕ) :
    binv ^ g * co (bsP g x) = co (P2 g x) - PowerSeries.X ^ x * Wb g x := by
  have hQ : binv ^ g * co (Q2 g x) = Wb g x := by
    simp only [Q2, Wb, map_sum, map_mul, co_C, mul_sum]
    apply sum_congr rfl
    intro s hs
    have hs' : s ≤ g := (mem_Icc.mp hs).2
    apply sum_congr rfl
    intro r hr
    have hr' : r + 1 ≤ g := by
      have := mem_range.mp hr
      omega
    rw [← binv_qP hr']
    ring
  rw [bsP, map_sub, map_mul, map_mul, map_pow, map_pow, co_bS, co_X]
  calc binv ^ g * (bS ^ g * co (P2 g x) - PowerSeries.X ^ x * co (Q2 g x))
      = (bS * binv) ^ g * co (P2 g x) -
          PowerSeries.X ^ x * (binv ^ g * co (Q2 g x)) := by ring
    _ = _ := by rw [bS_mul_binv, hQ, one_pow, one_mul]

/-! ### Coefficients -/

theorem coeff_uP (g i k : ℕ) :
    (uP g i).coeff k = if k = i then cw g i else 0 := by
  simp [uP, cw, Polynomial.coeff_C_mul_X_pow]

theorem coeff_Psum (g x k : ℕ) (f : ℕ → ℚ) :
    (∑ r ∈ range x, uP g (x - (r + 1)) * Polynomial.C (f r)).coeff k =
      if k < x then cw g k * f (x - 1 - k) else 0 := by
  rw [Polynomial.finset_sum_coeff]
  simp only [Polynomial.coeff_mul_C, coeff_uP]
  split_ifs with hk
  · rw [sum_eq_single (x - 1 - k)]
    · have e : k = x - (x - 1 - k + 1) := by omega
      rw [if_pos e, ← e]
    · intro r hrm hr
      have := mem_range.mp hrm
      have : k ≠ x - (r + 1) := by omega
      rw [if_neg this, zero_mul]
    · intro h
      exact absurd (mem_range.mpr (by omega)) h
  · apply sum_eq_zero
    intro r hr
    have := mem_range.mp hr
    have : k ≠ x - (r + 1) := by omega
    rw [if_neg this, zero_mul]

theorem coeff_P1 (g x k : ℕ) :
    (P1 g x).coeff k = if k < x then cw g k * ((x : ℚ) - k)⁻¹ else 0 := by
  unfold P1
  rw [coeff_Psum g x k (fun r => ((r : ℚ) + 1)⁻¹)]
  split_ifs with hk
  · congr 2
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  · rfl

theorem coeff_P2 (g x k : ℕ) :
    (P2 g x).coeff k = if k < x then cw g k * (((x : ℚ) - k)⁻¹) ^ 2 else 0 := by
  unfold P2
  rw [coeff_Psum g x k (fun r => ((r : ℚ) + 1)⁻¹ ^ 2)]
  split_ifs with hk
  · congr 3
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast
    ring
  · rfl

theorem coeff_Xbinv_pow_succ (s n : ℕ) :
    PowerSeries.coeff (n + 1) ((PowerSeries.X * binv) ^ (s + 1)) =
      (-1 : ℚ) ^ (s + 1) * (n.choose s : ℚ) := by
  have e : (PowerSeries.X * binv : QS) ^ (s + 1) =
      PowerSeries.C ((-1 : ℚ) ^ (s + 1)) * (PowerSeries.X ^ (s + 1) * rho ^ (s + 1)) := by
    unfold binv
    simp only [map_pow, map_neg, map_one]
    ring
  rw [e, PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow_mul', rho,
    PowerSeries.mk_one_pow_eq_mk_choose_add]
  split_ifs with h
  · rw [PowerSeries.coeff_mk]
    congr 2
    have : s + (n + 1 - (s + 1)) = n := by omega
    rw [this]
  · have : n < s := by omega
    simp [Nat.choose_eq_zero_of_lt this]

theorem coeff_Xbinv_pow_zero (s : ℕ) :
    PowerSeries.coeff 0 ((PowerSeries.X * binv) ^ (s + 1)) = 0 := by
  rw [PowerSeries.coeff_zero_eq_constantCoeff_apply]
  simp

theorem coeff_Wt_zero (g x : ℕ) :
    PowerSeries.coeff 0 (Wt g x) =
      -∑ s ∈ range g, (-1 : ℚ) ^ s / (s + 1) * ((x + g).choose (g - (s + 1)) : ℚ) := by
  unfold Wt
  rw [map_sum, ← sum_neg_distrib]
  apply sum_congr rfl
  intro s _
  rw [PowerSeries.coeff_C_mul, map_sub, coeff_Xbinv_pow_zero, PowerSeries.coeff_one]
  simp

theorem coeff_Wt_succ (g x n : ℕ) :
    PowerSeries.coeff (n + 1) (Wt g x) =
      ∑ s ∈ range g, (-1 : ℚ) ^ s / (s + 1) * ((x + g).choose (g - (s + 1)) : ℚ) *
        ((-1 : ℚ) ^ (s + 1) * (n.choose s : ℚ)) := by
  unfold Wt
  rw [map_sum]
  apply sum_congr rfl
  intro s _
  rw [PowerSeries.coeff_C_mul, map_sub, coeff_Xbinv_pow_succ, PowerSeries.coeff_one]
  simp

theorem coeff_Wb_succ (g x n : ℕ) :
    PowerSeries.coeff (n + 1) (Wb g x) =
      ∑ s ∈ Icc 2 g, (-1 : ℚ) ^ s / (s : ℚ) * ((x + g).choose (g - s) : ℚ) *
        ∑ r ∈ range (s - 1), ((r : ℚ) + 1)⁻¹ * ((-1 : ℚ) ^ (r + 1) * (n.choose r : ℚ)) := by
  unfold Wb
  rw [map_sum]
  apply sum_congr rfl
  intro s _
  rw [PowerSeries.coeff_C_mul, map_sum]
  congr 1
  apply sum_congr rfl
  intro r _
  rw [PowerSeries.coeff_C_mul, map_sub, coeff_Xbinv_pow_succ, PowerSeries.coeff_one]
  simp

theorem coeff_L1_uP (g x k : ℕ) :
    PowerSeries.coeff k (L1 * co (uP g x)) =
      if x ≤ k then ((k - x : ℕ) : ℚ)⁻¹ * cw g x else 0 := by
  rw [co_uP, ← mul_assoc, PowerSeries.coeff_mul_X_pow']
  split_ifs
  · rw [PowerSeries.coeff_mul_C, L1, PowerSeries.coeff_mk]
  · rfl

theorem coeff_L2_uP (g x k : ℕ) :
    PowerSeries.coeff k (L2 * co (uP g x)) =
      if x ≤ k then (((k - x : ℕ) : ℚ)⁻¹) ^ 2 * cw g x else 0 := by
  rw [co_uP, ← mul_assoc, PowerSeries.coeff_mul_X_pow']
  split_ifs
  · rw [PowerSeries.coeff_mul_C, L2, PowerSeries.coeff_mk]
  · rfl

/-! ### The first-moment identity (p0-formal-t) -/

def tau (g x k : ℕ) : ℚ := if x = k then -hS g x else ((x : ℚ) - k)⁻¹

theorem coeff_T (g x k : ℕ) :
    PowerSeries.coeff k (binv ^ g * co (tsP g x) - L1 * co (uP g x)) =
      cw g k * tau g x k := by
  rw [ts_series, map_sub, map_add, coeff_co, coeff_P1, PowerSeries.coeff_X_pow_mul',
    coeff_L1_uP]
  rcases lt_trichotomy k x with hk | hk | hk
  · have h1 : ¬ x ≤ k := by omega
    have h2 : x ≠ k := by omega
    simp [hk, h1, tau, h2]
  · subst hk
    simp only [lt_irrefl, if_false, le_refl, if_true, Nat.sub_self, coeff_Wt_zero,
      Nat.cast_zero, inv_zero, zero_mul, tau]
    rw [harmonic_binomial]
    unfold cw hS
    ring
  · obtain ⟨n, rfl⟩ : ∃ n, k = x + (n + 1) := ⟨k - x - 1, by omega⟩
    have h1 : ¬ x + (n + 1) < x := by omega
    have h2 : x ≤ x + (n + 1) := by omega
    have h3 : x ≠ x + (n + 1) := by omega
    have e : x + (n + 1) - x = n + 1 := by omega
    simp only [h1, if_false, h2, if_true, e, coeff_Wt_succ, tau, h3]
    have hterm : ∀ s ∈ range g,
        (-1 : ℚ) ^ s / (s + 1) * ((x + g).choose (g - (s + 1)) : ℚ) *
            ((-1 : ℚ) ^ (s + 1) * (n.choose s : ℚ)) =
          -(((n + 1).choose (s + 1) : ℚ) * ((x + g).choose (g - (s + 1)) : ℚ)) /
            ((n : ℚ) + 1) := by
      intro s _
      have h := choose_div_succ n s
      have hsq : (-1 : ℚ) ^ s * (-1 : ℚ) ^ s = 1 := by
        rw [← mul_pow]
        norm_num
      have hden : ((s : ℚ) + 1) ≠ 0 := by positivity
      have hden' : ((n : ℚ) + 1) ≠ 0 := by positivity
      field_simp
      field_simp at h
      linear_combination
        (-(((x + g).choose (g - (s + 1)) : ℚ)) * (n.choose s : ℚ) * ((n : ℚ) + 1)) * hsq -
          ((x + g).choose (g - (s + 1)) : ℚ) * h
    rw [sum_congr rfl hterm, ← sum_div, sum_neg_distrib]
    have hV := vandermonde_shift x g (n + 1)
    unfold cw
    rw [hV]
    have hden' : ((n : ℚ) + 1) ≠ 0 := by positivity
    have e2 : (x : ℚ) - ((x + (n + 1) : ℕ) : ℚ) = -((n : ℚ) + 1) := by
      push_cast
      ring
    rw [e2]
    push_cast
    field_simp
    ring

/-! ### The second-moment identity (p0-formal-b), off the diagonal coefficient -/

/-- Diagonal lower entry after division by `b^g` and the `L₁/L₂` shear. -/
def Ed (g x : ℕ) : QS :=
  binv ^ g * co (bsP g x) + L1 * co (uP g x) * PowerSeries.C (hS g x) +
    L2 * co (uP g x)

theorem inner_alt (n t : ℕ) :
    ∑ r ∈ range t, ((r : ℚ) + 1)⁻¹ * ((-1 : ℚ) ^ (r + 1) * (n.choose r : ℚ)) =
      ((-1 : ℚ) ^ t * (n.choose t : ℚ) - 1) / ((n : ℚ) + 1) := by
  have halt := alt_partial_sum n t
  rw [sum_range_succ'] at halt
  simp only [pow_zero, Nat.choose_zero_right, Nat.cast_one, mul_one] at halt
  have hterm : ∀ r ∈ range t,
      ((r : ℚ) + 1)⁻¹ * ((-1 : ℚ) ^ (r + 1) * (n.choose r : ℚ)) =
        (-1 : ℚ) ^ (r + 1) * ((n + 1).choose (r + 1) : ℚ) / ((n : ℚ) + 1) := by
    intro r _
    have h := choose_div_succ n r
    rw [show ((r : ℚ) + 1)⁻¹ * ((-1 : ℚ) ^ (r + 1) * (n.choose r : ℚ)) =
        (-1 : ℚ) ^ (r + 1) * ((n.choose r : ℚ) / ((r : ℚ) + 1)) by ring, h]
    ring
  rw [sum_congr rfl hterm, ← sum_div]
  congr 1
  linarith

theorem sum_Icc_two (g' : ℕ) (f : ℕ → ℚ) :
    ∑ s ∈ Icc 2 (g' + 1), f s = ∑ t ∈ range g', f (t + 2) := by
  rw [← Finset.Ico_add_one_right_eq_Icc, Finset.sum_Ico_eq_sum_range]
  have : g' + 1 + 1 - 2 = g' := by omega
  rw [this]
  apply sum_congr rfl
  intro t _
  rw [add_comm]

theorem coeff_B (g x k : ℕ) (hg : 1 ≤ g) (hk : k ≠ x) :
    PowerSeries.coeff k (Ed g x) = cw g k * (((x : ℚ) - k)⁻¹) ^ 2 := by
  unfold Ed
  rw [bs_series, map_add, map_add, map_sub, coeff_co, coeff_P2,
    PowerSeries.coeff_X_pow_mul', PowerSeries.coeff_mul_C, coeff_L1_uP, coeff_L2_uP]
  rcases lt_or_gt_of_ne hk with hk | hk
  · have h1 : ¬ x ≤ k := by omega
    simp [hk, h1]
  · obtain ⟨n, rfl⟩ : ∃ n, k = x + (n + 1) := ⟨k - x - 1, by omega⟩
    obtain ⟨g', rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
    have h1 : ¬ x + (n + 1) < x := by omega
    have h2 : x ≤ x + (n + 1) := by omega
    have e : x + (n + 1) - x = n + 1 := by omega
    simp only [h1, if_false, h2, if_true, e, coeff_Wb_succ]
    rw [sum_Icc_two]
    -- named pieces
    set C1 : ℚ := ((x + (g' + 1)).choose g' : ℚ) with hC1
    set S1 : ℚ := ∑ t ∈ range g', ((n + 1).choose (t + 2) : ℚ) *
      ((x + (g' + 1)).choose (g' + 1 - (t + 2)) : ℚ) with hS1
    set S2 : ℚ := ∑ t ∈ range g', (-1 : ℚ) ^ (t + 1) / ((t : ℚ) + 2) *
      ((x + (g' + 1)).choose (g' + 1 - (t + 2)) : ℚ) with hS2
    have hden' : ((n : ℚ) + 1) ≠ 0 := by positivity
    -- Vandermonde with the first two terms separated
    have hV : cw (g' + 1) (x + (n + 1)) = cw (g' + 1) x + ((n : ℚ) + 1) * C1 + S1 := by
      have h := vandermonde_shift x (g' + 1) (n + 1)
      rw [sum_range_succ'] at h
      have e3 : (∑ k ∈ range g', ((n + 1).choose (k + 1 + 1) : ℚ) *
          ((x + (g' + 1)).choose (g' + 1 - (k + 1 + 1)) : ℚ)) = S1 := by
        rw [hS1]
      rw [e3] at h
      simp only [zero_add, Nat.choose_one_right, Nat.add_sub_cancel] at h
      unfold cw
      rw [h, hC1]
      push_cast
      ring
    -- harmonic identity with the first term separated
    have hH : C1 + S2 = cw (g' + 1) x * hS (g' + 1) x := by
      have h := harmonic_binomial x (g' + 1)
      rw [sum_range_succ'] at h
      have e3 : (∑ k ∈ range g', (-1 : ℚ) ^ (k + 1) / (((k + 1 : ℕ) : ℚ) + 1) *
          ((x + (g' + 1)).choose (g' + 1 - (k + 1 + 1)) : ℚ)) = S2 := by
        rw [hS2]
        apply sum_congr rfl
        intro t _
        push_cast
        ring
      rw [e3] at h
      simp only [pow_zero, Nat.cast_zero, zero_add, Nat.add_sub_cancel, div_one,
        one_mul] at h
      unfold cw hS
      rw [hC1]
      linear_combination h
    -- the double sum
    have hsum : ∑ t ∈ range g', (-1 : ℚ) ^ (t + 2) / (((t + 2 : ℕ) : ℚ)) *
          ((x + (g' + 1)).choose (g' + 1 - (t + 2)) : ℚ) *
          ∑ r ∈ range (t + 2 - 1), ((r : ℚ) + 1)⁻¹ *
            ((-1 : ℚ) ^ (r + 1) * (n.choose r : ℚ)) =
        -S1 / ((n : ℚ) + 1) ^ 2 + S2 / ((n : ℚ) + 1) := by
      rw [hS1, hS2, neg_div, sum_div, sum_div, ← sum_neg_distrib, ← sum_add_distrib]
      apply sum_congr rfl
      intro t _
      have e4 : t + 2 - 1 = t + 1 := by omega
      rw [e4, inner_alt]
      have h : (n.choose (t + 1) : ℚ) / (((t : ℚ) + 1) + 1) =
          ((n + 1).choose (t + 2) : ℚ) / ((n : ℚ) + 1) := by
        have := choose_div_succ n (t + 1)
        push_cast at this
        exact this
      have hcast : (((t + 2 : ℕ)) : ℚ) = (t : ℚ) + 2 := by push_cast; ring
      rw [hcast]
      rw [show (-1 : ℚ) ^ (t + 2) = (-1) ^ t by ring,
        show (-1 : ℚ) ^ (t + 1) = -(-1) ^ t by ring]
      have hsq : (-1 : ℚ) ^ t * (-1 : ℚ) ^ t = 1 := by
        rw [← mul_pow]
        norm_num
      generalize ((x + (g' + 1)).choose (g' + 1 - (t + 2)) : ℚ) = B
      generalize ((n + 1).choose (t + 2) : ℚ) = Cn1 at h ⊢
      generalize (n.choose (t + 1) : ℚ) = Cn at h ⊢
      generalize (-1 : ℚ) ^ t = σ at hsq ⊢
      have ht2 : ((t : ℚ) + 2) ≠ 0 := by positivity
      have hCn : Cn = ((t : ℚ) + 2) * Cn1 / ((n : ℚ) + 1) := by
        have ht2' : ((t : ℚ) + 1 + 1) ≠ 0 := by positivity
        field_simp at h ⊢
        linear_combination h
      have hre : σ / ((t : ℚ) + 2) * B * ((-σ * Cn - 1) / ((n : ℚ) + 1)) =
          -(σ * σ) * B * Cn / ((t : ℚ) + 2) / ((n : ℚ) + 1) -
            σ * B / ((t : ℚ) + 2) / ((n : ℚ) + 1) := by
        ring
      rw [hre, hsq, hCn]
      field_simp
      ring
    rw [hsum]
    have e2 : (x : ℚ) - ((x + (n + 1) : ℕ) : ℚ) = -((n : ℚ) + 1) := by
      push_cast
      ring
    have hcw := (cw_pos (g' + 1) x).ne'
    have hh : hS (g' + 1) x = (C1 + S2) / cw (g' + 1) x := by
      rw [hH]
      field_simp
    rw [e2, hV, hh]
    push_cast
    field_simp
    ring

/-! ### Rank-one feature scalars and the entry coefficient formulas -/

def eR (x k : ℕ) : ℚ := if x = k then 1 else 0

def vR (x k : ℕ) : ℚ := if x = k then 0 else ((x : ℚ) - k)⁻¹

/-- The diagonal feature constant: actual coefficient divided by `c_k`. -/
def gam (g k : ℕ) : ℚ := PowerSeries.coeff k (Ed g k) / cw g k

def topF (g i j k : ℕ) : ℚ :=
  eR i k * vR j k + (vR i k - hS g k * eR i k) * eR j k

def lowF (g i j k : ℕ) : ℚ :=
  (vR i k - hS g k * eR i k) * vR j k + (-eR i k) * (vR j k) ^ 2 +
    (-(vR i k) ^ 2 - hS g k * vR i k + gam g k * eR i k) * eR j k

/-- Shear-normalized lower entry, divided by `b^g`. -/
def Eser (g i j : ℕ) : QS :=
  binv ^ g * co (bP g i j) - L1 * co (cP g i j) + L2 * co (aP g i j)

theorem natCast_sub_ne_zero {x k : ℕ} (h : x ≠ k) : (x : ℚ) - k ≠ 0 :=
  sub_ne_zero.mpr (by exact_mod_cast h)

theorem coeff_top (g i j k : ℕ) :
    PowerSeries.coeff k (co (cP g i j)) = cw g k * topF g i j k := by
  rw [coeff_co]
  unfold cP topF
  by_cases hij : i = j
  · subst hij
    simp only [if_true, neg_mul, Polynomial.coeff_neg, Polynomial.coeff_mul_C, coeff_uP]
    by_cases hk : k = i
    · subst hk
      simp [eR, vR, hS]
    · have hk' : i ≠ k := Ne.symm hk
      simp only [hk, hk', if_false, eR, vR]
      ring
  · simp only [hij, if_false, Polynomial.coeff_mul_C, Polynomial.coeff_sub, coeff_uP]
    by_cases hki : k = i
    · subst hki
      have hjk : j ≠ k := Ne.symm hij
      simp only [eR, vR, hij, hjk, eq_self_iff_true, if_true, if_false]
      ring
    · by_cases hkj : k = j
      · subst hkj
        have hik : i ≠ k := hij
        simp only [hki, if_false, if_true, eR, vR, hik, zero_sub]
        have hne := natCast_sub_ne_zero hik
        have hne' : (k : ℚ) - i ≠ 0 := by
          intro h; apply hne; linarith
        field_simp
        ring
      · have hik : i ≠ k := Ne.symm hki
        have hjk : j ≠ k := Ne.symm hkj
        simp [hki, hkj, hik, hjk, eR, vR]

theorem coeff_aP (g i j k : ℕ) :
    PowerSeries.coeff k (co (aP g i j)) = cw g k * (eR i k * eR j k) := by
  rw [coeff_co]
  unfold aP eR
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, coeff_uP]
    by_cases hk : k = i
    · subst hk; simp
    · have : i ≠ k := Ne.symm hk
      simp [hk, this]
  · rw [if_neg hij, Polynomial.coeff_zero]
    by_cases hik : i = k
    · subst hik
      have : j ≠ i := Ne.symm hij
      simp [this]
    · simp [hik]

theorem tau_divided_difference (g i j k : ℕ) (hij : i ≠ j) :
    (tau g i k - tau g j k) * ((j : ℚ) - (i : ℚ))⁻¹ = lowF g i j k := by
  have hji : (j : ℚ) - i ≠ 0 := by
    have := natCast_sub_ne_zero hij
    intro h; apply this; linarith
  unfold tau lowF eR vR
  by_cases hik : i = k
  · subst hik
    have hjk : j ≠ i := Ne.symm hij
    simp only [if_true, hjk, if_false]
    field_simp
    ring
  · by_cases hjk : j = k
    · subst hjk
      simp only [hik, if_false, if_true]
      have hne := natCast_sub_ne_zero hik
      field_simp
      ring
    · simp only [hik, hjk, if_false]
      have h1 := natCast_sub_ne_zero hik
      have h2 := natCast_sub_ne_zero hjk
      field_simp
      ring

theorem coeff_low (g i j k : ℕ) (hg : 1 ≤ g) :
    PowerSeries.coeff k (Eser g i j) = cw g k * lowF g i j k := by
  by_cases hij : i = j
  · subst hij
    have hE : Eser g i i = Ed g i := by
      unfold Eser Ed bP cP aP
      simp only [if_true, map_mul, map_neg, co_C]
      unfold hS
      ring
    rw [hE]
    by_cases hk : k = i
    · subst hk
      unfold lowF gam eR vR
      simp only [if_true]
      have := (cw_pos g k).ne'
      field_simp
      ring
    · rw [coeff_B g i k hg hk]
      have hik : i ≠ k := Ne.symm hk
      unfold lowF eR vR
      simp only [hik, if_false]
      ring
  · have hE : Eser g i j =
        ((binv ^ g * co (tsP g i) - L1 * co (uP g i)) -
          (binv ^ g * co (tsP g j) - L1 * co (uP g j))) *
          PowerSeries.C (((j : ℚ) - (i : ℚ))⁻¹) := by
      unfold Eser bP cP aP
      simp only [hij, if_false, map_mul, map_sub, map_zero, co_C, mul_zero, add_zero]
      ring
    rw [hE, PowerSeries.coeff_mul_C, map_sub, coeff_T, coeff_T,
      ← tau_divided_difference g i j k hij]
    ring

/-! ### Truncation -/

theorem X_pow_dvd_sub_trunc (N : ℕ) (x : QS) (α : ℕ → ℚ)
    (h : ∀ k < N, PowerSeries.coeff k x = α k) :
    PowerSeries.X ^ N ∣ x - ∑ k ∈ range N, PowerSeries.C (α k) * PowerSeries.X ^ k := by
  rw [PowerSeries.X_pow_dvd_iff]
  intro m hm
  rw [map_sub, map_sum]
  simp only [PowerSeries.coeff_C_mul, PowerSeries.coeff_X_pow, mul_ite, mul_one, mul_zero]
  rw [sum_ite_eq, if_pos (mem_range.mpr hm), h m hm, sub_self]

end

end Li2Lean.P0.Integerization.S08

#print axioms Li2Lean.P0.Integerization.S08.coeff_T
#print axioms Li2Lean.P0.Integerization.S08.coeff_B
#print axioms Li2Lean.P0.Integerization.S08.coeff_top
#print axioms Li2Lean.P0.Integerization.S08.coeff_low
#print axioms Li2Lean.P0.Integerization.S08.X_pow_dvd_sub_trunc
