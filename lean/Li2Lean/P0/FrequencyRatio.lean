/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyDistance

open Finset

namespace Li2Lean.P0.FrequencyLeaf

noncomputable section

lemma I_m_card {m : ℕ} (hm : 0 < m) (hm4 : 4 ∣ m) :
    (I_m m).card = m := by
  simp only [I_m, Nat.card_Icc]
  omega

lemma I_m_subset_J_m {m : ℕ} (hm : 0 < m) (hm4 : 4 ∣ m) : I_m m ⊆ J_m m := by
  intro i hi
  simp only [I_m, mem_Icc] at hi
  simp only [J_m, mem_range]
  omega

lemma column_product_eq_sdiff (m : ℕ) (S : Finset ℕ) (t : ℕ) :
    (∏ j ∈ J_m m, if j ∈ S then (1 : ℝ) else ((t + j : ℕ) : ℝ)) =
      ∏ j ∈ J_m m \ S, ((t + j : ℕ) : ℝ) := by
  have hfilter : (J_m m).filter (fun j => j ∉ S) = J_m m \ S := by
    ext j
    simp
  rw [← hfilter, prod_filter]
  apply prod_congr rfl
  intro j hj
  split_ifs <;> rfl

lemma frequencyVandermonde_pos (R : Finset ℕ) : 0 < frequencyVandermonde R := by
  apply prod_pos
  intro a ha
  apply prod_pos
  intro b hb
  split_ifs with hab
  · exact sub_pos.mpr (Nat.cast_lt.mpr hab)
  · norm_num

/-- Inserting a frequency adds exactly one absolute difference for every
old frequency to the positive Vandermonde. -/
lemma frequencyVandermonde_insert (T : Finset ℕ) (s : ℕ) (hs : s ∉ T) :
    frequencyVandermonde (insert s T) =
      frequencyVandermonde T * ∏ u ∈ T, |(s : ℝ) - u| := by
  unfold frequencyVandermonde
  rw [prod_insert hs, prod_insert hs]
  simp only [lt_self_iff_false, ↓reduceIte, one_mul]
  have hinner :
      (∏ a ∈ T, ∏ b ∈ insert s T, if a < b then (b - a : ℝ) else 1) =
        (∏ a ∈ T, if a < s then (s - a : ℝ) else 1) *
          ∏ a ∈ T, ∏ b ∈ T, if a < b then (b - a : ℝ) else 1 := by
    simp only [prod_insert hs, prod_mul_distrib]
  rw [hinner]
  calc
    (∏ b ∈ T, if s < b then (b - s : ℝ) else 1) *
        ((∏ a ∈ T, if a < s then (s - a : ℝ) else 1) *
          ∏ a ∈ T, ∏ b ∈ T, if a < b then (b - a : ℝ) else 1) =
      (∏ a ∈ T, ∏ b ∈ T, if a < b then (b - a : ℝ) else 1) *
        ∏ u ∈ T, (if s < u then (u - s : ℝ) else 1) *
          (if u < s then (s - u : ℝ) else 1) := by
            rw [prod_mul_distrib]
            ring
    _ = (∏ a ∈ T, ∏ b ∈ T, if a < b then (b - a : ℝ) else 1) *
        ∏ u ∈ T, |(s : ℝ) - u| := by
      congr 1
      apply prod_congr rfl
      intro u hu
      have hus : u ≠ s := by
        intro h
        subst u
        exact hs hu
      rcases lt_or_gt_of_ne hus with h | h
      · rw [ite_eq_right (not_lt.mpr h.le), ite_eq_left h, one_mul,
          abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h.le))]
      · rw [ite_eq_left h, ite_eq_right (not_lt.mpr h.le), mul_one,
          abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h.le))]
        ring

/-- Local insertion factor. It includes both frequency-dependent minors
and every contour--frequency factor from v10 `sec-frequency-tail.tex`. -/
def insertionFactor (m g : ℕ) (S T : Finset ℕ) {d : ℕ}
    (Z : Fin d → ℂ) (t : ℕ) : ℝ :=
  weight g t * (∏ u ∈ T, |(t : ℝ) - u|) ^ 2 *
    (∏ z : Fin d, ‖(t : ℂ) + Z z‖) /
      ((∏ i ∈ I_m m, ((t + i : ℕ) : ℝ)) *
        ∏ j ∈ J_m m \ S, ((t + j : ℕ) : ℝ))

lemma frequencyFactor_insert (m g : ℕ) (S T : Finset ℕ) {d : ℕ}
    (Z : Fin d → ℂ) (t : ℕ) (ht : t ∉ T) :
    frequencyFactor m g S (insert t T) d Z =
      frequencyFactor m g S T d Z * insertionFactor m g S T Z t := by
  unfold frequencyFactor insertionFactor
  rw [frequencyVandermonde_insert T t ht]
  simp only [prod_insert ht]
  rw [← column_product_eq_sdiff m S t]
  simp only [mul_pow, div_eq_mul_inv, mul_inv_rev]
  ring

lemma frequencyFactor_nonneg (m g : ℕ) (S R : Finset ℕ) {d : ℕ}
    (Z : Fin d → ℂ) : 0 ≤ frequencyFactor m g S R d Z := by
  unfold frequencyFactor weight
  positivity

/-- A frequency above `g=m/2` cannot meet the reflected contour, using
exactly the real-part bound in v10 `sec-frequency-tail.tex`. -/
lemma frequency_add_contour_pos {m g t : ℕ} (hgm : 2 * g = m)
    (hgt : g < t) {z : ℂ} (hz : -(m : ℝ) / 6 < z.re) :
    0 < ‖(t : ℂ) + z‖ := by
  have htr : (g : ℝ) < t := Nat.cast_lt.mpr hgt
  have hgr : 2 * (g : ℝ) = m := by exact_mod_cast hgm
  have hre : 0 < ((t : ℂ) + z).re := by
    simp only [Complex.add_re, Complex.natCast_re]
    linarith [show (0 : ℝ) ≤ g by positivity]
  exact lt_of_lt_of_le hre (Complex.re_le_norm _)

lemma insertionFactor_pos {m g : ℕ} (S T : Finset ℕ) {d : ℕ}
    (Z : Fin d → ℂ) (t : ℕ) (ht : t ∉ T) (hgm : 2 * g = m)
    (hgt : g < t) (hZ : ∀ z, -(m : ℝ) / 6 < (Z z).re) :
    0 < insertionFactor m g S T Z t := by
  have htp : 0 < t := lt_of_le_of_lt (Nat.zero_le g) hgt
  unfold insertionFactor
  apply div_pos
  · apply mul_pos
    · apply mul_pos (weight_pos g t hgt)
      apply pow_pos
      apply prod_pos
      intro u hu
      apply abs_pos.mpr
      intro h
      have : t = u := by exact_mod_cast (sub_eq_zero.mp h)
      exact ht (this ▸ hu)
    · exact prod_pos (fun z _ => frequency_add_contour_pos hgm hgt (hZ z))
  · apply mul_pos
    · apply prod_pos
      intro i hi
      exact Nat.cast_pos.mpr (by omega)
    · apply prod_pos
      intro j hj
      exact Nat.cast_pos.mpr (by omega)

/-- The first frequency-dependent minor contributes all `m` row factors. -/
lemma row_factor_ratio_le {m r s : ℕ} (hm : 0 < m) (hm4 : 4 ∣ m)
    (hr : 0 < r) (hs : s ≤ 3 * m / 2) (i : ℕ) (hi : i ∈ I_m m) :
    ((s + i : ℕ) : ℝ) / ((r + i : ℕ) : ℝ) ≤
      11 * (m : ℝ) / (4 * r) := by
  have hi' := hi
  simp only [I_m, mem_Icc] at hi'
  have hbN : 4 * (s + i) ≤ 11 * m := by omega
  have hb : ((s + i : ℕ) : ℝ) ≤ 11 * (m : ℝ) / 4 := by
    have : (4 : ℝ) * ((s + i : ℕ) : ℝ) ≤ 11 * (m : ℝ) := by
      exact_mod_cast hbN
    linarith
  have hri : (r : ℝ) ≤ ((r + i : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right r i
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  calc
    ((s + i : ℕ) : ℝ) / ((r + i : ℕ) : ℝ) ≤
        (11 * (m : ℝ) / 4) / ((r + i : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hb (le_trans hrR.le hri)
    _ ≤ (11 * (m : ℝ) / 4) / r :=
      div_le_div_of_nonneg_left (by positivity) hrR hri
    _ = 11 * (m : ℝ) / (4 * r) := by ring

/-- The second frequency-dependent minor contributes all `2m-|S|` columns. -/
lemma column_factor_ratio_le {m r s : ℕ} (hr : 0 < r)
    (hs : s ≤ 3 * m / 2) (j : ℕ) (hj : j ∈ J_m m) :
    ((s + j : ℕ) : ℝ) / ((r + j : ℕ) : ℝ) ≤
      7 * (m : ℝ) / (2 * r) := by
  simp only [J_m, mem_range] at hj
  have hbN : 2 * (s + j) ≤ 7 * m := by omega
  have hb : ((s + j : ℕ) : ℝ) ≤ 7 * (m : ℝ) / 2 := by
    have : (2 : ℝ) * ((s + j : ℕ) : ℝ) ≤ 7 * (m : ℝ) := by
      exact_mod_cast hbN
    linarith
  have hrj : (r : ℝ) ≤ ((r + j : ℕ) : ℝ) := by
    exact_mod_cast Nat.le_add_right r j
  have hrR : (0 : ℝ) < r := Nat.cast_pos.mpr hr
  calc
    ((s + j : ℕ) : ℝ) / ((r + j : ℕ) : ℝ) ≤
        (7 * (m : ℝ) / 2) / ((r + j : ℕ) : ℝ) :=
      div_le_div_of_nonneg_right hb (le_trans hrR.le hrj)
    _ ≤ (7 * (m : ℝ) / 2) / r :=
      div_le_div_of_nonneg_left (by positivity) hrR hrj
    _ = 7 * (m : ℝ) / (2 * r) := by ring

/-- Every contour--frequency cross factor is retained; the bound uses
the paper's exact `20m` cutoff and its two stated ellipse inequalities. -/
lemma contour_factor_ratio_le {m g r s : ℕ} (hm : 0 < m)
    (hgm : 2 * g = m) (hr : 20 * m < r) (hgs : g < s)
    {z : ℂ} (hzre : -(m : ℝ) / 6 < z.re) (hznorm : ‖z‖ < 5 * (m : ℝ) / 2) :
    ‖(r : ℂ) + z‖ / ‖(s : ℂ) + z‖ ≤ 27 * (r : ℝ) / (8 * m) := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hrR : 20 * (m : ℝ) < r := by exact_mod_cast hr
  have hgsR : (g : ℝ) < s := Nat.cast_lt.mpr hgs
  have hgmR : 2 * (g : ℝ) = m := by exact_mod_cast hgm
  have hden : (m : ℝ) / 3 ≤ ‖(s : ℂ) + z‖ := by
    have h := Complex.re_le_norm ((s : ℂ) + z)
    simp only [Complex.add_re, Complex.natCast_re] at h
    linarith
  have hnum : ‖(r : ℂ) + z‖ ≤ 9 * (r : ℝ) / 8 := by
    have h := norm_add_le (r : ℂ) z
    simp only [Complex.norm_natCast] at h
    linarith
  calc
    ‖(r : ℂ) + z‖ / ‖(s : ℂ) + z‖ ≤
        (9 * (r : ℝ) / 8) / ‖(s : ℂ) + z‖ :=
      div_le_div_of_nonneg_right hnum (norm_nonneg _)
    _ ≤ (9 * (r : ℝ) / 8) / ((m : ℝ) / 3) :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hden
    _ = 27 * (r : ℝ) / (8 * m) := by ring

lemma distance_product_upper {m r : ℕ} (T : Finset ℕ)
    (hcard : T.card = m - 1) (hr : ∀ u ∈ T, u ≤ r) :
    (∏ u ∈ T, |(r : ℝ) - u|) ≤ (r : ℝ) ^ (m - 1) := by
  calc
    (∏ u ∈ T, |(r : ℝ) - u|) ≤ ∏ _u ∈ T, (r : ℝ) := by
      apply prod_le_prod₀ (fun _ _ => abs_nonneg _)
      intro u hu
      rw [abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr (hr u hu)))]
      simp
    _ = (r : ℝ) ^ (m - 1) := by simp [hcard]

lemma distance_ratio_sq_le {m r s : ℕ} (hm4 : 4 ∣ m)
    (T : Finset ℕ) (hcard : T.card = m - 1) (hs : s ∉ T)
    (hr : ∀ u ∈ T, u ≤ r) :
    ((∏ u ∈ T, |(r : ℝ) - u|) / ∏ u ∈ T, |(s : ℝ) - u|) ^ 2 ≤
      ((r : ℝ) ^ (m - 1) / (separationFloor m : ℝ)) ^ 2 := by
  have hsep := separationFloor_le_distance_product hm4 T hcard s hs
  have hfloor : (0 : ℝ) < separationFloor m := by
    simp only [separationFloor, Nat.cast_mul]
    positivity
  apply pow_le_pow_left₀ (by positivity)
  calc
    (∏ u ∈ T, |(r : ℝ) - u|) / ∏ u ∈ T, |(s : ℝ) - u| ≤
        (r : ℝ) ^ (m - 1) / ∏ u ∈ T, |(s : ℝ) - u| :=
      div_le_div_of_nonneg_right (distance_product_upper T hcard hr) (by positivity)
    _ ≤ (r : ℝ) ^ (m - 1) / (separationFloor m : ℝ) :=
      div_le_div_of_nonneg_left (by positivity) hfloor hsep

/-- This identity only divides local insertion factors. Its later use
explicitly proves the replacement insertion factor positive. -/
lemma insertionFactor_ratio (m g : ℕ) (S T : Finset ℕ) {d : ℕ}
    (Z : Fin d → ℂ) (r s : ℕ) :
    insertionFactor m g S T Z r / insertionFactor m g S T Z s =
      (weight g r / weight g s) *
        ((∏ u ∈ T, |(r : ℝ) - u|) / ∏ u ∈ T, |(s : ℝ) - u|) ^ 2 *
        (∏ z : Fin d, ‖(r : ℂ) + Z z‖ / ‖(s : ℂ) + Z z‖) *
        (∏ i ∈ I_m m, ((s + i : ℕ) : ℝ) / ((r + i : ℕ) : ℝ)) *
        (∏ j ∈ J_m m \ S, ((s + j : ℕ) : ℝ) / ((r + j : ℕ) : ℝ)) := by
  simp only [insertionFactor, div_eq_mul_inv,
    mul_inv_rev, inv_inv, mul_pow, inv_pow, prod_mul_distrib, prod_inv_distrib]
  ring

lemma ratio_scale_identity {m d : ℕ} (hm : 0 < m) {r D : ℝ}
    (hr : r ≠ 0) (hD : D ≠ 0) :
    (r ^ (m - 1) / D) ^ 2 * (27 * r / (8 * (m : ℝ))) ^ d *
        (11 * (m : ℝ) / (4 * r)) ^ m *
        (7 * (m : ℝ) / (2 * r)) ^ (m + d) =
      (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ d *
        ((m : ℝ) ^ (2 * m) / (r ^ 2 * D ^ 2)) := by
  have hmR : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hm)
  have hrow : (11 * (m : ℝ) / (4 * r)) * (7 * (m : ℝ) / (2 * r)) =
      (77 / 8 : ℝ) * ((m : ℝ) / r) ^ 2 := by ring
  have hcross : (27 * r / (8 * (m : ℝ))) * (7 * (m : ℝ) / (2 * r)) =
      (189 / 16 : ℝ) := by field_simp; ring
  have hrpow : r ^ m = r ^ (m - 1) * r := by
    rw [← pow_succ]
    congr 1
    omega
  have hcancel : (r ^ (m - 1) / D) * ((m : ℝ) / r) ^ m =
      (m : ℝ) ^ m / (r * D) := by
    rw [div_pow, hrpow]
    field_simp
  calc
    (r ^ (m - 1) / D) ^ 2 * (27 * r / (8 * (m : ℝ))) ^ d *
        (11 * (m : ℝ) / (4 * r)) ^ m *
        (7 * (m : ℝ) / (2 * r)) ^ (m + d) =
      (r ^ (m - 1) / D) ^ 2 *
        ((11 * (m : ℝ) / (4 * r)) * (7 * (m : ℝ) / (2 * r))) ^ m *
        ((27 * r / (8 * (m : ℝ))) * (7 * (m : ℝ) / (2 * r))) ^ d := by
          rw [pow_add, mul_pow, mul_pow]
          ring
    _ = (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ d *
        ((r ^ (m - 1) / D) * ((m : ℝ) / r) ^ m) ^ 2 := by
      rw [hrow, hcross, mul_pow, mul_pow]
      rw [← pow_mul, ← pow_mul, Nat.mul_comm 2 m]
      ring
    _ = (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ d *
        ((m : ℝ) ^ (2 * m) / (r ^ 2 * D ^ 2)) := by
      rw [hcancel]
      simp only [div_pow, mul_pow, ← pow_mul, Nat.mul_comm m 2]

/-- All two-minor and contour factors in the first displayed estimate of
v10 `sec-frequency-tail.tex`, for the literal insertion factor. -/
theorem insertionFactor_ratio_bound {m g r s : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hgm : 2 * g = m)
    (S T : Finset ℕ) (hSI : S ⊆ I_m m) (hcard : T.card = m - 1)
    (hs : s ∉ T) (hgs : g < s) (hsite : s ≤ 3 * m / 2)
    (hr : 20 * m < r) (hmax : ∀ u ∈ T, u ≤ r)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    insertionFactor m g S T Z r / insertionFactor m g S T Z s ≤
      (weight g r / weight g s) * (77 / 8 : ℝ) ^ m *
        (189 / 16 : ℝ) ^ (m - S.card) *
        ((m : ℝ) ^ (2 * m) /
          ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2)) := by
  have hrpos : 0 < r := by omega
  have hSJ := hSI.trans (I_m_subset_J_m hm hm4)
  have hScard : S.card ≤ m := by
    simpa [I_m_card hm hm4] using card_le_card hSI
  have hJcard : (J_m m \ S).card = m + (m - S.card) := by
    rw [card_sdiff_of_subset hSJ]
    simp only [J_m, card_range]
    omega
  have hdistance := distance_ratio_sq_le hm4 T hcard hs hmax
  have hcontour : (∏ z : Fin (m - S.card),
      ‖(r : ℂ) + Z z‖ / ‖(s : ℂ) + Z z‖) ≤
        (27 * (r : ℝ) / (8 * m)) ^ (m - S.card) := by
    calc
      _ ≤ ∏ _z : Fin (m - S.card), 27 * (r : ℝ) / (8 * m) := by
        apply prod_le_prod₀ (fun _ _ => by positivity)
        intro z hz
        exact contour_factor_ratio_le hm hgm hr hgs (hZre z) (hZnorm z)
      _ = _ := by simp [div_pow]
  have hrows : (∏ i ∈ I_m m,
      ((s + i : ℕ) : ℝ) / ((r + i : ℕ) : ℝ)) ≤
        (11 * (m : ℝ) / (4 * r)) ^ m := by
    calc
      _ ≤ ∏ _i ∈ I_m m, 11 * (m : ℝ) / (4 * r) := by
        apply prod_le_prod₀ (fun _ _ => by positivity)
        intro i hi
        exact row_factor_ratio_le hm hm4 hrpos hsite i hi
      _ = _ := by simp [I_m_card hm hm4, div_pow]
  have hcols : (∏ j ∈ J_m m \ S,
      ((s + j : ℕ) : ℝ) / ((r + j : ℕ) : ℝ)) ≤
        (7 * (m : ℝ) / (2 * r)) ^ (m + (m - S.card)) := by
    calc
      _ ≤ ∏ _j ∈ J_m m \ S, 7 * (m : ℝ) / (2 * r) := by
        apply prod_le_prod₀ (fun _ _ => by positivity)
        intro j hj
        exact column_factor_ratio_le hrpos hsite j (mem_sdiff.mp hj).1
      _ = _ := by simp [hJcard, div_pow]
  have hweight : 0 ≤ weight g r / weight g s := by
    unfold weight
    positivity
  rw [insertionFactor_ratio]
  calc
    _ ≤ (weight g r / weight g s) *
        ((r : ℝ) ^ (m - 1) / (separationFloor m : ℝ)) ^ 2 *
        (27 * (r : ℝ) / (8 * m)) ^ (m - S.card) *
        (11 * (m : ℝ) / (4 * r)) ^ m *
        (7 * (m : ℝ) / (2 * r)) ^ (m + (m - S.card)) := by
      gcongr
    _ = _ := by
      rw [show (weight g r / weight g s) *
          ((r : ℝ) ^ (m - 1) / (separationFloor m : ℝ)) ^ 2 *
          (27 * (r : ℝ) / (8 * m)) ^ (m - S.card) *
          (11 * (m : ℝ) / (4 * r)) ^ m *
          (7 * (m : ℝ) / (2 * r)) ^ (m + (m - S.card)) =
        (weight g r / weight g s) *
          (((r : ℝ) ^ (m - 1) / (separationFloor m : ℝ)) ^ 2 *
            (27 * (r : ℝ) / (8 * m)) ^ (m - S.card) *
            (11 * (m : ℝ) / (4 * r)) ^ m *
            (7 * (m : ℝ) / (2 * r)) ^ (m + (m - S.card))) by ring]
      rw [ratio_scale_identity hm (Nat.cast_ne_zero.mpr (ne_of_gt hrpos))
        (show (separationFloor m : ℝ) ≠ 0 by
          simp only [separationFloor, Nat.cast_mul]
          positivity)]
      ring

/-- The scalar coefficient in the geometric estimate is bounded using
the proved literal weight and separation-floor estimates. -/
lemma geometric_coefficient_le {m g s k r : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hgm : 2 * g = m)
    (hgs : g < s) (hsite : s ≤ g + m) (hgr : g < r) (hr : 0 < r) :
    (weight g r / weight g s) * (77 / 8 : ℝ) ^ m *
        (189 / 16 : ℝ) ^ (m - k) *
        ((m : ℝ) ^ (2 * m) /
          ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2)) ≤
      (12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight g r := by
  have hm2 : 2 ∣ m := dvd_trans (by norm_num : 2 ∣ 4) hm4
  have hN : g + m = 3 * m / 2 := by omega
  have hw := exact_weight_ratio g m s r hgs hgr hsite
  rw [hN] at hw
  have hb : (189 / 16 : ℝ) ^ (m - k) ≤ (189 / 16 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le m k)
  have hscale := separationScale_of_lower m r hm hr (separationFloor_lower hm hm4)
  have hwr : 0 ≤ weight g r := (weight_pos g r hgr).le
  have hscale_nonneg : 0 ≤ (m : ℝ) ^ (2 * m) /
      ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2) := by positivity
  have hconstant := ratio_constant m hm hm2
  calc
    _ ≤ weight g r * (2 : ℝ) ^ (3 * m / 2) *
        (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
        (9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) := by
      gcongr
    _ = (weight g r * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) *
        ((2 : ℝ) ^ (3 * m / 2) * (77 / 8 : ℝ) ^ m *
          (189 / 16 : ℝ) ^ m * 9 * (36 : ℝ) ^ (m - 1)) := by ring
    _ ≤ (weight g r * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) *
        ((12500 : ℝ) ^ m / 4) :=
      mul_le_mul_of_nonneg_left hconstant (by positivity)
    _ = _ := by ring

/-- Full insertion estimate with no quotient of a configuration integrand. -/
theorem insertionFactor_le {m g r s : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hgm : 2 * g = m)
    (S T : Finset ℕ) (hSI : S ⊆ I_m m) (hcard : T.card = m - 1)
    (hs : s ∉ T) (hgs : g < s) (hsite : s ≤ g + m)
    (hr : 20 * m < r) (hmax : ∀ u ∈ T, u ≤ r)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    insertionFactor m g S T Z r ≤
      ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight g r) *
        insertionFactor m g S T Z s := by
  have hsite' : s ≤ 3 * m / 2 := by omega
  have hgr : g < r := by omega
  have hrpos : 0 < r := by omega
  have hratio := insertionFactor_ratio_bound hm hm4 hgm S T hSI hcard hs hgs
    hsite' hr hmax Z hZre hZnorm
  have hcoeff := geometric_coefficient_le (k := S.card) hm hm4 hgm hgs hsite hgr hrpos
  exact (div_le_iff₀ (insertionFactor_pos S T Z s hs hgm hgs hZre)).mp
    (hratio.trans hcoeff)

/-- The literal `f(R)` replacement bound from v10 `sec-frequency-tail.tex`.
Both frequency-dependent minors and all contour cross factors are present
in `frequencyFactor`. The conclusion is multiplicative, so a zero common
configuration factor is never divided out. -/
theorem frequencyFactor_replacement_le {m g r s : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hgm : 2 * g = m)
    (S R : Finset ℕ) (hSI : S ⊆ I_m m)
    (hR : admissible g m R) (hrmem : r ∈ R) (hs : s ∉ R)
    (hgs : g < s) (hsite : s ≤ g + m)
    (hr : 20 * m < r) (hmax : ∀ u ∈ R, u ≤ r)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    frequencyFactor m g S R (m - S.card) Z ≤
      ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight g r) *
        frequencyFactor m g S (replace g m R s r) (m - S.card) Z := by
  have hcard : (R.erase r).card = m - 1 := by
    rw [card_erase_of_mem hrmem, hR.2]
  have hs' : s ∉ R.erase r := by
    intro h
    exact hs (mem_erase.mp h).2
  have hbound := insertionFactor_le hm hm4 hgm S (R.erase r) hSI hcard hs' hgs
    hsite hr (fun u hu => hmax u (mem_erase.mp hu).2) Z hZre hZnorm
  calc
    frequencyFactor m g S R (m - S.card) Z =
        frequencyFactor m g S (R.erase r) (m - S.card) Z *
          insertionFactor m g S (R.erase r) Z r := by
      conv_lhs => rw [← insert_erase hrmem]
      exact frequencyFactor_insert m g S (R.erase r) Z r (by simp)
    _ ≤ frequencyFactor m g S (R.erase r) (m - S.card) Z *
        (((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight g r) *
          insertionFactor m g S (R.erase r) Z s) :=
      mul_le_mul_of_nonneg_left hbound (frequencyFactor_nonneg m g S (R.erase r) Z)
    _ = _ := by
      rw [replace, frequencyFactor_insert m g S (R.erase r) Z s hs']
      ring

/-- The paper-facing largest-frequency replacement, using its actual
least unused site in `{m/2+1,...,m/2+m}` and the unchanged `20m` cutoff. -/
theorem leastUnused_frequencyFactor_le {m : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (S R : Finset ℕ) (hSI : S ⊆ I_m m)
    (hR : admissible (m / 2) m R) (r : ℕ) (hrmem : r ∈ R)
    (hr : 20 * m < r) (hmax : ∀ u ∈ R, u ≤ r)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    let s := leastUnused (m / 2) m R hR r hrmem (by omega)
    frequencyFactor m (m / 2) S R (m - S.card) Z ≤
      ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight (m / 2) r) *
        frequencyFactor m (m / 2) S (replace (m / 2) m R s r) (m - S.card) Z := by
  dsimp only
  have hspec := leastUnused_spec (m / 2) m R hR r hrmem (show m / 2 + m < r by omega)
  exact frequencyFactor_replacement_le hm hm4 (by omega) S R hSI hR hrmem
    hspec.2.2 hspec.1 hspec.2.1 hr hmax Z hZre hZnorm

end

end Li2Lean.P0.FrequencyLeaf
