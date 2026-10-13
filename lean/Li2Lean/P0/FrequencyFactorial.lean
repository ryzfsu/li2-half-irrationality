/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean.P0.FrequencyLeaf

noncomputable section

/-- The exact factorial separation product in the v10 replacement estimate. -/
def separationFloor (m : ℕ) : ℕ :=
  Nat.factorial ((m - 1) / 2) * Nat.factorial (m / 2)

lemma factorial_lower_third (n : ℕ) :
    ((n : ℝ) / 3) ^ n ≤ (Nat.factorial n : ℝ) := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      rcases n with _ | n
      · norm_num
      · by_cases hn : n = 0
        · subst n
          norm_num
        · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
          have hpow : (1 + (n : ℝ)⁻¹) ^ n ≤ Real.exp 1 :=
            Real.one_add_inv_pow_le_exp
          have hexp : Real.exp 1 < 3 := Real.exp_one_lt_three
          have hratio : (1 + (n : ℝ)⁻¹) ^ n ≤ 3 := hpow.trans hexp.le
          have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast hn
          have hratio' :
                (((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n ≤ 3 := by
              rw [show ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 by norm_num]
              convert hratio using 1
              field_simp [hnR]
          have hbase : 0 ≤ ((n : ℝ) / 3) ^ n := by positivity
          have hratio_power :
              (((n + 1 : ℕ) : ℝ) / 3) ^ n ≤
                3 * ((n : ℝ) / 3) ^ n := by
            calc
              (((n + 1 : ℕ) : ℝ) / 3) ^ n =
                  ((n : ℝ) / 3) ^ n *
                    ((((n + 1 : ℕ) : ℝ) / (n : ℝ)) ^ n) := by
                rw [← mul_pow]
                field_simp [hnR]
              _ ≤ ((n : ℝ) / 3) ^ n * 3 :=
                mul_le_mul_of_nonneg_left hratio' hbase
              _ = 3 * ((n : ℝ) / 3) ^ n := by ring
          calc
            (((n + 1 : ℕ) : ℝ) / 3) ^ (n + 1) =
                (((n + 1 : ℕ) : ℝ) / 3) *
                  (((n + 1 : ℕ) : ℝ) / 3) ^ n := by
                    rw [pow_succ]
                    ring
            _ ≤ ((n + 1 : ℕ) : ℝ) / 3 *
                  (3 * ((n : ℝ) / 3) ^ n) := by
              gcongr
            _ = ((n + 1 : ℕ) : ℝ) * ((n : ℝ) / 3) ^ n := by ring
            _ ≤ ((n + 1 : ℕ) : ℝ) * (Nat.factorial n : ℝ) := by
              gcongr
              exact ih n (Nat.lt_succ_self n)
            _ = (Nat.factorial (n + 1) : ℝ) := by
              rw [Nat.factorial_succ]
              norm_num

lemma near_one_power_upper (a : ℕ) (ha : 0 < a) :
    (((a + 1 : ℕ) : ℝ) / a) ^ a ≤ 3 := by
  have haR : (a : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt ha)
  have h := (Real.one_add_inv_pow_le_exp (n := a)).trans Real.exp_one_lt_three.le
  rw [show ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 by norm_num]
  convert h using 1
  field_simp [haR]

lemma near_one_power_lower (a : ℕ) :
    (1 : ℝ) / 3 ≤ ((a : ℝ) / (a + 1)) ^ a := by
  by_cases ha : a = 0
  · subst a
    norm_num
  · have haPos : 0 < a := Nat.pos_of_ne_zero ha
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hbR : ((a + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hbound := near_one_power_upper a haPos
    have hrecip :
        ((a : ℝ) / (a + 1)) ^ a = 1 / ((((a + 1 : ℕ) : ℝ) / a) ^ a) := by
      rw [show ((a + 1 : ℕ) : ℝ) = (a : ℝ) + 1 by norm_num]
      have hbase : (a : ℝ) / ((a : ℝ) + 1) =
          1 / (((a : ℝ) + 1) / (a : ℝ)) := by
        field_simp [haR, hbR]
      calc
        ((a : ℝ) / ((a : ℝ) + 1)) ^ a =
            (1 / (((a : ℝ) + 1) / (a : ℝ))) ^ a := by rw [hbase]
        _ = 1 / ((((a : ℝ) + 1) / (a : ℝ)) ^ a) := by
          rw [div_pow, one_pow]
    rw [hrecip]
    exact one_div_le_one_div_of_le (by positivity) hbound

lemma adjacent_factorial_lower (a : ℕ) :
    ((a.factorial : ℝ) * ((a + 1).factorial : ℝ)) ≥
      ((((2 * (a + 1) : ℕ) : ℝ) / 6) ^ (2 * a + 1)) / 3 := by
  have ha := factorial_lower_third a
  have hb := factorial_lower_third (a + 1)
  have hr := near_one_power_lower a
  have hprod :
      (((a : ℝ) / 3) ^ a) * ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + 1)) ≤
        (a.factorial : ℝ) * ((a + 1).factorial : ℝ) := by
    exact mul_le_mul ha hb (by positivity) (by positivity)
  have hfactor :
      (((a : ℝ) / 3) ^ a) * ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + 1)) =
        ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) *
          ((a : ℝ) / (a + 1)) ^ a := by
    have hbase : (a : ℝ) / 3 =
        ((((a + 1 : ℕ) : ℝ) / 3) * ((a : ℝ) / (a + 1))) := by
      push_cast
      field_simp
    calc
      (((a : ℝ) / 3) ^ a) * ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + 1)) =
          ((((a + 1 : ℕ) : ℝ) / 3) ^ a) *
            ((a : ℝ) / (a + 1)) ^ a *
              ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + 1)) := by rw [hbase, mul_pow]
      _ = (((((a + 1 : ℕ) : ℝ) / 3) ^ a) *
            ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + 1))) *
              ((a : ℝ) / (a + 1)) ^ a := by ring
      _ = ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + (a + 1))) *
            ((a : ℝ) / (a + 1)) ^ a := by rw [← pow_add]
      _ = ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) *
            ((a : ℝ) / (a + 1)) ^ a := by
              rw [show a + (a + 1) = 2 * a + 1 by omega]
  have hbpos : 0 ≤ (((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1) := by positivity
  have hratio :
      ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) / 3 ≤
        ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) *
          ((a : ℝ) / (a + 1)) ^ a := by
    calc
      ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) / 3 =
          ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) * (1 / 3) := by ring
      _ ≤ ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) *
            ((a : ℝ) / (a + 1)) ^ a := mul_le_mul_of_nonneg_left hr hbpos
  have heq : (((a + 1 : ℕ) : ℝ) / 3) =
      (((2 * (a + 1) : ℕ) : ℝ) / 6) := by
    push_cast
    ring
  calc
    ((((2 * (a + 1) : ℕ) : ℝ) / 6) ^ (2 * a + 1)) / 3 =
        ((((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1)) / 3 := by rw [heq]
    _ ≤ (((a + 1 : ℕ) : ℝ) / 3) ^ (2 * a + 1) *
          ((a : ℝ) / (a + 1)) ^ a := hratio
    _ = (((a : ℝ) / 3) ^ a) * ((((a + 1 : ℕ) : ℝ) / 3) ^ (a + 1)) := hfactor.symm
    _ ≤ (a.factorial : ℝ) * ((a + 1).factorial : ℝ) := hprod

lemma separationFloor_lower {m : ℕ} (hm : 0 < m) (hm4 : 4 ∣ m) :
    ((m : ℝ) / 6) ^ (m - 1) / 3 ≤ (separationFloor m : ℝ) := by
  obtain ⟨a, rfl⟩ := hm4
  have ha : 0 < a := by omega
  have hleft : (4 * a - 1) / 2 = 2 * a - 1 := by omega
  have hright : (4 * a) / 2 = 2 * a := by omega
  have ha2 : 1 ≤ 2 * a := by omega
  have hmain := adjacent_factorial_lower (2 * a - 1)
  rw [separationFloor, hleft, hright]
  have hbase : ((4 * a : ℕ) : ℝ) / 6 =
      (((2 * ((2 * a - 1) + 1) : ℕ) : ℝ) / 6) := by
    norm_num [Nat.cast_mul, Nat.cast_sub ha2]
    ring
  rw [show 4 * a - 1 = 2 * (2 * a - 1) + 1 by omega]
  rw [hbase]
  simpa [Nat.cast_mul, Nat.sub_add_cancel ha2] using hmain

end

end Li2Lean.P0.FrequencyLeaf
