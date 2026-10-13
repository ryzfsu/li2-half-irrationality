/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourExternalFourier

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigContourExternalFourier
noncomputable section
open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigFejerMass

private theorem fourierChar_mul_local (k l : ℤ) (u : ℝ) :
    fourierChar k u * fourierChar l u = fourierChar (k + l) u := by
  unfold fourierChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourierChar_add_angle (k : ℤ) (u v : ℝ) :
    fourierChar k (u + v) = fourierChar k u * fourierChar k v := by
  unfold fourierChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourierChar_sub_angle_local (k : ℤ) (u theta : ℝ) :
    fourierChar k (u - theta) = fourierChar (-k) theta * fourierChar k u := by
  unfold fourierChar
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private theorem fourierChar_product_integral (d k : ℤ) (theta v : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fourierChar d (u - theta) * fourierChar k (u + v)) =
      if d + k = 0 then ((2 * Real.pi : ℝ) : ℂ) *
        (fourierChar (-d) theta * fourierChar k v) else 0 := by
  have heq (u : ℝ) :
      fourierChar d (u - theta) * fourierChar k (u + v) =
        (fourierChar (-d) theta * fourierChar k v) * fourierChar (d + k) u := by
    rw [fourierChar_sub_angle_local, fourierChar_add_angle, ← fourierChar_mul_local]
    ring
  simp_rw [heq]
  have hchar :
      (∫ u in (0 : ℝ)..(2 * Real.pi), fourierChar (d + k) u) =
        if d + k = 0 then ((2 * Real.pi : ℝ) : ℂ) else 0 := by
    simpa using (integral_fourierChar (d + k) 0)
  rw [intervalIntegral.integral_const_mul, hchar]
  by_cases h : d + k = 0 <;> simp [h] <;> ring

private theorem sum_pair_condition (n : ℕ) (C : ℂ) :
    (∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
      if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then C else 0) =
      (if n ≤ 48 then ((49 - n : ℕ) : ℂ) * C else 0) := by
  by_cases hn : n ≤ 48
  · have hinner (r : ℕ) (hr : r < 49) :
        (∑ s ∈ Finset.range 49,
          if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then C else 0) =
          (if r + n < 49 then C else 0) := by
      by_cases hrn : r + n < 49
      · have hmem : r + n ∈ Finset.range 49 := by simpa using hrn
        rw [Finset.sum_eq_single (r + n)]
        · simp only [Nat.cast_add]
          have heq : (r : ℤ) - ((r + n : ℕ) : ℤ) + (n : ℤ) = 0 := by omega
          have hlt : ¬ 49 ≤ r + n := by omega
          simp [heq, hlt]
        · intro b hb hne
          have hb' : b < 49 := Finset.mem_range.mp hb
          have hne' : (r : ℤ) - (b : ℤ) + (n : ℤ) ≠ 0 := by
            intro hzero
            have : b = r + n := by omega
            exact hne this
          simp [hne']
        · intro hnot
          exact (hnot hmem).elim
      · rw [if_neg hrn]
        apply Finset.sum_eq_zero
        intro s hs
        have hs' : s < 49 := Finset.mem_range.mp hs
        have hne : (r : ℤ) - (s : ℤ) + (n : ℤ) ≠ 0 := by
          intro hzero
          have : r + n = s := by omega
          omega
        simp [hne]
    have hsum : (∑ r ∈ Finset.range 49, if r + n < 49 then C else 0) =
        ((49 - n : ℕ) : ℂ) * C := by
      have hpred (r : ℕ) : r + n < 49 ↔ r < 49 - n := by omega
      simp_rw [hpred]
      have hsub : Finset.range (49 - n) ⊆ Finset.range 49 := by
        apply Finset.range_mono
        omega
      calc
        (∑ r ∈ Finset.range 49, if r < 49 - n then C else 0) =
            ∑ r ∈ Finset.range (49 - n), if r < 49 - n then C else 0 := by
          symm
          apply Finset.sum_subset hsub
          intro r hr hrnot
          have hr' : ¬ r < 49 - n := by
            intro h
            exact hrnot (Finset.mem_range.mpr h)
          simp [hr']
        _ = ∑ r ∈ Finset.range (49 - n), C := by
          apply Finset.sum_congr rfl
          intro r hr
          simp [Finset.mem_range.mp hr]
        _ = ((49 - n : ℕ) : ℂ) * C := by simp
    rw [Finset.sum_congr rfl (fun r hr => hinner r (Finset.mem_range.mp hr))]
    rw [hsum]
    simp [hn]
  · have hlarge : 49 ≤ n := by omega
    simp only [if_neg hn]
    apply Finset.sum_eq_zero
    intro r hr
    apply Finset.sum_eq_zero
    intro s hs
    have hr' : r < 49 := Finset.mem_range.mp hr
    have hs' : s < 49 := Finset.mem_range.mp hs
    have hne : (r : ℤ) - (s : ℤ) + (n : ℤ) ≠ 0 := by omega
    simp [hne]



private theorem complex_cos_char (k : ℕ) (u : ℝ) :
    ((Real.cos ((k : ℝ) * u) : ℝ) : ℂ) =
      (fourierChar (k : ℤ) u + fourierChar (-(k : ℤ)) u) / 2 := by
  unfold fourierChar
  have hpos : ((k : ℤ) : ℂ) * (u : ℂ) * Complex.I =
      (((k : ℝ) * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  have hneg : (((-(k : ℤ) : ℤ) : ℂ)) * (u : ℂ) * Complex.I =
      (-((k : ℝ) * u : ℝ) : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hpos, hneg, Complex.exp_mul_I, Complex.exp_mul_I]
  rw [Complex.cos_neg, Complex.sin_neg]
  rw [← Complex.ofReal_cos, ← Complex.ofReal_sin]
  simp [Complex.ofReal_neg]
  ring

private theorem sum_pair_condition_neg (n : ℕ) (C : ℂ) :
    (∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
      if (r : ℤ) - (s : ℤ) - (n : ℤ) = 0 then C else 0) =
      (if n ≤ 48 then ((49 - n : ℕ) : ℂ) * C else 0) := by
  rw [Finset.sum_comm]
  have hcond (r s : ℕ) :
      (s : ℤ) - (r : ℤ) - (n : ℤ) = 0 ↔
        (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 := by omega
  simp_rw [hcond]
  exact sum_pair_condition n C

theorem fejer48_shifted_cosine (n : ℕ) (theta v : ℝ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fejer48 (u - theta) * Real.cos ((n : ℝ) * (u + v))) =
      2 * Real.pi * (if n ≤ 48 then (1 - (n : ℝ) / 49) else 0) *
        Real.cos ((n : ℝ) * (theta + v)) := by
  apply Complex.ofReal_injective
  rw [← intervalIntegral.integral_ofReal]
  have heq (u : ℝ) :
      ((fejer48 (u - theta) * Real.cos ((n : ℝ) * (u + v)) : ℝ) : ℂ) =
        (49 : ℂ)⁻¹ * ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
          fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
            ((fourierChar (n : ℤ) (u + v) +
              fourierChar (-(n : ℤ)) (u + v)) / 2) := by
    rw [Complex.ofReal_mul, fejer48_eq_K48, complex_cos_char]
    simp only [K48]
    calc
      (49 : ℂ)⁻¹ * (∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
          fourierChar ((r : ℤ) - (s : ℤ)) (u - theta)) *
          ((fourierChar (n : ℤ) (u + v) +
            fourierChar (-(n : ℤ)) (u + v)) / 2) =
        (49 : ℂ)⁻¹ *
          ((∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
            fourierChar ((r : ℤ) - (s : ℤ)) (u - theta)) *
            ((fourierChar (n : ℤ) (u + v) +
              fourierChar (-(n : ℤ)) (u + v)) / 2)) := by ring
      _ = (49 : ℂ)⁻¹ * ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
          fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
            ((fourierChar (n : ℤ) (u + v) +
              fourierChar (-(n : ℤ)) (u + v)) / 2) := by
        congr 1
        rw [Finset.sum_mul]
        apply Finset.sum_congr rfl
        intro r hr
        rw [Finset.sum_mul]
  simp_rw [heq]
  rw [intervalIntegral.integral_const_mul]
  have hterm_cont (r s : ℕ) : Continuous
      (fun u : ℝ =>
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
          ((fourierChar (n : ℤ) (u + v) +
            fourierChar (-(n : ℤ)) (u + v)) / 2)) := by
    have hc1 : Continuous (fun u : ℝ =>
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta)) :=
      (continuous_fourierChar _).comp (continuous_id.sub continuous_const)
    have hc2 : Continuous (fun u : ℝ => fourierChar (n : ℤ) (u + v)) :=
      (continuous_fourierChar _).comp (continuous_id.add continuous_const)
    have hc3 : Continuous (fun u : ℝ => fourierChar (-(n : ℤ)) (u + v)) :=
      (continuous_fourierChar _).comp (continuous_id.add continuous_const)
    exact hc1.mul ((hc2.add hc3).div_const 2)
  have hterm (r s : ℕ) : IntervalIntegrable
      (fun u : ℝ =>
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
          ((fourierChar (n : ℤ) (u + v) +
            fourierChar (-(n : ℤ)) (u + v)) / 2))
      volume 0 (2 * Real.pi) :=
    (hterm_cont r s).intervalIntegrable _ _
  have hrow_cont (r : ℕ) : Continuous
      (fun u : ℝ => ∑ s ∈ Finset.range 49,
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
          ((fourierChar (n : ℤ) (u + v) +
            fourierChar (-(n : ℤ)) (u + v)) / 2)) := by
    apply continuous_finsetSum
    intro s hs
    exact hterm_cont r s
  have hrow (r : ℕ) : IntervalIntegrable
      (fun u : ℝ => ∑ s ∈ Finset.range 49,
        fourierChar ((r : ℤ) - (s : ℤ)) (u - theta) *
          ((fourierChar (n : ℤ) (u + v) +
            fourierChar (-(n : ℤ)) (u + v)) / 2))
      volume 0 (2 * Real.pi) :=
    (hrow_cont r).intervalIntegrable _ _
  rw [intervalIntegral.integral_finsetSum (fun r hr => hrow r)]
  have hR :
      (((2 * Real.pi * (if n ≤ 48 then 1 - (n : ℝ) / 49 else 0) *
        Real.cos ((n : ℝ) * (theta + v))) : ℝ) : ℂ) =
      (49 : ℂ)⁻¹ *
        ((49 : ℂ) *
          (((2 * Real.pi * (if n ≤ 48 then 1 - (n : ℝ) / 49 else 0) *
            Real.cos ((n : ℝ) * (theta + v))) : ℝ) : ℂ)) := by
    field_simp
  rw [hR]
  apply congrArg (fun z : ℂ => (49 : ℂ)⁻¹ * z)
  calc
    (∑ r ∈ Finset.range 49,
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          ∑ s ∈ Finset.range 49,
            fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
              ((fourierChar (n : ℤ) (x + v) +
                fourierChar (-(n : ℤ)) (x + v)) / 2)) =
      ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
        ∫ x in (0 : ℝ)..(2 * Real.pi),
          fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
            ((fourierChar (n : ℤ) (x + v) +
              fourierChar (-(n : ℤ)) (x + v)) / 2) := by
        apply Finset.sum_congr rfl
        intro r hr
        rw [intervalIntegral.integral_finsetSum (fun s hs => hterm r s)]
    _ = 49 *
        (((2 * Real.pi * (if n ≤ 48 then 1 - (n : ℝ) / 49 else 0) *
          Real.cos ((n : ℝ) * (theta + v))) : ℝ) : ℂ) := by
      have hsplit (r s : ℕ) :
          (∫ x in (0 : ℝ)..(2 * Real.pi),
            fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
              ((fourierChar (n : ℤ) (x + v) +
                fourierChar (-(n : ℤ)) (x + v)) / 2)) =
            ((∫ x in (0 : ℝ)..(2 * Real.pi),
                fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
                  fourierChar (n : ℤ) (x + v)) +
              (∫ x in (0 : ℝ)..(2 * Real.pi),
                fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
                  fourierChar (-(n : ℤ)) (x + v))) / 2 := by
        have heqfun (x : ℝ) :
            fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
                ((fourierChar (n : ℤ) (x + v) +
                  fourierChar (-(n : ℤ)) (x + v)) / 2) =
              (fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
                  fourierChar (n : ℤ) (x + v) +
                fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
                  fourierChar (-(n : ℤ)) (x + v)) / 2 := by ring
        have hp1_cont : Continuous (fun x : ℝ =>
            fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
              fourierChar (n : ℤ) (x + v)) :=
          (continuous_fourierChar _).comp (continuous_id.sub continuous_const) |>.mul
            ((continuous_fourierChar _).comp (continuous_id.add continuous_const))
        have hp2_cont : Continuous (fun x : ℝ =>
            fourierChar ((r : ℤ) - (s : ℤ)) (x - theta) *
              fourierChar (-(n : ℤ)) (x + v)) :=
          (continuous_fourierChar _).comp (continuous_id.sub continuous_const) |>.mul
            ((continuous_fourierChar _).comp (continuous_id.add continuous_const))
        have hp1 := hp1_cont.intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
        have hp2 := hp2_cont.intervalIntegrable (μ := volume) (0 : ℝ) (2 * Real.pi)
        rw [← intervalIntegral.integral_add hp1 hp2]
        rw [← intervalIntegral.integral_div]
        congr 1
        funext x
        exact heqfun x
      simp_rw [hsplit, fourierChar_product_integral]
      have hpos (r s : ℕ) :
          (if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then
              ((2 * Real.pi : ℝ) : ℂ) *
                (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (n : ℤ) v)
            else 0) =
          (if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then
              ((2 * Real.pi : ℝ) : ℂ) *
                (fourierChar (n : ℤ) theta * fourierChar (n : ℤ) v)
            else 0) := by
        by_cases h : (r : ℤ) - (s : ℤ) + (n : ℤ) = 0
        · have hd : -((r : ℤ) - (s : ℤ)) = (n : ℤ) := by omega
          simp [h, hd]
        · simp [h]
      have hneg (r s : ℕ) :
          (if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
              ((2 * Real.pi : ℝ) : ℂ) *
                (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (-(n : ℤ)) v)
            else 0) =
          (if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
              ((2 * Real.pi : ℝ) : ℂ) *
                (fourierChar (-(n : ℤ)) theta * fourierChar (-(n : ℤ)) v)
            else 0) := by
        by_cases h : (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0
        · have hd : -((r : ℤ) - (s : ℤ)) = -(n : ℤ) := by omega
          simp [h, hd]
        · simp [h]
      have hinner (r : ℕ) :
          (∑ s ∈ Finset.range 49,
            ((if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then
                ((2 * Real.pi : ℝ) : ℂ) *
                  (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (n : ℤ) v)
              else 0) +
             (if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
                ((2 * Real.pi : ℝ) : ℂ) *
                  (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (-(n : ℤ)) v)
              else 0)) / 2) =
            ((∑ s ∈ Finset.range 49,
                if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then
                  ((2 * Real.pi : ℝ) : ℂ) *
                    (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (n : ℤ) v)
                else 0) +
              ∑ s ∈ Finset.range 49,
                if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
                  ((2 * Real.pi : ℝ) : ℂ) *
                    (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (-(n : ℤ)) v)
                else 0) / 2 := by
        rw [← Finset.sum_div]
        rw [Finset.sum_add_distrib]
      calc
        (∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
            ((if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then
                ((2 * Real.pi : ℝ) : ℂ) *
                  (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (n : ℤ) v)
              else 0) +
             (if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
                ((2 * Real.pi : ℝ) : ℂ) *
                  (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (-(n : ℤ)) v)
              else 0)) / 2) =
          ∑ r ∈ Finset.range 49,
            ((∑ s ∈ Finset.range 49,
                if (r : ℤ) - (s : ℤ) + (n : ℤ) = 0 then
                  ((2 * Real.pi : ℝ) : ℂ) *
                    (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (n : ℤ) v)
                else 0) +
              ∑ s ∈ Finset.range 49,
                if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
                  ((2 * Real.pi : ℝ) : ℂ) *
                    (fourierChar (-((r : ℤ) - (s : ℤ))) theta * fourierChar (-(n : ℤ)) v)
                else 0) / 2 := by
            apply Finset.sum_congr rfl
            intro r hr
            exact hinner r
        _ = 49 *
            (((2 * Real.pi * (if n ≤ 48 then 1 - (n : ℝ) / 49 else 0) *
              Real.cos ((n : ℝ) * (theta + v))) : ℝ) : ℂ) := by
          rw [← Finset.sum_div]
          rw [Finset.sum_add_distrib]
          simp_rw [hpos, hneg]
          rw [sum_pair_condition]
          have hnegpair :
              (∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
                if (r : ℤ) - (s : ℤ) + (-(n : ℤ)) = 0 then
                  ((2 * Real.pi : ℝ) : ℂ) *
                    (fourierChar (-(n : ℤ)) theta * fourierChar (-(n : ℤ)) v)
                else 0) =
                (if n ≤ 48 then ((49 - n : ℕ) : ℂ) *
                  (((2 * Real.pi : ℝ) : ℂ) *
                    (fourierChar (-(n : ℤ)) theta * fourierChar (-(n : ℤ)) v)) else 0) := by
            convert sum_pair_condition_neg n
              (((2 * Real.pi : ℝ) : ℂ) *
                (fourierChar (-(n : ℤ)) theta * fourierChar (-(n : ℤ)) v)) using 1 <;>
              simp [sub_eq_add_neg]
          rw [hnegpair]
          by_cases hn : n ≤ 48
          · simp only [if_pos hn]
            rw [← fourierChar_add_angle, ← fourierChar_add_angle]
            calc
              (↑(49 - n) * (↑(2 * Real.pi) * fourierChar (n : ℤ) (theta + v)) +
                    ↑(49 - n) * (↑(2 * Real.pi) * fourierChar (-(n : ℤ)) (theta + v))) / 2 =
                  (↑(49 - n) * ↑(2 * Real.pi)) *
                    ((fourierChar (n : ℤ) (theta + v) +
                      fourierChar (-(n : ℤ)) (theta + v)) / 2) := by ring
              _ = (↑(49 - n) * ↑(2 * Real.pi)) *
                    (((Real.cos ((n : ℝ) * (theta + v)) : ℝ) : ℂ)) := by
                      rw [complex_cos_char]
              _ = 49 * ↑(2 * Real.pi * (1 - (n : ℝ) / 49) *
                    Real.cos ((n : ℝ) * (theta + v))) := by
                      rw [Nat.cast_sub (by omega)]
                      push_cast
                      ring
          · simp only [if_neg hn]
            norm_num


/-! The abstract orthogonality record used by the external coefficient layer
is now filled by the literal degree-48 kernel calculation above.  Keeping
this as a named theorem makes the source identity consume the actual
Fejer/Joukowski reference rather than an unconnected premise. -/

theorem fejer48_shifted_orthogonality_actual :
    Li2Lean.P0.ConfigContourExternalFourier.Fejer48ShiftedOrthogonality := by
  refine ⟨?_⟩
  intro k theta v
  simpa [Li2Lean.P0.ConfigContourSelfPotential.K48Coeff] using
    fejer48_shifted_cosine k theta v

/-- The sine moment of the literal 64-point Appendix A contour weights. -/
def contourSineFourierMoment (n : ℕ) : ℝ :=
  ∑ j : Fin 64, contourWeight j * Real.sin ((n : ℝ) * contourAngle j)

/-- Reflection of the actual Appendix A masses about the real axis makes all
sine moments vanish.  This statement is about the source table and midpoint
angles, not an abstract symmetric measure. -/
theorem contourSineFourierMoment_eq_zero (n : ℕ) :
    contourSineFourierMoment n = 0 := by
  let S : ℝ := ∑ j : Fin 64,
    contourWeight j * Real.sin ((n : ℝ) * contourAngle j)
  have hrev : S = ∑ j : Fin 64,
      contourWeight (reverseIndex j) *
        Real.sin ((n : ℝ) * contourAngle (reverseIndex j)) := by
    dsimp [S]
    rw [← Equiv.sum_comp reverseIndex
      (fun j => contourWeight j * Real.sin ((n : ℝ) * contourAngle j))]
  have hneg : (∑ j : Fin 64,
      contourWeight (reverseIndex j) *
        Real.sin ((n : ℝ) * contourAngle (reverseIndex j))) = -S := by
    dsimp [S]
    calc
      (∑ j : Fin 64, contourWeight (reverseIndex j) *
          Real.sin ((n : ℝ) * contourAngle (reverseIndex j))) =
          ∑ j : Fin 64, -(contourWeight j *
            Real.sin ((n : ℝ) * contourAngle j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        rw [contourWeight_reverse, contourAngle_reverse]
        have harg : (n : ℝ) * (2 * Real.pi - contourAngle j) =
            -(n : ℝ) * contourAngle j + (n : ℤ) * (2 * Real.pi) := by
          push_cast
          ring
        rw [harg, Real.sin_add_int_mul_two_pi]
        rw [show -(n : ℝ) * contourAngle j =
          -((n : ℝ) * contourAngle j) by ring, Real.sin_neg]
        ring
      _ = -S := by rw [Finset.sum_neg_distrib]
  have hself : S = -S := hrev.trans hneg
  dsimp [S, contourSineFourierMoment]
  linarith

/-- The external Abel coefficient for every positive frequency is the exact
degree-48 Fejer multiplier times the literal 64-point cosine moment.  In
particular, the formula also proves vanishing above frequency 48. -/
theorem externalFourierCoefficient_eq_actual_moment
    (k : ℕ) (hkpos : 1 ≤ k) (v : ℝ) :
    externalFourierCoefficient (k - 1) v =
      2 * Real.pi * contourFourierMoment k * Real.cos ((k : ℝ) * v) :=
  externalFourierCoefficient_eq_moment fejer48_shifted_orthogonality_actual
    k hkpos v

/-- The same exact coefficient formula in the natural Abel-series index. -/
theorem externalFourierCoefficient_eq_actual_moment_succ
    (n : ℕ) (v : ℝ) :
    externalFourierCoefficient n v =
      2 * Real.pi * contourFourierMoment (n + 1) *
        Real.cos ((n + 1 : ℝ) * v) := by
  have h := externalFourierCoefficient_eq_actual_moment (n + 1) (by omega) v
  simpa using h

/-- The external Joukowski logarithm therefore has a finite Fourier
evaluation on the original reference: all coefficients above degree 48
vanish by the literal Fejer multiplier.  This is the integral/sum exchange
from the Abel kernel followed by the exact source coefficient identity. -/
theorem externalLogKernel_integral_eq_finite_moment (q v : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * externalLogKernel q u v) =
      ∑ n ∈ Finset.range 48,
        (-(q ^ (n + 1) / (n + 1 : ℝ))) *
          (2 * Real.pi * contourFourierMoment (n + 1) *
            Real.cos ((n + 1 : ℝ) * v)) := by
  rw [externalLogKernel_integral_eq_tsum_fourier q v hq]
  have hzero : ∀ n ∉ Finset.range 48,
      (-(q ^ (n + 1) / (n + 1 : ℝ))) *
        externalFourierCoefficient n v = 0 := by
    intro n hn
    have hnlarge : 48 ≤ n := Nat.le_of_not_gt (by simpa using hn)
    have hmoment := externalFourierCoefficient_eq_actual_moment_succ n v
    rw [hmoment]
    have hcoeff : contourFourierMoment (n + 1) = 0 := by
      unfold contourFourierMoment K48Coeff
      simp [Nat.not_le_of_gt (by omega : 48 < n + 1)]
    rw [hcoeff]
    ring
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro n hn
  have h := externalFourierCoefficient_eq_actual_moment_succ n v
  simpa using congrArg
    (fun x : ℝ => (-(q ^ (n + 1) / (n + 1 : ℝ))) * x) h


end
end Li2Lean.P0.ConfigContourExternalFourier

#print axioms Li2Lean.P0.ConfigContourExternalFourier.fejer48_shifted_cosine
#print axioms Li2Lean.P0.ConfigContourExternalFourier.fejer48_shifted_orthogonality_actual
#print axioms Li2Lean.P0.ConfigContourExternalFourier.contourSineFourierMoment_eq_zero
#print axioms Li2Lean.P0.ConfigContourExternalFourier.externalFourierCoefficient_eq_actual_moment
#print axioms Li2Lean.P0.ConfigContourExternalFourier.externalLogKernel_integral_eq_finite_moment
