/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.L3Rate

/-!
# Weighted Prime Limits from the Chebyshev PNT

This module proves the literal finite piecewise-affine weighted-prime limit
from the Chebyshev theta PNT interface. It keeps the half-open profile
convention and all endpoint prime atoms explicit until their normalized
contributions are shown to vanish.
-/

open MeasureTheory Filter Topology

namespace Li2Lean

noncomputable def endpointPrimeLogAtom (y : ℝ) : ℝ :=
  if Nat.Prime ⌊y⌋₊ ∧ (⌊y⌋₊ : ℝ) = y then Real.log y else 0

noncomputable def thetaStrictFinite (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
    if Nat.Prime n ∧ (n : ℝ) < y then Real.log (n : ℝ) else 0

theorem thetaStrictFinite_eq (y : ℝ) (hy : 0 ≤ y) :
    thetaStrictFinite y = Chebyshev.theta y - endpointPrimeLogAtom y := by
  classical
  rw [thetaStrictFinite, Chebyshev.theta_eq_sum_Icc, Finset.sum_filter]
  by_cases hEq : (⌊y⌋₊ : ℝ) = y
  · have hmem : ⌊y⌋₊ ∈ Finset.Icc 0 ⌊y⌋₊ := Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩
    have hrest :
        (∑ n ∈ (Finset.Icc 0 ⌊y⌋₊).erase ⌊y⌋₊,
          if Nat.Prime n ∧ (n : ℝ) < y then Real.log (n : ℝ) else 0) =
        ∑ n ∈ (Finset.Icc 0 ⌊y⌋₊).erase ⌊y⌋₊,
          if Nat.Prime n then Real.log (n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ∈ Finset.Icc 0 ⌊y⌋₊ := Finset.mem_of_mem_erase hn
      have hne : n ≠ ⌊y⌋₊ := (Finset.mem_erase.mp hn).1
      have hn'' := Finset.mem_Icc.mp hn'
      have hlt : n < ⌊y⌋₊ := by omega
      have hltR : (n : ℝ) < y := by
        calc
          (n : ℝ) < (⌊y⌋₊ : ℝ) := by exact_mod_cast hlt
          _ = y := hEq
      simp [hltR]
    rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem, hrest]
    simp [endpointPrimeLogAtom, hEq]
  · have hfloor_lt : (⌊y⌋₊ : ℝ) < y := by
      apply lt_of_le_of_ne (Nat.floor_le hy)
      intro h
      exact hEq h
    have hsum :
        (∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
          (if Nat.Prime n ∧ (n : ℝ) < y then Real.log (n : ℝ) else 0)) =
        ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
          (if Nat.Prime n then Real.log (n : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2
      simp [hnle.trans_lt hfloor_lt]
    rw [hsum]
    simp [endpointPrimeLogAtom, hEq]

theorem thetaStrictFinite_extend (y z : ℝ) (hy : 0 ≤ y) (hyz : y ≤ z) :
    thetaStrictFinite y =
      ∑ n ∈ Finset.Icc 0 ⌊z⌋₊,
        if Nat.Prime n ∧ (n : ℝ) < y then Real.log (n : ℝ) else 0 := by
  classical
  unfold thetaStrictFinite
  apply Finset.sum_subset
  · exact Finset.Icc_subset_Icc_right (Nat.floor_mono hyz)
  · intro n hn hnz
    have hnle : n ≤ ⌊z⌋₊ := (Finset.mem_Icc.mp hn).2
    have hny : ⌊y⌋₊ < n := by
      exact lt_of_not_ge fun h => hnz (Finset.mem_Icc.mpr ⟨Nat.zero_le _, h⟩)
    have hnlt : y < (n : ℝ) := by
      have hnlo : (⌊y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hny
      have hlt := Nat.lt_floor_add_one y
      linarith
    simp [not_lt_of_ge hnlt.le]

noncomputable def primeIntervalThetaMass (a b x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
    if Nat.Prime n ∧ a * x ≤ (n : ℝ) ∧ (n : ℝ) < b * x then
      Real.log (n : ℝ) else 0

noncomputable def primeIntervalThetaMoment (a b x : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
    if Nat.Prime n ∧ a * x ≤ (n : ℝ) ∧ (n : ℝ) < b * x then
      (n : ℝ) * Real.log (n : ℝ) else 0

theorem primeIntervalThetaMass_eq_strict (a b x : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hx : 0 < x) :
    primeIntervalThetaMass a b x =
      thetaStrictFinite (b * x) - thetaStrictFinite (a * x) := by
  classical
  have hax : 0 ≤ a * x := mul_nonneg ha hx.le
  have hbx : 0 ≤ b * x := mul_nonneg (le_trans ha (le_of_lt hab)) hx.le
  have habx : a * x ≤ b * x := mul_le_mul_of_nonneg_right (le_of_lt hab) hx.le
  have hterm (n : ℕ) :
      (if Nat.Prime n ∧ (n : ℝ) < b * x then Real.log (n : ℝ) else 0) -
      (if Nat.Prime n ∧ (n : ℝ) < a * x then Real.log (n : ℝ) else 0) =
      (if Nat.Prime n ∧ a * x ≤ (n : ℝ) ∧ (n : ℝ) < b * x then
        Real.log (n : ℝ) else 0) := by
    by_cases hp : Nat.Prime n
    · by_cases hlo : (n : ℝ) < a * x
      · have hhi : (n : ℝ) < b * x := lt_of_lt_of_le hlo habx
        simp [hp, hlo, hhi]
      · by_cases hhi : (n : ℝ) < b * x
        · simp [hp, hlo, hhi, le_of_not_gt hlo]
        · simp [hp, hlo, hhi]
    · simp [hp]
  calc
    primeIntervalThetaMass a b x =
        ∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
          ((if Nat.Prime n ∧ (n : ℝ) < b * x then Real.log (n : ℝ) else 0) -
            (if Nat.Prime n ∧ (n : ℝ) < a * x then Real.log (n : ℝ) else 0)) := by
          unfold primeIntervalThetaMass
          apply Finset.sum_congr rfl
          intro n hn
          exact (hterm n).symm
    _ = (∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
          if Nat.Prime n ∧ (n : ℝ) < b * x then Real.log (n : ℝ) else 0) -
        (∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
          if Nat.Prime n ∧ (n : ℝ) < a * x then Real.log (n : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = thetaStrictFinite (b * x) - thetaStrictFinite (a * x) := by
          rw [thetaStrictFinite_extend (a * x) (b * x) hax habx]
          rfl

theorem primeIntervalThetaMass_eq_atoms (a b x : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hx : 0 < x) :
    primeIntervalThetaMass a b x =
      Chebyshev.theta (b * x) - Chebyshev.theta (a * x) +
        endpointPrimeLogAtom (a * x) - endpointPrimeLogAtom (b * x) := by
  rw [primeIntervalThetaMass_eq_strict a b x ha hab hx,
    thetaStrictFinite_eq (b * x) (mul_nonneg (le_trans ha (le_of_lt hab)) hx.le),
    thetaStrictFinite_eq (a * x) (mul_nonneg ha hx.le)]
  ring

noncomputable def endpointPrimeMomentAtom (y : ℝ) : ℝ :=
  y * endpointPrimeLogAtom y

private theorem log_scaled_div_tendsto_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Real.log (c * x) / x) atTop (𝓝 0) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hc
  have hlog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hcomp := hlog.comp hcx
  have hscale : Tendsto
      (fun x : ℝ => c * (Real.log (c * x) / (c * x))) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hcomp)
  have heq : (fun x : ℝ => Real.log (c * x) / x) =ᶠ[atTop]
      (fun x : ℝ => c * (Real.log (c * x) / (c * x))) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne', hc.ne']
  exact hscale.congr' heq.symm

theorem endpointPrimeLogAtom_scaled_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => endpointPrimeLogAtom (c * x) / x) atTop (𝓝 0) := by
  have hlog := log_scaled_div_tendsto_zero c hc
  have hnorm : Tendsto (fun x : ℝ => ‖Real.log (c * x) / x‖) atTop (𝓝 0) := by
    simpa using hlog.norm
  have hneg : Tendsto (fun x : ℝ => -‖Real.log (c * x) / x‖) atTop (𝓝 0) := by
    simpa using hnorm.neg
  have hnormAtom : Tendsto
      (fun x : ℝ => ‖endpointPrimeLogAtom (c * x) / x‖) atTop (𝓝 0) := by
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hnorm ?_ ?_
    · filter_upwards [] with x
      calc
        -‖Real.log (c * x) / x‖ ≤ 0 := neg_nonpos.mpr (norm_nonneg _)
        _ ≤ ‖endpointPrimeLogAtom (c * x) / x‖ := norm_nonneg _
    · filter_upwards [] with x
      have hbound : ‖endpointPrimeLogAtom (c * x) / x‖ ≤
          ‖Real.log (c * x) / x‖ := by
        unfold endpointPrimeLogAtom
        by_cases h : Nat.Prime ⌊c * x⌋₊ ∧ (⌊c * x⌋₊ : ℝ) = c * x
        · simp [h]
        · simp [h]
          positivity
      exact hbound
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormAtom

theorem endpointPrimeMomentAtom_scaled_zero (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => endpointPrimeMomentAtom (c * x) / x ^ 2)
      atTop (𝓝 0) := by
  have hlog := log_scaled_div_tendsto_zero c hc
  have hbase : Tendsto
      (fun x : ℝ => c * (Real.log (c * x) / x)) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hlog)
  have heq : (fun x : ℝ => (c * x) * Real.log (c * x) / x ^ 2) =ᶠ[atTop]
      (fun x : ℝ => c * (Real.log (c * x) / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
    <;> ring
  have hbase' : Tendsto
      (fun x : ℝ => (c * x) * Real.log (c * x) / x ^ 2) atTop (𝓝 0) :=
    hbase.congr' heq.symm
  have hnorm : Tendsto
      (fun x : ℝ => ‖(c * x) * Real.log (c * x) / x ^ 2‖) atTop (𝓝 0) := by
    simpa using hbase'.norm
  have hnormAtom : Tendsto
      (fun x : ℝ => ‖endpointPrimeMomentAtom (c * x) / x ^ 2‖) atTop (𝓝 0) := by
    have hneg : Tendsto
        (fun x : ℝ => -‖(c * x) * Real.log (c * x) / x ^ 2‖) atTop (𝓝 0) := by
      simpa using hnorm.neg
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hnorm ?_ ?_
    · filter_upwards [] with x
      calc
        -‖(c * x) * Real.log (c * x) / x ^ 2‖ ≤ 0 := neg_nonpos.mpr (norm_nonneg _)
        _ ≤ ‖endpointPrimeMomentAtom (c * x) / x ^ 2‖ := norm_nonneg _
    · filter_upwards [] with x
      unfold endpointPrimeMomentAtom endpointPrimeLogAtom
      by_cases h : Nat.Prime ⌊c * x⌋₊ ∧ (⌊c * x⌋₊ : ℝ) = c * x
      · simp [h]
      · simp [h]
        positivity
  exact tendsto_zero_iff_norm_tendsto_zero.mpr hnormAtom

noncomputable def thetaMomentStrictFinite (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
    if Nat.Prime n ∧ (n : ℝ) < y then (n : ℝ) * Real.log (n : ℝ) else 0

noncomputable def primeThetaMoment (y : ℝ) : ℝ :=
  ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
    (n : ℝ) * (if Nat.Prime n then Real.log (n : ℝ) else 0)

theorem thetaMomentStrictFinite_eq (y : ℝ) (hy : 0 ≤ y) :
    thetaMomentStrictFinite y = primeThetaMoment y - endpointPrimeMomentAtom y := by
  classical
  unfold thetaMomentStrictFinite primeThetaMoment
  by_cases hEq : (⌊y⌋₊ : ℝ) = y
  · have hmem : ⌊y⌋₊ ∈ Finset.Icc 0 ⌊y⌋₊ := Finset.mem_Icc.mpr ⟨Nat.zero_le _, le_rfl⟩
    have hrest :
        (∑ n ∈ (Finset.Icc 0 ⌊y⌋₊).erase ⌊y⌋₊,
          if Nat.Prime n ∧ (n : ℝ) < y then (n : ℝ) * Real.log (n : ℝ) else 0) =
        ∑ n ∈ (Finset.Icc 0 ⌊y⌋₊).erase ⌊y⌋₊,
          if Nat.Prime n then (n : ℝ) * Real.log (n : ℝ) else 0 := by
      apply Finset.sum_congr rfl
      intro n hn
      have hn' : n ∈ Finset.Icc 0 ⌊y⌋₊ := Finset.mem_of_mem_erase hn
      have hne : n ≠ ⌊y⌋₊ := (Finset.mem_erase.mp hn).1
      have hn'' := Finset.mem_Icc.mp hn'
      have hlt : n < ⌊y⌋₊ := by omega
      have hltR : (n : ℝ) < y := by
        calc
          (n : ℝ) < (⌊y⌋₊ : ℝ) := by exact_mod_cast hlt
          _ = y := hEq
      simp [hltR]
    rw [← Finset.sum_erase_add _ _ hmem, ← Finset.sum_erase_add _ _ hmem, hrest]
    simp [endpointPrimeMomentAtom, endpointPrimeLogAtom, hEq]
  · have hfloor_lt : (⌊y⌋₊ : ℝ) < y := by
      apply lt_of_le_of_ne (Nat.floor_le hy)
      intro h
      exact hEq h
    have hsum :
        (∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
          (if Nat.Prime n ∧ (n : ℝ) < y then (n : ℝ) * Real.log (n : ℝ) else 0)) =
        ∑ n ∈ Finset.Icc 0 ⌊y⌋₊,
          (if Nat.Prime n then (n : ℝ) * Real.log (n : ℝ) else 0) := by
      apply Finset.sum_congr rfl
      intro n hn
      have hnle : (n : ℝ) ≤ (⌊y⌋₊ : ℝ) := Nat.cast_le.mpr (Finset.mem_Icc.mp hn).2
      simp [hnle.trans_lt hfloor_lt]
    rw [hsum]
    simp [endpointPrimeMomentAtom, endpointPrimeLogAtom, hEq]

theorem thetaMomentStrictFinite_extend (y z : ℝ) (hyz : y ≤ z) :
    thetaMomentStrictFinite y =
      ∑ n ∈ Finset.Icc 0 ⌊z⌋₊,
        if Nat.Prime n ∧ (n : ℝ) < y then
          (n : ℝ) * Real.log (n : ℝ) else 0 := by
  classical
  unfold thetaMomentStrictFinite
  apply Finset.sum_subset
  · exact Finset.Icc_subset_Icc_right (Nat.floor_mono hyz)
  · intro n hn hnz
    have hny : ⌊y⌋₊ < n := by
      exact lt_of_not_ge fun h => hnz (Finset.mem_Icc.mpr ⟨Nat.zero_le _, h⟩)
    have hnlt : y < (n : ℝ) := by
      have hnlo : (⌊y⌋₊ : ℝ) + 1 ≤ n := by exact_mod_cast Nat.succ_le_of_lt hny
      have hlt := Nat.lt_floor_add_one y
      linarith
    simp [not_lt_of_ge hnlt.le]

theorem primeIntervalThetaMoment_eq_strict (a b x : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hx : 0 < x) :
    primeIntervalThetaMoment a b x =
      thetaMomentStrictFinite (b * x) - thetaMomentStrictFinite (a * x) := by
  classical
  have hax : 0 ≤ a * x := mul_nonneg ha hx.le
  have hbx : 0 ≤ b * x := mul_nonneg (le_trans ha (le_of_lt hab)) hx.le
  have habx : a * x ≤ b * x := mul_le_mul_of_nonneg_right (le_of_lt hab) hx.le
  have hterm (n : ℕ) :
      (if Nat.Prime n ∧ (n : ℝ) < b * x then (n : ℝ) * Real.log (n : ℝ) else 0) -
      (if Nat.Prime n ∧ (n : ℝ) < a * x then (n : ℝ) * Real.log (n : ℝ) else 0) =
      (if Nat.Prime n ∧ a * x ≤ (n : ℝ) ∧ (n : ℝ) < b * x then
        (n : ℝ) * Real.log (n : ℝ) else 0) := by
    by_cases hp : Nat.Prime n
    · by_cases hlo : (n : ℝ) < a * x
      · have hhi : (n : ℝ) < b * x := lt_of_lt_of_le hlo habx
        simp [hp, hlo, hhi]
      · by_cases hhi : (n : ℝ) < b * x
        · simp [hp, hlo, hhi, le_of_not_gt hlo]
        · simp [hp, hlo, hhi]
    · simp [hp]
  calc
    primeIntervalThetaMoment a b x =
        ∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
          ((if Nat.Prime n ∧ (n : ℝ) < b * x then (n : ℝ) * Real.log (n : ℝ) else 0) -
            (if Nat.Prime n ∧ (n : ℝ) < a * x then (n : ℝ) * Real.log (n : ℝ) else 0)) := by
          unfold primeIntervalThetaMoment
          apply Finset.sum_congr rfl
          intro n hn
          exact (hterm n).symm
    _ = (∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
          if Nat.Prime n ∧ (n : ℝ) < b * x then
            (n : ℝ) * Real.log (n : ℝ) else 0) -
        (∑ n ∈ Finset.Icc 0 ⌊b * x⌋₊,
          if Nat.Prime n ∧ (n : ℝ) < a * x then
            (n : ℝ) * Real.log (n : ℝ) else 0) := by
          rw [Finset.sum_sub_distrib]
    _ = thetaMomentStrictFinite (b * x) - thetaMomentStrictFinite (a * x) := by
          rw [thetaMomentStrictFinite_extend (a * x) (b * x) habx]
          rfl

theorem primeIntervalThetaMoment_eq_atoms (a b x : ℝ)
    (ha : 0 ≤ a) (hab : a < b) (hx : 0 < x) :
    primeIntervalThetaMoment a b x =
      primeThetaMoment (b * x) - primeThetaMoment (a * x) +
        endpointPrimeMomentAtom (a * x) - endpointPrimeMomentAtom (b * x) := by
  rw [primeIntervalThetaMoment_eq_strict a b x ha hab hx,
    thetaMomentStrictFinite_eq (b * x) (mul_nonneg (le_trans ha (le_of_lt hab)) hx.le),
    thetaMomentStrictFinite_eq (a * x) (mul_nonneg ha hx.le)]
  ring

def singletonPrimeAffineProfile (q : PrimeAffinePiece) : PrimeAffineProfile where
  pieces := [q]

theorem singletonPrimeAffineProfile_eval (q : PrimeAffinePiece) (t : ℝ) :
    (singletonPrimeAffineProfile q).eval t =
      if (q.lo : ℝ) ≤ t ∧ t < (q.hi : ℝ) then
        (q.slope : ℝ) * t + (q.intercept : ℝ) else 0 := by
  simp [singletonPrimeAffineProfile, PrimeAffineProfile.eval]

theorem weightedPrimeSum_singleton_eq_finite (q : PrimeAffinePiece) (x : ℝ) (hx : 0 < x) :
    weightedPrimeSum (singletonPrimeAffineProfile q) x =
      ∑ n ∈ Finset.Icc 0 ⌊(q.hi : ℝ) * x⌋₊,
        if Nat.Prime n ∧ (q.lo : ℝ) * x ≤ (n : ℝ) ∧
            (n : ℝ) < (q.hi : ℝ) * x then
          ((q.slope : ℝ) * ((n : ℝ) / x) + (q.intercept : ℝ)) *
            Real.log (n : ℝ) else 0 := by
  classical
  have hzero : ∀ n ∉ Finset.Icc 0 ⌊(q.hi : ℝ) * x⌋₊,
      (if Nat.Prime n then
        (singletonPrimeAffineProfile q).eval ((n : ℝ) / x) * Real.log (n : ℝ)
       else 0) = 0 := by
    intro n hn
    have hnle : ¬ n ≤ ⌊(q.hi : ℝ) * x⌋₊ := by
      intro hle
      exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hle⟩)
    have hfloor_lt : ⌊(q.hi : ℝ) * x⌋₊ < n := Nat.lt_of_not_ge hnle
    have hnlo : ((q.hi : ℝ) * x) < (n : ℝ) := by
      have hcast : (⌊(q.hi : ℝ) * x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
        exact_mod_cast Nat.succ_le_of_lt hfloor_lt
      linarith [Nat.lt_floor_add_one ((q.hi : ℝ) * x)]
    have hnot : ¬ ((q.lo : ℝ) ≤ (n : ℝ) / x ∧ (n : ℝ) / x < (q.hi : ℝ)) := by
      intro h
      have hupper := (div_lt_iff₀ hx).mp h.2
      linarith
    rw [singletonPrimeAffineProfile_eval]
    simp [hnot]
  unfold weightedPrimeSum
  rw [tsum_eq_sum hzero]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : Nat.Prime n
  · rw [if_pos hp, singletonPrimeAffineProfile_eval]
    have hlo : (q.lo : ℝ) ≤ (n : ℝ) / x ↔ (q.lo : ℝ) * x ≤ (n : ℝ) :=
      le_div_iff₀ hx
    have hhi : (n : ℝ) / x < (q.hi : ℝ) ↔ (n : ℝ) < (q.hi : ℝ) * x :=
      div_lt_iff₀ hx
    simp [hlo, hhi, hp]
  · simp [hp]

theorem weightedPrimeSum_singleton_eq_moments (q : PrimeAffinePiece) (x : ℝ) (hx : 0 < x) :
    weightedPrimeSum (singletonPrimeAffineProfile q) x =
      ((q.slope : ℝ) / x) * primeIntervalThetaMoment (q.lo : ℝ) (q.hi : ℝ) x +
        (q.intercept : ℝ) * primeIntervalThetaMass (q.lo : ℝ) (q.hi : ℝ) x := by
  rw [weightedPrimeSum_singleton_eq_finite q x hx]
  unfold primeIntervalThetaMoment primeIntervalThetaMass
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro n hn
  split_ifs <;> field_simp [hx.ne'] <;> ring

theorem weightedPrimeSum_singleton_eq_theta_atoms (q : PrimeAffinePiece) (x : ℝ) (hx : 0 < x) :
    weightedPrimeSum (singletonPrimeAffineProfile q) x =
      ((q.slope : ℝ) / x) *
          (primeThetaMoment ((q.hi : ℝ) * x) - primeThetaMoment ((q.lo : ℝ) * x) +
            endpointPrimeMomentAtom ((q.lo : ℝ) * x) -
              endpointPrimeMomentAtom ((q.hi : ℝ) * x)) +
        (q.intercept : ℝ) *
          (Chebyshev.theta ((q.hi : ℝ) * x) - Chebyshev.theta ((q.lo : ℝ) * x) +
            endpointPrimeLogAtom ((q.lo : ℝ) * x) -
              endpointPrimeLogAtom ((q.hi : ℝ) * x)) := by
  rw [weightedPrimeSum_singleton_eq_moments q x hx,
    primeIntervalThetaMoment_eq_atoms (q.lo : ℝ) (q.hi : ℝ) x
      (by exact_mod_cast q.lo_pos.le) (by exact_mod_cast q.lo_lt_hi) hx,
    primeIntervalThetaMass_eq_atoms (q.lo : ℝ) (q.hi : ℝ) x
      (by exact_mod_cast q.lo_pos.le) (by exact_mod_cast q.lo_lt_hi) hx]
private noncomputable def weightedPrimeTerm (pieces : List PrimeAffinePiece)
    (x : ℝ) (n : ℕ) : ℝ :=
  if Nat.Prime n then (PrimeAffineProfile.mk pieces).eval ((n : ℝ) / x) * Real.log (n : ℝ)
  else 0

private theorem weightedPrimeTerm_singleton_summable
    (q : PrimeAffinePiece) (x : ℝ) (hx : 0 < x) :
    Summable (weightedPrimeTerm [q] x) := by
  classical
  apply summable_of_ne_finset_zero (s := Finset.Icc 0 ⌊(q.hi : ℝ) * x⌋₊)
  intro n hn
  have hnle : ¬ n ≤ ⌊(q.hi : ℝ) * x⌋₊ := by
    intro hle
    exact hn (Finset.mem_Icc.mpr ⟨Nat.zero_le _, hle⟩)
  have hfloor_lt : ⌊(q.hi : ℝ) * x⌋₊ < n := Nat.lt_of_not_ge hnle
  have hnlo : ((q.hi : ℝ) * x) < (n : ℝ) := by
    have hcast : (⌊(q.hi : ℝ) * x⌋₊ : ℝ) + 1 ≤ (n : ℝ) := by
      exact_mod_cast Nat.succ_le_of_lt hfloor_lt
    linarith [Nat.lt_floor_add_one ((q.hi : ℝ) * x)]
  have hnot : ¬ ((q.lo : ℝ) ≤ (n : ℝ) / x ∧ (n : ℝ) / x < (q.hi : ℝ)) := by
    intro h
    have hupper := (div_lt_iff₀ hx).mp h.2
    linarith
  rw [weightedPrimeTerm]
  by_cases hp : Nat.Prime n
  · simp [hp, PrimeAffineProfile.eval, hnot]
  · simp [hp]

private theorem weightedPrimeTerm_summable
    (pieces : List PrimeAffinePiece) (x : ℝ) (hx : 0 < x) :
    Summable (weightedPrimeTerm pieces x) := by
  induction pieces with
  | nil =>
      apply summable_of_ne_finset_zero (s := ∅)
      intro n hn
      simp [weightedPrimeTerm, PrimeAffineProfile.eval]
  | cons q qs ih =>
      have hsingle := weightedPrimeTerm_singleton_summable q x hx
      have hsplit : weightedPrimeTerm (q :: qs) x =
          (fun n => weightedPrimeTerm [q] x n + weightedPrimeTerm qs x n) := by
        funext n
        by_cases hp : Nat.Prime n
        · by_cases hq : (q.lo : ℝ) ≤ (n : ℝ) / x ∧ (n : ℝ) / x < (q.hi : ℝ)
          · simp [weightedPrimeTerm, PrimeAffineProfile.eval, hp, hq]
            ring
          · simp [weightedPrimeTerm, PrimeAffineProfile.eval, hp, hq]
        · simp [weightedPrimeTerm, hp]
      rw [hsplit]
      exact hsingle.add ih

theorem weightedPrimeSum_list_eq_singletons
    (pieces : List PrimeAffinePiece) (x : ℝ) (hx : 0 < x) :
    weightedPrimeSum (PrimeAffineProfile.mk pieces) x =
      (pieces.map fun q => weightedPrimeSum (singletonPrimeAffineProfile q) x).sum := by
  induction pieces with
  | nil =>
      simp [weightedPrimeSum, PrimeAffineProfile.eval]
  | cons q qs ih =>
      have hsingle := weightedPrimeTerm_singleton_summable q x hx
      have htail := weightedPrimeTerm_summable qs x hx
      have hsplit : weightedPrimeTerm (q :: qs) x =
          (fun n => weightedPrimeTerm [q] x n + weightedPrimeTerm qs x n) := by
        funext n
        by_cases hp : Nat.Prime n
        · by_cases hq : (q.lo : ℝ) ≤ (n : ℝ) / x ∧ (n : ℝ) / x < (q.hi : ℝ)
          · simp [weightedPrimeTerm, PrimeAffineProfile.eval, hp, hq]
            ring
          · simp [weightedPrimeTerm, PrimeAffineProfile.eval, hp, hq]
        · simp [weightedPrimeTerm, hp]
      calc
        weightedPrimeSum (PrimeAffineProfile.mk (q :: qs)) x =
            ∑' n, weightedPrimeTerm (q :: qs) x n := rfl
        _ = ∑' n, (weightedPrimeTerm [q] x n + weightedPrimeTerm qs x n) := by
              rw [hsplit]
        _ = (∑' n, weightedPrimeTerm [q] x n) +
            (∑' n, weightedPrimeTerm qs x n) := hsingle.tsum_add htail
        _ = weightedPrimeSum (singletonPrimeAffineProfile q) x +
            weightedPrimeSum (PrimeAffineProfile.mk qs) x := rfl
        _ = weightedPrimeSum (singletonPrimeAffineProfile q) x +
            (qs.map fun r => weightedPrimeSum (singletonPrimeAffineProfile r) x).sum := by
              rw [ih]
        _ = ((q :: qs).map fun r =>
            weightedPrimeSum (singletonPrimeAffineProfile r) x).sum := by
              simp [List.map_cons, List.sum_cons]

private noncomputable def primeLogCoeff (n : ℕ) : ℝ :=
  if Nat.Prime n then Real.log (n : ℝ) else 0

private theorem primeLogCoeff_sum (y : ℝ) :
    (∑ n ∈ Finset.Icc 0 ⌊y⌋₊, primeLogCoeff n) = Chebyshev.theta y := by
  rw [Chebyshev.theta_eq_sum_Icc]
  simp only [primeLogCoeff, Finset.sum_filter]

theorem primeThetaMoment_eq_partial_summation (y : ℝ) (hy : 0 ≤ y) :
    primeThetaMoment y = y * Chebyshev.theta y - ∫ t in Set.Ioc 0 y, Chebyshev.theta t := by
  have hdiff : ∀ t ∈ Set.Icc (0 : ℝ) y, DifferentiableAt ℝ (fun u => u) t := by
    intro t ht
    exact differentiableAt_id
  have hint : IntegrableOn (deriv (fun u : ℝ => u)) (Set.Icc 0 y) := by
    simpa using (integrableOn_const (s := Set.Icc (0 : ℝ) y) (C := (1 : ℝ)))
  calc
    primeThetaMoment y =
        ∑ n ∈ Finset.Icc 0 ⌊y⌋₊, (n : ℝ) * primeLogCoeff n := by
          rfl
    _ = y * (∑ n ∈ Finset.Icc 0 ⌊y⌋₊, primeLogCoeff n) -
        ∫ t in Set.Ioc 0 y, deriv (fun u : ℝ => u) t *
          (∑ n ∈ Finset.Icc 0 ⌊t⌋₊, primeLogCoeff n) := by
          exact sum_mul_eq_sub_integral_mul (c := primeLogCoeff) hy hdiff hint
    _ = y * Chebyshev.theta y - ∫ t in Set.Ioc 0 y, Chebyshev.theta t := by
      rw [primeLogCoeff_sum]
      congr 1
      apply integral_congr_ae
      filter_upwards [] with t
      simp [primeLogCoeff_sum]

private theorem hPNT_theta_linear_bounds (hpnt : hPNT) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ T : ℝ, 1 ≤ T ∧ ∀ t : ℝ, T ≤ t →
      (1 - ε) * t ≤ Chebyshev.theta t ∧
      Chebyshev.theta t ≤ (1 + ε) * t := by
  have hratio := (Metric.tendsto_nhds.mp hpnt) ε hε
  have habs : ∀ᶠ t : ℝ in atTop,
      |Chebyshev.theta t / t - 1| < ε := by
    filter_upwards [hratio] with t ht
    simpa [Real.dist_eq, abs_sub_comm] using ht
  obtain ⟨T, hT⟩ := Filter.eventually_atTop.mp habs
  refine ⟨max T 1, le_max_right T 1, ?_⟩
  intro t ht
  have hsmall := hT t (le_trans (le_max_left T 1) ht)
  have htpos : 0 < t := lt_of_lt_of_le zero_lt_one
    (le_trans (le_max_right T 1) ht)
  have hab := abs_lt.mp hsmall
  have hlow : 1 - ε < Chebyshev.theta t / t := by linarith
  have hupp : Chebyshev.theta t / t < 1 + ε := by linarith
  constructor
  · exact le_of_lt ((lt_div_iff₀ htpos).mp hlow)
  · exact le_of_lt ((div_lt_iff₀ htpos).mp hupp)

/- The Cesaro average of theta follows by splitting off a fixed initial interval
and comparing the remaining integral with the integral of `(1 ± ε) * t`. -/
private theorem thetaIntegral_tendsto_half (hpnt : hPNT) :
    Tendsto (fun y : ℝ => (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2)
      atTop (𝓝 (1 / 2 : ℝ)) := by
  have hinv : Tendsto (fun y : ℝ => y⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hinv2 : Tendsto (fun y : ℝ => (y ^ 2)⁻¹) atTop (𝓝 0) := by
    simpa [one_div, pow_two] using hinv.pow 2
  refine tendsto_order.mpr ⟨?_, ?_⟩
  · intro a ha
    let ε : ℝ := min (1 / 2) ((1 / 2 - a) / 2)
    have hεpos : 0 < ε := by
      dsimp [ε]
      positivity
    have hεlt : ε < 1 := by
      dsimp [ε]
      have : 0 < 1 / 2 - a := by linarith
      linarith [min_le_left (1 / 2 : ℝ) ((1 / 2 - a) / 2)]
    obtain ⟨T, hT, htheta⟩ := hPNT_theta_linear_bounds hpnt hεpos
    let K : ℝ := T * Chebyshev.theta T
    let low : ℝ → ℝ := fun y =>
      ((1 - ε) * (y ^ 2 - T ^ 2) / 2) / y ^ 2
    have hlowLim : Tendsto low atTop (𝓝 ((1 - ε) / 2)) := by
      have hfac : Tendsto (fun y : ℝ => 1 - T ^ 2 / y ^ 2) atTop (𝓝 1) := by
        have hquot : Tendsto (fun y : ℝ => T ^ 2 / y ^ 2) atTop (𝓝 0) := by
          simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv2)
        simpa using tendsto_const_nhds.sub hquot
      have hlim : Tendsto
          (fun y : ℝ => ((1 - ε) / 2) * (1 - T ^ 2 / y ^ 2)) atTop
          (𝓝 ((1 - ε) / 2)) := by
        simpa using tendsto_const_nhds.mul hfac
      have heq : low =ᶠ[atTop]
          (fun y : ℝ => ((1 - ε) / 2) * (1 - T ^ 2 / y ^ 2)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        dsimp [low]
        field_simp [hy.ne']
        <;> ring
      exact hlim.congr' heq.symm
    have haLow : a < (1 - ε) / 2 := by
      dsimp [ε]
      have hδ : 0 < 1 / 2 - a := by linarith
      have hεle : min (1 / 2 : ℝ) ((1 / 2 - a) / 2) ≤ (1 / 2 - a) / 2 := min_le_right _ _
      nlinarith
    have heventLow : ∀ᶠ y : ℝ in atTop, a < low y :=
      (tendsto_order.mp hlowLim).1 a haLow
    have heventBound : ∀ᶠ y : ℝ in atTop,
        low y ≤ (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2 := by
      filter_upwards [Filter.eventually_atTop.2 ⟨T, fun y hy => hy⟩] with y hy
      have hypos : 0 < y := lt_of_lt_of_le (by linarith) hy
      have htheta0T : IntervalIntegrable Chebyshev.theta volume 0 T :=
        Chebyshev.theta_mono.intervalIntegrable
      have hthetaTy : IntervalIntegrable Chebyshev.theta volume T y :=
        Chebyshev.theta_mono.intervalIntegrable
      have hlowMono : Monotone (fun t : ℝ => (1 - ε) * t) := by
        intro u v huv
        exact mul_le_mul_of_nonneg_left huv (by linarith)
      have hlowInt : IntervalIntegrable (fun t : ℝ => (1 - ε) * t) volume T y :=
        hlowMono.intervalIntegrable
      have hTailLower := intervalIntegral.integral_mono_on hy hlowInt hthetaTy
        (fun t ht => (htheta t ht.1).1)
      have hTailLower' : (1 - ε) * (y ^ 2 - T ^ 2) / 2 ≤
          ∫ t in T..y, Chebyshev.theta t := by
        calc
          (1 - ε) * (y ^ 2 - T ^ 2) / 2 =
              ∫ t in T..y, (1 - ε) * t := by
                rw [intervalIntegral.integral_const_mul, integral_id]
                ring
          _ ≤ ∫ t in T..y, Chebyshev.theta t := hTailLower
      have hHeadLower : 0 ≤ ∫ t in (0 : ℝ)..T, Chebyshev.theta t :=
        intervalIntegral.integral_nonneg (by linarith) (fun t ht => Chebyshev.theta_nonneg t)
      have hsplit := intervalIntegral.integral_add_adjacent_intervals htheta0T hthetaTy
      have hfullLower : (1 - ε) * (y ^ 2 - T ^ 2) / 2 ≤
          ∫ t in (0 : ℝ)..y, Chebyshev.theta t := by
        rw [← hsplit]
        linarith
      have hdiv := div_le_div_of_nonneg_right hfullLower (sq_nonneg y)
      calc
        low y = ((1 - ε) * (y ^ 2 - T ^ 2) / 2) / y ^ 2 := rfl
        _ ≤ (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2 := hdiv
    filter_upwards [heventLow, heventBound] with y hLow hBound
    exact lt_of_lt_of_le hLow hBound
  · intro b hb
    let ε : ℝ := min (1 / 2) ((b - 1 / 2) / 2)
    have hεpos : 0 < ε := by
      dsimp [ε]
      positivity
    have hεlt : ε < 1 := by
      dsimp [ε]
      have : 0 < b - 1 / 2 := by linarith
      linarith [min_le_left (1 / 2 : ℝ) ((b - 1 / 2) / 2)]
    obtain ⟨T, hT, htheta⟩ := hPNT_theta_linear_bounds hpnt hεpos
    let K : ℝ := T * Chebyshev.theta T
    let high : ℝ → ℝ := fun y =>
      (K + (1 + ε) * (y ^ 2 - T ^ 2) / 2) / y ^ 2
    have hinvK : Tendsto (fun y : ℝ => K / y ^ 2) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv2)
    have hfac : Tendsto (fun y : ℝ => 1 - T ^ 2 / y ^ 2) atTop (𝓝 1) := by
      have hquot : Tendsto (fun y : ℝ => T ^ 2 / y ^ 2) atTop (𝓝 0) := by
        simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hinv2)
      simpa using tendsto_const_nhds.sub hquot
    have hscaled : Tendsto
        (fun y : ℝ => ((1 + ε) / 2) * (1 - T ^ 2 / y ^ 2)) atTop
        (𝓝 ((1 + ε) / 2)) := by
      simpa using tendsto_const_nhds.mul hfac
    have hhighLim : Tendsto high atTop (𝓝 ((1 + ε) / 2)) := by
      have hlim : Tendsto
          (fun y : ℝ => K / y ^ 2 + ((1 + ε) / 2) * (1 - T ^ 2 / y ^ 2))
          atTop (𝓝 ((1 + ε) / 2)) := by
        simpa using hinvK.add hscaled
      have heq : high =ᶠ[atTop]
          (fun y : ℝ => K / y ^ 2 + ((1 + ε) / 2) * (1 - T ^ 2 / y ^ 2)) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
        dsimp [high]
        field_simp [hy.ne']
        <;> ring
      exact hlim.congr' heq.symm
    have hUpperLim : (1 + ε) / 2 < b := by
      dsimp [ε]
      have hδ : 0 < b - 1 / 2 := by linarith
      have hεle : min (1 / 2 : ℝ) ((b - 1 / 2) / 2) ≤ (b - 1 / 2) / 2 := min_le_right _ _
      nlinarith
    have heventHigh : ∀ᶠ y : ℝ in atTop, high y < b :=
      (tendsto_order.mp hhighLim).2 b hUpperLim
    have heventBound : ∀ᶠ y : ℝ in atTop,
        (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2 ≤ high y := by
      filter_upwards [Filter.eventually_atTop.2 ⟨T, fun y hy => hy⟩] with y hy
      have hypos : 0 < y := lt_of_lt_of_le (by linarith) hy
      have htheta0T : IntervalIntegrable Chebyshev.theta volume 0 T :=
        Chebyshev.theta_mono.intervalIntegrable
      have hthetaTy : IntervalIntegrable Chebyshev.theta volume T y :=
        Chebyshev.theta_mono.intervalIntegrable
      have huppMono : Monotone (fun t : ℝ => (1 + ε) * t) := by
        intro u v huv
        exact mul_le_mul_of_nonneg_left huv (by linarith)
      have huppInt : IntervalIntegrable (fun t : ℝ => (1 + ε) * t) volume T y :=
        huppMono.intervalIntegrable
      have hTailUpper := intervalIntegral.integral_mono_on hy hthetaTy huppInt
        (fun t ht => (htheta t ht.1).2)
      have hTailUpper' : ∫ t in T..y, Chebyshev.theta t ≤
          (1 + ε) * (y ^ 2 - T ^ 2) / 2 := by
        calc
          ∫ t in T..y, Chebyshev.theta t ≤ ∫ t in T..y, (1 + ε) * t := hTailUpper
          _ = (1 + ε) * (y ^ 2 - T ^ 2) / 2 := by
                rw [intervalIntegral.integral_const_mul, integral_id]
                ring
      have hheadUpper : ∫ t in (0 : ℝ)..T, Chebyshev.theta t ≤ K := by
        calc
          ∫ t in (0 : ℝ)..T, Chebyshev.theta t ≤ ∫ _t in (0 : ℝ)..T, Chebyshev.theta T := by
            apply intervalIntegral.integral_mono_on (by linarith) htheta0T intervalIntegrable_const
            intro t ht
            exact Chebyshev.theta_mono ht.2
          _ = K := by
            simp [K, intervalIntegral.integral_const, smul_eq_mul]
      have hsplit := intervalIntegral.integral_add_adjacent_intervals htheta0T hthetaTy
      have hfullUpper : ∫ t in (0 : ℝ)..y, Chebyshev.theta t ≤
          K + (1 + ε) * (y ^ 2 - T ^ 2) / 2 := by
        rw [← hsplit]
        linarith
      have hdiv := div_le_div_of_nonneg_right hfullUpper (sq_nonneg y)
      calc
        (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2 =
            (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2 := rfl
        _ ≤ (K + (1 + ε) * (y ^ 2 - T ^ 2) / 2) / y ^ 2 := hdiv
        _ = high y := rfl
    filter_upwards [heventHigh, heventBound] with y hHigh hBound
    exact lt_of_le_of_lt hBound hHigh

private theorem primeThetaMoment_div_sq_tendsto_half (hpnt : hPNT) :
    Tendsto (fun y : ℝ => primeThetaMoment y / y ^ 2) atTop (𝓝 (1 / 2 : ℝ)) := by
  have hmain : Tendsto
      (fun y : ℝ => Chebyshev.theta y / y -
        (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2)
      atTop (𝓝 (1 - 1 / 2 : ℝ)) := by
    exact hpnt.sub (thetaIntegral_tendsto_half hpnt)
  have heq : (fun y : ℝ => primeThetaMoment y / y ^ 2) =ᶠ[atTop]
      (fun y : ℝ => Chebyshev.theta y / y -
        (∫ t in (0 : ℝ)..y, Chebyshev.theta t) / y ^ 2) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with y hy
    rw [primeThetaMoment_eq_partial_summation y (le_of_lt hy)]
    rw [← intervalIntegral.integral_of_le (le_of_lt hy)]
    field_simp [hy.ne']
    <;> ring
  have hlim := hmain.congr' heq.symm
  have htarget : (1 - 1 / 2 : ℝ) = 1 / 2 := by norm_num
  rw [htarget] at hlim
  exact hlim

/-- The prime first moment has its expected quadratic asymptotic under `hPNT`. -/
theorem primeThetaMoment_scaled_limit (hpnt : hPNT) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => primeThetaMoment (c * x) / x ^ 2)
      atTop (𝓝 (c ^ 2 / 2)) := by
  have hcx : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    tendsto_id.const_mul_atTop hc
  have hmoment := (primeThetaMoment_div_sq_tendsto_half hpnt).comp hcx
  have hscaled : Tendsto
      (fun x : ℝ => c ^ 2 * (primeThetaMoment (c * x) / (c * x) ^ 2))
      atTop (𝓝 (c ^ 2 / 2)) := by
    simpa [div_eq_mul_inv] using (tendsto_const_nhds.mul hmoment)
  have heq : (fun x : ℝ => primeThetaMoment (c * x) / x ^ 2) =ᶠ[atTop]
      (fun x : ℝ => c ^ 2 * (primeThetaMoment (c * x) / (c * x) ^ 2)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne', hc.ne']
    <;> ring
  exact hscaled.congr' heq.symm

theorem singletonPrimeAffineProfile_integral (q : PrimeAffinePiece) :
    (∫ t : ℝ, (singletonPrimeAffineProfile q).eval t) =
      ((q.slope : ℝ) * (((q.hi : ℝ) ^ 2 - (q.lo : ℝ) ^ 2) / 2)) +
        (q.intercept : ℝ) * ((q.hi : ℝ) - (q.lo : ℝ)) := by
  have heval : (fun t : ℝ => (singletonPrimeAffineProfile q).eval t) =
      Set.indicator (Set.Ico (q.lo : ℝ) (q.hi : ℝ))
        (fun t : ℝ => (q.slope : ℝ) * t + (q.intercept : ℝ)) := by
    funext t
    by_cases h : (q.lo : ℝ) ≤ t ∧ t < (q.hi : ℝ)
    · simp [singletonPrimeAffineProfile_eval, h, Set.mem_Ico]
    · simp [singletonPrimeAffineProfile_eval, h, Set.mem_Ico]
  rw [heval, MeasureTheory.integral_indicator measurableSet_Ico,
    MeasureTheory.integral_Ico_eq_integral_Ioc]
  have hle : (q.lo : ℝ) ≤ (q.hi : ℝ) := by exact_mod_cast q.lo_lt_hi.le
  rw [← intervalIntegral.integral_of_le hle]
  have hid : IntervalIntegrable (fun t : ℝ => t) volume (q.lo : ℝ) (q.hi : ℝ) :=
    continuous_id.intervalIntegrable _ _
  have hlin : IntervalIntegrable (fun t : ℝ => (q.slope : ℝ) * t) volume
      (q.lo : ℝ) (q.hi : ℝ) := hid.const_mul (q.slope : ℝ)
  have hc : IntervalIntegrable (fun _ : ℝ => (q.intercept : ℝ)) volume
      (q.lo : ℝ) (q.hi : ℝ) := intervalIntegrable_const
  have hsum : (fun t : ℝ => (q.slope : ℝ) * t + (q.intercept : ℝ)) =
      (fun t : ℝ => (q.slope : ℝ) * t) + (fun _ : ℝ => (q.intercept : ℝ)) := by
    funext t
    rfl
  calc
    (∫ t : ℝ in (q.lo : ℝ)..(q.hi : ℝ),
        (q.slope : ℝ) * t + (q.intercept : ℝ)) =
        (∫ t : ℝ in (q.lo : ℝ)..(q.hi : ℝ), (q.slope : ℝ) * t) +
          (∫ t : ℝ in (q.lo : ℝ)..(q.hi : ℝ), (q.intercept : ℝ)) := by
            rw [hsum]
            exact intervalIntegral.integral_add hlin hc
    _ = ((q.slope : ℝ) * (((q.hi : ℝ) ^ 2 - (q.lo : ℝ) ^ 2) / 2)) +
          (q.intercept : ℝ) * ((q.hi : ℝ) - (q.lo : ℝ)) := by
            rw [intervalIntegral.integral_const_mul, integral_id,
              intervalIntegral.integral_const]
            simp only [smul_eq_mul]
            ring

theorem PrimeAffineProfile.eval_cons (q : PrimeAffinePiece)
    (qs : List PrimeAffinePiece) (t : ℝ) :
    (PrimeAffineProfile.mk (q :: qs)).eval t =
      (singletonPrimeAffineProfile q).eval t + (PrimeAffineProfile.mk qs).eval t := by
  simp [PrimeAffineProfile.eval, singletonPrimeAffineProfile]

private theorem singletonPrimeAffineProfile_eval_integrable (q : PrimeAffinePiece) :
    Integrable (fun t : ℝ => (singletonPrimeAffineProfile q).eval t) := by
  rw [show (fun t : ℝ => (singletonPrimeAffineProfile q).eval t) =
      Set.indicator (Set.Ico (q.lo : ℝ) (q.hi : ℝ))
        (fun t : ℝ => (q.slope : ℝ) * t + (q.intercept : ℝ)) from by
        funext t
        by_cases h : (q.lo : ℝ) ≤ t ∧ t < (q.hi : ℝ)
        · simp [singletonPrimeAffineProfile_eval, h, Set.mem_Ico]
        · simp [singletonPrimeAffineProfile_eval, h, Set.mem_Ico]]
  have hcont : Continuous (fun t : ℝ => (q.slope : ℝ) * t + (q.intercept : ℝ)) :=
    continuous_const.mul continuous_id |>.add continuous_const
  have hIco : IntegrableOn
      (fun t : ℝ => (q.slope : ℝ) * t + (q.intercept : ℝ))
      (Set.Ico (q.lo : ℝ) (q.hi : ℝ)) volume := by
    exact hcont.continuousOn.integrableOn_compact isCompact_Icc |>.mono_set
      Set.Ico_subset_Icc_self
  exact hIco.integrable_indicator measurableSet_Ico

private theorem primeAffineProfile_eval_integrable (pieces : List PrimeAffinePiece) :
    Integrable (fun t : ℝ => (PrimeAffineProfile.mk pieces).eval t) := by
  induction pieces with
  | nil =>
      simp [PrimeAffineProfile.eval]
  | cons q qs ih =>
      have hsplit : (fun t : ℝ => (PrimeAffineProfile.mk (q :: qs)).eval t) =
          (fun t : ℝ => (singletonPrimeAffineProfile q).eval t) +
            (fun t : ℝ => (PrimeAffineProfile.mk qs).eval t) := by
        funext t
        exact PrimeAffineProfile.eval_cons q qs t
      rw [hsplit]
      exact singletonPrimeAffineProfile_eval_integrable q |>.add ih

theorem primeAffineProfile_integral_eq_sum_singletons (pieces : List PrimeAffinePiece) :
    (∫ t : ℝ, (PrimeAffineProfile.mk pieces).eval t) =
      (pieces.map fun q => ∫ t : ℝ, (singletonPrimeAffineProfile q).eval t).sum := by
  induction pieces with
  | nil =>
      simp [PrimeAffineProfile.eval]
  | cons q qs ih =>
      have hq := singletonPrimeAffineProfile_eval_integrable q
      have htail := primeAffineProfile_eval_integrable qs
      have hsplit : (fun t : ℝ => (PrimeAffineProfile.mk (q :: qs)).eval t) =
          (fun t : ℝ => (singletonPrimeAffineProfile q).eval t) +
            (fun t : ℝ => (PrimeAffineProfile.mk qs).eval t) := by
        funext t
        exact PrimeAffineProfile.eval_cons q qs t
      calc
        (∫ t : ℝ, (PrimeAffineProfile.mk (q :: qs)).eval t) =
            ∫ t : ℝ, ((singletonPrimeAffineProfile q).eval t +
              (PrimeAffineProfile.mk qs).eval t) := by
                simp only [PrimeAffineProfile.eval_cons]
        _ = (∫ t : ℝ, (singletonPrimeAffineProfile q).eval t) +
            (∫ t : ℝ, (PrimeAffineProfile.mk qs).eval t) :=
              MeasureTheory.integral_add hq htail
        _ = (∫ t : ℝ, (singletonPrimeAffineProfile q).eval t) +
            (qs.map fun r => ∫ t : ℝ, (singletonPrimeAffineProfile r).eval t).sum := by
              rw [ih]
        _ = ((q :: qs).map fun r => ∫ t : ℝ, (singletonPrimeAffineProfile r).eval t).sum := by
              simp [List.map_cons, List.sum_cons]

/- The singleton identity retains the literal half-open weighted sum, including
the lower and upper endpoint atoms, before taking the limit. -/
theorem weightedPrimeSum_singleton_limit (hpnt : hPNT) (q : PrimeAffinePiece) :
    Tendsto
      (fun x : ℝ => weightedPrimeSum (singletonPrimeAffineProfile q) x / x)
      atTop
      (𝓝 (((q.slope : ℝ) * (((q.hi : ℝ) ^ 2 - (q.lo : ℝ) ^ 2) / 2)) +
        (q.intercept : ℝ) * ((q.hi : ℝ) - (q.lo : ℝ)))) := by
  let a : ℝ := q.lo
  let b : ℝ := q.hi
  have ha : 0 < a := by
    dsimp [a]
    exact_mod_cast q.lo_pos
  have hb : 0 < b := by
    dsimp [b]
    exact_mod_cast lt_trans q.lo_pos q.lo_lt_hi
  have hthetaB := hPNT_theta_scaled hpnt b hb
  have hthetaA := hPNT_theta_scaled hpnt a ha
  have hlogAtomA := endpointPrimeLogAtom_scaled_zero a ha
  have hlogAtomB := endpointPrimeLogAtom_scaled_zero b hb
  have hmass : Tendsto
      (fun x : ℝ => (Chebyshev.theta (b * x) - Chebyshev.theta (a * x) +
        endpointPrimeLogAtom (a * x) - endpointPrimeLogAtom (b * x)) / x)
      atTop (𝓝 (b - a)) := by
    have hratio := (hthetaB.sub hthetaA).add (hlogAtomA.sub hlogAtomB)
    have heq : (fun x : ℝ =>
        (Chebyshev.theta (b * x) - Chebyshev.theta (a * x) +
          endpointPrimeLogAtom (a * x) - endpointPrimeLogAtom (b * x)) / x) =ᶠ[atTop]
        (fun x : ℝ => Chebyshev.theta (b * x) / x - Chebyshev.theta (a * x) / x +
          (endpointPrimeLogAtom (a * x) / x - endpointPrimeLogAtom (b * x) / x)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
      <;> ring
    have htarget : (b - a) + (0 - 0 : ℝ) = b - a := by ring
    rw [htarget] at hratio
    exact hratio.congr' heq.symm
  have hmomentB := primeThetaMoment_scaled_limit hpnt b hb
  have hmomentA := primeThetaMoment_scaled_limit hpnt a ha
  have hmomentAtomA := endpointPrimeMomentAtom_scaled_zero a ha
  have hmomentAtomB := endpointPrimeMomentAtom_scaled_zero b hb
  have hmoment : Tendsto
      (fun x : ℝ => (primeThetaMoment (b * x) - primeThetaMoment (a * x) +
        endpointPrimeMomentAtom (a * x) - endpointPrimeMomentAtom (b * x)) / x ^ 2)
      atTop (𝓝 ((b ^ 2 - a ^ 2) / 2)) := by
    have hratio := (hmomentB.sub hmomentA).add (hmomentAtomA.sub hmomentAtomB)
    have heq : (fun x : ℝ =>
        (primeThetaMoment (b * x) - primeThetaMoment (a * x) +
          endpointPrimeMomentAtom (a * x) - endpointPrimeMomentAtom (b * x)) / x ^ 2) =ᶠ[atTop]
        (fun x : ℝ => primeThetaMoment (b * x) / x ^ 2 - primeThetaMoment (a * x) / x ^ 2 +
          (endpointPrimeMomentAtom (a * x) / x ^ 2 - endpointPrimeMomentAtom (b * x) / x ^ 2)) := by
      filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
      field_simp [hx.ne']
      <;> ring
    have htarget : (b ^ 2 / 2 - a ^ 2 / 2) + (0 - 0 : ℝ) =
        (b ^ 2 - a ^ 2) / 2 := by ring
    rw [htarget] at hratio
    exact hratio.congr' heq.symm
  have hmain : Tendsto
      (fun x : ℝ => (q.slope : ℝ) *
          ((primeThetaMoment (b * x) - primeThetaMoment (a * x) +
            endpointPrimeMomentAtom (a * x) - endpointPrimeMomentAtom (b * x)) / x ^ 2) +
        (q.intercept : ℝ) *
          ((Chebyshev.theta (b * x) - Chebyshev.theta (a * x) +
            endpointPrimeLogAtom (a * x) - endpointPrimeLogAtom (b * x)) / x))
      atTop
      (𝓝 (((q.slope : ℝ) * ((b ^ 2 - a ^ 2) / 2)) +
        (q.intercept : ℝ) * (b - a))) := by
    simpa [a, b] using
      (tendsto_const_nhds.mul hmoment).add (tendsto_const_nhds.mul hmass)
  have heq : (fun x : ℝ => weightedPrimeSum (singletonPrimeAffineProfile q) x / x) =ᶠ[atTop]
      (fun x : ℝ => (q.slope : ℝ) *
          ((primeThetaMoment (b * x) - primeThetaMoment (a * x) +
            endpointPrimeMomentAtom (a * x) - endpointPrimeMomentAtom (b * x)) / x ^ 2) +
        (q.intercept : ℝ) *
          ((Chebyshev.theta (b * x) - Chebyshev.theta (a * x) +
            endpointPrimeLogAtom (a * x) - endpointPrimeLogAtom (b * x)) / x)) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    rw [weightedPrimeSum_singleton_eq_theta_atoms q x hx]
    field_simp [hx.ne']
    <;> ring
  have hlim := hmain.congr' heq.symm
  simpa [a, b] using hlim

private theorem weightedPrimeSum_list_normalized_limit (hpnt : hPNT)
    (pieces : List PrimeAffinePiece) :
    Tendsto
      (fun x : ℝ => (pieces.map fun q =>
        weightedPrimeSum (singletonPrimeAffineProfile q) x / x).sum)
      atTop
      (𝓝 ((pieces.map fun q =>
        ∫ t : ℝ, (singletonPrimeAffineProfile q).eval t).sum)) := by
  induction pieces with
  | nil =>
      simp
  | cons q qs ih =>
      have hq := weightedPrimeSum_singleton_limit hpnt q
      have hq' : Tendsto
          (fun x : ℝ => weightedPrimeSum (singletonPrimeAffineProfile q) x / x)
          atTop (𝓝 (∫ t : ℝ, (singletonPrimeAffineProfile q).eval t)) := by
        simpa [singletonPrimeAffineProfile_integral] using hq
      simpa [List.map_cons, List.sum_cons] using hq'.add ih

private theorem list_map_sum_div (pieces : List PrimeAffinePiece)
    (f : PrimeAffinePiece → ℝ) (x : ℝ) :
    (pieces.map f).sum / x = (pieces.map fun q => f q / x).sum := by
  induction pieces with
  | nil => simp
  | cons q qs ih =>
      simp only [List.map_cons, List.sum_cons]
      rw [add_div, ih]

/-! The resulting limit is additive over the original `List`, so repeated
pieces remain repeated contributions and are never collapsed through a finset. -/
theorem l3WeightedPrimeLimit_of_hPNT (hpnt : hPNT) :
    ∀ P : PrimeAffineProfile,
      Tendsto (fun x : ℝ => weightedPrimeSum P x / x) atTop
        (𝓝 (∫ t : ℝ, P.eval t)) := by
  intro P
  cases P with
  | mk pieces =>
      have hsum := weightedPrimeSum_list_normalized_limit hpnt pieces
      have heq : (fun x : ℝ => weightedPrimeSum (PrimeAffineProfile.mk pieces) x / x) =ᶠ[atTop]
          (fun x : ℝ => (pieces.map fun q =>
            weightedPrimeSum (singletonPrimeAffineProfile q) x / x).sum) := by
        filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
        rw [weightedPrimeSum_list_eq_singletons pieces x hx]
        exact list_map_sum_div pieces
          (fun q => weightedPrimeSum (singletonPrimeAffineProfile q) x) x
      have hfinal : Tendsto
          (fun x : ℝ => weightedPrimeSum (PrimeAffineProfile.mk pieces) x / x)
          atTop (𝓝 ((pieces.map fun q =>
            ∫ t : ℝ, (singletonPrimeAffineProfile q).eval t).sum)) :=
        hsum.congr' heq.symm
      rw [← primeAffineProfile_integral_eq_sum_singletons pieces] at hfinal
      exact hfinal

/-! This closes the `L3WeightedPrimeLimit` interface conditional only on the
explicit Chebyshev theta PNT hypothesis `hPNT`. -/
theorem l3WeightedPrimeLimit_from_hPNT : L3WeightedPrimeLimit := by
  intro hpnt P
  exact l3WeightedPrimeLimit_of_hPNT hpnt P

end Li2Lean
