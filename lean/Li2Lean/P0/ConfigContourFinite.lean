/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Config

set_option maxHeartbeats 2000000

open scoped BigOperators
open Finset

namespace Li2Lean.P0.ConfigContourFinite

noncomputable section

def gridSize : ℕ := ConfigData.contourGridCount
def degree : ℕ := ConfigData.fejerDegree
def denominator : ℕ := ConfigData.referenceDenominator

def massUnit (j : ℕ) : ℕ := ConfigData.contourMassUnits.getD j 0

def mass (j : ℕ) : ℝ := (massUnit j : ℝ) / (denominator : ℝ)

def angle (j : ℕ) : ℝ :=
  2 * Real.pi * ((2 * (j : ℝ) + 1) / (gridSize : ℝ)) / 2

def fejerCoefficient (n : ℕ) : ℝ :=
  if n ≤ degree then
    ((degree + 1 - n : ℕ) : ℝ) / ((degree + 1 : ℕ) : ℝ)
  else 0

def cosineMoment (n : ℕ) : ℝ :=
  ∑ j ∈ range gridSize, mass j * Real.cos (n * angle j)

def sineMoment (n : ℕ) : ℝ :=
  ∑ j ∈ range gridSize, mass j * Real.sin (n * angle j)

def fejerDensity (v : ℝ) : ℝ :=
  (∑ j ∈ range gridSize,
    mass j * (1 + 2 * ∑ n ∈ range degree,
      fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j)))) /
      (2 * Real.pi)

theorem gridSize_eq : gridSize = 64 := rfl

theorem degree_eq : degree = 48 := rfl

theorem denominator_eq : denominator = 1000000000000 := rfl

theorem massUnit_length : ConfigData.contourMassUnits.length = gridSize := by
  change ConfigData.contourMassUnits.length = 64
  exact ConfigData.contourMassUnits_length

theorem massUnit_sum : ∑ j ∈ range gridSize, massUnit j = 267885951940 := by
  decide +kernel

theorem mass_sum : ∑ j ∈ range gridSize, mass j =
    (267885951940 : ℝ) / denominator := by
  unfold mass
  rw [← Finset.sum_div]
  have hcast :
      (∑ j ∈ range gridSize, (massUnit j : ℝ)) =
        (∑ j ∈ range gridSize, massUnit j : ℕ) := by
    norm_num
  rw [hcast, massUnit_sum]
  norm_num [denominator]

theorem massUnit_reflection (j : ℕ) (hj : j < gridSize) :
    massUnit j = massUnit (gridSize - 1 - j) := by
  rw [gridSize_eq] at hj ⊢
  have hj' : j ≤ 63 := Nat.lt_succ_iff.mp (by simpa using hj)
  change ConfigData.contourMassUnits.getD j 0 =
    ConfigData.contourMassUnits.getD (63 - j) 0
  interval_cases j <;> decide +kernel

theorem mass_reflection (j : ℕ) (hj : j < gridSize) :
    mass j = mass (gridSize - 1 - j) := by
  unfold mass
  rw [massUnit_reflection j hj]

theorem angle_reflection (j : ℕ) (hj : j < gridSize) :
    angle (gridSize - 1 - j) = 2 * Real.pi - angle j := by
  rw [gridSize_eq] at hj ⊢
  have hjle : j ≤ 63 := Nat.lt_succ_iff.mp (by simpa using hj)
  have hcast : ((63 - j : ℕ) : ℝ) = (63 : ℝ) - (j : ℝ) := by
    rw [Nat.cast_sub hjle]
    norm_num
  simp only [angle, gridSize, ConfigData.contourGridCount]
  rw [hcast]
  push_cast
  ring

private theorem cos_reflection (n j : ℕ) (hj : j < gridSize) :
    Real.cos (n * angle (gridSize - 1 - j)) = Real.cos (n * angle j) := by
  rw [angle_reflection j hj]
  have h : (n : ℝ) * (2 * Real.pi - angle j) =
      -(n : ℝ) * angle j + (n : ℤ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h, Real.cos_add_int_mul_two_pi]
  simpa [neg_mul] using Real.cos_neg ((n : ℝ) * angle j)

private theorem sin_reflection (n j : ℕ) (hj : j < gridSize) :
    Real.sin (n * angle (gridSize - 1 - j)) = -Real.sin (n * angle j) := by
  rw [angle_reflection j hj]
  have h : (n : ℝ) * (2 * Real.pi - angle j) =
      -(n : ℝ) * angle j + (n : ℤ) * (2 * Real.pi) := by
    push_cast
    ring
  rw [h, Real.sin_add_int_mul_two_pi]
  simpa [neg_mul] using Real.sin_neg ((n : ℝ) * angle j)

theorem cosineMoment_reflection (n : ℕ) :
    cosineMoment n =
      ∑ j ∈ range gridSize, mass j * Real.cos (n * angle (gridSize - 1 - j)) := by
  unfold cosineMoment
  calc
    (∑ j ∈ range gridSize, mass j * Real.cos (n * angle j)) =
        ∑ j ∈ range gridSize,
          mass (gridSize - 1 - j) * Real.cos (n * angle (gridSize - 1 - j)) := by
      rw [← Finset.sum_range_reflect
        (fun j => mass j * Real.cos (n * angle j)) gridSize]
    _ = ∑ j ∈ range gridSize, mass j * Real.cos (n * angle (gridSize - 1 - j)) := by
      apply Finset.sum_congr rfl
      intro j hj
      have hj' : j < gridSize := mem_range.mp hj
      rw [mass_reflection j hj']

theorem sineMoment_eq_zero (n : ℕ) : sineMoment n = 0 := by
  unfold sineMoment
  have hsymm :
      (∑ j ∈ range gridSize, mass j * Real.sin (n * angle j)) =
        -∑ j ∈ range gridSize, mass j * Real.sin (n * angle j) := by
    calc
      (∑ j ∈ range gridSize, mass j * Real.sin (n * angle j)) =
          ∑ j ∈ range gridSize,
            mass (gridSize - 1 - j) * Real.sin (n * angle (gridSize - 1 - j)) := by
        rw [← Finset.sum_range_reflect
          (fun j => mass j * Real.sin (n * angle j)) gridSize]
      _ = ∑ j ∈ range gridSize, -(mass j * Real.sin (n * angle j)) := by
        apply Finset.sum_congr rfl
        intro j hj
        have hj' : j < gridSize := mem_range.mp hj
        rw [mass_reflection j hj']
        rw [sin_reflection n j hj']
        ring
      _ = -∑ j ∈ range gridSize, mass j * Real.sin (n * angle j) := by
        rw [Finset.sum_neg_distrib]
  linarith [hsymm]

private theorem shiftedCosineSum (n : ℕ) (v : ℝ) :
    (∑ j ∈ range gridSize,
      mass j * Real.cos ((n : ℝ) * v - (n : ℝ) * angle j)) =
      Real.cos ((n : ℝ) * v) * cosineMoment n +
        Real.sin ((n : ℝ) * v) * sineMoment n := by
  calc
    (∑ j ∈ range gridSize,
      mass j * Real.cos ((n : ℝ) * v - (n : ℝ) * angle j)) =
        ∑ j ∈ range gridSize,
          (Real.cos ((n : ℝ) * v) * (mass j * Real.cos ((n : ℝ) * angle j)) +
            Real.sin ((n : ℝ) * v) * (mass j * Real.sin ((n : ℝ) * angle j))) := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [Real.cos_sub]
      ring
    _ = Real.cos ((n : ℝ) * v) * cosineMoment n +
          Real.sin ((n : ℝ) * v) * sineMoment n := by
      rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      simp [cosineMoment, sineMoment, mul_comm, mul_left_comm, mul_assoc]

theorem fejerDensity_fourierExpansion (v : ℝ) :
    fejerDensity v =
      (∑ j ∈ range gridSize, mass j) / (2 * Real.pi) +
        (1 / Real.pi) *
          ∑ n ∈ range degree,
            fejerCoefficient (n + 1) * cosineMoment (n + 1) *
              Real.cos ((n + 1 : ℕ) * v) := by
  unfold fejerDensity
  have hsum :
      (∑ j ∈ range gridSize,
        mass j * (1 + 2 * ∑ n ∈ range degree,
          fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j)))) =
      (∑ j ∈ range gridSize, mass j) +
        2 * ∑ n ∈ range degree,
          fejerCoefficient (n + 1) *
            (Real.cos ((n + 1 : ℕ) * v) * cosineMoment (n + 1) +
              Real.sin ((n + 1 : ℕ) * v) * sineMoment (n + 1)) := by
    calc
      (∑ j ∈ range gridSize,
          mass j * (1 + 2 * ∑ n ∈ range degree,
            fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j)))) =
          ∑ j ∈ range gridSize, mass j +
            ∑ j ∈ range gridSize,
              mass j * (2 * ∑ n ∈ range degree,
                fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j))) := by
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j hj
        ring
      _ = (∑ j ∈ range gridSize, mass j) +
            2 * ∑ j ∈ range gridSize, ∑ n ∈ range degree,
              mass j * (fejerCoefficient (n + 1) *
                Real.cos ((n + 1) * (v - angle j))) := by
        congr 1
        calc
          (∑ j ∈ range gridSize,
              mass j * (2 * ∑ n ∈ range degree,
                fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j)))) =
              ∑ j ∈ range gridSize,
                2 * (mass j * ∑ n ∈ range degree,
                  fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = 2 * ∑ j ∈ range gridSize,
                (mass j * ∑ n ∈ range degree,
                  fejerCoefficient (n + 1) * Real.cos ((n + 1) * (v - angle j))) := by
            rw [Finset.mul_sum]
          _ = 2 * ∑ j ∈ range gridSize, ∑ n ∈ range degree,
                mass j * (fejerCoefficient (n + 1) *
                  Real.cos ((n + 1) * (v - angle j))) := by
            apply congrArg (fun x : ℝ => 2 * x)
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = (∑ j ∈ range gridSize, mass j) +
            2 * ∑ n ∈ range degree, ∑ j ∈ range gridSize,
              mass j * (fejerCoefficient (n + 1) *
                Real.cos ((n + 1) * (v - angle j))) := by
        congr 1
        rw [Finset.sum_comm]
      _ = (∑ j ∈ range gridSize, mass j) +
            2 * ∑ n ∈ range degree,
              fejerCoefficient (n + 1) *
                (Real.cos ((n + 1 : ℕ) * v) * cosineMoment (n + 1) +
                  Real.sin ((n + 1 : ℕ) * v) * sineMoment (n + 1)) := by
        apply congrArg (fun x : ℝ => (∑ j ∈ range gridSize, mass j) + 2 * x)
        apply Finset.sum_congr rfl
        intro n hn
        calc
          (∑ j ∈ range gridSize,
              mass j * (fejerCoefficient (n + 1) *
                Real.cos ((n + 1) * (v - angle j)))) =
              ∑ j ∈ range gridSize,
                fejerCoefficient (n + 1) *
                  (mass j * Real.cos ((n + 1) * (v - angle j))) := by
            apply Finset.sum_congr rfl
            intro j hj
            ring
          _ = fejerCoefficient (n + 1) *
                ∑ j ∈ range gridSize,
                  mass j * Real.cos ((n + 1) * (v - angle j)) := by
            rw [Finset.mul_sum]
          _ = fejerCoefficient (n + 1) *
                (Real.cos ((n + 1 : ℕ) * v) * cosineMoment (n + 1) +
                  Real.sin ((n + 1 : ℕ) * v) * sineMoment (n + 1)) := by
            apply congrArg (fun x : ℝ => fejerCoefficient (n + 1) * x)
            calc
              (∑ j ∈ range gridSize,
                  mass j * Real.cos ((n + 1) * (v - angle j))) =
                  ∑ j ∈ range gridSize,
                    mass j * Real.cos ((n + 1 : ℕ) * v - (n + 1 : ℕ) * angle j) := by
                apply Finset.sum_congr rfl
                intro j hj
                congr 2
                push_cast
                ring
              _ = Real.cos ((n + 1 : ℕ) * v) * cosineMoment (n + 1) +
                    Real.sin ((n + 1 : ℕ) * v) * sineMoment (n + 1) := by
                exact shiftedCosineSum (n + 1) v
  rw [hsum]
  simp_rw [sineMoment_eq_zero, mul_zero, add_zero]
  field_simp [Real.pi_ne_zero]
  apply congrArg (fun x : ℝ => (∑ j ∈ range gridSize, mass j) + 2 * x)
  apply Finset.sum_congr rfl
  intro n hn
  ring_nf

theorem fejerCoefficient_eq (n : ℕ) (hn : 1 ≤ n) (hK : n ≤ degree) :
    fejerCoefficient n =
      ((degree + 1 - n : ℕ) : ℝ) / ((degree + 1 : ℕ) : ℝ) := by
  simp [fejerCoefficient, hK]

theorem fejerCoefficient_eq_zero (n : ℕ) (hK : degree < n) :
    fejerCoefficient n = 0 := by
  simp [fejerCoefficient, hK]

theorem fejerCoefficient_support : ∀ n, degree < n → fejerCoefficient n = 0 := by
  intro n hn
  exact fejerCoefficient_eq_zero n hn

end

end Li2Lean.P0.ConfigContourFinite
