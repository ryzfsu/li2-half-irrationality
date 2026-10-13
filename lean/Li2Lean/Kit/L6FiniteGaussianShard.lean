/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace ContourKit

noncomputable section

/-- The three collision-free points used for the finite L6 shard.
They lie on the real axis, viewed as a subset of the complex plane. -/
def l6AtomicPoint (i : Fin 3) : ℝ := i.1

/-- The signed masses (1,-2,1), whose total mass is zero. -/
def l6AtomicWeight (i : Fin 3) : ℝ :=
  if i = 1 then -2 else 1

/-- The finite Gaussian quadratic form for the explicit signed atomic measure. -/
def l6GaussianQuadratic (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    l6AtomicWeight i * l6AtomicWeight j *
      Real.exp (-t * (l6AtomicPoint i - l6AtomicPoint j) ^ 2)

/-- The Frullani constant term for the same finite signed measure. -/
def l6FrullaniConstantTerm (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    l6AtomicWeight i * l6AtomicWeight j * Real.exp (-t)

/-- The finite Frullani Gaussian integrand before integrating in t. -/
def l6FrullaniGaussianQuadratic (t : ℝ) : ℝ :=
  ∑ i : Fin 3, ∑ j : Fin 3,
    l6AtomicWeight i * l6AtomicWeight j *
      (Real.exp (-t * (l6AtomicPoint i - l6AtomicPoint j) ^ 2) - Real.exp (-t))

/-- Generic finite cancellation of the Frullani constant term for any
finite real signed weight vector of total mass zero. -/
theorem finite_frullani_constant_zero {ι : Type*} [Fintype ι]
    (w : ι → ℝ) (hw : (∑ i, w i) = 0) (c : ℝ) :
    (∑ i, ∑ j, w i * w j * c) = 0 := by
  calc
    _ = ((∑ i, ∑ j, w i * w j) * c) := by
      simp_rw [← Finset.sum_mul]
    _ = (((∑ i, w i) * (∑ j, w j)) * c) := by
      rw [← Finset.sum_mul_sum]
    _ = 0 := by simp [hw]

/-- The signed atomic configuration has total mass zero. This is the
finite analogue of the zero-mass hypothesis in docs/6406, Section L6. -/
theorem l6Atomic_mass_zero :
    (∑ i : Fin 3, l6AtomicWeight i) = 0 := by
  rw [Fin.sum_univ_three]
  norm_num [l6AtomicWeight]

/-- The three support points are collision-free. -/
theorem l6Atomic_points_injective :
    Function.Injective l6AtomicPoint := by
  intro i j h
  fin_cases i <;> fin_cases j <;> simp [l6AtomicPoint] at h ⊢

/-- The constant term in the Frullani integrand cancels exactly because
the signed mass is zero. -/
theorem l6Frullani_constant_cancels (t : ℝ) :
    l6FrullaniConstantTerm t = 0 := by
  unfold l6FrullaniConstantTerm
  exact finite_frullani_constant_zero l6AtomicWeight l6Atomic_mass_zero
    (Real.exp (-t))

/-- Direct expansion of the finite Gaussian quadratic form for
the (0,1,2) / (1,-2,1) configuration. -/
theorem l6GaussianQuadratic_explicit (t : ℝ) :
    l6GaussianQuadratic t =
      6 - 8 * Real.exp (-t) + 2 * Real.exp (-4 * t) := by
  simp only [l6GaussianQuadratic, Fin.sum_univ_three]
  simp [l6AtomicPoint, l6AtomicWeight]
  ring_nf

/-- The Gaussian quadratic form factors as an explicit square times
a positive polynomial, giving the finite sum-of-squares certificate. -/
theorem l6GaussianQuadratic_factor (t : ℝ) :
    l6GaussianQuadratic t =
      2 * (1 - Real.exp (-t)) ^ 2 *
        (Real.exp (-t) ^ 2 + 2 * Real.exp (-t) + 3) := by
  rw [l6GaussianQuadratic_explicit]
  have h4 : Real.exp (-4 * t) = Real.exp (-t) ^ 4 := by
    convert Real.exp_nat_mul (-t) 4 using 1 <;> ring_nf
  rw [h4]
  ring

/-- A literal two-square form for the same Gaussian quadratic form. -/
theorem l6GaussianQuadratic_sumOfSquares (t : ℝ) :
    l6GaussianQuadratic t =
      2 * ((1 - Real.exp (-t)) * (1 + Real.exp (-t))) ^ 2 +
        4 * (1 - Real.exp (-t)) ^ 2 := by
  rw [l6GaussianQuadratic_factor]
  ring

/-- The explicit finite Gaussian quadratic form is nonnegative for every
real parameter t. -/
theorem l6GaussianQuadratic_nonneg (t : ℝ) :
    0 ≤ l6GaussianQuadratic t := by
  rw [l6GaussianQuadratic_sumOfSquares]
  positivity

/-- On this zero-mass configuration, the Frullani Gaussian integrand
equals the Gaussian quadratic form term by term after cancellation. -/
theorem l6FrullaniGaussian_cancellation (t : ℝ) :
    l6FrullaniGaussianQuadratic t = l6GaussianQuadratic t := by
  simp only [l6FrullaniGaussianQuadratic, l6GaussianQuadratic,
    Fin.sum_univ_three]
  simp [l6AtomicPoint, l6AtomicWeight]
  ring_nf

/-- The finite Frullani Gaussian integrand is nonnegative. This is the
fully explicit atomic instance of the L6 Gaussian square step in
docs/6406 and docs/6333, Section 5.3. -/
theorem l6FrullaniGaussian_nonneg (t : ℝ) :
    0 ≤ l6FrullaniGaussianQuadratic t := by
  rw [l6FrullaniGaussian_cancellation]
  exact l6GaussianQuadratic_nonneg t

#print axioms l6Atomic_mass_zero
#print axioms l6Atomic_points_injective
#print axioms finite_frullani_constant_zero
#print axioms l6Frullani_constant_cancels
#print axioms l6GaussianQuadratic_explicit
#print axioms l6GaussianQuadratic_factor
#print axioms l6GaussianQuadratic_sumOfSquares
#print axioms l6GaussianQuadratic_nonneg
#print axioms l6FrullaniGaussian_cancellation
#print axioms l6FrullaniGaussian_nonneg

end

end ContourKit
