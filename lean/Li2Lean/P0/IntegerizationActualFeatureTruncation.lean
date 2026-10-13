/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationWeightedFeatures
import Li2Lean.P0.IntegerizationActualFeatureWeights
import Mathlib.RingTheory.PowerSeries.Basic
import Mathlib.RingTheory.Ideal.Quotient.Defs
import Mathlib.RingTheory.Ideal.Span

namespace Li2Lean.P0.Integerization
open Finset

/-- Determinant divisibility is preserved by entrywise congruence.
This makes finite coefficient truncation sufficient for formal series. -/
theorem dvd_det_of_entrywise_congr
    {R n : Type*} [CommRing R] [Fintype n] [DecidableEq n]
    (d : R) (M A : Matrix n n R)
    (h : ∀ i j, d ∣ M i j - A i j) (hA : d ∣ A.det) :
    d ∣ M.det := by
  let I : Ideal R := Ideal.span {d}
  let q := Ideal.Quotient.mk I
  have hmap : q.mapMatrix M = q.mapMatrix A := by
    ext i j
    exact Ideal.Quotient.eq.mpr (Ideal.mem_span_singleton.mpr (h i j))
  have hzero : q A.det = 0 :=
    (Ideal.Quotient.eq_zero_iff_mem).mpr (Ideal.mem_span_singleton.mpr hA)
  apply Ideal.mem_span_singleton.mp
  change M.det ∈ I
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change q M.det = 0
  rw [RingHom.map_det, hmap, ← RingHom.map_det, hzero]

/-- The actual support and actual exponent, for every finite subset of the
paper's three feature families. The vector values may be arbitrary. -/
theorem p0_actual_finite_feature_divisibility
    {R : Type*} [CommRing R] (a : R) (h : ℕ)
    (F : Finset (ℕ × Fin 3)) (hF : ∀ f ∈ F, p0FeatureAllowed h f)
    (u v : F → Fin (8*h) → R) :
    a ^ (13*h^2-4*h) ∣ Matrix.det
      (Matrix.of fun i j => ∑ f : F, u f i * (a ^ f.val.1 * v f j)) := by
  apply pow_dvd_det_weighted_rank_one
  intro p hp
  exact p0_actual_feature_exponent_lower_bound h
    (fun j => (p j).val)
    (fun i j hij => hp (Subtype.ext hij))
    (fun j => hF (p j).val (p j).property)

/-- Source coefficient interface for the actual determinant divisor.
Matching coefficients below the target exponent is sufficient; no infinite
determinant expansion or unproved divisibility witness is assumed. -/
theorem p0_actual_feature_divisibility_of_coefficients
    {R : Type*} [CommRing R] (h : ℕ)
    (M : Matrix (Fin (8*h)) (Fin (8*h)) (PowerSeries R))
    (F : Finset (ℕ × Fin 3)) (hF : ∀ f ∈ F, p0FeatureAllowed h f)
    (u v : F → Fin (8*h) → PowerSeries R)
    (hcoeff : ∀ i j k, k < 13*h^2-4*h →
      PowerSeries.coeff k (M i j) =
      PowerSeries.coeff k
        (∑ f : F, u f i * (PowerSeries.X ^ f.val.1 * v f j))) :
    PowerSeries.X ^ (13*h^2-4*h) ∣ M.det := by
  apply dvd_det_of_entrywise_congr _
    M (Matrix.of fun i j => ∑ f : F, u f i * (PowerSeries.X ^ f.val.1 * v f j))
  · intro i j
    apply PowerSeries.X_pow_dvd_iff.mpr
    intro k hk
    simp only [map_sub, Matrix.of_apply]
    exact sub_eq_zero.mpr (hcoeff i j k hk)
  · exact p0_actual_finite_feature_divisibility PowerSeries.X h F hF u v


/-- Every finite coefficient of a series matrix has exactly the paper's
three rank-one features; forbidden support positions contribute zero. -/
theorem p0_actual_feature_divisibility_of_three_coefficients
    {R : Type*} [CommRing R] (h : ℕ)
    (M : Matrix (Fin (8*h)) (Fin (8*h)) (PowerSeries R))
    (u v : (ℕ × Fin 3) → Fin (8*h) → R)
    (hsupport : ∀ f i j, ¬p0FeatureAllowed h f → u f i * v f j = 0)
    (hcoeff : ∀ i j k, k < 13*h^2-4*h →
      PowerSeries.coeff k (M i j) = ∑ t : Fin 3, u (k,t) i * v (k,t) j) :
    PowerSeries.X ^ (13*h^2-4*h) ∣ M.det := by
  classical
  let N := 13*h^2-4*h
  let F := (Finset.range N ×ˢ (Finset.univ : Finset (Fin 3))).filter
    (p0FeatureAllowed h)
  apply p0_actual_feature_divisibility_of_coefficients h M F
    (fun f hf => (Finset.mem_filter.mp hf).2)
    (fun f i => PowerSeries.C (u f.val i))
    (fun f j => PowerSeries.C (v f.val j))
  intro i j k hk
  rw [hcoeff i j k hk]
  simp only [map_sum, PowerSeries.coeff_C_mul, PowerSeries.coeff_mul_C,
    PowerSeries.coeff_X_pow, ite_mul, one_mul, zero_mul, mul_ite, mul_zero]
  rw [Finset.sum_coe_sort F (fun f => if k = f.1 then u f i * v f j else 0)]
  change (∑ t : Fin 3, u (k,t) i * v (k,t) j) =
    ∑ f ∈ F, if k = f.1 then u f i * v f j else 0
  dsimp only [F]
  rw [Finset.sum_filter]
  have hremove : (∑ f ∈ Finset.range N ×ˢ (Finset.univ : Finset (Fin 3)),
      if p0FeatureAllowed h f then
        (if k = f.1 then u f i * v f j else 0) else 0) =
      ∑ f ∈ Finset.range N ×ˢ (Finset.univ : Finset (Fin 3)),
        if k = f.1 then u f i * v f j else 0 := by
    apply Finset.sum_congr rfl
    intro f hf
    by_cases ha : p0FeatureAllowed h f
    · simp [ha]
    · simp [ha, hsupport f i j ha]
  rw [hremove, Finset.sum_product]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t ht
  simp [hk, N]

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.dvd_det_of_entrywise_congr
#print axioms Li2Lean.P0.Integerization.p0_actual_finite_feature_divisibility
#print axioms Li2Lean.P0.Integerization.p0_actual_feature_divisibility_of_coefficients

#print axioms Li2Lean.P0.Integerization.p0_actual_feature_divisibility_of_three_coefficients

