/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Integerization

namespace Li2Lean.P0.Integerization

noncomputable section

/-- Exact determinant multiplier for the frozen two-block row scaling. -/
private theorem p0RowScale_prod_add {a : ℚ} {m d : ℕ} :
    (∏ r : Fin (2 * m), p0RowScale a m d r) =
      (d : ℚ) ^ (3 * m) * (a - 1) ^ (m * (m / 2)) := by
  let e : ℚ := (d : ℚ)^2 * (a - 1)^(m / 2)
  let equiv : (Fin m ⊕ Fin m) ≃ Fin (2 * m) :=
    finSumFinEquiv.trans (finCongr (show m + m = 2 * m by omega))
  calc
    (∏ r : Fin (2 * m), p0RowScale a m d r) =
        ∏ x : Fin m ⊕ Fin m, p0RowScale a m d (equiv x) := by
          exact (Equiv.prod_comp equiv
            (fun r : Fin (2 * m) => p0RowScale a m d r)).symm
    _ = (∏ x : Fin m, (d : ℚ)) *
          ∏ x : Fin m, ((d : ℚ)^2 * (a - 1)^(m / 2)) := by
          simp [Fintype.prod_sum_type, p0RowScale, equiv,
            finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
            Fin.val_castAdd]
    _ = (d : ℚ)^m * ((d : ℚ)^2 * (a - 1)^(m / 2))^m := by simp
    _ = ((d : ℚ)^3 * (a - 1)^(m / 2))^m := by
          rw [← mul_pow]
          congr 1
          ring
    _ = (d : ℚ) ^ (3 * m) * (a - 1) ^ (m * (m / 2)) := by
          rw [mul_pow, ← pow_mul, ← pow_mul]
          rw [Nat.mul_comm (m / 2) m]

/-- The exact product of the two blocks of row factors. -/
theorem p0RowScale_prod {a : ℚ} {m d : ℕ} :
    (∏ r : Fin (2 * m), p0RowScale a m d r) =
      (d : ℚ) ^ (3 * m) * (a - 1) ^ (m * (m / 2)) :=
  p0RowScale_prod_add

/-- Exact feature weight in docs/6333 §8.2 and the frozen v10 blueprint. -/
theorem p0_feature_exponent (h : ℕ) :
    2 * (∑ k ∈ Finset.range h, k) +
        3 * (∑ k ∈ Finset.Ico h (3 * h), k) = 13 * h ^ 2 - 4 * h := by
  have hsum2h : ∑ k ∈ Finset.range (2 * h), k = h * (2 * h - 1) := by
    rw [Finset.sum_range_id]
    rw [show (2 * h) * (2 * h - 1) = 2 * (h * (2 * h - 1)) by ring]
    exact Nat.mul_div_cancel_left _ (by norm_num)
  have hIco :
      (∑ k ∈ Finset.Ico h (3 * h), k) = (2 * h) * h + h * (2 * h - 1) := by
    rw [Finset.sum_Ico_eq_sum_range (fun k : ℕ => k) h (3 * h)]
    rw [show 3 * h - h = 2 * h by omega]
    rw [Finset.sum_add_distrib]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    simp only [Nat.cast_id]
    rw [hsum2h]
  have hsum1 : 2 * (∑ k ∈ Finset.range h, k) = h * (h - 1) := by
    simpa [Nat.mul_comm] using Finset.sum_range_id_mul_two h
  have hsub1 : h * (h - 1) = h ^ 2 - h := by
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_one, pow_two]
  have hsub2 : h * (2 * h - 1) = 2 * h ^ 2 - h := by
    rw [Nat.mul_sub_left_distrib]
    simp only [Nat.mul_one]
    ring_nf
  rw [hsum1, hIco, hsub1, hsub2]
  ring_nf
  have hle1 : h ≤ h ^ 2 := by
    rw [pow_two]
    exact Nat.le_mul_self h
  omega

/-- The feature exponent in the paper's m-index convention. -/
theorem p0_feature_exponent_m (m h : ℕ) (hm : m = 4 * h) :
    2 * (∑ k ∈ Finset.range h, k) +
        3 * (∑ k ∈ Finset.Ico h (3 * h), k) =
      13 * h ^ 2 - 4 * h ∧ 13 * h ^ 2 - 4 * h = 13 * m ^ 2 / 16 - m := by
  subst hm
  constructor
  · exact p0_feature_exponent h
  · have hpow : 13 * (4 * h) ^ 2 = 16 * (13 * h ^ 2) := by ring
    rw [hpow]
    rw [Nat.mul_div_cancel_left (13 * h ^ 2) (by norm_num : 0 < 16)]

/--
If an injective coefficient map makes a polynomial divisible by a power of
`X`, the original polynomial was already divisible by that power. This is
the coefficientwise step used to descend formal divisibility from `Q` to
`Z`.
-/
theorem x_pow_dvd_of_map_injective
    {R S : Type} [Semiring R] [Semiring S] (f : R →+* S)
    (hf : Function.Injective f) {P : Polynomial R} {N : ℕ}
    (h : Polynomial.X ^ N ∣ Polynomial.map f P) :
    Polynomial.X ^ N ∣ P := by
  apply Polynomial.X_pow_dvd_iff.2
  intro k hk
  apply hf
  have hz := (Polynomial.X_pow_dvd_iff.mp h) k hk
  simpa only [Polynomial.coeff_map, map_zero] using hz

/-- The one-variable integer specialization of `x_pow_dvd_of_map_injective`. -/
theorem int_poly_x_pow_dvd_of_rat_map
    {P : Polynomial ℤ} {N : ℕ}
    (h : Polynomial.X ^ N ∣ Polynomial.map (Int.castRingHom ℚ) P) :
    Polynomial.X ^ N ∣ P := by
  exact x_pow_dvd_of_map_injective (Int.castRingHom ℚ)
    Int.cast_injective h

/--
The same descent for a polynomial whose coefficients are themselves integer
polynomials. It is convenient when the outer variable is the formal base
and the coefficients carry the pencil variable.
-/
theorem int_bivariate_x_pow_dvd_of_rat_map
    {P : Polynomial (Polynomial ℤ)} {N : ℕ}
    (h : Polynomial.X ^ N ∣
      Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) P) :
    Polynomial.X ^ N ∣ P := by
  exact x_pow_dvd_of_map_injective
    (Polynomial.mapRingHom (Int.castRingHom ℚ))
    (Polynomial.map_injective (Int.castRingHom ℚ) Int.cast_injective) h

end

end Li2Lean.P0.Integerization
