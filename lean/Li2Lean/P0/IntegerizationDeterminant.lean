/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationBottom
import Li2Lean.P0.IntegerizationProofs

namespace Li2Lean.P0.Integerization

noncomputable section

/-- The literal `a = 2` determinant is represented by an integer polynomial
after the product of the two block row scales. -/
theorem p0_determinant_integerized_two (m : ℕ) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
          p0RationalDeterminant 2 m := by
  rcases p0_determinant_integerized_of_rows
      (a := 2) (m := m) (d := p0DenominatorLcm m)
      (p0_integerizedRows_two m) with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  calc
    Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (∏ r : Fin (2 * m),
          p0RowScale 2 m (p0DenominatorLcm m) r) *
          p0RationalDeterminant 2 m := hP
    _ = Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
          p0RationalDeterminant 2 m := by
      rw [p0RowScale_prod]
      norm_num

/-- When the paper's index condition `4 ∣ m` holds, the determinant
specialization is exactly the canonical P0 polynomial. -/
theorem p0_canonical_integerized_two (m : ℕ) (hm : 4 ∣ m) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
          p0CanonicalPolynomial 2 m := by
  rcases p0_determinant_integerized_two m with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  simpa [p0CanonicalPolynomial, p0RationalDeterminant, hm] using hP

/-- Realification of the canonical integerizer, in the coefficient map used
by the `P0Family` interface. -/
theorem p0_canonical_integerized_two_real (m : ℕ) (hm : 4 ∣ m) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℝ) P =
        Polynomial.C ((p0DenominatorLcm m : ℝ) ^ (3 * m)) *
          (p0CanonicalPolynomial 2 m).map (algebraMap ℚ ℝ) := by
  rcases p0_canonical_integerized_two m hm with ⟨P, hP⟩
  refine ⟨P, ?_⟩
  have hcomp :
      (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  have hmap :
      Polynomial.map (algebraMap ℚ ℝ)
          (Polynomial.map (Int.castRingHom ℚ) P) =
        Polynomial.map (Int.castRingHom ℝ) P := by
    rw [Polynomial.map_map, hcomp]
  calc
    Polynomial.map (Int.castRingHom ℝ) P =
        Polynomial.map (algebraMap ℚ ℝ)
          (Polynomial.map (Int.castRingHom ℚ) P) := hmap.symm
    _ = Polynomial.map (algebraMap ℚ ℝ)
          (Polynomial.C ((p0DenominatorLcm m : ℚ) ^ (3 * m)) *
            p0CanonicalPolynomial 2 m) := congrArg _ hP
    _ = _ := by simp

end

end Li2Lean.P0.Integerization
