/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFormalBase

namespace Li2Lean.P0.Integerization

noncomputable section

def formalTScaled (g i : ℕ) : BivPoly :=
  (aVar - ratConst 1) ^ g *
      (∑ r ∈ Finset.range i,
        formalU g (i - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹)) +
    aVar ^ i *
      (∑ s ∈ Finset.range g,
        ratConst (((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
          (Nat.choose (i + g) (g - (s + 1)) : ℚ)) *
          formalQNum g (s + 1))

theorem formalTScaled_outerEval_two (g i : ℕ) :
    outerEval 2 (formalTScaled g i) =
      Polynomial.C (p0TQ 2 g i) := by
  simp only [formalTScaled, map_add, map_mul, map_pow, map_sum]
  simp_rw [formalQNum_outerEval_two, formalU_outerEval_two]
  simp [outerEval, aVar, ratConst, Polynomial.evalRingHom,
    Polynomial.eval₂RingHom, p0TQ]
  have hunit : Polynomial.C (2 : ℚ) - 1 = 1 := by
    simpa only [Polynomial.C_sub, Polynomial.C_1] using
      (congrArg Polynomial.C (show (2 : ℚ) - 1 = 1 by norm_num))
  rw [hunit, one_pow]
  simp [div_eq_mul_inv]


def formalBScaled (g i : ℕ) : BivPoly :=
  (aVar - ratConst 1) ^ g *
      (∑ r ∈ Finset.range i,
        formalU g (i - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹ ^ 2)) -
    aVar ^ i *
      (∑ s ∈ Finset.Icc 2 g,
        ratConst (((-1 : ℚ) ^ s / (s : ℚ)) *
          (Nat.choose (i + g) (g - s) : ℚ)) *
          (∑ r ∈ Finset.range (s - 1),
            ratConst ((r + 1 : ℚ)⁻¹) * formalQNum g (r + 1)))

theorem formalBScaled_outerEval_two (g i : ℕ) :
    outerEval 2 (formalBScaled g i) =
      Polynomial.C (p0BQQ 2 g i) := by
  simp only [formalBScaled, map_sub, map_add, map_mul, map_pow, map_sum]
  simp_rw [formalQNum_outerEval_two, formalU_outerEval_two]
  simp [outerEval, aVar, ratConst, Polynomial.evalRingHom,
    Polynomial.eval₂RingHom, p0BQQ]
  have hunit : Polynomial.C (2 : ℚ) - 1 = 1 := by
    simpa only [Polynomial.C_sub, Polynomial.C_1] using
      (congrArg Polynomial.C (show (2 : ℚ) - 1 = 1 by norm_num))
  rw [hunit, one_pow]
  simp [div_eq_mul_inv]
  simp [mul_comm, mul_left_comm, mul_assoc]
#print axioms formalBScaled_outerEval_two
#print axioms formalTScaled_outerEval_two

def formalC (g i j : ℕ) : BivPoly :=
  if i = j then
    -formalU g i * ratConst (∑ s ∈ Finset.range g, ((i + s + 1 : ℚ)⁻¹))
  else
    (formalU g i - formalU g j) * ratConst (((j : ℚ) - (i : ℚ))⁻¹)

def formalA (g i j : ℕ) : BivPoly :=
  if i = j then formalU g i else 0

theorem formalC_outerEval_two (g i j : ℕ) :
    outerEval 2 (formalC g i j) =
      Polynomial.C (p0CQ 2 g i j) := by
  by_cases hij : i = j
  · subst j
    simp only [formalC, if_true]
    rw [map_mul, map_neg, formalU_outerEval_two]
    simp [outerEval, ratConst, Polynomial.evalRingHom,
      Polynomial.eval₂RingHom, p0CQ]
  · simp only [formalC, hij, if_false]
    rw [map_mul, map_sub, formalU_outerEval_two,
      formalU_outerEval_two]
    simp [outerEval, ratConst, Polynomial.evalRingHom,
      Polynomial.eval₂RingHom, p0CQ, hij, div_eq_mul_inv]

theorem formalA_outerEval_two (g i j : ℕ) :
    outerEval 2 (formalA g i j) =
      Polynomial.C (p0AQ 2 g i j) := by
  by_cases hij : i = j
  · subst j
    simp only [formalA, if_true]
    rw [formalU_outerEval_two]
    simp [p0AQ]
  · simp [formalA, hij, p0AQ]

/-! ### The full formal pencil entries

The off-diagonal `B` entries are divided differences of the first moment.  The
diagonal entries use the separately cleared second moment.  Keeping these as
one definition makes the subsequent matrix specialization statement
entrywise and avoids smuggling a determinant identity into the definition.
-/

def formalB (g i j : ℕ) : BivPoly :=
  if i = j then formalBScaled g i
  else (formalTScaled g i - formalTScaled g j) *
    ratConst (((j : ℚ) - (i : ℚ))⁻¹)

theorem formalB_outerEval_two (g i j : ℕ) :
    outerEval 2 (formalB g i j) =
      Polynomial.C (p0BQ 2 g i j) := by
  by_cases hij : i = j
  · subst hij
    simp only [formalB, if_true]
    rw [formalBScaled_outerEval_two]
    simp [p0BQ, p0BQQ]
  · simp only [formalB, hij, if_false]
    rw [map_mul, map_sub, formalTScaled_outerEval_two,
      formalTScaled_outerEval_two]
    simp [p0BQ, outerEval, ratConst, Polynomial.evalRingHom,
      Polynomial.eval₂RingHom, hij, div_eq_mul_inv]

def formalMatrix (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) BivPoly := fun r c =>
  let i := m / 4 + (if r.val < m then r.val else r.val - m)
  let j := c.val
  if r.val < m then
    formalC (m / 2) i j
  else
    formalB (m / 2) i j - Polynomial.C Polynomial.X * formalA (m / 2) i j

theorem formalMatrix_outerEval_two (m : ℕ) :
    (formalMatrix m).map (outerEval 2) = p0MatrixQ 2 m := by
  classical
  apply Matrix.ext
  intro r c
  by_cases hr : r.val < m
  · simp only [formalMatrix, p0MatrixQ, dif_pos hr, if_pos hr,
      Matrix.map_apply, formalC_outerEval_two, map_sub, map_mul,
      formalB_outerEval_two, formalA_outerEval_two]
  · simp only [formalMatrix, p0MatrixQ, dif_neg hr, if_neg hr,
      Matrix.map_apply, formalC_outerEval_two, map_sub, map_mul,
      formalB_outerEval_two, formalA_outerEval_two]
    simp [p0MatrixQ, hr, outerEval, ratConst,
      Polynomial.evalRingHom, Polynomial.eval₂RingHom]

theorem formalDet_outerEval_two (m : ℕ) :
    outerEval 2 (Matrix.det (formalMatrix m)) =
      Matrix.det (p0MatrixQ 2 m) := by
  have hdet := RingHom.map_det (outerEval 2) (formalMatrix m)
  calc
    outerEval 2 (Matrix.det (formalMatrix m)) =
        Matrix.det ((outerEval 2).mapMatrix (formalMatrix m)) := hdet
    _ = Matrix.det (p0MatrixQ 2 m) := by
      congr 1
      exact formalMatrix_outerEval_two m

def formalCanonicalPolynomial (m : ℕ) : BivPoly :=
  Matrix.det (formalMatrix m)

theorem formalCanonical_outerEval_two (m : ℕ) (hm : 4 ∣ m) :
    outerEval 2 (formalCanonicalPolynomial m) =
      p0CanonicalPolynomial 2 m := by
  unfold formalCanonicalPolynomial
  rw [formalDet_outerEval_two]
  simp [p0CanonicalPolynomial, hm]

#print axioms formalC_outerEval_two
#print axioms formalA_outerEval_two
#print axioms formalB_outerEval_two
#print axioms formalMatrix_outerEval_two
#print axioms formalDet_outerEval_two
#print axioms formalCanonical_outerEval_two

end

end Li2Lean.P0.Integerization
