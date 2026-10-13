/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Integerization

namespace Li2Lean.P0.Integerization

noncomputable section

/-!
## Formal outer parameter, first denominator-free pieces

The existing P0 source is parameterized by a rational `a` at each use.  The
paper's integerization argument first treats `a` as a polynomial variable.
This file starts that construction over `Q`: the outer variable is `a` and
the coefficient ring is the polynomial ring in the pencil variable `T`.

`formalQNum` is the denominator-free numerator of `Q_s(a)`.  It is used only
when `s <= g`; the specialization theorem below is stated at `a = 2`, where
the denominator is a unit.  No feature-divisibility or integer-coefficient
claim is made here.
-/

abbrev BivPoly := Polynomial (Polynomial ℚ)

def aVar : BivPoly := Polynomial.X

def ratConst (r : ℚ) : BivPoly := Polynomial.C (Polynomial.C r)

def outerEval (a : ℚ) : BivPoly →+* Polynomial ℚ :=
  Polynomial.evalRingHom (Polynomial.C a)

def formalU (g i : ℕ) : BivPoly :=
  ratConst (Nat.choose (i + g) g) * aVar ^ i

def formalQNum (g s : ℕ) : BivPoly :=
  (aVar - ratConst 1) ^ (g - s) *
    (aVar ^ s - (aVar - ratConst 1) ^ s)

private lemma outerEval_aVar_two :
    outerEval 2 aVar = Polynomial.C (2 : ℚ) := by
  simp [outerEval, aVar]

private lemma outerEval_ratConst_two (r : ℚ) :
    outerEval 2 (ratConst r) = Polynomial.C r := by
  simp [outerEval, ratConst]

theorem formalQNum_outerEval_two (g s : ℕ) :
    outerEval 2 (formalQNum g s) =
      Polynomial.C (p0Q 2 s) := by
  simp only [formalQNum, map_mul, map_sub, map_pow,
    outerEval_aVar_two, outerEval_ratConst_two]
  rw [show Polynomial.C (2 : ℚ) - Polynomial.C 1 = Polynomial.C 1 by
    rw [← Polynomial.C_sub]
    norm_num]
  simp only [p0Q]
  have hq : (2 : ℚ) / (2 - 1) = 2 := by norm_num
  rw [hq]
  simp

theorem formalU_outerEval_two (g i : ℕ) :
    outerEval 2 (formalU g i) =
      Polynomial.C (p0UQ 2 g i) := by
  simp only [formalU, map_mul, map_pow, outerEval_aVar_two,
    outerEval_ratConst_two]
  simp [p0UQ]
  ring

#print axioms formalQNum_outerEval_two
#print axioms formalU_outerEval_two

end

end Li2Lean.P0.Integerization
