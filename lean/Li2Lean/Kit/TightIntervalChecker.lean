/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.IntervalChecker

/-!
Exact rational interval operations that preserve nonzero centers.

These definitions reuse `ContourKit.QInterval` and its real containment
predicate. The original symmetric multiplication and checker are unchanged.
Four-corner multiplication, sign-aware squaring, and inversion away from zero
are sufficient arithmetic primitives for the C-A potential formulas in
`core/certificates/dual/check_dual.py`; identifying the transcendental formulas
and validating the complete C-A receipt are separate analytic obligations.
-/

namespace ContourKit
namespace QInterval

/-- The smallest interval containing the four endpoint products. -/
def tightMul (I J : QInterval) : QInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi))
       (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi))
       (max (I.hi * J.lo) (I.hi * J.hi)),
   le_trans (le_trans (min_le_left _ _) (min_le_left _ _))
     (le_trans (le_max_left _ _) (le_max_left _ _))⟩

private theorem fourCorners_lower {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have hac : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have had : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hbc : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hbd : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  by_cases hy0 : 0 ≤ y
  · have hax := mul_le_mul_of_nonneg_right hx.1 hy0
    by_cases ha0 : 0 ≤ a
    · exact hac.trans ((mul_le_mul_of_nonneg_left hy.1 ha0).trans hax)
    · exact had.trans ((mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha0)).trans hax)
  · have hbx := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
    by_cases hb0 : 0 ≤ b
    · exact hbc.trans ((mul_le_mul_of_nonneg_left hy.1 hb0).trans hbx)
    · exact hbd.trans ((mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hb0)).trans hbx)

private theorem fourCorners_upper {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have hac : a*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    le_trans (le_max_left _ _) (le_max_left _ _)
  have had : a*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    le_trans (le_max_right _ _) (le_max_left _ _)
  have hbc : b*c ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    le_trans (le_max_left _ _) (le_max_right _ _)
  have hbd : b*d ≤ max (max (a*c) (a*d)) (max (b*c) (b*d)) :=
    le_trans (le_max_right _ _) (le_max_right _ _)
  by_cases hy0 : 0 ≤ y
  · have hxb := mul_le_mul_of_nonneg_right hx.2 hy0
    by_cases hb0 : 0 ≤ b
    · exact hxb.trans ((mul_le_mul_of_nonneg_left hy.2 hb0).trans hbd)
    · exact hxb.trans ((mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge hb0)).trans hbc)
  · have hxa := mul_le_mul_of_nonpos_right hx.1 (le_of_not_ge hy0)
    by_cases ha0 : 0 ≤ a
    · exact hxa.trans ((mul_le_mul_of_nonneg_left hy.2 ha0).trans had)
    · exact hxa.trans ((mul_le_mul_of_nonpos_left hy.1 (le_of_not_ge ha0)).trans hac)

/-- Exact real containment for the four-corner product. No sign premise. -/
theorem mem_tightMul {I J : QInterval} {x y : ℝ}
    (hx : I.Contains x) (hy : J.Contains y) :
    (tightMul I J).Contains (x * y) := by
  simp only [Contains, tightMul, Rat.cast_min, Rat.cast_max, Rat.cast_mul]
  exact ⟨fourCorners_lower hx hy, fourCorners_upper hx hy⟩

/-- An interval containing all four corners contains the entire tight hull. -/
theorem tightMul_minimal {I J K : QInterval}
    (hll : K.Contains ((I.lo : ℝ) * J.lo))
    (hlh : K.Contains ((I.lo : ℝ) * J.hi))
    (hhl : K.Contains ((I.hi : ℝ) * J.lo))
    (hhh : K.Contains ((I.hi : ℝ) * J.hi))
    {z : ℝ} (hz : (tightMul I J).Contains z) : K.Contains z := by
  simp only [Contains, tightMul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] at hz
  exact ⟨(le_min (le_min hll.1 hlh.1) (le_min hhl.1 hhh.1)).trans hz.1,
    hz.2.trans (max_le (max_le hll.2 hlh.2) (max_le hhl.2 hhh.2))⟩

/-- The new product always refines the original symmetric product. -/
theorem tightMul_refines_mul {I J : QInterval} {z : ℝ}
    (hz : (tightMul I J).Contains z) : (mul I J).Contains z := by
  have hI : (I.lo : ℝ) ≤ I.hi := by exact_mod_cast I.ordered
  have hJ : (J.lo : ℝ) ≤ J.hi := by exact_mod_cast J.ordered
  exact tightMul_minimal
    (mem_mul ⟨le_rfl, hI⟩ ⟨le_rfl, hJ⟩)
    (mem_mul ⟨le_rfl, hI⟩ ⟨hJ, le_rfl⟩)
    (mem_mul ⟨hI, le_rfl⟩ ⟨le_rfl, hJ⟩)
    (mem_mul ⟨hI, le_rfl⟩ ⟨hJ, le_rfl⟩) hz

/-- Exact square hull: monotone on either half-line, zero at a crossing. -/
def tightSquare (I : QInterval) : QInterval :=
  if hp : 0 ≤ I.lo then
    ⟨I.lo ^ 2, I.hi ^ 2, (sq_le_sq₀ hp (hp.trans I.ordered)).2 I.ordered⟩
  else if hn : I.hi ≤ 0 then
    ⟨I.hi ^ 2, I.lo ^ 2, by
      have h := (sq_le_sq₀ (neg_nonneg.mpr hn)
        (neg_nonneg.mpr (I.ordered.trans hn))).2 (neg_le_neg I.ordered)
      simpa only [neg_sq] using h⟩
  else
    ⟨0, max (I.lo ^ 2) (I.hi ^ 2),
      (sq_nonneg I.lo).trans (le_max_left _ _)⟩

/-- Exact real containment for the sign-aware square. -/
theorem mem_tightSquare {I : QInterval} {x : ℝ}
    (hx : I.Contains x) : (tightSquare I).Contains (x ^ 2) := by
  unfold tightSquare
  split_ifs with hp hn
  · have hpR : 0 ≤ (I.lo : ℝ) := by exact_mod_cast hp
    have hx0 := hpR.trans hx.1
    have hhi0 := hx0.trans hx.2
    simp only [Contains, Rat.cast_pow]
    exact ⟨(sq_le_sq₀ hpR hx0).2 hx.1, (sq_le_sq₀ hx0 hhi0).2 hx.2⟩
  · have hnR : (I.hi : ℝ) ≤ 0 := by exact_mod_cast hn
    have hx0 := hx.2.trans hnR
    have hlo0 := hx.1.trans hx0
    simp only [Contains, Rat.cast_pow]
    constructor
    · simpa only [neg_sq] using
        (sq_le_sq₀ (neg_nonneg.mpr hnR) (neg_nonneg.mpr hx0)).2 (neg_le_neg hx.2)
    · simpa only [neg_sq] using
        (sq_le_sq₀ (neg_nonneg.mpr hx0) (neg_nonneg.mpr hlo0)).2 (neg_le_neg hx.1)
  · simp only [Contains, Rat.cast_zero, Rat.cast_max, Rat.cast_pow]
    refine ⟨sq_nonneg x, ?_⟩
    by_cases hx0 : 0 ≤ x
    · exact ((sq_le_sq₀ hx0 (hx0.trans hx.2)).2 hx.2).trans (le_max_right _ _)
    · have hx0' := le_of_not_ge hx0
      have h := (sq_le_sq₀ (neg_nonneg.mpr hx0')
        (neg_nonneg.mpr (hx.1.trans hx0'))).2 (neg_le_neg hx.1)
      have h' : x ^ 2 ≤ (I.lo : ℝ) ^ 2 := by simpa only [neg_sq] using h
      exact h'.trans (le_max_left _ _)

/-- An executable domain check: inversion accepts exactly intervals away from zero. -/
def checkInvDomain (I : QInterval) : Bool := decide (0 < I.lo ∨ I.hi < 0)

theorem checkInvDomain_spec {I : QInterval} :
    checkInvDomain I = true ↔ 0 < I.lo ∨ I.hi < 0 := by
  simp only [checkInvDomain, decide_eq_true_eq]

/-- Reciprocal endpoints reverse order on either component of the nonzero reals. -/
def tightInv (I : QInterval) (h : 0 < I.lo ∨ I.hi < 0) : QInterval :=
  ⟨1 / I.hi, 1 / I.lo, by
    rcases h with hp | hn
    · exact one_div_le_one_div_of_le hp I.ordered
    · exact one_div_le_one_div_of_neg_of_le hn I.ordered⟩

/-- The inverse domain guard proves every enclosed point is nonzero. -/
theorem ne_zero_of_invDomain {I : QInterval} {x : ℝ}
    (h : 0 < I.lo ∨ I.hi < 0) (hx : I.Contains x) : x ≠ 0 := by
  rcases h with hp | hn
  · have hpR : 0 < (I.lo : ℝ) := by exact_mod_cast hp
    exact ne_of_gt (hpR.trans_le hx.1)
  · have hnR : (I.hi : ℝ) < 0 := by exact_mod_cast hn
    exact ne_of_lt (hx.2.trans_lt hnR)

/-- Real reciprocal containment, with both positive and negative domains supported. -/
theorem mem_tightInv {I : QInterval} {x : ℝ}
    (h : 0 < I.lo ∨ I.hi < 0) (hx : I.Contains x) :
    (tightInv I h).Contains (1 / x) := by
  simp only [Contains, tightInv, Rat.cast_div, Rat.cast_one]
  rcases h with hp | hn
  · have hpR : 0 < (I.lo : ℝ) := by exact_mod_cast hp
    have hx0 := hpR.trans_le hx.1
    exact ⟨one_div_le_one_div_of_le hx0 hx.2, one_div_le_one_div_of_le hpR hx.1⟩
  · have hnR : (I.hi : ℝ) < 0 := by exact_mod_cast hn
    have hx0 := hx.2.trans_lt hnR
    exact ⟨one_div_le_one_div_of_neg_of_le hnR hx.2,
      one_div_le_one_div_of_neg_of_le hx0 hx.1⟩

/-- Tight division reuses the explicit reciprocal domain proof. -/
def tightDiv (I J : QInterval) (h : 0 < J.lo ∨ J.hi < 0) : QInterval :=
  tightMul I (tightInv J h)

theorem mem_tightDiv {I J : QInterval} {x y : ℝ}
    (h : 0 < J.lo ∨ J.hi < 0) (hx : I.Contains x) (hy : J.Contains y) :
    (tightDiv I J h).Contains (x / y) := by
  simpa only [tightDiv, div_eq_mul_inv, one_mul] using mem_tightMul hx (mem_tightInv h hy)

end QInterval

/-- Horner evaluation using the exact endpoint product and the existing coefficients. -/
def tightIntervalHorner : List ℚ → QInterval → QInterval
  | [], _ => QInterval.point 0
  | a :: as, I => QInterval.add (QInterval.point a)
      (QInterval.tightMul I (tightIntervalHorner as I))

theorem tightIntervalHorner_sound (coefficients : List ℚ) (I : QInterval)
    {x : ℝ} (hx : I.Contains x) :
    (tightIntervalHorner coefficients I).Contains (horner coefficients x) := by
  induction coefficients with
  | nil => simpa [tightIntervalHorner, horner] using QInterval.mem_point (0 : ℚ)
  | cons a coefficients ih =>
      simpa only [tightIntervalHorner, horner] using
        QInterval.mem_add (QInterval.mem_point a) (QInterval.mem_tightMul hx ih)

/-- The same Taylor-cell data, evaluated with the sharper product. -/
def TaylorCell.tightPolynomialRange (C : TaylorCell) : QInterval :=
  tightIntervalHorner C.coefficients (shift C.domain C.center)

/-- A sharper executable check with exactly the original Taylor-cell inputs. -/
def checkTightTaylorCell (lower : ℚ) (C : TaylorCell) : Bool :=
  decide (0 ≤ C.remainder ∧ lower ≤ C.tightPolynomialRange.lo - C.remainder)

/-- Directed Taylor soundness reuses the existing analytic remainder predicate. -/
theorem checkTightTaylorCell_lower_sound {f : ℝ → ℝ} {lower : ℚ} {C : TaylorCell}
    (hcheck : checkTightTaylorCell lower C = true)
    (hrem : TaylorLowerRemainderValid f C) {x : ℝ} (hx : C.domain.Contains x) :
    (lower : ℝ) ≤ f x := by
  have hc : 0 ≤ C.remainder ∧ lower ≤ C.tightPolynomialRange.lo - C.remainder :=
    of_decide_eq_true hcheck
  have hpoly := tightIntervalHorner_sound C.coefficients
    (shift C.domain C.center) (mem_shift hx)
  have hmargin : (lower : ℝ) ≤ (C.tightPolynomialRange.lo : ℝ) - C.remainder := by
    exact_mod_cast hc.2
  have hlow : (C.tightPolynomialRange.lo : ℝ) ≤
      horner C.coefficients (x - C.center) := hpoly.1
  have hr := hrem x hx
  linarith

/-- Two-sided Taylor soundness is an immediate use of the same arithmetic check. -/
theorem checkTightTaylorCell_sound {f : ℝ → ℝ} {lower : ℚ} {C : TaylorCell}
    (hcheck : checkTightTaylorCell lower C = true)
    (hrem : TaylorRemainderValid f C) {x : ℝ} (hx : C.domain.Contains x) :
    (lower : ℝ) ≤ f x := by
  apply checkTightTaylorCell_lower_sound hcheck ?_ hx
  intro y hy
  exact (abs_le.mp (hrem y hy)).1

end ContourKit
