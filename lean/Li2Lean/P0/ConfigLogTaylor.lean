/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Agents.F_L8.Types
import Mathlib.Analysis.SpecialFunctions.Log.Deriv

/-!
Exact rational logarithm enclosures for the v10 Appendix A expressions.

The finite arithmetic checks below imply real logarithm bounds by the proved
atanh series remainder. No analytic enclosure or Taylor remainder is an input
to their soundness statements. These scalar operations do not, on their own,
identify the reference potentials or certify the complete C-A cell tables.
-/

namespace Li2Lean.P0.ConfigLogTaylor

open ContourKit Finset

/-- The rational atanh coordinate for a positive logarithm argument. -/
def logCoordinate (q : ℚ) : ℚ := (q - 1) / (q + 1)

/-- Twice the first `n` odd terms of the atanh series. -/
def logPolynomial (q : ℚ) (n : ℕ) : ℚ :=
  2 * ∑ k ∈ Finset.range n,
    logCoordinate q ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)

/-- An exact geometric bound for the omitted odd series terms. -/
def logRemainder (q : ℚ) (n : ℕ) : ℚ :=
  2 * (|logCoordinate q| ^ (2 * n + 1) / (1 - logCoordinate q ^ 2))

theorem abs_logCoordinate_lt_one {q : ℚ} (hq : 0 < q) :
    |(logCoordinate q : ℝ)| < 1 := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : (0 : ℝ) < q + 1 := by linarith
  simp only [logCoordinate, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
    Rat.cast_add]
  rw [abs_lt]
  constructor
  · rw [lt_div_iff₀ hd]
    linarith
  · rw [div_lt_iff₀ hd]
    linarith

theorem logCoordinate_ratio {q : ℚ} (hq : 0 < q) :
    (1 + (logCoordinate q : ℝ)) / (1 - (logCoordinate q : ℝ)) = q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hd : (q : ℝ) + 1 ≠ 0 := by linarith
  simp only [logCoordinate, Rat.cast_div, Rat.cast_sub, Rat.cast_one,
    Rat.cast_add]
  field_simp
  ring

/-- The analytic remainder for every positive rational logarithm argument.
This is the semantic theorem consumed by the finite arithmetic checker. -/
theorem logPolynomial_remainder {q : ℚ} (hq : 0 < q) (n : ℕ) :
    |Real.log (q : ℝ) - (logPolynomial q n : ℝ)| ≤
      (logRemainder q n : ℝ) := by
  have h := Real.sum_range_sub_log_div_le (abs_logCoordinate_lt_one hq) n
  rw [logCoordinate_ratio hq] at h
  have hboth := abs_le.mp h
  push_cast [logPolynomial, logRemainder]
  apply abs_le.mpr
  constructor <;> nlinarith [hboth.1, hboth.2]

/-- For arguments at least one, the lower series bound is directed and
does not spend the geometric remainder a second time. -/
theorem logPolynomial_le_log {q : ℚ} (hq : 1 ≤ q) (n : ℕ) :
    (logPolynomial q n : ℝ) ≤ Real.log (q : ℝ) := by
  have hqpos : 0 < q := lt_of_lt_of_le (by norm_num) hq
  have hx : (0 : ℝ) ≤ logCoordinate q := by
    have : 0 ≤ logCoordinate q := by
      unfold logCoordinate
      exact div_nonneg (sub_nonneg.mpr hq) (by linarith)
    exact_mod_cast this
  have h := Real.sum_range_le_log_div hx
    (lt_of_le_of_lt (le_abs_self _) (abs_logCoordinate_lt_one hqpos)) n
  rw [logCoordinate_ratio hqpos] at h
  push_cast [logPolynomial]
  linarith

/-- A purely rational check for a logarithm enclosure over an entire cell. -/
def checkLogInterval (n : ℕ) (domain enclosure : QInterval) : Bool :=
  decide (0 < domain.lo ∧
    enclosure.lo ≤ logPolynomial domain.lo n - logRemainder domain.lo n ∧
    logPolynomial domain.hi n + logRemainder domain.hi n ≤ enclosure.hi)

/-- Soundness includes monotonic transport from both rational endpoints.
Only the Boolean arithmetic check and real cell membership are premises. -/
theorem checkLogInterval_sound {n : ℕ} {domain enclosure : QInterval}
    (hcheck : checkLogInterval n domain enclosure = true)
    {x : ℝ} (hx : domain.Contains x) : enclosure.Contains (Real.log x) := by
  have hs : 0 < domain.lo ∧
      enclosure.lo ≤ logPolynomial domain.lo n - logRemainder domain.lo n ∧
      logPolynomial domain.hi n + logRemainder domain.hi n ≤ enclosure.hi :=
    of_decide_eq_true hcheck
  have hlo := abs_le.mp (logPolynomial_remainder hs.1 n)
  have hhi := abs_le.mp (logPolynomial_remainder
    (lt_of_lt_of_le hs.1 domain.ordered) n)
  have hpos : (0 : ℝ) < domain.lo := by exact_mod_cast hs.1
  have hxpos : 0 < x := lt_of_lt_of_le hpos hx.1
  have hleft := Real.log_le_log hpos hx.1
  have hright := Real.log_le_log hxpos hx.2
  have hloR : (enclosure.lo : ℝ) ≤
      (logPolynomial domain.lo n : ℝ) - (logRemainder domain.lo n : ℝ) := by
    exact_mod_cast hs.2.1
  have hhiR : (logPolynomial domain.hi n : ℝ) +
      (logRemainder domain.hi n : ℝ) ≤ (enclosure.hi : ℝ) := by
    exact_mod_cast hs.2.2
  constructor <;> linarith

/-- The lower-cell check used when only a directed lower bound is required. -/
def checkLogLowerCell (n : ℕ) (cell : Li2Lean.F_L8.ReceiptCell) : Bool :=
  decide (0 < cell.lo ∧
    cell.lower ≤ logPolynomial cell.lo n - logRemainder cell.lo n)

/-- The C-A receipt model obtains its genuine analytic lower remainder from
the rational log check, rather than taking that remainder as a premise. -/
theorem checkLogLowerCell_remainder {n : ℕ} {cell : Li2Lean.F_L8.ReceiptCell}
    (hcheck : checkLogLowerCell n cell = true) (hwidth : cell.lo ≤ cell.hi) :
    cell.modelRemainderValid Real.log hwidth := by
  have hs : 0 < cell.lo ∧
      cell.lower ≤ logPolynomial cell.lo n - logRemainder cell.lo n :=
    of_decide_eq_true hcheck
  intro x hx
  have hpos : (0 : ℝ) < cell.lo := by exact_mod_cast hs.1
  have hlog := Real.log_le_log hpos hx.1
  have hrem := (abs_le.mp (logPolynomial_remainder hs.1 n)).1
  have hmargin : (cell.lower : ℝ) ≤
      (logPolynomial cell.lo n : ℝ) - (logRemainder cell.lo n : ℝ) := by
    exact_mod_cast hs.2
  simp only [Li2Lean.F_L8.ReceiptCell.model, horner, mul_zero, add_zero,
    Rat.cast_zero, neg_zero]
  linarith

/-- Convenient point upper bound: the supplied comparison is exact rational
arithmetic and the logarithmic remainder is proved internally. -/
theorem log_lt_of_rational {q upper : ℚ} (hq : 0 < q) (n : ℕ)
    (hbound : logPolynomial q n + logRemainder q n < upper) :
    Real.log (q : ℝ) < (upper : ℝ) := by
  have h := (abs_le.mp (logPolynomial_remainder hq n)).2
  have hb : (logPolynomial q n : ℝ) + (logRemainder q n : ℝ) < (upper : ℝ) := by
    exact_mod_cast hbound
  linarith

end Li2Lean.P0.ConfigLogTaylor
