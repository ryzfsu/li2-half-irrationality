/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSelfMeasure

open MeasureTheory

namespace Li2Lean.P0.Config.SelfCells

noncomputable section

lemma log_lattice_distance (m : ℕ) (hm : 0 < m) (i j : ℕ) (hij : i ≠ j) :
    Real.log |(i : ℝ) / m - (j : ℝ) / m| =
      Real.log (Nat.dist i j : ℝ) - Real.log (m : ℝ) := by
  have hm0 : (m : ℝ) ≠ 0 := by positivity
  have hd0 : (i : ℝ) - (j : ℝ) ≠ 0 := by
    intro h
    apply hij
    exact_mod_cast sub_eq_zero.mp h
  have heq : (i : ℝ) / m - (j : ℝ) / m = ((i : ℝ) - j) / m := by ring
  rw [heq, Real.log_abs, Real.log_div hd0 hm0, nat_dist_cast, Real.log_abs]

/-- Each ordered pair splits exactly into its actual cell integral,
the diagonal self-cell cost, and the nonnegative distance error. -/
lemma pair_log_identity (m : ℕ) (hm : 0 < m) (i j : ℕ) :
    (if i = j then 0 else Real.log |(i : ℝ) / m - (j : ℝ) / m|) =
      (m : ℝ) ^ 2 * cellLogIntegral m i j +
        (if i = j then Real.log (m : ℝ) + 3 / 2 else 0) +
        (if i = j then 0 else cellError (Nat.dist i j - 1)) := by
  rw [cellLogIntegral_scaled m hm i j, unitCellLog_nat_dist]
  by_cases hij : i = j
  · subst j
    simp only [ite_true, Nat.dist_self, Nat.cast_zero, unitCellLog_zero]
    ring
  · rw [if_neg hij, if_neg hij, if_neg hij,
      unitCellLog_nat (Nat.dist i j) (Nat.dist_pos_of_ne hij),
      log_lattice_distance m hm i j hij]
    ring

lemma diagonal_constant_sum (sites : Finset ℕ) (c : ℝ) :
    (∑ i ∈ sites, ∑ j ∈ sites, if i = j then c else 0) = (sites.card : ℝ) * c := by
  calc
    _ = ∑ i ∈ sites, c := by
      apply Finset.sum_congr rfl
      intro i hi
      simp [hi]
    _ = _ := by simp

/-- Exact decomposition of the ordered logarithmic sum against the actual
product cell measure. -/
theorem latticeOffDiagonalLogSum_eq (m : ℕ) (hm : 0 < m) (sites : Finset ℕ) :
    latticeOffDiagonalLogSum m sites =
      (m : ℝ) ^ 2 *
        (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
          ∂((latticeCellMeasure m sites).prod (latticeCellMeasure m sites))) +
      (sites.card : ℝ) * (Real.log (m : ℝ) + 3 / 2) +
      (∑ i ∈ sites, ∑ j ∈ sites,
        if i = j then 0 else cellError (Nat.dist i j - 1)) := by
  unfold latticeOffDiagonalLogSum
  simp_rw [pair_log_identity m hm]
  simp_rw [Finset.sum_add_distrib]
  rw [diagonal_constant_sum, latticeCellMeasure_log_eq]
  simp_rw [Finset.mul_sum]

end
end Li2Lean.P0.Config.SelfCells

namespace Li2Lean.P0.Config

/-- The literal v10 `eq:config-self` from docs/6333, section 5, for every
finite set of distinct nonnegative lattice sites and every positive mesh
denominator. There is no maximum-frequency, positivity-of-integrand, or
separation assumption. -/
theorem selfCellBound : SelfCellBound := by
  intro m hm sites
  rw [SelfCells.latticeOffDiagonalLogSum_eq m hm sites]
  have herror := SelfCells.cellError_double_sum_le sites
  nlinarith

end Li2Lean.P0.Config
