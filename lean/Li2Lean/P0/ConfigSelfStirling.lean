/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib.Analysis.SpecialFunctions.Stirling
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Tactic

open Filter
open scoped Topology

namespace Li2Lean.P0.Config.SelfCells

noncomputable section

/-- Robbins' stepwise bound in the pinned Mathlib makes this corrected
logarithmic Stirling sequence increasing. -/
lemma correctedStirling_monotone : Monotone (fun n : ℕ =>
    Real.log (Stirling.stirlingSeq (n + 1)) - 1 / (12 * ((n + 1 : ℕ) : ℝ))) := by
  apply monotone_nat_of_le_succ
  intro n
  have hs := Stirling.log_stirlingSeq_sdiff_le (n + 1)
  have hden :
      (1 : ℝ) / (12 * ((n + 1 : ℕ) : ℝ) * (((n + 1 : ℕ) : ℝ) + 1)) =
        1 / (12 * ((n + 1 : ℕ) : ℝ)) -
          1 / (12 * ((n + 2 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [hden] at hs
  simp only [Nat.add_assoc] at hs
  simpa only [Nat.add_assoc] using sub_nonneg.mp (by linarith :
    0 ≤ (Real.log (Stirling.stirlingSeq (n + 2)) - 1 / (12 * ((n + 2 : ℕ) : ℝ))) -
      (Real.log (Stirling.stirlingSeq (n + 1)) - 1 / (12 * ((n + 1 : ℕ) : ℝ))))

lemma correctedStirling_tendsto : Tendsto (fun n : ℕ =>
    Real.log (Stirling.stirlingSeq (n + 1)) - 1 / (12 * ((n + 1 : ℕ) : ℝ)))
    atTop (𝓝 (Real.log (Real.sqrt Real.pi))) := by
  have hlog := (Real.continuousAt_log (show Real.sqrt Real.pi ≠ 0 by positivity)).tendsto.comp
    (Stirling.tendsto_stirlingSeq_sqrt_pi.comp (tendsto_add_atTop_nat 1))
  have hrem : Tendsto (fun n : ℕ => 1 / (12 * ((n + 1 : ℕ) : ℝ))) atTop (𝓝 0) := by
    simpa only [div_mul_eq_div_div, Function.comp_def] using
      (tendsto_const_div_atTop_nhds_zero_nat (1 / 12 : ℝ)).comp (tendsto_add_atTop_nat 1)
  simpa only [sub_zero, Function.comp_apply] using hlog.sub hrem

/-- The effective upper Stirling bound, derived from Mathlib's full
Stirling limit and Robbins' successive-difference estimate. -/
theorem log_factorial_stirling_upper (n : ℕ) (hn : 0 < n) :
    Real.log (n.factorial : ℝ) ≤
      (n : ℝ) * Real.log n - n + Real.log n / 2 +
        Real.log (2 * Real.pi) / 2 + 1 / (12 * n) := by
  have hc : Real.log (Stirling.stirlingSeq n) - 1 / (12 * (n : ℝ)) ≤
      Real.log (Real.sqrt Real.pi) := by
    have h := correctedStirling_monotone.ge_of_tendsto correctedStirling_tendsto (n - 1)
    simpa [Nat.sub_add_cancel hn] using h
  have hnR : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hn)
  rw [Stirling.log_stirlingSeq_formula, Real.log_mul (by norm_num) hnR,
    Real.log_div hnR (Real.exp_ne_zero 1), Real.log_exp,
    Real.log_sqrt Real.pi_pos.le] at hc
  rw [Real.log_mul (by norm_num) (ne_of_gt Real.pi_pos)]
  linarith

/-- The primitive increment supplies enough remainder to pay the entire
Robbins upper error, preserving the paper's exact `log(2*pi)` budget. -/
theorem quadraticLogIncrement_lower (n : ℕ) (hn : 0 < n) :
    (n : ℝ) * Real.log n - n + Real.log n / 2 + 1 / (12 * n) ≤
      (((n : ℝ) + 1) ^ 2 / 2 * Real.log ((n : ℝ) + 1) -
        3 / 4 * ((n : ℝ) + 1) ^ 2) -
      ((n : ℝ) ^ 2 / 2 * Real.log n - 3 / 4 * (n : ℝ) ^ 2) := by
  have hnR : (0 : ℝ) < n := Nat.cast_pos.mpr hn
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hlog := Real.le_log_one_add_of_nonneg (show 0 ≤ (1 : ℝ) / n by positivity)
  have harg : 1 + (1 : ℝ) / n = ((n : ℝ) + 1) / n := by field_simp
  have hrat : (2 : ℝ) * (1 / n) / (1 / n + 2) = 2 / (2 * (n : ℝ) + 1) := by
    field_simp
    ring
  rw [harg, hrat, Real.log_div (by positivity) hnR.ne'] at hlog
  have hmul := mul_le_mul_of_nonneg_left hlog
    (show 0 ≤ ((n : ℝ) + 1) ^ 2 / 2 by positivity)
  have hident : ((n : ℝ) + 1) ^ 2 / 2 * (2 / (2 * (n : ℝ) + 1)) -
      (n : ℝ) / 2 - 3 / 4 = 1 / (4 * (2 * (n : ℝ) + 1)) := by
    field_simp
    ring
  have hrem : (1 : ℝ) / (12 * n) ≤ 1 / (4 * (2 * (n : ℝ) + 1)) := by
    apply one_div_le_one_div_of_le (by positivity)
    linarith
  rw [← hident] at hrem
  nlinarith

/-- The primitive `H` restricted to nonnegative lattice arguments. The
formula has the paper's exact zero convention because `Real.log 0 = 0`. -/
def latticeH (n : ℕ) : ℝ :=
  (n : ℝ) ^ 2 / 2 * Real.log n - 3 / 4 * (n : ℝ) ^ 2

/-- The exact lattice-distance error `e_(n+1)` of v10 `eq:config-self`. -/
def cellError (n : ℕ) : ℝ :=
  Real.log ((n + 1 : ℕ) : ℝ) - (latticeH (n + 2) + latticeH n - 2 * latticeH (n + 1))

/-- Half of the off-diagonal error budget remaining after the exact
`3/2` diagonal-cell cost. -/
def cellErrorBudget : ℝ := Real.log (2 * Real.pi) / 2 - 3 / 4

lemma cellErrorBudget_nonneg : 0 ≤ cellErrorBudget := by
  have h2 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 1 by norm_num)
  have h3 := Real.le_log_one_add_of_nonneg (show (0 : ℝ) ≤ 2 by norm_num)
  norm_num at h2 h3
  have h6 : Real.log 6 ≤ Real.log (2 * Real.pi) :=
    Real.log_le_log (by norm_num) (by nlinarith [Real.pi_gt_three])
  have heq : Real.log (6 : ℝ) = Real.log 2 + Real.log 3 := by
    rw [← Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ≠ 0)]
    norm_num
  rw [heq] at h6
  unfold cellErrorBudget
  linarith

/-- Exact telescoping of the finite distance-error sum. -/
theorem sum_cellError (N : ℕ) :
    (∑ n ∈ Finset.range N, cellError n) =
      Real.log (N.factorial : ℝ) - latticeH (N + 1) + latticeH N - 3 / 4 := by
  induction N with
  | zero => norm_num [latticeH]
  | succ N ih =>
      rw [Finset.sum_range_succ, ih, cellError,
        Nat.factorial_succ, Nat.cast_mul,
        Real.log_mul (by positivity) (by positivity)]
      simp only [Nat.add_assoc]
      ring

/-- Every finite initial sum obeys the paper's sharp total error budget.
The Robbins remainder is paid by the exact primitive increment; no
upper bound on the largest lattice distance is imposed. -/
theorem sum_cellError_le (N : ℕ) :
    (∑ n ∈ Finset.range N, cellError n) ≤ cellErrorBudget := by
  rcases Nat.eq_zero_or_pos N with hN | hN
  · subst N
    simpa using cellErrorBudget_nonneg
  · have hs := log_factorial_stirling_upper N hN
    have hH : (N : ℝ) * Real.log N - N + Real.log N / 2 + 1 / (12 * N) ≤
        latticeH (N + 1) - latticeH N := by
      simpa only [latticeH, Nat.cast_add, Nat.cast_one] using quadraticLogIncrement_lower N hN
    rw [sum_cellError]
    unfold cellErrorBudget
    linarith

end

end Li2Lean.P0.Config.SelfCells
