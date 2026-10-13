/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyTailArithmetic

/-!
# The literal binomial frequency generating function

This file proves the generating-function and scalar-tail step of v10
`sec-frequency-tail.tex`. All sums use the actual `frequencyWeightReal`.
Convergence is obtained from the classical binomial geometric series.
-/

namespace Li2Lean.P0.FrequencyGenerating

noncomputable section

open scoped BigOperators

/-- The literal real weight from v10; definitionally equal to `P0.frequencyWeightReal`. -/
abbrev frequencyWeightReal (g r : ℕ) : ℝ :=
  (Nat.choose (r - 1) g : ℝ) / (2 : ℝ) ^ r

/-- The full weighted generating series, with exactly the paper's range `r > g`. -/
def weightedTerm (g : ℕ) (t : ℝ) (r : ℕ) : ℝ :=
  if g < r then frequencyWeightReal g r * t ^ r else 0

/-- A literal frequency tail, with exactly the strict cutoff `r > H`. -/
def tailTerm (g H r : ℕ) : ℝ :=
  if H < r then frequencyWeightReal g r else 0

/-- The paper's `b_m`, prior to any scalar majorization. -/
def tailCoefficient (m : ℕ) : ℝ :=
  ((m : ℝ) / 1600) * (12500 : ℝ) ^ m *
    ∑' r : ℕ, tailTerm (m / 2) (20 * m) r

theorem weight_nonneg (g r : ℕ) : 0 ≤ frequencyWeightReal g r := by
  unfold frequencyWeightReal
  positivity

/-- The shifted form of the paper's exact generating function. -/
theorem hasSum_weighted_shift (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    HasSum (fun n : ℕ =>
      frequencyWeightReal g (n + g + 1) * t ^ (n + g + 1))
      ((t / (2 - t)) ^ (g + 1)) := by
  have hnorm : ‖t / 2‖ < 1 := by
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    linarith
  have hs := (hasSum_choose_mul_geometric_of_norm_lt_one g hnorm).mul_right
    ((t / 2) ^ (g + 1))
  convert hs using 1
  · funext n
    simp only [frequencyWeightReal, Nat.add_sub_cancel, div_pow]
    rw [show n + g + 1 = n + (g + 1) by omega, pow_add, pow_add]
    ring
  · rw [one_div_mul_eq_div, ← div_pow]
    congr 1
    field_simp

/-- `sum_{r>g} w_r t^r = (t/(2-t))^(g+1)`, with convergence included. -/
theorem hasSum_weighted (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    HasSum (weightedTerm g t) ((t / (2 - t)) ^ (g + 1)) := by
  have hz : ∑ r ∈ Finset.range (g + 1), weightedTerm g t r = 0 := by
    apply Finset.sum_eq_zero
    intro r hr
    simp only [Finset.mem_range] at hr
    simp [weightedTerm, show ¬g < r by omega]
  have hs : HasSum (fun n : ℕ => weightedTerm g t (n + (g + 1)))
      ((t / (2 - t)) ^ (g + 1)) := by
    simpa [weightedTerm, Nat.add_assoc, show ∀ n : ℕ, g < n + (g + 1) by omega]
      using hasSum_weighted_shift g ht0 ht2
  have h := (hasSum_nat_add_iff (g + 1)).mp hs
  simpa only [hz, add_zero] using h

/-- The same exact series written literally over the paper's subtype `r > g`. -/
theorem hasSum_weighted_subtype (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    HasSum (fun r : {r : ℕ // g < r} => frequencyWeightReal g r.val * t ^ r.val)
      ((t / (2 - t)) ^ (g + 1)) := by
  apply (hasSum_subtype_iff_indicator
    (s := {r : ℕ | g < r}) (f := fun r => frequencyWeightReal g r * t ^ r)).2
  refine (hasSum_weighted g ht0 ht2).congr_fun ?_
  intro r
  by_cases hr : g < r <;> simp [weightedTerm, Set.indicator, hr]

/-- The exact evaluation at `t=15/8` in v10, including summability. -/
theorem hasSum_weighted_fifteen_eighths (g : ℕ) :
    HasSum (weightedTerm g (15 / 8)) ((15 : ℝ) ^ (g + 1)) := by
  have h := hasSum_weighted g (t := 15 / 8) (by norm_num) (by norm_num)
  norm_num at h ⊢
  exact h

theorem weightedTerm_nonneg (g r : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    0 ≤ weightedTerm g t r := by
  unfold weightedTerm
  split_ifs
  · exact mul_nonneg (weight_nonneg g r) (pow_nonneg ht r)
  · exact le_rfl

theorem tailTerm_nonneg (g H r : ℕ) : 0 ≤ tailTerm g H r := by
  unfold tailTerm
  split_ifs
  · exact weight_nonneg g r
  · exact le_rfl

/-- The literal strict-cutoff tail is summable, by domination by the generating series. -/
theorem summable_tail (g H : ℕ) (hgH : g ≤ H) :
    Summable (tailTerm g H) := by
  apply Summable.of_nonneg_of_le (tailTerm_nonneg g H) _
    (hasSum_weighted_fifteen_eighths g).summable
  intro r
  by_cases hr : H < r
  · have hgr : g < r := lt_of_le_of_lt hgH hr
    simp only [tailTerm, weightedTerm, ite_eq_left hr, ite_eq_left hgr]
    have hp : (1 : ℝ) ≤ (15 / 8 : ℝ) ^ r := one_le_pow₀ (by norm_num)
    nlinarith [weight_nonneg g r]
  · simp only [tailTerm, ite_eq_right hr]
    exact weightedTerm_nonneg g r (by norm_num)

/-- Every finite strict tail is bounded by the convergent full strict tail. -/
theorem finiteWeightTail_le_tsum (g H M : ℕ) (hgH : g ≤ H) :
    (∑ r ∈ Finset.Ioc H M, frequencyWeightReal g r) ≤
      ∑' r : ℕ, tailTerm g H r := by
  have hs := summable_tail g H hgH
  calc
    (∑ r ∈ Finset.Ioc H M, frequencyWeightReal g r) =
        ∑ r ∈ Finset.Ioc H M, tailTerm g H r := by
      apply Finset.sum_congr rfl
      intro r hr
      rw [tailTerm, ite_eq_left (Finset.mem_Ioc.mp hr).1]
    _ ≤ ∑' r : ℕ, tailTerm g H r :=
      Summable.sum_le_tsum (Finset.Ioc H M)
        (fun r _ => tailTerm_nonneg g H r) hs

/-- The exact exponential tail bound furnished by the evaluation at `15/8`. -/
theorem tail_le_generating_bound (g H : ℕ) (hgH : g ≤ H) :
    (∑' r : ℕ, tailTerm g H r) ≤
      (8 / 15 : ℝ) ^ H * (15 : ℝ) ^ (g + 1) := by
  have hs := summable_tail g H hgH
  have hweighted := hasSum_weighted_fifteen_eighths g
  have hpoint : ∀ r : ℕ,
      (15 / 8 : ℝ) ^ H * tailTerm g H r ≤ weightedTerm g (15 / 8) r := by
    intro r
    by_cases hr : H < r
    · have hgr : g < r := lt_of_le_of_lt hgH hr
      simp only [tailTerm, weightedTerm, ite_eq_left hr, ite_eq_left hgr]
      calc
        (15 / 8 : ℝ) ^ H * frequencyWeightReal g r ≤
            (15 / 8 : ℝ) ^ r * frequencyWeightReal g r := by
          apply mul_le_mul_of_nonneg_right _ (weight_nonneg g r)
          exact pow_le_pow_right₀ (by norm_num) (Nat.le_of_lt hr)
        _ = frequencyWeightReal g r * (15 / 8 : ℝ) ^ r := mul_comm _ _
    · simp only [tailTerm, ite_eq_right hr, mul_zero]
      exact weightedTerm_nonneg g r (by norm_num)
  have h := Summable.tsum_le_tsum hpoint (hs.mul_left _) hweighted.summable
  rw [tsum_mul_left, hweighted.tsum_eq] at h
  have hp : 0 < (15 / 8 : ℝ) ^ H := by positivity
  have hi : (8 / 15 : ℝ) ^ H * (15 / 8 : ℝ) ^ H = 1 := by
    rw [← mul_pow]
    norm_num
  have h' := mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ (8 / 15 : ℝ) ^ H)
  simpa only [← mul_assoc, hi, one_mul] using h'

/-- The half-size binomial parameter incurs at most the factor `15 * 4^m`. -/
theorem fifteen_pow_half_le (m : ℕ) :
    (15 : ℝ) ^ (m / 2 + 1) ≤ 15 * (4 : ℝ) ^ m := by
  rw [pow_succ, mul_comm]
  apply mul_le_mul_of_nonneg_left _ (by norm_num)
  calc
    (15 : ℝ) ^ (m / 2) ≤ (16 : ℝ) ^ (m / 2) :=
      pow_le_pow_left₀ (by norm_num) (by norm_num) _
    _ = (4 : ℝ) ^ (2 * (m / 2)) := by rw [pow_mul]; norm_num
    _ ≤ (4 : ℝ) ^ m := pow_le_pow_right₀ (by norm_num) (by omega)

/-- The actual `b_m` satisfies the scalar estimate used by the existing absorption lemma. -/
theorem tailCoefficient_le_paperTailBound (m : ℕ) :
    tailCoefficient m ≤ FrequencyTailArithmetic.paperTailBound m := by
  have ht := tail_le_generating_bound (m / 2) (20 * m) (by omega)
  have hp := fifteen_pow_half_le m
  unfold tailCoefficient FrequencyTailArithmetic.paperTailBound
    FrequencyTailArithmetic.geometricTailBase
  calc
    ((m : ℝ) / 1600) * (12500 : ℝ) ^ m *
        (∑' r : ℕ, tailTerm (m / 2) (20 * m) r) ≤
      ((m : ℝ) / 1600) * (12500 : ℝ) ^ m *
        ((8 / 15 : ℝ) ^ (20 * m) * (15 : ℝ) ^ (m / 2 + 1)) := by
          exact mul_le_mul_of_nonneg_left ht (by positivity)
    _ ≤ ((m : ℝ) / 1600) * (12500 : ℝ) ^ m *
        ((8 / 15 : ℝ) ^ (20 * m) * (15 * (4 : ℝ) ^ m)) := by
          gcongr
    _ = (15 * (m : ℝ) / 1600) *
        ((50000 : ℝ) * (8 / 15 : ℝ) ^ 20) ^ m := by
          rw [mul_pow, pow_mul]
          have hp : (50000 : ℝ) ^ m = (12500 : ℝ) ^ m * (4 : ℝ) ^ m := by
            rw [← mul_pow]
            norm_num
          rw [hp]
          ring

/-- The fully instantiated generating-function estimate closes the scalar R5 budget. -/
theorem tailCoefficient_le_replacementTailRatio (m : ℕ) :
    tailCoefficient m ≤ FrequencyTail.replacementTailRatio m :=
  (tailCoefficient_le_paperTailBound m).trans
    (FrequencyTailArithmetic.paperTailBound_le_replacementTailRatio m)

theorem tailCoefficient_lt_half (m : ℕ) : tailCoefficient m < 1 / 2 :=
  lt_of_le_of_lt (tailCoefficient_le_paperTailBound m)
    (FrequencyTailArithmetic.paperTailBound_lt_half m)

end

end Li2Lean.P0.FrequencyGenerating
