/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyFinite
import Li2Lean.P0.FrequencyGenerating

open Finset

namespace Li2Lean.P0.FrequencyFinite

open Li2Lean.P0.FrequencyLeaf

noncomputable section

/-! Assembly of the exact finite replacement sum with the proved binomial
generating-function tail. The analytic ratio input is explicit; the
infinite contour-envelope passage is a separate theorem. -/

theorem weight_eq_generatingWeight (g r : ℕ) :
    weight g r = FrequencyGenerating.frequencyWeightReal g r := by
  simp [weight, FrequencyGenerating.frequencyWeightReal, div_eq_mul_inv]

/-- The finite coefficient is bounded by the paper's actual infinite-tail
coefficient `b_m`, with summability discharged by the generating function. -/
theorem finiteTailCoefficient_le_tailCoefficient (m M : ℕ) :
    finiteTailCoefficient m M ≤ FrequencyGenerating.tailCoefficient m := by
  unfold finiteTailCoefficient FrequencyGenerating.tailCoefficient
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [weight_eq_generatingWeight] using
    FrequencyGenerating.finiteWeightTail_le_tsum (m / 2) (20 * m) M (by omega)

theorem finiteTailCoefficient_le_replacementTailRatio (m M : ℕ) :
    finiteTailCoefficient m M ≤ FrequencyTail.replacementTailRatio m :=
  (finiteTailCoefficient_le_tailCoefficient m M).trans
    (FrequencyGenerating.tailCoefficient_le_replacementTailRatio m)

theorem frequencyZ_nonneg (m M : ℕ) (S : Finset ℕ) (d : ℕ) (Z : Fin d → ℂ) :
    0 ≤ frequencyZ m M S d Z := by
  unfold frequencyZ finiteZ
  exact Finset.sum_nonneg (fun R _ => frequencyFactor_nonneg m (m / 2) S R d Z)

theorem frequencyZ_sub_nonneg {m M : ℕ} (hM : 20 * m ≤ M)
    (S : Finset ℕ) (d : ℕ) (Z : Fin d → ℂ) :
    0 ≤ frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z := by
  unfold frequencyZ
  rw [finiteZ_sub_eq_tail hM]
  exact Finset.sum_nonneg (fun R _ => frequencyFactor_nonneg _ _ _ R _ _)

/-- The paper's exact finite replacement inequality with the actual
infinite-tail coefficient `b_m`. -/
theorem finiteFrequencyTail_of_ratio {m M : ℕ}
    (hm : 0 < m) (hM : 20 * m ≤ M) (S : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ)
    (hratio : ∀ R ∈ tailFamily m M,
      frequencyFactor m (m / 2) S R d Z ≤
        ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (largest R : ℝ) ^ 2) *
          weight (m / 2) (largest R)) *
          frequencyFactor m (m / 2) S (replacement m R) d Z) :
    frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z ≤
      FrequencyGenerating.tailCoefficient m * frequencyZ m M S d Z := by
  exact (finiteFrequencyTransfer_of_ratio hm hM S d Z hratio).trans
    (mul_le_mul_of_nonneg_right (finiteTailCoefficient_le_tailCoefficient m M)
      (frequencyZ_nonneg m M S d Z))

/-- Finite-cutoff form of v10 `eq:frequency-cutoff`, after the exact
replacement transport, generating function, and `b_m < 1/2` absorption.
Only the analytic multiplicative ratio remains as an input here. -/
theorem finiteFrequencyCutoff_of_ratio {m M : ℕ}
    (hm : 0 < m) (hM : 20 * m ≤ M) (S : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ)
    (hratio : ∀ R ∈ tailFamily m M,
      frequencyFactor m (m / 2) S R d Z ≤
        ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (largest R : ℝ) ^ 2) *
          weight (m / 2) (largest R)) *
          frequencyFactor m (m / 2) S (replacement m R) d Z) :
    frequencyZ m M S d Z ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * frequencyZ m (20 * m) S d Z := by
  have htail := frequencyZ_sub_nonneg hM S d Z
  have heq : frequencyZ m (20 * m) S d Z +
      (frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z) =
      frequencyZ m M S d Z := by ring
  have hbound : frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z ≤
      FrequencyTail.replacementTailRatio m *
        (frequencyZ m (20 * m) S d Z +
          (frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z)) := by
    rw [heq]
    exact (finiteFrequencyTail_of_ratio hm hM S d Z hratio).trans
      (mul_le_mul_of_nonneg_right
        (FrequencyGenerating.tailCoefficient_le_replacementTailRatio m)
        (frequencyZ_nonneg m M S d Z))
  simpa only [heq] using FrequencyTail.finiteCutoff_absorption htail hbound

end

end Li2Lean.P0.FrequencyFinite
