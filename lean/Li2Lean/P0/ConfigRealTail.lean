/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigSegment

open MeasureTheory

namespace Li2Lean.P0.ConfigRealTail

noncomputable section

open Li2Lean.LogSegment Li2Lean.P0.ConfigSegment

/-- The elementary logarithm estimate for a real cell strictly to the left
of the evaluation point. No numerical enclosure is assumed. -/
theorem log_difference_le {a b t : ℝ} (hab : a ≤ b) (ht : b < t) :
    Real.log |t - a| - Real.log |t - b| ≤ (b - a) / (t - b) := by
  have ha : 0 < t - a := by linarith
  have hb : 0 < t - b := by linarith
  rw [abs_of_pos ha, abs_of_pos hb, ← Real.log_div ha.ne' hb.ne']
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  have heq : (t - a) / (t - b) - 1 = (b - a) / (t - b) := by
    field_simp
    ring
  rwa [heq] at h

/-- Reflected-cell slope lower bound for the positive-frequency field. -/
theorem log_add_difference_ge {a b t : ℝ} (ha : 0 < t + a) (hb : 0 < t + b) :
    (b - a) / (t + b) ≤ Real.log (t + b) - Real.log (t + a) := by
  have h := Real.log_le_sub_one_of_pos (div_pos ha hb)
  rw [Real.log_div ha.ne' hb.ne'] at h
  have heq : (t + a) / (t + b) - 1 = -(b - a) / (t + b) := by
    field_simp
    ring
  rw [heq] at h
  simp only [neg_div] at h
  linarith

/-- Actual frequency-reference mass normalization in the same density units
as the endpoint formula; checked using the exact Appendix A integers. -/
theorem frequencyReferenceDensity_sum :
    (∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j) = 32 := by
  have hq :
      (∑ j ∈ Finset.range 160,
        (32 : ℚ) * (ConfigData.frequencyMassUnits.getD j 0 : ℚ) /
          (ConfigData.referenceDenominator : ℚ)) = 32 := by decide +kernel
  unfold referenceDensity
  have hreal := congrArg (fun q : ℚ => (q : ℝ)) hq
  push_cast at hreal
  exact hreal

theorem referenceCellRight_le_end {start : ℝ} {j count : ℕ}
    (hj : j ∈ Finset.range count) :
    referenceCellRight start j ≤ start + (count : ℝ) / 32 := by
  have hc : ((j + 1 : ℕ) : ℝ) ≤ (count : ℝ) := by
    exact_mod_cast (Finset.mem_range.mp hj)
  unfold referenceCellRight
  linarith

/-- The actual frequency-reference derivative on the full tail; its finite
formula follows from the proved integral identity, not a derivative callback. -/
theorem frequencyReferencePotential_hasDerivAt {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    HasDerivAt frequencyReferencePotential
      (∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j *
        (Real.log |t - referenceCellLeft (1 / 2) j| -
          Real.log |t - referenceCellRight (1 / 2) j|)) t := by
  apply hasDerivAt_referencePotential
  · intro j hj
    have hb := referenceCellRight_le_end (start := (1 / 2 : ℝ)) hj
    have ha := referenceCellLeft_le_right (1 / 2) j
    norm_num at hb
    linarith
  · intro j hj
    have hb := referenceCellRight_le_end (start := (1 / 2 : ℝ)) hj
    norm_num at hb
    linarith

/-- The `1/(t-11/2)` slope bound for the actual positive frequency reference
used in v10 (5.8). Its mass and support are the literal Appendix A ones. -/
theorem frequencyReferencePotential_deriv_le {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    deriv frequencyReferencePotential t ≤ 1 / (t - 11 / 2) := by
  rw [(frequencyReferencePotential_hasDerivAt ht).deriv]
  calc
    _ ≤ ∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j *
        ((1 / 32 : ℝ) / (t - 11 / 2)) := by
      apply Finset.sum_le_sum
      intro j hj
      apply mul_le_mul_of_nonneg_left _ (referenceDensity_nonneg _ _)
      have hb := referenceCellRight_le_end (start := (1 / 2 : ℝ)) hj
      norm_num at hb
      have htb : referenceCellRight (1 / 2) j < t := lt_of_le_of_lt hb ht
      have hcell := log_difference_le (referenceCellLeft_le_right (1 / 2) j) htb
      have hwidth : referenceCellRight (1 / 2) j - referenceCellLeft (1 / 2) j =
          (1 / 32 : ℝ) := by
        simp only [referenceCellRight, referenceCellLeft, Nat.cast_add, Nat.cast_one]
        ring
      rw [hwidth] at hcell
      apply le_trans hcell
      apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
    _ = 32 * ((1 / 32 : ℝ) / (t - 11 / 2)) := by
      rw [← Finset.sum_mul, frequencyReferenceDensity_sum]
    _ = 1 / (t - 11 / 2) := by ring

/-- Exact derivative of the paper's fixed frequency field. -/
theorem B0_hasDerivAt {t : ℝ} (ht : 0 < t) :
    HasDerivAt Config.B0
      (Real.log (t + 5 / 4) - Real.log (t + 1 / 4) +
        (Real.log (t + 2) - Real.log t)) t := by
  have h1 := hasDerivAt_integral_log_add
    (t := t) (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) (by linarith) (by linarith)
  have h2 := hasDerivAt_integral_log_add
    (t := t) (a := (0 : ℝ)) (b := (2 : ℝ)) (by linarith) (by linarith)
  simpa only [Config.B0, add_zero] using! h1.add h2

/-- The actual fixed field contributes at least `3/(t+2)` in v10 (5.8). -/
theorem B0_deriv_ge {t : ℝ} (ht : 0 < t) :
    3 / (t + 2) ≤ deriv Config.B0 t := by
  rw [(B0_hasDerivAt ht).deriv]
  have h1 := log_add_difference_ge
    (t := t) (a := (1 / 4 : ℝ)) (b := (5 / 4 : ℝ)) (by linarith) (by linarith)
  have h2 := log_add_difference_ge
    (t := t) (a := (0 : ℝ)) (b := (2 : ℝ)) (by linarith) (by linarith)
  norm_num at h1 h2
  have h3 : 1 / (t + 2) ≤ 1 / (t + 5 / 4) := by
    apply div_le_div_of_nonneg_left (by norm_num) (by linarith) (by linarith)
  simp only [div_eq_mul_inv] at h1 h2 h3 ⊢
  linarith

/-- Exact derivative of the literal entropy field `psi` on its open half-line. -/
theorem psi_hasDerivAt {t : ℝ} (ht : (1 / 2 : ℝ) < t) :
    HasDerivAt Config.psi
      (Real.log t - Real.log (t - 1 / 2) - Real.log 2) t := by
  have ht0 : t ≠ 0 := by linarith
  have ht1 : t - 1 / 2 ≠ 0 := by linarith
  have h1 := Real.hasDerivAt_mul_log ht0
  have h2 := (Real.hasDerivAt_mul_log ht1).comp t ((hasDerivAt_id t).sub_const (1 / 2))
  have h3 := (hasDerivAt_id t).mul_const (Real.log 2)
  unfold Config.psi
  simpa only [Function.comp_def, id_eq, Pi.sub_apply, mul_one, one_mul, sub_zero, add_sub_add_right_eq_sub] using!
    ((h1.sub h2).sub_const ((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))).sub h3

/-- The entropy contribution to the actual derivative envelope. -/
theorem psi_deriv_le {t : ℝ} (ht : (1 / 2 : ℝ) < t) :
    deriv Config.psi t ≤ 1 / (2 * (t - 1 / 2)) - Real.log 2 := by
  rw [(psi_hasDerivAt ht).deriv]
  have h := log_difference_le (t := t) (a := (0 : ℝ)) (b := (1 / 2 : ℝ))
    (by norm_num) ht
  have ht0 : 0 < t := by linarith
  have ht1 : 0 < t - 1 / 2 := by linarith
  simp only [sub_zero, abs_of_pos ht0, abs_of_pos ht1] at h
  have heq : (1 / 2 : ℝ) / (t - 1 / 2) = 1 / (2 * (t - 1 / 2)) := by
    field_simp
  rw [heq] at h
  linarith

/-- The real-field part of the literal C-A `Wmu`. The remaining summand is
`-Leta(-t)`, supplied by the actual pinned/contour reference. -/
def realTailPart (t : ℝ) : ℝ :=
  Config.B0 t - Config.psi t - 2 * frequencyReferencePotential t

/-- The entire real-frequency part of v10 (5.8), proved from the actual
reference. This closes these three analytic contributions without any
interval-enclosure, differentiability, or callback hypothesis. -/
theorem realTailPart_deriv_ge {t : ℝ} (ht : (11 / 2 : ℝ) < t) :
    Real.log 2 - 1 / (2 * (t - 1 / 2)) + 3 / (t + 2) -
      2 / (t - 11 / 2) ≤ deriv realTailPart t := by
  have ht0 : 0 < t := by linarith
  have ht1 : (1 / 2 : ℝ) < t := by linarith
  have hderiv := ((B0_hasDerivAt ht0).sub (psi_hasDerivAt ht1)).sub
    ((frequencyReferencePotential_hasDerivAt ht).const_mul 2)
  have heq : deriv realTailPart t = deriv Config.B0 t - deriv Config.psi t -
      2 * deriv frequencyReferencePotential t := by
    rw [(B0_hasDerivAt ht0).deriv, (psi_hasDerivAt ht1).deriv,
      (frequencyReferencePotential_hasDerivAt ht).deriv]
    exact hderiv.deriv
  rw [heq]
  have hb := B0_deriv_ge ht0
  have hp := psi_deriv_le ht1
  have hf := frequencyReferencePotential_deriv_le ht
  simp only [div_eq_mul_inv] at hb hp hf ⊢
  linarith

end

end Li2Lean.P0.ConfigRealTail
