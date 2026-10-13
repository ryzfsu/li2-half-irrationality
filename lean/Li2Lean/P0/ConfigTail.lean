/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigAnalytic

namespace Li2Lean.P0.ConfigTail

noncomputable section

/-- Rational part of the v10 tail-slope expression (5.8). -/
def tailSlopeRationalV10 (t : ℝ) : ℝ :=
  -1 / (2 * (t - 1 / 2)) + 3 / (t + 2) -
    2 / (t - 11 / 2) - 1 / (t - 751 / 5000)

/-- The explicit lower derivative expression in v10 (5.8). -/
def tailSlopeV10 (t : ℝ) : ℝ := Real.log 2 + tailSlopeRationalV10 t

def tailSlopeFloorV10 : ℝ := 28975217729 / 991618303000

theorem tailSlopeRationalV10_mono_after_cutoff {t : ℝ}
    (ht : (81 / 10 : ℝ) ≤ t) :
    tailSlopeRationalV10 (81 / 10) ≤ tailSlopeRationalV10 t := by
  have ht05 : (1 / 2 : ℝ) < t := by linarith
  have ht55 : (11 / 2 : ℝ) < t := by linarith
  have htd : (751 / 5000 : ℝ) < t := by linarith
  have htdiff : tailSlopeRationalV10 t - tailSlopeRationalV10 (81 / 10) =
      (t - 81 / 10) *
        ((1 / 2 : ℝ) / ((81 / 10 - 1 / 2) * (t - 1 / 2)) +
          2 / ((81 / 10 - 11 / 2) * (t - 11 / 2)) +
          1 / ((81 / 10 - 751 / 5000) * (t - 751 / 5000)) -
          3 / ((81 / 10 + 2) * (t + 2))) := by
    unfold tailSlopeRationalV10
    have h1 : t - 1 / 2 ≠ 0 := ne_of_gt (sub_pos.mpr ht05)
    have h2 : t + 2 ≠ 0 := by linarith
    have h3 : t - 11 / 2 ≠ 0 := ne_of_gt (sub_pos.mpr ht55)
    have h4 : t - 751 / 5000 ≠ 0 := ne_of_gt (sub_pos.mpr htd)
    have h1' : 2 * (t - 1 / 2) ≠ 0 := mul_ne_zero (by norm_num) h1
    have h2' : t + 2 ≠ 0 := h2
    have h3' : t - 11 / 2 ≠ 0 := h3
    have h4' : t - 751 / 5000 ≠ 0 := h4
    have hc1 : (81 / 10 - 1 / 2 : ℝ) ≠ 0 := by norm_num
    have hc2 : (81 / 10 + 2 : ℝ) ≠ 0 := by norm_num
    have hc3 : (81 / 10 - 11 / 2 : ℝ) ≠ 0 := by norm_num
    have hc4 : (81 / 10 - 751 / 5000 : ℝ) ≠ 0 := by norm_num
    have hn1 : 2 * t - 1 ≠ 0 := by linarith
    have hn3 : 2 * t - 11 ≠ 0 := by linarith
    have hn4 : 5000 * t - 751 ≠ 0 := by linarith
    have hn4' : -751 + t * 5000 ≠ 0 := by linarith
    field_simp [h1', h2', h3', h4', hc1, hc2, hc3, hc4, hn1, hn3, hn4, hn4']
    ring_nf
    field_simp [hn4']
    ring
  have hleft : 0 < ((81 / 10 : ℝ) + 2) * (t + 2) := by positivity
  have hright : 0 < ((81 / 10 : ℝ) - 11 / 2) * (t - 11 / 2) := by positivity
  have hdom :
      3 / (((81 / 10 : ℝ) + 2) * (t + 2)) ≤
        2 / (((81 / 10 : ℝ) - 11 / 2) * (t - 11 / 2)) := by
    rw [div_le_div_iff₀ hleft hright]
    norm_num
    nlinarith [ht]
  have hcoef : 0 ≤
      (1 / 2 : ℝ) / ((81 / 10 - 1 / 2) * (t - 1 / 2)) +
        2 / ((81 / 10 - 11 / 2) * (t - 11 / 2)) +
        1 / ((81 / 10 - 751 / 5000) * (t - 751 / 5000)) -
        3 / ((81 / 10 + 2) * (t + 2)) := by
    have hpos₁ : 0 ≤
        (1 / 2 : ℝ) / ((81 / 10 - 1 / 2) * (t - 1 / 2)) := by positivity
    have hpos₂ : 0 ≤
        1 / ((81 / 10 - 751 / 5000) * (t - 751 / 5000)) := by positivity
    nlinarith
  have hprod : 0 ≤ (t - 81 / 10) *
      ((1 / 2 : ℝ) / ((81 / 10 - 1 / 2) * (t - 1 / 2)) +
        2 / ((81 / 10 - 11 / 2) * (t - 11 / 2)) +
        1 / ((81 / 10 - 751 / 5000) * (t - 751 / 5000)) -
        3 / ((81 / 10 + 2) * (t + 2))) :=
    mul_nonneg (sub_nonneg.mpr ht) hcoef
  have hdiff_nonneg : 0 ≤
      tailSlopeRationalV10 t - tailSlopeRationalV10 (81 / 10) := by
    rw [htdiff]
    exact hprod
  linarith

/-- The exact endpoint comparison in the v10 tail estimate (5.8). -/
theorem tailSlopeV10_cutoff_eq_floor :
    tailSlopeV10 (81 / 10) =
      Real.log 2 - (693 / 1000 : ℝ) + tailSlopeFloorV10 := by
  unfold tailSlopeV10 tailSlopeRationalV10 tailSlopeFloorV10
  norm_num
  ring

/-- The right side of v10 (5.8) has the stated pointwise minimum on the full
tail. This closes the rational monotonicity and endpoint arithmetic; the
separate potential estimate `deriv W_mu ≥ tailSlopeV10` is still the input
needed to obtain the corresponding `CAReceipt.tail_derivative` field. -/
theorem tailSlopeV10_pointwise_minimum {t : ℝ}
    (ht : (81 / 10 : ℝ) ≤ t) :
    tailSlopeFloorV10 ≤ tailSlopeV10 t := by
  have hlog := Li2Lean.P0.ConfigAnalytic.logTwoEnclosure_v10.1
  have hmono := tailSlopeRationalV10_mono_after_cutoff ht
  have hcut : tailSlopeFloorV10 ≤ tailSlopeV10 (81 / 10) := by
    rw [tailSlopeV10_cutoff_eq_floor]
    dsimp [tailSlopeFloorV10]
    linarith [hlog]
  have hmono' : tailSlopeV10 (81 / 10) ≤ tailSlopeV10 t := by
    unfold tailSlopeV10
    linarith
  exact le_trans hcut hmono'

/-- Application form: once the v10 potential derivative dominates its
explicit envelope (5.8), it has the exact rational lower bound on the tail. -/
theorem derivative_lower_of_v10_envelope {f : ℝ → ℝ} {t : ℝ}
    (ht : (81 / 10 : ℝ) ≤ t)
    (henvelope : tailSlopeV10 t ≤ deriv f t) :
    tailSlopeFloorV10 ≤ deriv f t :=
  le_trans (tailSlopeV10_pointwise_minimum ht) henvelope

end

end Li2Lean.P0.ConfigTail
