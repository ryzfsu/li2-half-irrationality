/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigLogTaylor

namespace Li2Lean.P0.ConfigLogEnclosures

open ContourKit Li2Lean.P0.ConfigLogTaylor

/-- The exact v10 Appendix A Joukowski scale, without decimal conversion. -/
def referenceScale : ℚ := 24233 / 20000

/-- A twelve-decimal enclosure of the actual `log c` in v10 (5.5) and
(5.6), obtained solely from eight rational atanh terms and the proved tail. -/
theorem log_referenceScale_enclosure_v10 :
    (191983067064 / 1000000000000 : ℝ) ≤ Real.log (24233 / 20000 : ℝ) ∧
      Real.log (24233 / 20000 : ℝ) ≤ (191983067065 / 1000000000000 : ℝ) := by
  let domain : QInterval := QInterval.point referenceScale
  let enclosure : QInterval :=
    ⟨191983067064 / 1000000000000, 191983067065 / 1000000000000, by norm_num⟩
  have hcheck : checkLogInterval 8 domain enclosure = true := by
    norm_num [checkLogInterval, domain, enclosure, QInterval.point,
      referenceScale, logPolynomial, logRemainder, logCoordinate, Finset.sum_range_succ]
  have h := checkLogInterval_sound hcheck (QInterval.mem_point referenceScale)
  norm_num [QInterval.Contains, domain, enclosure, referenceScale] at h ⊢
  exact h

/-- The tighter rational `log 2` enclosure explicitly stated after v10
(5.9). The finite checker uses fourteen odd terms and includes its tail. -/
theorem logTwo_tight_enclosure_v10 :
    (693147180559 / 1000000000000 : ℝ) ≤ Real.log 2 ∧
      Real.log 2 ≤ (693147180560 / 1000000000000 : ℝ) := by
  let domain : QInterval := QInterval.point 2
  let enclosure : QInterval :=
    ⟨693147180559 / 1000000000000, 693147180560 / 1000000000000, by norm_num⟩
  have hcheck : checkLogInterval 14 domain enclosure = true := by
    norm_num [checkLogInterval, domain, enclosure, QInterval.point,
      logPolynomial, logRemainder, logCoordinate, Finset.sum_range_succ]
  have h := checkLogInterval_sound hcheck (QInterval.mem_point 2)
  norm_num [QInterval.Contains, domain, enclosure] at h ⊢
  exact h

/-! A strict endpoint follows from the same rational enclosure by a direct
exponential Taylor lower bound.  This keeps the original v10 denominator
and discharges callers that need `<` rather than `≤`. -/
theorem logTwo_strict_upper_v10 :
    Real.log 2 < (693147180560 / 1000000000000 : ℝ) := by
  let r : ℝ := 693147180560 / 1000000000000
  have hr : 0 < r := by
    dsimp [r]
    norm_num
  have hr1 : |r| ≤ 1 := by
    rw [abs_of_pos hr]
    dsimp [r]
    norm_num
  have hbound := Real.exp_bound (x := r) hr1 (n := 16) (by norm_num)
  have hlow :
      (∑ m ∈ Finset.range 16, r ^ m / m.factorial) -
          r ^ 16 * ((Nat.succ 16 : ℝ) /
            ((Nat.factorial 16 : ℝ) * (16 : ℝ))) ≤ Real.exp r := by
    have h' := (abs_sub_le_iff.mp hbound).2
    simp only [abs_of_pos hr] at h'
    linarith
  have hpoly :
      (2 : ℝ) <
        (∑ m ∈ Finset.range 16, r ^ m / m.factorial) -
          r ^ 16 * ((Nat.succ 16 : ℝ) /
            ((Nat.factorial 16 : ℝ) * (16 : ℝ))) := by
    dsimp [r]
    norm_num [Finset.sum_range_succ, Nat.factorial]
  have hexp : (2 : ℝ) < Real.exp r := lt_of_lt_of_le hpoly hlow
  simpa [r] using (Real.log_lt_iff_lt_exp (by norm_num)).2 hexp

end Li2Lean.P0.ConfigLogEnclosures
