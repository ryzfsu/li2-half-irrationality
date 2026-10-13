/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigLogTaylor
import Li2Lean.P0.ConfigAnalytic

namespace Li2Lean.P0.ConfigPrimitiveEnclosure

/-- The positive radial loss of the v10 real-cell primitive is increasing
on `[0,1]`. This proof also includes its continuous value at zero. -/
theorem segmentPrimitive_radial_mono {x a : ℝ}
    (hx : 0 ≤ x) (hxa : x ≤ a) (ha : 0 < a) (ha1 : a ≤ 1) :
    x * (1 - Real.log x) ≤ a * (1 - Real.log a) := by
  have hloga : Real.log a ≤ 0 := Real.log_nonpos ha.le ha1
  by_cases hx0 : x = 0
  · rw [hx0]
    simp only [zero_mul]
    exact mul_nonneg ha.le (by linarith)
  · have hxpos : 0 < x := lt_of_le_of_ne hx (Ne.symm hx0)
    have h := Real.log_le_sub_one_of_pos (div_pos ha hxpos)
    rw [Real.log_div ha.ne' hxpos.ne'] at h
    have hm := mul_le_mul_of_nonneg_left h hx
    have hc : x * (a / x - 1) = a - x := by
      field_simp
    rw [hc] at hm
    have hp : 0 ≤ (a - x) * (-Real.log a) :=
      mul_nonneg (sub_nonneg.mpr hxa) (neg_nonneg.mpr hloga)
    nlinarith

/-- A rigorous enclosure across the logarithmic singularity of
`F(v)=v(log|v|-1)`, the literal primitive in v10 (5.1) and Appendix A.
The formula has value zero at zero under Lean's real-log convention. -/
theorem abs_segmentPrimitive_le {v a : ℝ}
    (ha : 0 < a) (ha1 : a ≤ 1) (hv : |v| ≤ a) :
    |v * (Real.log |v| - 1)| ≤ a * (1 - Real.log a) := by
  have hlog : Real.log |v| ≤ 0 :=
    Real.log_nonpos (abs_nonneg v) (le_trans hv ha1)
  rw [abs_mul, abs_of_nonpos (show Real.log |v| - 1 ≤ 0 by linarith), neg_sub]
  exact segmentPrimitive_radial_mono (abs_nonneg v) hv ha ha1

/-- A dyadic, entirely rational loss bound using the already proved v10
upper enclosure of `log 2`. This avoids slow series evaluation near zero. -/
theorem abs_segmentPrimitive_dyadic {v : ℝ} (k : ℕ)
    (hv : |v| ≤ 1 / (2 : ℝ) ^ k) :
    |v * (Real.log |v| - 1)| ≤
      (1 + (k : ℝ) * (6931473 / 10000000 : ℝ)) / (2 : ℝ) ^ k := by
  have hpow : 0 < (2 : ℝ) ^ k := by positivity
  have hpow1 : 1 ≤ (2 : ℝ) ^ k := one_le_pow₀ (by norm_num)
  have ha : (0 : ℝ) < 1 / (2 : ℝ) ^ k := by positivity
  have ha1 : (1 : ℝ) / 2 ^ k ≤ 1 := by
    exact (div_le_one hpow).mpr hpow1
  have h := abs_segmentPrimitive_le ha ha1 hv
  have hlog : Real.log (1 / (2 : ℝ) ^ k) = -(k : ℝ) * Real.log 2 := by
    rw [Real.log_div (by norm_num) hpow.ne', Real.log_pow, Real.log_one]
    ring
  rw [hlog] at h
  have hl := Li2Lean.P0.ConfigAnalytic.logTwoEnclosure_v10.2.le
  calc
    |v * (Real.log |v| - 1)| ≤
        (1 + (k : ℝ) * Real.log 2) / (2 : ℝ) ^ k := by
      convert h using 1
      ring
    _ ≤ _ := by gcongr

/-- The actual pinned C-A mesh width is `1/8192`. This enclosure includes
all zero-crossing primitive arguments at a reference-cell endpoint. -/
theorem abs_segmentPrimitive_pinned_mesh_v10 {v : ℝ}
    (hv : |v| ≤ (1 / 8192 : ℝ)) :
    |v * (Real.log |v| - 1)| < (1 / 800 : ℝ) := by
  have h := abs_segmentPrimitive_dyadic (v := v) 13 (by norm_num; exact hv)
  norm_num at h ⊢
  linarith

/-- The actual frequency C-A mesh width is `(81/10-1/2)/16384 = 19/40960`.
The enclosing dyadic radius `1/2048` gives this directed rational bound. -/
theorem abs_segmentPrimitive_frequency_mesh_v10 {v : ℝ}
    (hv : |v| ≤ (19 / 40960 : ℝ)) :
    |v * (Real.log |v| - 1)| < (43 / 10000 : ℝ) := by
  have hv' : |v| ≤ (1 : ℝ) / 2 ^ 11 := by norm_num; linarith
  have h := abs_segmentPrimitive_dyadic (v := v) 11 hv'
  norm_num at h ⊢
  linarith

end Li2Lean.P0.ConfigPrimitiveEnclosure
