/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.FrequencyRatio

open Finset

namespace Li2Lean.P0.FrequencyLeaf

noncomputable section

/-- The actual v10 ellipse has the real-part lower bound used in the
frequency replacement proof. -/
theorem p0EllipsePoint_re_lower {m : ℕ} (hm : 0 < m) (u : ℝ) :
    -(m : ℝ) / 6 < (p0EllipsePoint m u).re := by
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  have hbase : -(1 : ℝ) / 6 < (11281 : ℝ) / 10000 +
      ((12783 : ℝ) / 10000) * Real.cos u := by
    nlinarith [Real.neg_one_le_cos u]
  have hmul := mul_lt_mul_of_pos_left hbase hmR
  simp only [p0EllipsePoint, Complex.mul_re, Complex.add_re,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im,
    zero_mul, mul_zero, sub_zero, add_zero] at *
  nlinarith

/-- The scaled contour avoids every integer pole in `J_m`. -/
theorem p0EllipsePoint_ne_nat {m : ℕ} (hm : 0 < m) (u : ℝ)
    {j : ℕ} (hj : j < 2 * m) :
    p0EllipsePoint m u ≠ (j : ℂ) := by
  intro hz
  have him := congrArg Complex.im hz
  have hre := congrArg Complex.re hz
  have him' : (m : ℝ) * ((229 : ℝ) / 200 * Real.sin u) = 0 := by
    simpa only [p0EllipsePoint, Complex.mul_im, Complex.add_im,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.natCast_im, zero_mul, mul_zero, one_mul, zero_add, add_zero] using him
  have hs : Real.sin u = 0 := by
    have hmB : (0 : ℝ) < (m : ℝ) * ((229 : ℝ) / 200) := by positivity
    nlinarith
  have hre' : (m : ℝ) *
      ((11281 : ℝ) / 10000 + ((12783 : ℝ) / 10000) * Real.cos u) =
        (j : ℝ) := by
    simpa only [p0EllipsePoint, Complex.mul_re, Complex.add_re,
      Complex.ofReal_im, Complex.ofReal_re, Complex.I_re, Complex.I_im,
      Complex.natCast_re, zero_mul, mul_zero, one_mul, zero_add, add_zero,
      sub_zero] using hre
  have hjR : (j : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hj
  have htrig := Real.sin_sq_add_cos_sq u
  rw [hs] at htrig
  have hc2 : (Real.cos u) ^ 2 = 1 := by nlinarith
  rcases sq_eq_one_iff.mp hc2 with hc | hc
  · rw [hc] at hre'
    nlinarith
  · rw [hc] at hre'
    have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg _
    nlinarith

/-- The actual v10 ellipse satisfies `|z|<5m/2`. The use of the circle
identity retains the true ellipse rather than a larger rectangular bound. -/
theorem p0EllipsePoint_norm_upper {m : ℕ} (hm : 0 < m) (u : ℝ) :
    ‖p0EllipsePoint m u‖ < 5 * (m : ℝ) / 2 := by
  let e : ℂ := Complex.ofReal ((11281 : ℝ) / 10000 +
      ((12783 : ℝ) / 10000) * Real.cos u) +
    Complex.I * Complex.ofReal (((229 : ℝ) / 200) * Real.sin u)
  have he_re : e.re = (11281 : ℝ) / 10000 +
      ((12783 : ℝ) / 10000) * Real.cos u := by
    simp only [e, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have he_im : e.im = ((229 : ℝ) / 200) * Real.sin u := by
    simp only [e, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  have he_sq : ‖e‖ ^ 2 =
      ((11281 : ℝ) / 10000 + ((12783 : ℝ) / 10000) * Real.cos u) ^ 2 +
        (((229 : ℝ) / 200) * Real.sin u) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, he_re, he_im]
    ring
  have hcircle := Real.sin_sq_add_cos_sq u
  have hcos := Real.cos_le_one u
  have hcos_sq : (Real.cos u) ^ 2 ≤ 1 := by
    nlinarith [sq_nonneg (Real.sin u)]
  have hsq : ‖e‖ ^ 2 ≤ ((1504 : ℝ) / 625) ^ 2 := by
    rw [he_sq]
    nlinarith
  have hsmall : ‖e‖ < (5 : ℝ) / 2 := by nlinarith [norm_nonneg e]
  have hmR : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  calc
    ‖p0EllipsePoint m u‖ = (m : ℝ) * ‖e‖ := by
      simp only [p0EllipsePoint, e, norm_mul, Complex.norm_real, Real.norm_natCast]
    _ < (m : ℝ) * (5 / 2) := mul_lt_mul_of_pos_left hsmall hmR
    _ = 5 * (m : ℝ) / 2 := by ring

/-- Literal v10 replacement on the actual scaled contour: all geometric
inputs are discharged for `p0EllipsePoint`; no quotient of `Q_m` occurs. -/
theorem leastUnused_frequencyFactor_ellipse_le {m : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (S R : Finset ℕ) (hSI : S ⊆ I_m m)
    (hR : admissible (m / 2) m R) (r : ℕ) (hrmem : r ∈ R)
    (hr : 20 * m < r) (hmax : ∀ v ∈ R, v ≤ r)
    (u : Fin (m - S.card) → ℝ) :
    let s := leastUnused (m / 2) m R hR r hrmem (by omega)
    frequencyFactor m (m / 2) S R (m - S.card) (fun z => p0EllipsePoint m (u z)) ≤
      ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight (m / 2) r) *
        frequencyFactor m (m / 2) S (replace (m / 2) m R s r) (m - S.card)
          (fun z => p0EllipsePoint m (u z)) := by
  exact leastUnused_frequencyFactor_le hm hm4 S R hSI hR r hrmem hr hmax
    (fun z => p0EllipsePoint m (u z))
    (fun z => p0EllipsePoint_re_lower hm (u z))
    (fun z => p0EllipsePoint_norm_upper hm (u z))

end

end Li2Lean.P0.FrequencyLeaf
