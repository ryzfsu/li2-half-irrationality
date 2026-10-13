/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

open MeasureTheory

namespace ContourKit

noncomputable section

/-- The Gaussian integral in the plane, with the normalization used by L6. -/
theorem integral_exp_neg_mul_sq_norm_complex {a : ℝ} (ha : 0 < a) :
    ∫ u : ℂ, Real.exp (-a * ‖u‖ ^ 2) = Real.pi / a := by
  simpa [Complex.finrank_real_complex] using
    GaussianFourier.integral_rexp_neg_mul_sq_norm (V := ℂ) ha

/-- Translation invariance gives the centered planar Gaussian integral. -/
theorem integral_exp_neg_mul_sq_norm_sub_complex {a : ℝ} (ha : 0 < a)
    (c : ℂ) :
    ∫ u : ℂ, Real.exp (-a * ‖u - c‖ ^ 2) = Real.pi / a := by
  calc
    ∫ u : ℂ, Real.exp (-a * ‖u - c‖ ^ 2) =
        ∫ u : ℂ, Real.exp (-a * ‖u‖ ^ 2) := by
          simpa only [sub_eq_add_neg] using
            (MeasureTheory.integral_add_right_eq_self
              (μ := (volume : Measure ℂ))
              (fun u : ℂ => Real.exp (-a * ‖u‖ ^ 2)) (-c))
    _ = Real.pi / a := integral_exp_neg_mul_sq_norm_complex ha

/--
Completing the square factors a pair of planar Gaussians through their common
center. This is the kernel identity underlying the explicit SOS representation
of the mass-zero logarithmic energy in `lem:dual-lower`.
-/
theorem gaussianKernelConvolution_eq (t : ℝ) (ht : 0 < t) (z w : ℂ) :
    ∫ u : ℂ,
        Real.exp (-2 * t * ‖z - u‖ ^ 2) *
          Real.exp (-2 * t * ‖w - u‖ ^ 2) =
      (Real.pi / (4 * t)) * Real.exp (-t * ‖z - w‖ ^ 2) := by
  have hdist (u : ℂ) :
      ‖z - u‖ ^ 2 + ‖w - u‖ ^ 2 =
        2 * ‖u - (z + w) / 2‖ ^ 2 + (1 / 2 : ℝ) * ‖z - w‖ ^ 2 := by
    simp_rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, Complex.add_re, Complex.add_im,
      Complex.div_ofNat_re, Complex.div_ofNat_im]
    ring
  have hpoint (u : ℂ) :
      Real.exp (-2 * t * ‖z - u‖ ^ 2) *
        Real.exp (-2 * t * ‖w - u‖ ^ 2) =
      Real.exp (-(4 * t) * ‖u - (z + w) / 2‖ ^ 2) *
        Real.exp (-t * ‖z - w‖ ^ 2) := by
    calc
      Real.exp (-2 * t * ‖z - u‖ ^ 2) *
          Real.exp (-2 * t * ‖w - u‖ ^ 2) =
          Real.exp (-2 * t * ‖z - u‖ ^ 2 + -2 * t * ‖w - u‖ ^ 2) := by rw [← Real.exp_add]
      _ = Real.exp (-(4 * t) * ‖u - (z + w) / 2‖ ^ 2 +
          -t * ‖z - w‖ ^ 2) := by
        congr 1
        calc
          -2 * t * ‖z - u‖ ^ 2 + -2 * t * ‖w - u‖ ^ 2 =
          (-2 * t) * (‖z - u‖ ^ 2 + ‖w - u‖ ^ 2) := by ring
          _ = -(4 * t) * ‖u - (z + w) / 2‖ ^ 2 +
          -t * ‖z - w‖ ^ 2 := by rw [hdist u]; ring
      _ = Real.exp (-(4 * t) * ‖u - (z + w) / 2‖ ^ 2) *
          Real.exp (-t * ‖z - w‖ ^ 2) := by rw [Real.exp_add]
  calc
    ∫ u : ℂ,
        Real.exp (-2 * t * ‖z - u‖ ^ 2) *
          Real.exp (-2 * t * ‖w - u‖ ^ 2) =
        ∫ u : ℂ,
          Real.exp (-(4 * t) * ‖u - (z + w) / 2‖ ^ 2) *
            Real.exp (-t * ‖z - w‖ ^ 2) := by
          apply integral_congr_ae
          exact Filter.Eventually.of_forall hpoint
    _ = (∫ u : ℂ, Real.exp (-(4 * t) * ‖u - (z + w) / 2‖ ^ 2)) *
          Real.exp (-t * ‖z - w‖ ^ 2) := by rw [integral_mul_const]
    _ = (Real.pi / (4 * t)) * Real.exp (-t * ‖z - w‖ ^ 2) := by
          rw [integral_exp_neg_mul_sq_norm_sub_complex
            (mul_pos (by norm_num) ht) ((z + w) / 2)]

end

end ContourKit
