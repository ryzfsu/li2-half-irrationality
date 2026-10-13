/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourReference

/-!
# The exact v10 Joukowski logarithmic kernel

These are the literal `c=24233/20000` and `q=1333/24233` occurring in
docs/6333 (5.5). The logarithmic factorization is stated off the diagonal:
Lean's real-valued `Real.log 0` convention must not turn the pointwise
factorization into a false assertion at a collision. An integral use must
separately justify its almost-everywhere and integrability steps.
-/

namespace Li2Lean.P0.ConfigContourKernel

noncomputable section

def contourScale : ℝ := 24233 / 20000

def contourRatio : ℝ := 1333 / 24233

def phase (u : ℝ) : ℂ := Complex.exp ((u : ℂ) * Complex.I)

theorem contourScale_pos : 0 < contourScale := by
  norm_num [contourScale]

theorem contourRatio_nonneg : 0 ≤ contourRatio := by
  norm_num [contourRatio]

theorem contourRatio_lt_one : contourRatio < 1 := by
  norm_num [contourRatio]

theorem phase_ne_zero (u : ℝ) : phase u ≠ 0 := Complex.exp_ne_zero _

theorem norm_phase (u : ℝ) : ‖phase u‖ = 1 := by
  simp [phase, Complex.norm_exp]

/-- The exact affine Joukowski expression for the paper's ellipse. -/
theorem ellipse_eq_joukowski (u : ℝ) :
    Li2Lean.p0EllipsePoint 1 u = (11281 / 10000 : ℂ) +
      (contourScale : ℂ) * phase u +
        (contourScale * contourRatio : ℝ) / phase u := by
  have hp : phase u = (Real.cos u : ℂ) + (Real.sin u : ℂ) * Complex.I := by
    exact Complex.exp_ofReal_mul_I u
  have hn : (phase u)⁻¹ =
      (Real.cos u : ℂ) - (Real.sin u : ℂ) * Complex.I := by
    rw [phase, ← Complex.exp_neg]
    rw [show -((u : ℂ) * Complex.I) = ((-u : ℝ) : ℂ) * Complex.I by
      push_cast; ring]
    rw [Complex.exp_ofReal_mul_I]
    simp only [Real.cos_neg, Real.sin_neg, Complex.ofReal_neg]
    ring
  simp only [div_eq_mul_inv]
  rw [hn, hp]
  simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
    contourScale, contourRatio]
  push_cast
  ring

/-- The algebraic factorization underlying the contour Fourier formula
in v10 (5.5), valid also at collisions before taking logarithms. -/
theorem ellipse_difference_factorization (u v : ℝ) :
    Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v =
      (contourScale : ℂ) * (phase u - phase v) *
        (1 - (contourRatio : ℂ) / (phase u * phase v)) := by
  rw [ellipse_eq_joukowski, ellipse_eq_joukowski]
  push_cast
  field_simp [phase_ne_zero u, phase_ne_zero v]
  ring

theorem correction_ne_zero (u v : ℝ) :
    1 - (contourRatio : ℂ) / (phase u * phase v) ≠ 0 := by
  intro h
  have heq : (contourRatio : ℂ) / (phase u * phase v) = 1 := by
    exact (sub_eq_zero.mp h).symm
  have hn := congrArg norm heq
  rw [norm_div, norm_mul, norm_phase, norm_phase,
    Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg] at hn
  norm_num at hn
  exact (ne_of_lt contourRatio_lt_one) hn

/-- The exact logarithmic kernel split behind (5.5), with the necessary
off-diagonal hypothesis made explicit. -/
theorem ellipse_log_distance (u v : ℝ) (huv : phase u ≠ phase v) :
    Real.log ‖Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v‖ =
      Real.log contourScale + Real.log ‖phase u - phase v‖ +
        Real.log ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖ := by
  rw [ellipse_difference_factorization, norm_mul, norm_mul]
  have hc : ‖(contourScale : ℂ)‖ ≠ 0 := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos contourScale_pos]
    exact ne_of_gt contourScale_pos
  have hd : ‖phase u - phase v‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr huv)
  have he : ‖1 - (contourRatio : ℂ) / (phase u * phase v)‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (correction_ne_zero u v)
  rw [Real.log_mul (mul_ne_zero hc hd) he, Real.log_mul hc hd,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos contourScale_pos]

end

end Li2Lean.P0.ConfigContourKernel
