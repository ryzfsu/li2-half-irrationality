/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigFejerMass

/-!
# The actual contour reference on the negative frequency axis

The derivative is taken under the original Fejer parameter integral.  Its
dominating function uses the exact left vertex `-751/5000`, and the bound
uses the exact contour mass already proved from exponential orthogonality.
-/

open MeasureTheory Filter Set
open scoped Topology

namespace Li2Lean.P0.ConfigContourTail

noncomputable section

open ConfigContourReference ConfigFejerMass

def leftClearance : ℝ := 751 / 5000
def contourMass : ℝ := 267885951940 / 1000000000000
def ellipseX (u : ℝ) : ℝ := 11281 / 10000 + (12783 / 10000) * Real.cos u
def ellipseY (u : ℝ) : ℝ := (229 / 200) * Real.sin u

def tailKernel (t u : ℝ) : ℝ :=
  (1 / 2 : ℝ) * Real.log ((t + ellipseX u) ^ 2 + ellipseY u ^ 2)

def tailKernelDeriv (t u : ℝ) : ℝ :=
  (t + ellipseX u) / ((t + ellipseX u) ^ 2 + ellipseY u ^ 2)

theorem ellipseX_lower (u : ℝ) : -leftClearance ≤ ellipseX u := by
  have h := Real.neg_one_le_cos u
  norm_num [ellipseX, leftClearance]
  linarith

theorem shiftedX_pos {t : ℝ} (ht : leftClearance < t) (u : ℝ) :
    0 < t + ellipseX u := by
  linarith [ellipseX_lower u]

theorem denominator_pos {t : ℝ} (ht : leftClearance < t) (u : ℝ) :
    0 < (t + ellipseX u) ^ 2 + ellipseY u ^ 2 :=
  add_pos_of_pos_of_nonneg (sq_pos_of_pos (shiftedX_pos ht u)) (sq_nonneg _)

theorem continuous_ellipseX : Continuous ellipseX := by
  unfold ellipseX
  fun_prop

theorem continuous_ellipseY : Continuous ellipseY := by
  unfold ellipseY
  fun_prop

theorem continuous_density : Continuous contourDensity := by
  unfold contourDensity
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul (continuous_fejer48.comp (continuous_id.sub continuous_const))

theorem continuous_tailKernel {t : ℝ} (ht : leftClearance < t) :
    Continuous (tailKernel t) := by
  unfold tailKernel
  apply Continuous.const_mul
  exact (((continuous_const.add continuous_ellipseX).pow 2).add
    (continuous_ellipseY.pow 2)).log (fun u => ne_of_gt (denominator_pos ht u))

theorem continuous_tailKernelDeriv {t : ℝ} (ht : leftClearance < t) :
    Continuous (tailKernelDeriv t) := by
  unfold tailKernelDeriv
  exact (continuous_const.add continuous_ellipseX).div
    (((continuous_const.add continuous_ellipseX).pow 2).add (continuous_ellipseY.pow 2))
    (fun u => ne_of_gt (denominator_pos ht u))

/-- The real scalar kernel is exactly the negative-axis complex log norm. -/
theorem tailKernel_eq_log_norm (t u : ℝ) :
    tailKernel t u = Real.log ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ := by
  have hs : ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ ^ 2 =
      (t + ellipseX u) ^ 2 + ellipseY u ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Li2Lean.p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
      Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.neg_re,
      Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im, Complex.add_re,
      Complex.add_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im,
      zero_mul, mul_zero, sub_zero, add_zero, zero_add, neg_zero, ellipseX, ellipseY]
    ring
  have h := Real.log_pow ‖-(t : ℂ) - Li2Lean.p0EllipsePoint 1 u‖ 2
  rw [hs] at h
  unfold tailKernel
  norm_num at h
  linarith

theorem hasDerivAt_tailKernel {t : ℝ} (ht : leftClearance < t) (u : ℝ) :
    HasDerivAt (fun s => tailKernel s u) (tailKernelDeriv t u) t := by
  have hd := (((hasDerivAt_id t).add_const (ellipseX u)).pow 2).add_const
    (ellipseY u ^ 2)
  have hl := (hd.log (ne_of_gt (denominator_pos ht u))).const_mul (1 / 2 : ℝ)
  convert hl using 1 <;> dsimp [tailKernel, tailKernelDeriv] <;> ring

theorem tailKernelDeriv_nonneg {t : ℝ} (ht : leftClearance < t) (u : ℝ) :
    0 ≤ tailKernelDeriv t u :=
  div_nonneg (shiftedX_pos ht u).le (denominator_pos ht u).le

/-- Pointwise derivative bound from the literal left ellipse vertex. -/
theorem tailKernelDeriv_le {t : ℝ} (ht : leftClearance < t) (u : ℝ) :
    tailKernelDeriv t u ≤ 1 / (t - leftClearance) := by
  unfold tailKernelDeriv
  rw [div_le_div_iff₀ (denominator_pos ht u) (sub_pos.mpr ht)]
  have hx := ellipseX_lower u
  have hp := shiftedX_pos ht u
  nlinarith [sq_nonneg (ellipseY u)]

def contourTailDerivative (t : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ u in (0 : ℝ)..(2 * Real.pi),
    contourDensity u * tailKernelDeriv t u

/-- Differentiation of the original v10 contour potential. All regularity
and domination premises are proved for the literal ellipse and density. -/
theorem hasDerivAt_contourReferencePotential_neg {t : ℝ}
    (ht : leftClearance < t) :
    HasDerivAt (fun s : ℝ => contourReferencePotential (-(s : ℂ)))
      (contourTailDerivative t) t := by
  let mu : Measure ℝ := volume.restrict (Set.Ioc (0 : ℝ) (2 * Real.pi))
  let b : ℝ := (t + leftClearance) / 2
  have hb : leftClearance < b := by dsimp [b]; linarith
  have hbt : b < t := by dsimp [b]; linarith
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  let F : ℝ → ℝ → ℝ := fun s u => contourDensity u * tailKernel s u
  let F' : ℝ → ℝ → ℝ := fun s u => contourDensity u * tailKernelDeriv s u
  let bound : ℝ → ℝ := fun u => contourDensity u * (1 / (b - leftClearance))
  have hFi {s : ℝ} (hs : leftClearance < s) :
      Integrable (F s) mu :=
    ((continuous_density.mul (continuous_tailKernel hs)).intervalIntegrable _ _).1
  have hDi {s : ℝ} (hs : leftClearance < s) :
      Continuous (F' s) := continuous_density.mul (continuous_tailKernelDeriv hs)
  have hBi : Integrable bound mu :=
    ((continuous_density.mul continuous_const).intervalIntegrable _ _).1
  have hbound : ∀ᵐ u ∂mu, ∀ s ∈ Set.Ioi b, ‖F' s u‖ ≤ bound u := by
    filter_upwards [] with u
    intro s hs
    have hbs : b < s := hs
    have hds : leftClearance < s := lt_trans hb hs
    have hrec : (1 : ℝ) / (s - leftClearance) ≤ 1 / (b - leftClearance) :=
      one_div_le_one_div_of_le (sub_pos.mpr hb) (by linarith)
    have hnon : 0 ≤ F' s u :=
      mul_nonneg (contourDensity_nonneg u) (tailKernelDeriv_nonneg hds u)
    rw [Real.norm_eq_abs, abs_of_nonneg hnon]
    exact mul_le_mul_of_nonneg_left ((tailKernelDeriv_le hds u).trans hrec)
      (contourDensity_nonneg u)
  have hdiff : ∀ᵐ u ∂mu, ∀ s ∈ Set.Ioi b,
      HasDerivAt (fun x => F x u) (F' s u) s := by
    filter_upwards [] with u
    intro s hs
    exact (hasDerivAt_tailKernel (lt_trans hb hs) u).const_mul (contourDensity u)
  have hmeas : ∀ᶠ s in 𝓝 t, AEStronglyMeasurable (F s) mu := by
    filter_upwards [Ioi_mem_nhds hbt] with s hs
    exact (continuous_density.mul (continuous_tailKernel (lt_trans hb hs))).aestronglyMeasurable
  have hderiv := (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := mu) (F := F) (F' := F') (bound := bound)
    (Ioi_mem_nhds hbt) hmeas (hFi ht) (hDi ht).aestronglyMeasurable
    hbound hBi hdiff).2
  have heq (s : ℝ) : contourReferencePotential (-(s : ℂ)) =
      (2 * Real.pi)⁻¹ * ∫ u, F s u ∂mu := by
    unfold contourReferencePotential contourReferenceIntegral
    simp only [← tailKernel_eq_log_norm]
    rw [intervalIntegral.integral_of_le hpi]
  have heqD : contourTailDerivative t =
      (2 * Real.pi)⁻¹ * ∫ u, F' t u ∂mu := by
    unfold contourTailDerivative
    rw [intervalIntegral.integral_of_le hpi]
  rw [heqD]
  simpa only [← heq] using hderiv.const_mul ((2 * Real.pi)⁻¹)

/-- The actual contour slope pays only its exact Appendix A mass. -/
theorem contourTailDerivative_le {t : ℝ} (ht : leftClearance < t) :
    contourTailDerivative t ≤ contourMass / (t - leftClearance) := by
  have hpi : (0 : ℝ) ≤ 2 * Real.pi := by positivity
  have hint₁ : IntervalIntegrable
      (fun u => contourDensity u * tailKernelDeriv t u) volume 0 (2 * Real.pi) :=
    (continuous_density.mul (continuous_tailKernelDeriv ht)).intervalIntegrable _ _
  have hint₂ : IntervalIntegrable
      (fun u => contourDensity u * (1 / (t - leftClearance))) volume 0 (2 * Real.pi) :=
    (continuous_density.mul continuous_const).intervalIntegrable _ _
  have hi := intervalIntegral.integral_mono_on hpi hint₁ hint₂ (fun u hu =>
    mul_le_mul_of_nonneg_left (tailKernelDeriv_le ht u) (contourDensity_nonneg u))
  have hnorm : (2 * Real.pi)⁻¹ *
      (∫ u in (0 : ℝ)..(2 * Real.pi), contourDensity u * (1 / (t - leftClearance))) =
      contourMass / (t - leftClearance) := by
    rw [intervalIntegral.integral_mul_const, integral_contourDensity, contourWeight_sum]
    unfold contourMass
    have hp : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    field_simp
  exact (mul_le_mul_of_nonneg_left hi (by positivity : 0 ≤ (2 * Real.pi)⁻¹)).trans_eq hnorm

/-- The usable actual-potential derivative bound for the last term in
v10 (5.8). -/
theorem contourReferencePotential_neg_deriv_le {t : ℝ} (ht : leftClearance < t) :
    deriv (fun s : ℝ => contourReferencePotential (-(s : ℂ))) t ≤
      contourMass / (t - leftClearance) := by
  rw [(hasDerivAt_contourReferencePotential_neg ht).deriv]
  exact contourTailDerivative_le ht

end

end Li2Lean.P0.ConfigContourTail
