/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

open MeasureTheory

namespace ContourKit

noncomputable section

/-- The planar logarithmic kernel with electrostatic sign. -/
noncomputable def logEnergyKernel (z w : ℂ) : ℝ :=
  -Real.log ‖z - w‖

/-- A smooth compactly supported real density of total mass zero. -/
structure SmoothCompactZeroDensity (f : ℂ → ℝ) : Prop where
  smooth : ContDiff ℝ ⊤ f
  compact_support : HasCompactSupport f
  zero_mass : ∫ z : ℂ, f z = 0
  log_energy_integrable : Integrable
    (fun x : ℂ × ℂ => logEnergyKernel x.1 x.2 * f x.1 * f x.2)
    (volume.prod volume)

/-- The `-log ‖z-w‖` quadratic energy of a signed planar density. -/
noncomputable def densityLogEnergy (f : ℂ → ℝ) : ℝ :=
  ∫ x : ℂ × ℂ, logEnergyKernel x.1 x.2 * f x.1 * f x.2
    ∂(volume.prod volume)

/-- Gaussian convolution appearing in the two-dimensional square factorization. -/
noncomputable def gaussianScore (f : ℂ → ℝ) (t : ℝ) (u : ℂ) : ℝ :=
  ∫ z : ℂ, Real.exp (-2 * t * ‖z - u‖ ^ 2) * f z

/-- The quadratic form of the Gaussian kernel `exp (-t ‖z-w‖²)`. -/
noncomputable def gaussianQuadratic (f : ℂ → ℝ) (t : ℝ) : ℝ :=
  ∫ x : ℂ × ℂ, Real.exp (-t * ‖x.1 - x.2‖ ^ 2) * f x.1 * f x.2
    ∂(volume.prod volume)

/-- Frullani weight; the value at nonpositive `t` is fixed to zero. -/
noncomputable def frullaniWeight (q : ℝ → ℝ) (t : ℝ) : ℝ :=
  if 0 < t then q t / (2 * t) else 0

/--
The analytic identities in the Frullani/Gaussian proof. The first is the
zero-mass cancellation of the constant Gaussian term; the second is the planar
convolution identity with coefficient `4t/π`. These remain explicit proof
obligations rather than hidden axioms.
-/
structure FrullaniGaussianCertificate (f : ℂ → ℝ) where
  regularity : SmoothCompactZeroDensity f
  gaussian_pair_integrable : ∀ t, 0 < t → Integrable
    (fun x : ℂ × ℂ => Real.exp (-t * ‖x.1 - x.2‖ ^ 2) * f x.1 * f x.2)
    (volume.prod volume)
  gaussianScore_integrable : ∀ t, 0 < t →
    Integrable (fun u : ℂ => gaussianScore f t u ^ 2) volume
  gaussian_square : ∀ t, 0 < t →
    gaussianQuadratic f t = (4 * t / Real.pi) *
      ∫ u : ℂ, gaussianScore f t u ^ 2
  frullani_weight_integrable :
    Integrable (frullaniWeight (gaussianQuadratic f)) volume
  frullani_energy :
    densityLogEnergy f = ∫ t : ℝ, frullaniWeight (gaussianQuadratic f) t

/-- Gaussian positive type follows from the explicit convolution sum of squares. -/
theorem gaussianQuadratic_nonneg {f : ℂ → ℝ}
    (h : FrullaniGaussianCertificate f) {t : ℝ} (ht : 0 < t) :
    0 ≤ gaussianQuadratic f t := by
  rw [h.gaussian_square t ht]
  apply mul_nonneg
  · positivity
  · exact integral_nonneg (fun u => sq_nonneg (gaussianScore f t u))

/--
The Frullani representation and Gaussian square factorization imply the
correct-sign energy inequality for a smooth compactly supported zero-mass
signed density.
-/
theorem densityLogEnergy_nonneg_of_frullaniGaussian {f : ℂ → ℝ}
    (h : FrullaniGaussianCertificate f) : 0 ≤ densityLogEnergy f := by
  rw [h.frullani_energy]
  apply integral_nonneg
  intro t
  by_cases ht : 0 < t
  · simp [frullaniWeight, ht]
    exact div_nonneg (gaussianQuadratic_nonneg h ht)
      (le_of_lt (mul_pos (by norm_num) ht))
  · simp [frullaniWeight, ht]

end

end ContourKit

namespace ContourKit
noncomputable section
/-- The three-variable integrand used to expand a Gaussian convolution square. -/
def gaussianScoreSquareIntegrand (f : ℂ → ℝ) (t : ℝ)
    (x : ℂ × (ℂ × ℂ)) : ℝ :=
  (Real.exp (-2 * t * ‖x.2.1 - x.1‖ ^ 2) * f x.2.1) *
    (Real.exp (-2 * t * ‖x.2.2 - x.1‖ ^ 2) * f x.2.2)

/--
The explicit Gaussian square integrand is integrable for every positive scale
when the density is smooth and compactly supported. The proof uses a Gaussian
dominator and separates the remaining density factors over product measures.
-/
theorem gaussianScoreSquareIntegrand_integrable_of_smoothCompactZeroDensity
    {f : ℂ → ℝ} (h : SmoothCompactZeroDensity f) {t : ℝ} (ht : 0 < t) :
    Integrable (gaussianScoreSquareIntegrand f t)
      (volume.prod (volume.prod volume)) := by
  let weightedDensity : ℂ → ℝ := fun z =>
    Real.exp (2 * t * ‖z‖ ^ 2) * |f z|
  have hfContinuous : Continuous f := h.smooth.continuous
  have hfIntegrable : Integrable f volume :=
    hfContinuous.integrable_of_hasCompactSupport h.compact_support
  have habsIntegrable : Integrable (fun z : ℂ => |f z|) volume := by
    simpa [Real.norm_eq_abs] using hfIntegrable.norm
  have hweightedContinuous : Continuous weightedDensity := by
    dsimp [weightedDensity]
    fun_prop
  have hweightedCompact : HasCompactSupport weightedDensity := by
    dsimp [weightedDensity]
    exact h.compact_support.abs.mul_left
  have hweightedIntegrable : Integrable weightedDensity volume :=
    hweightedContinuous.integrable_of_hasCompactSupport hweightedCompact
  have hGaussian : Integrable
      (fun u : ℂ => Real.exp (-t * ‖u‖ ^ 2)) volume := by
    have hc : Integrable
        (fun u : ℂ => Complex.exp (-(t : ℂ) * (‖u‖ ^ 2 : ℂ))) volume := by
      have hc' := GaussianFourier.integrable_cexp_neg_mul_sq_norm_add
        (V := ℂ) (b := (t : ℂ)) (by simpa using ht) (0 : ℂ) (0 : ℂ)
      simpa using hc'
    have hr := hc.norm
    convert hr using 1
    ext u
    rw [Complex.norm_exp]
    have hreal : (-(t : ℂ) * (‖u‖ ^ 2 : ℂ)).re = -t * ‖u‖ ^ 2 := by
      rw [Complex.mul_re]
      norm_num [RCLike.ofReal_re, ht.ne']
      rw [pow_two]
      change ((‖u‖ : ℂ) * (‖u‖ : ℂ)).re = ‖u‖ ^ 2
      rw [Complex.mul_re]
      simp [RCLike.ofReal_re, RCLike.ofReal_im, pow_two]
    rw [hreal]
  have hpair : Integrable
      (fun p : ℂ × ℂ => weightedDensity p.1 * |f p.2|)
      (volume.prod volume) := hweightedIntegrable.mul_prod habsIntegrable
  have hdom : Integrable
      (fun x : ℂ × (ℂ × ℂ) =>
        Real.exp (-t * ‖x.1‖ ^ 2) *
          (weightedDensity x.2.1 * |f x.2.2|))
      (volume.prod (volume.prod volume)) := hGaussian.mul_prod hpair
  have hkernel (u z w : ℂ) :
      Real.exp (-2 * t * ‖z - u‖ ^ 2) *
        Real.exp (-2 * t * ‖w - u‖ ^ 2) ≤
      Real.exp (-t * ‖u‖ ^ 2) * Real.exp (2 * t * ‖z‖ ^ 2) := by
    have htriangle : ‖u‖ ≤ ‖z - u‖ + ‖z‖ := by
      calc
        ‖u‖ = ‖(u - z) + z‖ := by congr 1 <;> abel
        _ ≤ ‖u - z‖ + ‖z‖ := norm_add_le _ _
        _ = ‖z - u‖ + ‖z‖ := by rw [norm_sub_rev]
    have hsquare : ‖u‖ ^ 2 ≤ 2 * ‖z - u‖ ^ 2 + 2 * ‖z‖ ^ 2 := by
      have hsquare' : ‖u‖ ^ 2 ≤ (‖z - u‖ + ‖z‖) ^ 2 :=
        (sq_le_sq₀ (norm_nonneg _) (by positivity)).2 htriangle
      nlinarith [hsquare', sq_nonneg (‖z - u‖ - ‖z‖)]
    have hfirstArg : -2 * t * ‖z - u‖ ^ 2 ≤
        -t * ‖u‖ ^ 2 + 2 * t * ‖z‖ ^ 2 := by
      have hsquareMul := mul_le_mul_of_nonneg_left hsquare ht.le
      nlinarith [hsquareMul]
    have hfirst : Real.exp (-2 * t * ‖z - u‖ ^ 2) ≤
        Real.exp (-t * ‖u‖ ^ 2) * Real.exp (2 * t * ‖z‖ ^ 2) := by
      calc
        Real.exp (-2 * t * ‖z - u‖ ^ 2) ≤
            Real.exp (-t * ‖u‖ ^ 2 + 2 * t * ‖z‖ ^ 2) :=
          Real.exp_le_exp.mpr hfirstArg
        _ = Real.exp (-t * ‖u‖ ^ 2) * Real.exp (2 * t * ‖z‖ ^ 2) := by
          rw [Real.exp_add]
    have hsecond : Real.exp (-2 * t * ‖w - u‖ ^ 2) ≤ 1 := by
      apply Real.exp_le_one_iff.mpr
      have hnonneg : 0 ≤ (2 * t) * ‖w - u‖ ^ 2 :=
        mul_nonneg (by positivity) (sq_nonneg _)
      nlinarith [hnonneg]
    calc
      _ ≤ (Real.exp (-t * ‖u‖ ^ 2) * Real.exp (2 * t * ‖z‖ ^ 2)) * 1 :=
        mul_le_mul hfirst hsecond (by positivity) (by positivity)
      _ = _ := by ring
  have hbound (x : ℂ × (ℂ × ℂ)) :
      ‖gaussianScoreSquareIntegrand f t x‖ ≤
        Real.exp (-t * ‖x.1‖ ^ 2) *
          (weightedDensity x.2.1 * |f x.2.2|) := by
    change |(Real.exp (-2 * t * ‖x.2.1 - x.1‖ ^ 2) * f x.2.1) *
      (Real.exp (-2 * t * ‖x.2.2 - x.1‖ ^ 2) * f x.2.2)| ≤ _
    have hE1 : 0 ≤ Real.exp (-2 * t * ‖x.2.1 - x.1‖ ^ 2) := (Real.exp_pos _).le
    have hE2 : 0 ≤ Real.exp (-2 * t * ‖x.2.2 - x.1‖ ^ 2) := (Real.exp_pos _).le
    calc
      |(Real.exp (-2 * t * ‖x.2.1 - x.1‖ ^ 2) * f x.2.1) *
          (Real.exp (-2 * t * ‖x.2.2 - x.1‖ ^ 2) * f x.2.2)| =
          (Real.exp (-2 * t * ‖x.2.1 - x.1‖ ^ 2) *
            Real.exp (-2 * t * ‖x.2.2 - x.1‖ ^ 2)) *
            (|f x.2.1| * |f x.2.2|) := by
              simp only [abs_mul, abs_of_nonneg hE1, abs_of_nonneg hE2]
              ring
      _ ≤ (Real.exp (-t * ‖x.1‖ ^ 2) *
            Real.exp (2 * t * ‖x.2.1‖ ^ 2)) *
            (|f x.2.1| * |f x.2.2|) := by
              exact mul_le_mul_of_nonneg_right (hkernel x.1 x.2.1 x.2.2)
                (mul_nonneg (abs_nonneg _) (abs_nonneg _))
      _ = Real.exp (-t * ‖x.1‖ ^ 2) *
            (weightedDensity x.2.1 * |f x.2.2|) := by
              dsimp [weightedDensity]
              ring
  have hcont : Continuous (gaussianScoreSquareIntegrand f t) := by
    unfold gaussianScoreSquareIntegrand
    fun_prop (disch := exact hfContinuous)
  have hmeas : AEStronglyMeasurable (gaussianScoreSquareIntegrand f t)
      (volume.prod (volume.prod volume)) := hcont.aestronglyMeasurable
  apply Integrable.mono' hdom hmeas
  filter_upwards with x
  have hrhs : 0 ≤ Real.exp (-t * ‖x.1‖ ^ 2) *
      (weightedDensity x.2.1 * |f x.2.2|) := by
    positivity
  simpa [Real.norm_eq_abs, abs_of_nonneg hrhs] using hbound x
