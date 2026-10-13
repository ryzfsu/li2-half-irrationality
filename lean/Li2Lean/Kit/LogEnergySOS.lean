/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.LogEnergy
import Li2Lean.Kit.GaussianConvolution

open MeasureTheory

namespace ContourKit

noncomputable section

/-! ### Extended-kernel representatives -/

/-- The collision-faithful extension of `logEnergyKernel`. -/
def extendedLogEnergyKernel (z w : ℂ) : WithTop ℝ :=
  if z = w then ⊤ else (logEnergyKernel z w : WithTop ℝ)

theorem extendedLogEnergyKernel_eq_top_of_collision (z : ℂ) :
    extendedLogEnergyKernel z z = ⊤ := by
  simp [extendedLogEnergyKernel]

/-- The real kernel uses Lean's finite convention `Real.log 0 = 0` on collisions. -/
theorem extendedLogEnergyKernel_collision_encoding (z : ℂ) :
    extendedLogEnergyKernel z z = ⊤ ∧
      (logEnergyKernel z z : WithTop ℝ) = 0 := by
  constructor
  · exact extendedLogEnergyKernel_eq_top_of_collision z
  · simp [logEnergyKernel]

theorem extendedLogEnergyKernel_eq_real_of_ne {z w : ℂ} (h : z ≠ w) :
    extendedLogEnergyKernel z w = (logEnergyKernel z w : WithTop ℝ) := by
  simp [extendedLogEnergyKernel, h]

theorem extendedLogEnergyKernel_eq_neg_log_norm_of_ne {z w : ℂ} (h : z ≠ w) :
    extendedLogEnergyKernel z w = ((-Real.log ‖z - w‖ : ℝ) : WithTop ℝ) := by
  simpa [logEnergyKernel] using extendedLogEnergyKernel_eq_real_of_ne h

/-- The diagonal has zero planar product Lebesgue measure. -/
theorem logEnergyDiagonal_null_volume :
    (volume.prod volume : Measure (ℂ × ℂ)) {x : ℂ × ℂ | x.1 = x.2} = 0 := by
  change (volume.prod volume) (Set.diagonal ℂ) = 0
  rw [MeasureTheory.Measure.measure_prod_null measurableSet_diagonal]
  filter_upwards with z
  simp [Set.preimage, Set.diagonal]

/-- Absolute continuity of both factors transfers diagonal nullity. -/
theorem logEnergyDiagonal_null_of_absolutelyContinuous {μ ν : Measure ℂ} [SFinite ν]
    (hμ : μ ≪ volume) (hν : ν ≪ volume) :
    (μ.prod ν) {x : ℂ × ℂ | x.1 = x.2} = 0 := by
  exact (Measure.AbsolutelyContinuous.prod (μ := μ) (ν := ν)
    (μ' := volume) (ν' := volume) hμ hν).null_mono logEnergyDiagonal_null_volume

/-- The extended and finite representatives agree almost everywhere off collisions. -/
theorem extendedLogEnergyKernel_ae_eq_of_absolutelyContinuous {μ ν : Measure ℂ} [SFinite ν]
    (hμ : μ ≪ volume) (hν : ν ≪ volume) :
    (fun x : ℂ × ℂ => extendedLogEnergyKernel x.1 x.2) =ᵐ[μ.prod ν]
      (fun x => (logEnergyKernel x.1 x.2 : WithTop ℝ)) := by
  have hne : ∀ᵐ x : ℂ × ℂ ∂(μ.prod ν), x.1 ≠ x.2 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using
      logEnergyDiagonal_null_of_absolutelyContinuous hμ hν
  filter_upwards [hne] with x hx
  simp [extendedLogEnergyKernel, hx]

/-- Lebesgue specialization of the extended-kernel a.e. identity. -/
theorem extendedLogEnergyKernel_ae_eq_volume :
    (fun x : ℂ × ℂ => extendedLogEnergyKernel x.1 x.2) =ᵐ[volume.prod volume]
      (fun x => (logEnergyKernel x.1 x.2 : WithTop ℝ)) := by
  exact extendedLogEnergyKernel_ae_eq_of_absolutelyContinuous
    Measure.AbsolutelyContinuous.rfl Measure.AbsolutelyContinuous.rfl

/-! ### Gaussian square integrability -/

/--
Under the exact Fubini integrability hypothesis, the Gaussian quadratic is the
`4t/π` multiple of the explicit convolution square. The only measure-theoretic
input is integrability of the full, displayed three-variable integrand.
-/
theorem gaussianQuadratic_eq_scoreSquare_of_fubini {f : ℂ → ℝ}
    (t : ℝ) (ht : 0 < t)
    (hFubini : Integrable (gaussianScoreSquareIntegrand f t)
      (volume.prod (volume.prod volume))) :
    gaussianQuadratic f t = (4 * t / Real.pi) *
      ∫ u : ℂ, gaussianScore f t u ^ 2 := by
  have hsquare (u : ℂ) : gaussianScore f t u ^ 2 =
      ∫ p : ℂ × ℂ, gaussianScoreSquareIntegrand f t (u, p)
        ∂(volume.prod volume) := by
    rw [gaussianScore, pow_two, ← MeasureTheory.integral_prod_mul]
    rfl
  have hswap :
      (∫ u : ℂ, ∫ p : ℂ × ℂ,
        gaussianScoreSquareIntegrand f t (u, p) ∂(volume.prod volume) ∂volume) =
      ∫ p : ℂ × ℂ, ∫ u : ℂ,
        gaussianScoreSquareIntegrand f t (u, p) ∂volume ∂(volume.prod volume) := by
    exact MeasureTheory.integral_integral_swap hFubini
  have hinner (z w : ℂ) :
      ∫ u : ℂ, gaussianScoreSquareIntegrand f t (u, (z, w)) ∂volume =
        (Real.pi / (4 * t)) *
          (Real.exp (-t * ‖z - w‖ ^ 2) * f z * f w) := by
    calc
      ∫ u : ℂ, gaussianScoreSquareIntegrand f t (u, (z, w)) ∂volume =
          ∫ u : ℂ,
            (Real.exp (-2 * t * ‖z - u‖ ^ 2) *
              Real.exp (-2 * t * ‖w - u‖ ^ 2)) * (f z * f w) ∂volume := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun u => by
                  simp [gaussianScoreSquareIntegrand]
                  ring
      _ = (∫ u : ℂ,
            Real.exp (-2 * t * ‖z - u‖ ^ 2) *
              Real.exp (-2 * t * ‖w - u‖ ^ 2) ∂volume) * (f z * f w) := by
                rw [MeasureTheory.integral_mul_const]
      _ = (Real.pi / (4 * t)) *
            (Real.exp (-t * ‖z - w‖ ^ 2) * f z * f w) := by
                rw [gaussianKernelConvolution_eq t ht z w]
                ring
  have hpair :
      (∫ p : ℂ × ℂ, ∫ u : ℂ,
        gaussianScoreSquareIntegrand f t (u, p) ∂volume ∂(volume.prod volume)) =
      (Real.pi / (4 * t)) * gaussianQuadratic f t := by
    calc
      ∫ p : ℂ × ℂ, ∫ u : ℂ,
          gaussianScoreSquareIntegrand f t (u, p) ∂volume ∂(volume.prod volume) =
          ∫ p : ℂ × ℂ,
            (Real.pi / (4 * t)) *
              (Real.exp (-t * ‖p.1 - p.2‖ ^ 2) * f p.1 * f p.2)
              ∂(volume.prod volume) := by
                apply integral_congr_ae
                exact Filter.Eventually.of_forall fun p => by
                  simpa [mul_assoc] using hinner p.1 p.2
      _ = (Real.pi / (4 * t)) * gaussianQuadratic f t := by
            rw [gaussianQuadratic, MeasureTheory.integral_const_mul]
  have hbase :
      ∫ u : ℂ, gaussianScore f t u ^ 2 =
        (Real.pi / (4 * t)) * gaussianQuadratic f t := by
    calc
      ∫ u : ℂ, gaussianScore f t u ^ 2 =
          ∫ u : ℂ, ∫ p : ℂ × ℂ,
            gaussianScoreSquareIntegrand f t (u, p) ∂(volume.prod volume) ∂volume := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall hsquare
      _ = ∫ p : ℂ × ℂ, ∫ u : ℂ,
          gaussianScoreSquareIntegrand f t (u, p) ∂volume ∂(volume.prod volume) := hswap
      _ = (Real.pi / (4 * t)) * gaussianQuadratic f t := hpair
  calc
    gaussianQuadratic f t = (4 * t / Real.pi) *
        ((Real.pi / (4 * t)) * gaussianQuadratic f t) := by
          have ht4 : (4 : ℝ) * t ≠ 0 :=
            ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 4) ht)
          field_simp [Real.pi_ne_zero, ht4]
    _ = (4 * t / Real.pi) * ∫ u : ℂ, gaussianScore f t u ^ 2 := by
          rw [← hbase]

/-- The explicit Gaussian square identity proves positive type at each scale. -/
theorem gaussianQuadratic_nonneg_of_fubini {f : ℂ → ℝ}
    (t : ℝ) (ht : 0 < t)
    (hFubini : Integrable (gaussianScoreSquareIntegrand f t)
      (volume.prod (volume.prod volume))) :
    0 ≤ gaussianQuadratic f t := by
  rw [gaussianQuadratic_eq_scoreSquare_of_fubini t ht hFubini]
  apply mul_nonneg
  · positivity
  · exact integral_nonneg (fun u => sq_nonneg (gaussianScore f t u))

/--
Build the existing L6 certificate while deriving its Gaussian square field
from the explicit three-variable Fubini hypothesis.
-/
theorem frullaniGaussianCertificateOfFubini {f : ℂ → ℝ}
    (regularity : SmoothCompactZeroDensity f)
    (pairIntegrable : ∀ t, 0 < t → Integrable
      (fun x : ℂ × ℂ =>
        Real.exp (-t * ‖x.1 - x.2‖ ^ 2) * f x.1 * f x.2)
      (volume.prod volume))
    (scoreIntegrable : ∀ t, 0 < t →
      Integrable (fun u : ℂ => gaussianScore f t u ^ 2) volume)
    (scoreSquareFubini : ∀ t, 0 < t →
      Integrable (gaussianScoreSquareIntegrand f t)
        (volume.prod (volume.prod volume)))
    (weightIntegrable :
      Integrable (frullaniWeight (gaussianQuadratic f)) volume)
    (frullaniEnergy : densityLogEnergy f =
      ∫ t : ℝ, frullaniWeight (gaussianQuadratic f) t) :
    FrullaniGaussianCertificate f :=
  { regularity := regularity
    gaussian_pair_integrable := pairIntegrable
    gaussianScore_integrable := scoreIntegrable
    gaussian_square := fun t ht =>
      gaussianQuadratic_eq_scoreSquare_of_fubini t ht (scoreSquareFubini t ht)
    frullani_weight_integrable := weightIntegrable
    frullani_energy := frullaniEnergy }

/--
The L6 signed-density positivity theorem with the Gaussian square identity
proved internally; only the displayed regularity, integrability and Frullani
representation facts remain certificate inputs.
-/
theorem densityLogEnergy_nonneg_of_fubiniCertificate {f : ℂ → ℝ}
    (regularity : SmoothCompactZeroDensity f)
    (pairIntegrable : ∀ t, 0 < t → Integrable
      (fun x : ℂ × ℂ =>
        Real.exp (-t * ‖x.1 - x.2‖ ^ 2) * f x.1 * f x.2)
      (volume.prod volume))
    (scoreIntegrable : ∀ t, 0 < t →
      Integrable (fun u : ℂ => gaussianScore f t u ^ 2) volume)
    (scoreSquareFubini : ∀ t, 0 < t →
      Integrable (gaussianScoreSquareIntegrand f t)
        (volume.prod (volume.prod volume)))
    (weightIntegrable :
      Integrable (frullaniWeight (gaussianQuadratic f)) volume)
    (frullaniEnergy : densityLogEnergy f =
      ∫ t : ℝ, frullaniWeight (gaussianQuadratic f) t) :
    0 ≤ densityLogEnergy f := by
  exact densityLogEnergy_nonneg_of_frullaniGaussian
    (frullaniGaussianCertificateOfFubini regularity pairIntegrable
      scoreIntegrable scoreSquareFubini weightIntegrable frullaniEnergy)

/-- Build the certificate using compact support to discharge square Fubini. -/
theorem frullaniGaussianCertificateOfSmoothCompactZeroDensity {f : ℂ → ℝ}
    (regularity : SmoothCompactZeroDensity f)
    (pairIntegrable : ∀ t, 0 < t → Integrable
      (fun x : ℂ × ℂ =>
        Real.exp (-t * ‖x.1 - x.2‖ ^ 2) * f x.1 * f x.2)
      (volume.prod volume))
    (scoreIntegrable : ∀ t, 0 < t →
      Integrable (fun u : ℂ => gaussianScore f t u ^ 2) volume)
    (weightIntegrable :
      Integrable (frullaniWeight (gaussianQuadratic f)) volume)
    (frullaniEnergy : densityLogEnergy f =
      ∫ t : ℝ, frullaniWeight (gaussianQuadratic f) t) :
    FrullaniGaussianCertificate f :=
  frullaniGaussianCertificateOfFubini regularity pairIntegrable scoreIntegrable
    (fun _t ht => gaussianScoreSquareIntegrand_integrable_of_smoothCompactZeroDensity
      regularity ht)
    weightIntegrable frullaniEnergy

/-- The energy inequality with the square-Fubini field derived from regularity. -/
theorem densityLogEnergy_nonneg_of_smoothCompactZeroDensity {f : ℂ → ℝ}
    (regularity : SmoothCompactZeroDensity f)
    (pairIntegrable : ∀ t, 0 < t → Integrable
      (fun x : ℂ × ℂ =>
        Real.exp (-t * ‖x.1 - x.2‖ ^ 2) * f x.1 * f x.2)
      (volume.prod volume))
    (scoreIntegrable : ∀ t, 0 < t →
      Integrable (fun u : ℂ => gaussianScore f t u ^ 2) volume)
    (weightIntegrable :
      Integrable (frullaniWeight (gaussianQuadratic f)) volume)
    (frullaniEnergy : densityLogEnergy f =
      ∫ t : ℝ, frullaniWeight (gaussianQuadratic f) t) :
    0 ≤ densityLogEnergy f := by
  exact densityLogEnergy_nonneg_of_frullaniGaussian
    (frullaniGaussianCertificateOfSmoothCompactZeroDensity regularity pairIntegrable
      scoreIntegrable weightIntegrable frullaniEnergy)

end

end ContourKit
