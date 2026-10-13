/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.Kit.GaussianConvolution
import Li2Lean.Kit.LogEnergySOS

open MeasureTheory
open Filter

namespace Li2Lean
namespace P0

noncomputable section

/-!
## Concrete Gaussian/Fubini adapter

The logarithmic kernel is kept separate from the finite real convention at a
collision.  The Gaussian lemmas below work directly with finite positive
measures, so a contour measure need not have a planar density.  They expose
the exact three-variable Fubini premise needed for the square identity.
-/

/-- Gaussian score of a finite measure at scale `t`. -/
noncomputable def p0GaussianScore (mu : Measure ℂ) (t : ℝ) (u : ℂ) : ℝ :=
  ∫ z : ℂ, Real.exp (-2 * t * ‖z - u‖ ^ 2) ∂mu

/-- Gaussian pair interaction of two measures at scale `t`. -/
noncomputable def p0GaussianPair (mu nu : Measure ℂ) (t : ℝ) : ℝ :=
  ∫ p : ℂ × ℂ, Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂(mu.prod nu)

/-- The displayed three-variable integrand used by the Gaussian Fubini step. -/
def p0GaussianFubiniIntegrand (mu nu : Measure ℂ) (t : ℝ)
    (x : ℂ × (ℂ × ℂ)) : ℝ :=
  Real.exp (-2 * t * ‖x.2.1 - x.1‖ ^ 2) *
    Real.exp (-2 * t * ‖x.2.2 - x.1‖ ^ 2)

theorem p0GaussianScore_mul (mu nu : Measure ℂ) [SFinite mu] [SFinite nu]
    (t : ℝ) (u : ℂ) :
    p0GaussianScore mu t u * p0GaussianScore nu t u =
      ∫ p : ℂ × ℂ, p0GaussianFubiniIntegrand mu nu t (u, p)
        ∂(mu.prod nu) := by
  rw [p0GaussianScore, p0GaussianScore, ← MeasureTheory.integral_prod_mul]
  rfl

theorem p0GaussianPair_eq_score_mul (mu nu : Measure ℂ) [SFinite mu] [SFinite nu]
    (t : ℝ) (ht : 0 < t)
    (hFubini : Integrable (p0GaussianFubiniIntegrand mu nu t)
      (volume.prod (mu.prod nu))) :
    p0GaussianPair mu nu t = (4 * t / Real.pi) *
      ∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore nu t u := by
  have hswap :
      (∫ u : ℂ, ∫ p : ℂ × ℂ,
        p0GaussianFubiniIntegrand mu nu t (u, p) ∂(mu.prod nu) ∂volume) =
      ∫ p : ℂ × ℂ, ∫ u : ℂ,
        p0GaussianFubiniIntegrand mu nu t (u, p) ∂volume ∂(mu.prod nu) := by
    exact MeasureTheory.integral_integral_swap hFubini
  have hinner (z w : ℂ) :
      ∫ u : ℂ, p0GaussianFubiniIntegrand mu nu t (u, (z, w)) ∂volume =
        (Real.pi / (4 * t)) * Real.exp (-t * ‖z - w‖ ^ 2) := by
    simp only [p0GaussianFubiniIntegrand]
    exact ContourKit.gaussianKernelConvolution_eq t ht z w
  have hpair :
      (∫ p : ℂ × ℂ, ∫ u : ℂ,
        p0GaussianFubiniIntegrand mu nu t (u, p) ∂volume ∂(mu.prod nu)) =
      (Real.pi / (4 * t)) * p0GaussianPair mu nu t := by
    calc
      (∫ p : ℂ × ℂ, ∫ u : ℂ,
          p0GaussianFubiniIntegrand mu nu t (u, p) ∂volume ∂(mu.prod nu)) =
          ∫ p : ℂ × ℂ, (Real.pi / (4 * t)) *
            Real.exp (-t * ‖p.1 - p.2‖ ^ 2) ∂(mu.prod nu) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun p => hinner p.1 p.2
      _ = (Real.pi / (4 * t)) * p0GaussianPair mu nu t := by
        rw [p0GaussianPair, MeasureTheory.integral_const_mul]
  calc
    p0GaussianPair mu nu t = (4 * t / Real.pi) *
        ((Real.pi / (4 * t)) * p0GaussianPair mu nu t) := by
          have ht4 : (4 : ℝ) * t ≠ 0 :=
            ne_of_gt (mul_pos (by norm_num : (0 : ℝ) < 4) ht)
          field_simp [Real.pi_ne_zero, ht4]
    _ = (4 * t / Real.pi) *
        (∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore nu t u) := by
          rw [← hpair, ← hswap]
          apply congrArg (fun x => (4 * t / Real.pi) * x)
          apply integral_congr_ae
          exact Filter.Eventually.of_forall fun u => (p0GaussianScore_mul mu nu t u).symm

theorem p0GaussianDifference_nonneg_of_fubini
    (mu nu : Measure ℂ) [SFinite mu] [SFinite nu]
    (t : ℝ) (ht : 0 < t)
    (hmm : Integrable (p0GaussianFubiniIntegrand mu mu t)
      (volume.prod (mu.prod mu)))
    (hnn : Integrable (p0GaussianFubiniIntegrand nu nu t)
      (volume.prod (nu.prod nu)))
    (hmn : Integrable (p0GaussianFubiniIntegrand mu nu t)
      (volume.prod (mu.prod nu)))
    (hscoremm : Integrable (fun u : ℂ =>
      p0GaussianScore mu t u * p0GaussianScore mu t u) volume)
    (hscorenn : Integrable (fun u : ℂ =>
      p0GaussianScore nu t u * p0GaussianScore nu t u) volume)
    (hscoremn : Integrable (fun u : ℂ =>
      p0GaussianScore mu t u * p0GaussianScore nu t u) volume) :
    0 ≤ p0GaussianPair mu mu t + p0GaussianPair nu nu t -
      2 * p0GaussianPair mu nu t := by
  have hsq : Integrable (fun u : ℂ =>
      (p0GaussianScore mu t u - p0GaussianScore nu t u) ^ 2) volume := by
    have hlin : Integrable (fun u : ℂ =>
        p0GaussianScore mu t u * p0GaussianScore mu t u +
        p0GaussianScore nu t u * p0GaussianScore nu t u -
        2 * (p0GaussianScore mu t u * p0GaussianScore nu t u)) volume := by
      exact (hscoremm.add hscorenn).sub (hscoremn.const_mul 2)
    convert hlin using 1
    funext u
    ring
  have hsq_nonneg : 0 ≤ ∫ u : ℂ,
      (p0GaussianScore mu t u - p0GaussianScore nu t u) ^ 2 :=
    integral_nonneg (fun u => sq_nonneg _)
  have hsq_expand :
      (∫ u : ℂ, (p0GaussianScore mu t u - p0GaussianScore nu t u) ^ 2) =
      (∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore mu t u) +
      (∫ u : ℂ, p0GaussianScore nu t u * p0GaussianScore nu t u) -
      2 * (∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore nu t u) := by
    have hlin : Integrable (fun u : ℂ =>
        p0GaussianScore mu t u * p0GaussianScore mu t u +
        p0GaussianScore nu t u * p0GaussianScore nu t u) volume :=
      hscoremm.add hscorenn
    calc
      (∫ u : ℂ, (p0GaussianScore mu t u - p0GaussianScore nu t u) ^ 2) =
          ∫ u : ℂ, (p0GaussianScore mu t u * p0GaussianScore mu t u +
            p0GaussianScore nu t u * p0GaussianScore nu t u) -
            2 * (p0GaussianScore mu t u * p0GaussianScore nu t u) := by
              apply integral_congr_ae
              exact Filter.Eventually.of_forall fun u => by ring
      _ = (∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore mu t u +
            p0GaussianScore nu t u * p0GaussianScore nu t u) -
            ∫ u : ℂ, 2 * (p0GaussianScore mu t u * p0GaussianScore nu t u) := by
              rw [integral_sub hlin (hscoremn.const_mul 2)]
      _ = _ := by rw [integral_add hscoremm hscorenn, integral_const_mul]
  rw [p0GaussianPair_eq_score_mul mu mu t ht hmm,
    p0GaussianPair_eq_score_mul nu nu t ht hnn,
    p0GaussianPair_eq_score_mul mu nu t ht hmn]
  have hcoef : 0 ≤ (4 * t / Real.pi : ℝ) := by positivity
  have hfactor :
      (4 * t / Real.pi * (∫ u : ℂ,
        p0GaussianScore mu t u * p0GaussianScore mu t u) +
        4 * t / Real.pi * (∫ u : ℂ,
          p0GaussianScore nu t u * p0GaussianScore nu t u) -
        2 * (4 * t / Real.pi * (∫ u : ℂ,
          p0GaussianScore mu t u * p0GaussianScore nu t u))) =
      (4 * t / Real.pi) *
        ((∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore mu t u) +
          (∫ u : ℂ, p0GaussianScore nu t u * p0GaussianScore nu t u) -
          2 * (∫ u : ℂ, p0GaussianScore mu t u * p0GaussianScore nu t u)) := by
    ring
  rw [hfactor, ← hsq_expand]
  exact mul_nonneg hcoef hsq_nonneg

/-! ### Collision semantics for the actual finite-energy contour measure -/

theorem p0FiniteEnergyCondition_eta_atomless {M : P0AdmissibleMeasures}
    (h : P0FiniteEnergyCondition M) : ∀ z : ℂ, M.eta {z} = 0 :=
  h.2.2.2.2.1

/-- Frequency domination by Lebesgue measure implies atomlessness. -/
theorem p0AdmissibleMeasures_frequency_atomless (M : P0AdmissibleMeasures) :
    ∀ t : ℝ, M.mu {t} = 0 := by
  intro t
  have hle := M.mu_le_density {t}
  have hzero : (volume.restrict (Set.Ici (1 / 2 : ℝ))) {t} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton t)]
    apply le_antisymm
    · exact (measure_mono Set.inter_subset_left).trans_eq (by simp)
    · exact bot_le
  exact le_antisymm (hle.trans (le_of_eq hzero)) bot_le

/--
The collision-faithful extended kernel agrees almost everywhere with the
finite-energy real kernel.  The proof uses only the explicit atomless clause;
integrability of `-log ‖z-w‖` is not used to assign a value to a Dirac atom.
-/
theorem p0FiniteEnergy_eta_extendedKernel_ae {M : P0AdmissibleMeasures}
    (h : P0FiniteEnergyCondition M) :
    (fun x : ℂ × ℂ => ContourKit.extendedLogEnergyKernel x.1 x.2) =ᵐ[M.eta.prod M.eta]
      (fun x => (li2LogKernel x.1 x.2 : WithTop ℝ)) := by
  have hmass : M.eta Set.univ = 1 := by
    simpa [P0AdmissibleMeasures.eta, p0CompanionMeasure] using M.companion_mass
  letI : IsFiniteMeasure M.eta := ⟨by rw [hmass]; simp⟩
  have hdiag : (M.eta.prod M.eta) {x : ℂ × ℂ | x.1 = x.2} = 0 := by
    change (M.eta.prod M.eta) (Set.diagonal ℂ) = 0
    rw [Measure.measure_prod_null measurableSet_diagonal]
    filter_upwards with z
    simpa [Set.preimage, Set.diagonal] using p0FiniteEnergyCondition_eta_atomless h z
  have hne : ∀ᵐ x : ℂ × ℂ ∂(M.eta.prod M.eta), x.1 ≠ x.2 := by
    rw [ae_iff]
    simpa only [not_ne_iff] using hdiag
  filter_upwards [hne] with x hx
  simp [ContourKit.extendedLogEnergyKernel, ContourKit.logEnergyKernel,
    li2LogKernel, hx]

/-! ### Specialization to the actual admissible contour/frequency pair -/

noncomputable def p0FrequencyMeasure (M : P0AdmissibleMeasures) : Measure ℂ :=
  p0ReflectedFrequencyMeasure M.mu

structure P0AdmissibleGaussianFubiniCertificate (M : P0AdmissibleMeasures) where
  eta_eta_fubini : ∀ t : ℝ, 0 < t →
    Integrable (p0GaussianFubiniIntegrand M.eta M.eta t)
      (volume.prod (M.eta.prod M.eta))
  frequency_frequency_fubini : ∀ t : ℝ, 0 < t →
    Integrable (p0GaussianFubiniIntegrand (p0FrequencyMeasure M)
      (p0FrequencyMeasure M) t)
      (volume.prod ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M)))
  eta_frequency_fubini : ∀ t : ℝ, 0 < t →
    Integrable (p0GaussianFubiniIntegrand M.eta (p0FrequencyMeasure M) t)
      (volume.prod (M.eta.prod (p0FrequencyMeasure M)))
  eta_score_integrable : ∀ t : ℝ, 0 < t →
    Integrable (fun u : ℂ => p0GaussianScore M.eta t u * p0GaussianScore M.eta t u)
      volume
  frequency_score_integrable : ∀ t : ℝ, 0 < t →
    Integrable (fun u : ℂ => p0GaussianScore (p0FrequencyMeasure M) t u *
      p0GaussianScore (p0FrequencyMeasure M) t u) volume
  mixed_score_integrable : ∀ t : ℝ, 0 < t →
    Integrable (fun u : ℂ => p0GaussianScore M.eta t u *
      p0GaussianScore (p0FrequencyMeasure M) t u) volume

theorem p0AdmissibleGaussianDifference_nonneg
    (M : P0AdmissibleMeasures)
    (h : P0AdmissibleGaussianFubiniCertificate M)
    (t : ℝ) (ht : 0 < t) :
    0 ≤ p0GaussianPair M.eta M.eta t +
      p0GaussianPair (p0FrequencyMeasure M) (p0FrequencyMeasure M) t -
      2 * p0GaussianPair M.eta (p0FrequencyMeasure M) t := by
  have heta_mass : M.eta Set.univ = 1 := M.companion_mass
  have hfreq_map : Measurable (fun t : ℝ => (-(t : ℂ))) :=
    measurable_neg.comp Complex.measurable_ofReal
  have hfreq_mass : p0FrequencyMeasure M Set.univ = 1 := by
    unfold p0FrequencyMeasure p0ReflectedFrequencyMeasure
    rw [Measure.map_apply hfreq_map MeasurableSet.univ]
    simpa using M.frequency_mass
  letI : IsFiniteMeasure M.eta := ⟨by rw [heta_mass]; simp⟩
  letI : IsFiniteMeasure (p0FrequencyMeasure M) := ⟨by rw [hfreq_mass]; simp⟩
  exact p0GaussianDifference_nonneg_of_fubini M.eta (p0FrequencyMeasure M) t ht
    (h.eta_eta_fubini t ht) (h.frequency_frequency_fubini t ht)
    (h.eta_frequency_fubini t ht) (h.eta_score_integrable t ht)
    (h.frequency_score_integrable t ht) (h.mixed_score_integrable t ht)

end

end P0
end Li2Lean
