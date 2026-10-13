/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Concrete

open MeasureTheory

namespace Li2Lean
namespace P0

noncomputable section

/-!
## Finite-energy Frullani statement for the admissible pair

This leaf freezes the actual energy difference on (eta, reflected mu). The
finite-energy hypothesis supplies the three logarithmic-kernel integrability
facts. Gaussian score/Fubini, Frullani-weight integrability, and the Frullani
representation remain named certificate obligations.
-/

/-- Gaussian pair kernel at a fixed scale. -/
def p0GaussianPairIntegrand (t : ℝ) (p : ℂ × ℂ) : ℝ :=
  Real.exp (-t * ‖p.1 - p.2‖ ^ 2)

/-- Signed Gaussian pair interaction for the actual admissible pair. -/
noncomputable def p0AdmissibleGaussianDifference
    (M : P0AdmissibleMeasures) (t : ℝ) : ℝ :=
  p0GaussianPair M.eta M.eta t +
    p0GaussianPair (p0FrequencyMeasure M) (p0FrequencyMeasure M) t -
    2 * p0GaussianPair M.eta (p0FrequencyMeasure M) t

/-- The actual finite-energy logarithmic difference from the admissible data. -/
noncomputable def p0AdmissibleLogEnergyDifference
    (M : P0AdmissibleMeasures) : ℝ :=
  li2LogInteraction M.eta M.eta +
    (∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂(M.mu.prod M.mu)) -
    2 * (∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(M.eta.prod M.mu))

/-- Common-plane logarithmic energy of eta minus the reflected frequency measure. -/
noncomputable def p0AdmissibleCommonLogEnergyDifference
    (M : P0AdmissibleMeasures) : ℝ :=
  li2LogInteraction M.eta M.eta +
    li2LogInteraction (p0FrequencyMeasure M) (p0FrequencyMeasure M) -
    2 * li2LogInteraction M.eta (p0FrequencyMeasure M)

theorem p0FiniteEnergy_logEnergyData
    (M : P0AdmissibleMeasures) (hfinite : P0FiniteEnergyCondition M) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (M.eta.prod M.eta) ∧
    Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      (M.mu.prod M.mu) ∧
    Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
      (M.eta.prod M.mu) := by
  rcases hfinite with ⟨_, _, _, hetaLog, _, hfreqLog, hmixedLog⟩
  exact ⟨hetaLog, hfreqLog, hmixedLog⟩

theorem p0GaussianPairIntegrable_of_finite_mass
    (mu nu : Measure ℂ) (hmu : mu Set.univ < ⊤) (hnu : nu Set.univ < ⊤)
    (t : ℝ) (ht : 0 ≤ t) :
    Integrable (p0GaussianPairIntegrand t) (mu.prod nu) := by
  letI : IsFiniteMeasure mu := ⟨hmu⟩
  letI : IsFiniteMeasure nu := ⟨hnu⟩
  have hconst : Integrable (fun _ : ℂ × ℂ => (1 : ℝ)) (mu.prod nu) :=
    integrable_const 1
  have hmeas : AEStronglyMeasurable (p0GaussianPairIntegrand t) (mu.prod nu) := by
    have hcont : Continuous (p0GaussianPairIntegrand t) := by
      unfold p0GaussianPairIntegrand
      fun_prop
    exact hcont.aestronglyMeasurable
  apply Integrable.mono' hconst hmeas
  filter_upwards with p
  change |Real.exp (-t * ‖p.1 - p.2‖ ^ 2)| ≤ 1
  rw [abs_of_nonneg (Real.exp_nonneg _)]
  apply Real.exp_le_one_iff.mpr
  have htprod : 0 ≤ t * ‖p.1 - p.2‖ ^ 2 :=
    mul_nonneg ht (sq_nonneg _)
  linarith

theorem p0AdmissibleFrequencyMeasure_mass (M : P0AdmissibleMeasures) :
    p0FrequencyMeasure M Set.univ = 1 := by
  have hmap : Measurable (fun t : ℝ => (-(t : ℂ))) :=
    measurable_neg.comp Complex.measurable_ofReal
  unfold p0FrequencyMeasure p0ReflectedFrequencyMeasure
  rw [Measure.map_apply hmap MeasurableSet.univ]
  simpa using M.frequency_mass

theorem p0AdmissibleGaussianPairs_integrable
    (M : P0AdmissibleMeasures) (t : ℝ) (ht : 0 ≤ t) :
    Integrable (p0GaussianPairIntegrand t) (M.eta.prod M.eta) ∧
    Integrable (p0GaussianPairIntegrand t)
      ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M)) ∧
    Integrable (p0GaussianPairIntegrand t)
      (M.eta.prod (p0FrequencyMeasure M)) := by
  have heta : M.eta Set.univ < ⊤ := by
    have hmass : M.eta Set.univ = 1 := M.companion_mass
    rw [hmass]
    simp
  have hfreq : p0FrequencyMeasure M Set.univ < ⊤ := by
    rw [p0AdmissibleFrequencyMeasure_mass]
    simp
  exact ⟨p0GaussianPairIntegrable_of_finite_mass M.eta M.eta heta heta t ht,
    p0GaussianPairIntegrable_of_finite_mass (p0FrequencyMeasure M)
      (p0FrequencyMeasure M) hfreq hfreq t ht,
    p0GaussianPairIntegrable_of_finite_mass M.eta (p0FrequencyMeasure M)
      heta hfreq t ht⟩

/--
The remaining Frullani bridge for the concrete admissible energy. This records
the pair-score/Fubini proof, weight integrability, and the kernel-to-Frullani
identity independently, so none is inferred from finite logarithmic energy.
-/
structure P0AdmissibleFrullaniCertificate (M : P0AdmissibleMeasures) where
  gaussian : P0AdmissibleGaussianFubiniCertificate M
  frequency_log_integrable : Integrable
    (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M))
  mixed_log_integrable : Integrable
    (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      (M.eta.prod (p0FrequencyMeasure M))
  weight_integrable : Integrable
    (ContourKit.frullaniWeight (p0AdmissibleGaussianDifference M)) volume
  regularized_kernel_transfer :
    p0AdmissibleLogEnergyDifference M =
      p0AdmissibleCommonLogEnergyDifference M
  frullani_energy : p0AdmissibleCommonLogEnergyDifference M =
    ∫ t : ℝ, ContourKit.frullaniWeight (p0AdmissibleGaussianDifference M) t

/--
The minimal closed L6 consequence for the actual admissible pair. The first
four outputs certify the logarithmic and Gaussian pair integrability at issue;
the last output is the signed log-energy inequality. The Frullani bridge itself
is the explicit certificate above.
-/
theorem p0FiniteEnergy_admissibleLogEnergy_nonneg
    (M : P0AdmissibleMeasures) (hfinite : P0FiniteEnergyCondition M)
    (hfr : P0AdmissibleFrullaniCertificate M) :
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (M.eta.prod M.eta) ∧
    Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
      (M.mu.prod M.mu) ∧
    Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
      (M.eta.prod M.mu) ∧
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M)) ∧
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
      (M.eta.prod (p0FrequencyMeasure M)) ∧
    (Integrable (p0GaussianPairIntegrand 1) (M.eta.prod M.eta) ∧
      Integrable (p0GaussianPairIntegrand 1)
        ((p0FrequencyMeasure M).prod (p0FrequencyMeasure M)) ∧
      Integrable (p0GaussianPairIntegrand 1)
        (M.eta.prod (p0FrequencyMeasure M))) ∧
    Integrable (ContourKit.frullaniWeight (p0AdmissibleGaussianDifference M)) volume ∧
    0 ≤ p0AdmissibleLogEnergyDifference M := by
  have hlog := p0FiniteEnergy_logEnergyData M hfinite
  refine ⟨hlog.1, hlog.2.1, hlog.2.2,
    hfr.frequency_log_integrable, hfr.mixed_log_integrable,
    p0AdmissibleGaussianPairs_integrable M 1 (by norm_num),
    hfr.weight_integrable, ?_⟩
  rw [hfr.regularized_kernel_transfer, hfr.frullani_energy]
  apply integral_nonneg
  intro t
  by_cases ht : 0 < t
  · simp [ContourKit.frullaniWeight, ht, p0AdmissibleGaussianDifference]
    exact div_nonneg (p0AdmissibleGaussianDifference_nonneg M hfr.gaussian t ht)
      (le_of_lt (mul_pos (by norm_num) ht))
  · simp [ContourKit.frullaniWeight, ht]

end

end P0
end Li2Lean
