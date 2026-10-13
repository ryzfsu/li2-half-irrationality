/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourSelfPotential
import Li2Lean.P0.ConfigPinnedTail

open MeasureTheory

namespace Li2Lean.P0.ConfigSlackSemanticIdentity

noncomputable section

open Li2Lean.LogSegment
open ConfigSegment ConfigReferenceSymmetry ConfigContourReference ConfigPinnedTail

/-- The exact real-axis reflected-frequency potential, in endpoint form. -/
theorem reflectedFrequencyPotential_ofReal_eq_endpoints (x : ℝ) :
    reflectedFrequencyPotential (x : ℂ) =
      ∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits j *
          (primitive (x + referenceCellRight (1 / 2) j) -
            primitive (x + referenceCellLeft (1 / 2) j)) := by
  unfold reflectedFrequencyPotential
  rw [← Complex.ofReal_neg, frequencyReferenceComplexPotential_ofReal,
    frequencyReferencePotential_eq_endpoints]
  apply Finset.sum_congr rfl
  intro j hj
  rw [show -x - referenceCellLeft (1 / 2) j =
      -(x + referenceCellLeft (1 / 2) j) by ring,
    show -x - referenceCellRight (1 / 2) j =
      -(x + referenceCellRight (1 / 2) j) by ring,
    ConfigPinnedTail.primitive_neg, ConfigPinnedTail.primitive_neg]
  ring

/-- The literal first variation on the real axis, with every real segment
potential replaced by its exact C-A endpoint sum. The Fejer term stays as the
original integral because its self-potential Fourier identity is a separate
analytic obligation. -/
theorem actualWeta_ofReal_eq_endpoints (x : ℝ) :
    Config.Weta actualReference (x : ℂ) =
      (primitive (x - 1 / 4) - primitive (x - 5 / 4) +
        (primitive x - primitive (x - 2))) -
      (x * Real.log 2 +
        (primitive (x + 1 / 2) - primitive x) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
      2 * ((∑ j ∈ Finset.range 32,
          referenceDensity ConfigData.pinnedMassUnits j *
            (primitive (x - referenceCellLeft (1 / 4) j) -
              primitive (x - referenceCellRight (1 / 4) j))) +
        contourReferencePotential (x : ℂ)) -
      (∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits j *
          (primitive (x + referenceCellRight (1 / 2) j) -
            primitive (x + referenceCellLeft (1 / 2) j))) := by
  change Config.A0 (x : ℂ) - Config.phi (x : ℂ) -
      2 * (pinnedReferenceComplexPotential (x : ℂ) +
        contourReferencePotential (x : ℂ)) -
      reflectedFrequencyPotential (x : ℂ) = _
  rw [A0_ofReal_eq_endpoints, phi_ofReal_eq_endpoints,
    pinnedReferenceComplexPotential_ofReal, pinnedReferencePotential_eq_endpoints,
    reflectedFrequencyPotential_ofReal_eq_endpoints]

/-- The literal frequency first variation equals the actual segment fields
and the original Fejer contour integral. -/
theorem actualWmu_eq_reference_integrals (t : ℝ) :
    Config.Wmu actualReference t =
      Config.B0 t - Config.psi t -
        2 * frequencyReferencePotential t -
        pinnedReferencePotential (-t) -
        contourReferencePotential (-(t : ℂ)) := by
  simp only [Config.Wmu, actualReference, etaReferencePotential]
  change Config.B0 t - Config.psi t -
      2 * frequencyReferencePotential t -
        (pinnedReferenceComplexPotential ((-t : ℝ) : ℂ) +
          contourReferencePotential ((-t : ℝ) : ℂ)) = _
  rw [pinnedReferenceComplexPotential_ofReal]
  have hneg : ((-t : ℝ) : ℂ) = -(t : ℂ) := by push_cast; ring
  rw [hneg]
  ring

/-- The literal frequency first variation with its pinned and frequency
segments written as exact endpoint sums. -/
theorem actualWmu_eq_endpoints (t : ℝ) :
    Config.Wmu actualReference t =
      (primitive (t + 5 / 4) - primitive (t + 1 / 4) +
        (primitive (t + 2) - primitive t)) - Config.psi t -
      2 * (∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits j *
          (primitive (t - referenceCellLeft (1 / 2) j) -
            primitive (t - referenceCellRight (1 / 2) j))) -
      (∑ j ∈ Finset.range 32,
        referenceDensity ConfigData.pinnedMassUnits j *
          (primitive (t + referenceCellRight (1 / 4) j) -
            primitive (t + referenceCellLeft (1 / 4) j))) -
      contourReferencePotential (-(t : ℂ)) := by
  rw [actualWmu_eq_reference_integrals, B0_eq_endpoints,
    frequencyReferencePotential_eq_endpoints]
  have hpinned : pinnedReferencePotential (-t) =
      ∑ j ∈ Finset.range 32,
        referenceDensity ConfigData.pinnedMassUnits j *
          (primitive (t + referenceCellRight (1 / 4) j) -
            primitive (t + referenceCellLeft (1 / 4) j)) := by
    unfold pinnedReferencePotential pinnedReferenceMeasure
    rw [ConfigPinnedTail.referenceNegativePotential_eq_endpoints]
  rw [hpinned]

/-- Literal contour `Weta` source identity; this does not replace a model
remainder by a callback or assume the Fourier self-potential formula. -/
theorem actualWeta_eq_source (z : ℂ) :
    Config.Weta actualReference z =
      Config.A0 z - Config.phi z -
        2 * (pinnedReferenceComplexPotential z + contourReferencePotential z) -
        reflectedFrequencyPotential z := by
  rfl

/-- The exact pointwise Fejer/Joukowski logarithmic factorization used by the
literal contour kernel, away from the parameter diagonal. -/
theorem fejerJoukowski_log_distance (u v : ℝ)
    (huv : ConfigContourKernel.phase u ≠ ConfigContourKernel.phase v) :
    Real.log ‖Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v‖ =
      Real.log ConfigContourKernel.contourScale +
        Real.log ‖ConfigContourKernel.phase u - ConfigContourKernel.phase v‖ +
        Real.log ‖1 - (ConfigContourKernel.contourRatio : ℂ) /
          (ConfigContourKernel.phase u * ConfigContourKernel.phase v)‖ :=
  ConfigContourKernel.ellipse_log_distance u v huv

/-- The degree-48 Fejer density is its finite Fourier kernel. -/
theorem fejer48_eq_finite_fourier (u : ℝ) :
    (ConfigContourReference.fejer48 u : ℂ) =
      ConfigContourSelfPotential.K48 u :=
  ConfigContourSelfPotential.fejer48_eq_K48 u

/-- Exact residual interface for the still-unproved contour Fourier step. -/
theorem contourFourier_residual_spec :
    ConfigContourSelfPotential.ContourSelfPotentialFourierObligation ↔
      ∀ u : ℝ,
        ConfigContourReference.contourReferencePotential
            (Li2Lean.p0EllipsePoint 1 u) =
          ConfigContourSelfPotential.contourSelfPotentialFourier u := by
  rfl

/-- The analytic residual consists precisely of collision-nullness,
integrability, and the preceding Fourier identity. -/
theorem contourAnalytic_residual_spec :
    ConfigContourSelfPotential.ContourSelfPotentialAnalyticObligation ↔
      ((volume.prod volume)
          (ConfigContourSelfPotential.contourPointCollisionSet ∩
            ConfigContourSelfPotential.contourParameterSquare) = 0 ∧
        Integrable ConfigContourSelfPotential.contourLogDistanceKernel
          ((volume.prod volume).restrict
            ConfigContourSelfPotential.contourParameterSquare) ∧
        (∀ u : ℝ,
          ConfigContourReference.contourReferencePotential
              (Li2Lean.p0EllipsePoint 1 u) =
            ConfigContourSelfPotential.contourSelfPotentialFourier u)) := by
  rfl

end

end Li2Lean.P0.ConfigSlackSemanticIdentity
