/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.ConfigSegment
import Li2Lean.P0.ConfigContourMeasure
import Li2Lean.P0.ConfigReferenceSymmetry

/-!
# Exact v10 reference packaging

This file packages the three measures used by the v10 contour dual.  The
measures are definitions, while the admissibility and finite-energy claims are
kept as an explicit certificate: no unproved density, support, or
integrability fact is hidden behind an unproved callback.
-/

open MeasureTheory Set

namespace Li2Lean.P0.ReferencePackaging

noncomputable section

open ConfigSegment ConfigContourMeasure ConfigReferenceSymmetry

/-- The pinned C-A measure from the Appendix-A cell array. -/
def kappa0 : Measure ℝ := ConfigSegment.pinnedReferenceMeasure

/-- The Fejer contour measure from v10 (5.4), with its `du/(2*pi)` scale. -/
def nu0 : Measure ℂ := ConfigContourMeasure.contourReferenceMeasure

/-- The positive-half-line frequency measure from the Appendix-A cell array. -/
def mu0 : Measure ℝ := ConfigSegment.frequencyReferenceMeasure

/-- The companion measure used in v10 (5.1), built from these same measures. -/
def eta0 : Measure ℂ := p0CompanionMeasure kappa0 nu0

/-- The exact callbacks attached to the reference measures.  In particular,
`LmuNegative` is the reflected integral of `mu0`; it is not a free function. -/
def referencePotentials : Config.DualReferencePotentials :=
  ConfigReferenceSymmetry.actualReference

theorem referencePotentials_LmuNegative (z : ℂ) :
    referencePotentials.LmuNegative z =
      ∫ t, Real.log ‖z + (t : ℂ)‖ ∂mu0 := by
  exact ConfigReferenceSymmetry.actualReference_LmuNegative z

/-- Exact mass of the contour component, as certified by the Fejer integer
array and the `du/(2*pi)` normalization. -/
theorem nu0_mass : nu0 univ =
    ENNReal.ofReal (267885951940 / 1000000000000 : ℝ) := by
  exact ConfigContourMeasure.contourReferenceMeasure_univ

/-- The contour component is atomless. -/
theorem nu0_singleton (z : ℂ) : nu0 {z} = 0 := by
  exact ConfigContourMeasure.contourReferenceMeasure_singleton z

/-- All facts still needed to construct a literal `P0AdmissibleMeasures` are
represented as fields.  The finite-energy field is exactly the seven-clause
`P0FiniteEnergyCondition` from `Contour.lean`; no weaker surrogate is used. -/
structure P0ReferenceFiniteEnergyCertificate where
  kappa_le_density :
    kappa0 ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
  nu_supported : Measure.support nu0 ⊆ Gamma
  companion_mass : eta0 univ = 1
  mu_le_density :
    mu0 ≤ volume.restrict (Set.Ici (1 / 2 : ℝ))
  frequency_mass : mu0 univ = 1
  finite_energy :
    P0FiniteEnergyCondition
      { kappa := kappa0
        nu := nu0
        mu := mu0
        kappa_le_density := kappa_le_density
        nu_supported := nu_supported
        companion_mass := companion_mass
        mu_le_density := mu_le_density
        frequency_mass := frequency_mass }

/-- The exact paper reference, once the explicit certificate obligations are
supplied. -/
noncomputable def M0 (c : P0ReferenceFiniteEnergyCertificate) :
    P0AdmissibleMeasures :=
  { kappa := kappa0
    nu := nu0
    mu := mu0
    kappa_le_density := c.kappa_le_density
    nu_supported := c.nu_supported
    companion_mass := c.companion_mass
    mu_le_density := c.mu_le_density
    frequency_mass := c.frequency_mass }

theorem M0_finite_energy (c : P0ReferenceFiniteEnergyCertificate) :
    P0FiniteEnergyCondition (M0 c) := by
  exact c.finite_energy

theorem M0_eta (c : P0ReferenceFiniteEnergyCertificate) :
    (M0 c).eta = eta0 := by
  rfl

theorem M0_mu (c : P0ReferenceFiniteEnergyCertificate) :
    (M0 c).mu = mu0 := by
  rfl

/-- Named proof obligations for the literal reference.  This proposition is
intentionally not inhabited here: proving it is the remaining admissibility
and finite-energy closure task. -/
def referenceClosureObligations : Prop :=
  kappa0 ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) ∧
  Measure.support nu0 ⊆ Gamma ∧
  eta0 univ = 1 ∧
  mu0 ≤ volume.restrict (Set.Ici (1 / 2 : ℝ)) ∧
  mu0 univ = 1 ∧
  ∃ h : P0AdmissibleMeasures,
    h.kappa = kappa0 ∧ h.nu = nu0 ∧ h.mu = mu0 ∧
    P0FiniteEnergyCondition h

end
end Li2Lean.P0.ReferencePackaging
