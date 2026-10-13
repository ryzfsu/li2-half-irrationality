/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeSweptFiniteEnergy

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

/-! ## Concrete harmonic-sweep adapter

The output measure is the actual harmonic sweep bind.  The constructor proves the
support, mass, cap, and component equalities directly; only the semantic cost
ledger remains an input to the certificate.  In particular, the ledger is not
repackaged here as an energy conclusion field.
-/

noncomputable def p0TubeSweep {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) : P0AdmissibleMeasures := by
  refine
    { kappa := M.kappa
      nu := TubeEnergy.tubeSwept M.nu
      mu := M.mu
      kappa_le_density := M.kappa_le_density
      nu_supported := ?_
      companion_mass := ?_
      mu_le_density := M.mu_le_density
      frequency_mass := M.frequency_mass }
  · apply Measure.support_subset_of_isClosed TubeInterior.isCompact_Gamma.isClosed
    change TubeEnergy.tubeSwept M.nu Gammaᶜ = 0
    exact TubeEnergy.tubeSwept_boundary_support M.nu
  · simpa [p0CompanionMeasure, Measure.add_apply,
      TubeEnergy.tubeSwept_univ,
      Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ] using M.companion_mass

@[simp] theorem p0TubeSweep_kappa {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) :
    (p0TubeSweep M).kappa = M.kappa := rfl

@[simp] theorem p0TubeSweep_nu {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) :
    (p0TubeSweep M).nu = sweptMeasure M.nu TubeEnergy.tubeSweep := rfl

@[simp] theorem p0TubeSweep_mu {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) :
    (p0TubeSweep M).mu = M.mu := rfl

/-- The actual swept output preserves the full finite-energy predicate. -/
theorem p0TubeSweep_finite
    {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ)
    (hM : p0TubeFiniteEnergyCondition M) :
    P0FiniteEnergyCondition (p0TubeSweep M) := by
  apply p0Tube_sweep_finite_energy hδ hδmax M hM (p0TubeSweep M)
  · rfl
  · rfl
  · rfl

/-! ## Certificate constructor and infimum adapter

The first theorem is the strongest unconditional constructor available from the
current leaves.  Its only analytic input is the existing energy-comparison obligation
whose cost ledger is consumed by
p0TubeAlpha_ge_of_transfer in the infimum theorem.
-/

noncomputable def p0TubeTransferCertificate_of_energy_obligations
    {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (hEnergy :
      P0TubeEnergyComparisonObligations δ TubeEnergy.tubeSweep p0TubeSweep) :
    P0TubeTransferCertificate δ := by
  refine
    { leaves := actualTubeMergedLeafBundle
      omega := TubeEnergy.tubeSweep
      sweep := p0TubeSweep
      sweep_kappa := fun M => rfl
      sweep_nu := fun M => rfl
      sweep_mu := fun M => rfl
      sweep_finite := ?_
      energy := hEnergy }
  intro M hM
  exact p0TubeSweep_finite hδ hδmax M hM

/-- Direct WithTop infimum passage using the concrete harmonic sweep. -/
theorem p0TubeAlpha_ge_of_energy_obligations
    {δ alpha : ℝ}
    (hδ : 0 < δ) (hδmax : δ ≤ tubeRadiusMax)
    (hEnergy :
      P0TubeEnergyComparisonObligations δ TubeEnergy.tubeSweep p0TubeSweep)
    (hGammaBdd : BddBelow (Set.range p0ExtendedEnergy))
    (halpha : (alpha : WithTop ℝ) ≤ alphaGamma) :
    ((alpha - 300 * δ : ℝ) : WithTop ℝ) ≤ p0TubeAlpha δ := by
  exact p0TubeAlpha_ge_of_transfer hδ hδmax
    (p0TubeAdmissibleMeasures_nonempty δ)
    (p0TubeTransferCertificate_of_energy_obligations hδ.le hδmax hEnergy)
    hGammaBdd halpha

end
end Li2Lean.P0
