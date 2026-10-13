/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Agents.G_L7
import Li2Lean.P0.Contour
import Li2Lean.P0.DualAlgebra
import Li2Lean.P0.TubeCircleMeasure
import Li2Lean.P0.TubeExteriorInverse
import Li2Lean.P0.TubeInteriorPromotion

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

/-! ## The actual tube-side admissible class

`P0AdmissibleMeasures` is the contour problem: its contour component is
supported on `Gamma`.  A tube competitor needs a separate type because its
contour component is supported only on `tube δ`.  Keeping the two types
separate prevents a tube measure from being silently treated as a contour
measure before the sweep has been supplied.
-/

structure P0TubeAdmissibleMeasures (δ : ℝ) where
  kappa : Measure ℝ
  nu : Measure ℂ
  mu : Measure ℝ
  kappa_le_density :
    kappa ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
  nu_supported : Measure.support nu ⊆ tube δ
  companion_mass : p0CompanionMeasure kappa nu Set.univ = 1
  mu_le_density : mu ≤ volume.restrict (Set.Ici (1 / 2 : ℝ))
  frequency_mass : mu Set.univ = 1

/-! The tube class is nonempty for every radius: the zero tube component is
admissible, while the two real components use their unit-mass density caps. -/

theorem p0TubeAdmissibleMeasures_nonempty (δ : ℝ) :
    Nonempty (P0TubeAdmissibleMeasures δ) := by
  refine ⟨{
    kappa := volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
    nu := 0
    mu := volume.restrict (Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ))
    kappa_le_density := le_rfl
    nu_supported := by simp
    companion_mass := ?_
    mu_le_density := ?_
    frequency_mass := ?_ }⟩
  · rw [p0CompanionMeasure, Measure.add_apply,
      Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp [Real.volume_Icc]
    norm_num
  · exact Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl
  · rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num

noncomputable def P0TubeAdmissibleMeasures.eta
    {δ : ℝ} (M : P0TubeAdmissibleMeasures δ) : Measure ℂ :=
  p0CompanionMeasure M.kappa M.nu

/-! ## The genuine finite-energy domain and its extended value

These are the same atomless and logarithmic-integrability conditions used by
the contour problem.  They are repeated for the tube type because the latter
has a different support condition.  In particular, the atomless clause is
not inferred from the density caps or from the sweep leaves.
-/

def p0TubeFiniteEnergyCondition {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) : Prop :=
  Integrable (fun t : ℝ => t) M.mu ∧
  Integrable (fun z : ℂ => p0CompanionField z) M.eta ∧
  Integrable (fun t : ℝ => p0RegularizedFrequencyField t) M.mu ∧
  Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2)
    (M.eta.prod M.eta) ∧
  (∀ z : ℂ, M.eta {z} = 0) ∧
  Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
    (M.mu.prod M.mu) ∧
  Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
    (M.eta.prod M.mu)

noncomputable def p0TubeRegularizedEnergyValue {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) : ℝ :=
  (9 / 2 : ℝ) - 2 * ell +
    ∫ z : ℂ, p0CompanionField z ∂M.eta +
    ∫ t : ℝ, p0RegularizedFrequencyField t ∂M.mu +
    li2LogInteraction M.eta M.eta +
    ∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2
      ∂(M.mu.prod M.mu) +
    ∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2
      ∂(M.eta.prod M.mu)

/-! ## Explicit component gaps

The transfer comparison is an algebraic consequence of the actual field and
interaction gaps.  These definitions name those gaps directly; they are not
certificate fields which repeat the final energy inequality.  The analytic
work is therefore concentrated in bounds for `p0TubeFieldGap` and
`p0TubeInteractionGap`.
-/

noncomputable def p0TubeFieldGap {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) (N : P0AdmissibleMeasures) : ℝ :=
  (∫ z : ℂ, p0CompanionField z ∂N.eta -
      ∫ z : ℂ, p0CompanionField z ∂M.eta) +
    (∫ t : ℝ, p0RegularizedFrequencyField t ∂N.mu -
      ∫ t : ℝ, p0RegularizedFrequencyField t ∂M.mu)

noncomputable def p0TubeInteractionGap {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) (N : P0AdmissibleMeasures) : ℝ :=
  (li2LogInteraction N.eta N.eta - li2LogInteraction M.eta M.eta) +
    ((∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2
        ∂(N.mu.prod N.mu)) -
      ∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2
        ∂(M.mu.prod M.mu)) +
    ((∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2
        ∂(N.eta.prod N.mu)) -
      ∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2
        ∂(M.eta.prod M.mu))

theorem p0Tube_energy_gap_eq_components
    {δ : ℝ} (M : P0TubeAdmissibleMeasures δ) (N : P0AdmissibleMeasures) :
    p0RegularizedEnergyValue N - p0TubeRegularizedEnergyValue M =
      p0TubeFieldGap M N + p0TubeInteractionGap M N := by
  unfold p0RegularizedEnergyValue p0TubeRegularizedEnergyValue
    p0TubeFieldGap p0TubeInteractionGap
  ring

noncomputable def p0TubeExtendedEnergy {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ) : WithTop ℝ := by
  classical
  exact if _h : p0TubeFiniteEnergyCondition M then
    (p0TubeRegularizedEnergyValue M : WithTop ℝ) else ⊤

theorem p0TubeExtendedEnergy_eq_value_of_finite {δ : ℝ}
    (M : P0TubeAdmissibleMeasures δ)
    (hM : p0TubeFiniteEnergyCondition M) :
    p0TubeExtendedEnergy M = (p0TubeRegularizedEnergyValue M : WithTop ℝ) := by
  unfold p0TubeExtendedEnergy
  simp [hM]

theorem p0ExtendedEnergy_eq_value_of_finite
    (M : P0AdmissibleMeasures)
    (hM : P0FiniteEnergyCondition M) :
    p0ExtendedEnergy M = (p0RegularizedEnergyValue M : WithTop ℝ) := by
  unfold p0ExtendedEnergy
  simp [hM]

noncomputable def p0TubeAlpha (δ : ℝ) : WithTop ℝ :=
  sInf (Set.range (p0TubeExtendedEnergy (δ := δ)))

/-! ## The merged analytic leaves

This bundle records exactly the concrete leaves that are already proved.  It
does not fill the final sweep-energy comparison, the exterior pair Green
bound, or the continuum numerical certificate; those remain fields of the
transfer certificate below.
-/

structure TubeMergedLeafBundle : Prop where
  interior : TubeInterior.ActualInteriorSweepPaperAdapter
  circle_average : L7CircleAverageStatement
  circle_product_integrable :
    ∀ z w : ℂ, ∀ {r : ℝ}, 0 < r →
      Integrable
        (fun p : ℂ × ℂ => realLogKernel p.1 p.2)
        ((circleProbability z r).prod (circleProbability w r))
  circle_pair_energy_le :
    ∀ z w : ℂ, ∀ {r : ℝ}, 0 < r →
      (∫ p : ℂ × ℂ, realLogKernel p.1 p.2
        ∂((circleProbability z r).prod (circleProbability w r))) ≤
        -Real.log (max r ‖z - w‖)
  exterior_inverse :
    ∀ z : ℂ, ellipseLevel z ≤ 0 →
      1 ≤ ‖ellipseExteriorInverse z‖ ∧
        joukowski (ellipseExteriorInverse z) = z
  exterior_correction :
    ∀ {δ : ℝ} {z : ℂ}, 0 ≤ δ → z ∈ tube δ →
      0 ≤ exteriorCorrection ellipseExteriorInverse z ∧
        exteriorCorrection ellipseExteriorInverse z ≤ δ / semiMinor

theorem actualTubeMergedLeafBundle : TubeMergedLeafBundle := by
  refine
    { interior := TubeInterior.actualInteriorSweepPaperAdapter
      circle_average := g_l7_circle_average
      circle_product_integrable := ?_
      circle_pair_energy_le := ?_
      exterior_inverse := ?_
      exterior_correction := ?_ }
  · intro z w r hr
    exact integrable_realLogKernel_circleProbability_prod z w hr
  · intro z w r hr
    exact circleProbability_pair_energy_le z w hr
  · intro z hz
    exact ellipseExteriorInverse_spec z hz
  · intro δ z hδ hz
    exact ellipseExteriorCorrection_bound hδ hz

/-! ## Independent scalar transfer from the component ledger

The analytic sweep leaves provide separate field and interaction costs.  This
lemma combines those costs with the exact v10  margin; it does not
assume the final energy comparison as a certificate field.
-/

theorem p0Tube_energy_comparison_of_costs
    {δ : ℝ} (hδ : 0 < δ)
    (M : P0TubeAdmissibleMeasures δ)
    (sweep : P0TubeAdmissibleMeasures δ → P0AdmissibleMeasures)
    {s b : ℝ} (_hs0 : 0 ≤ s) (hs1 : s ≤ 1)
    (hb : b ≤ s * (δ / semiMinor))
    (hF : p0TubeFieldGap M (sweep M) ≤ 288 * s * δ / semiMinor)
    (hI : p0TubeInteractionGap M (sweep M) ≤ 3 * b) :
    p0RegularizedEnergyValue (sweep M) ≤
      p0TubeRegularizedEnergyValue M + 300 * δ := by
  have hI' : p0TubeInteractionGap M (sweep M) ≤
      3 * s * δ / semiMinor := by
    calc
      p0TubeInteractionGap M (sweep M) ≤ 3 * b := hI
      _ ≤ 3 * (s * (δ / semiMinor)) :=
        mul_le_mul_of_nonneg_left hb (by norm_num)
      _ = 3 * s * δ / semiMinor := by ring
  have hsum : p0TubeFieldGap M (sweep M) +
      p0TubeInteractionGap M (sweep M) ≤ 291 * s * δ / semiMinor := by
    calc
      p0TubeFieldGap M (sweep M) + p0TubeInteractionGap M (sweep M) ≤
          (288 * s * δ / semiMinor) + (3 * s * δ / semiMinor) :=
        add_le_add hF hI'
      _ = 291 * s * δ / semiMinor := by ring
  have hmargin := tube_error_cost_lt_300 hδ hs1
  have hgap : p0RegularizedEnergyValue (sweep M) -
      p0TubeRegularizedEnergyValue M ≤ 300 * δ := by
    rw [p0Tube_energy_gap_eq_components]
    exact hsum.trans hmargin.le
  linarith

/-! ## The remaining semantic transfer fields

The `sweep` output is a genuine `P0AdmissibleMeasures`, so all contour caps,
mass identities and `Gamma` support are checked by its constructor.  The
finite-energy premise and its preservation are explicit.  The Green, source,
collar, barrier, and field-cost obligations are collected in the same shape
as `TubeTransferObligations`; the independent component ledger below records
the remaining field and interaction bounds without assuming their conclusion.
The harmonic kernel is a field of the certificate.  It is deliberately not
identified with `TubeInterior.interiorSweep`: that family is proved only for
interior points, while the paper transfer also needs the exterior Poisson
kernel and its boundary branch.
-/

structure P0TubeEnergyComparisonObligations (δ : ℝ)
    (omega : ℂ → Measure ℂ)
    (sweep : P0TubeAdmissibleMeasures δ → P0AdmissibleMeasures) where
  greenD : ℂ → ℂ → ℝ
  interiorCost : ℝ → ℝ → ℝ
  exteriorCost : ℝ → ℝ → ℝ
  energyCost : ℝ → ℝ → ℝ
  green_collar :
    TubeTransferObligations ellipseExteriorInverse omega
      greenD interiorCost exteriorCost energyCost
  /-- Independent bounds for the actual field and interaction gaps. -/
  cost_ledger : ∀ M, p0TubeFiniteEnergyCondition M →
    ∃ s b : ℝ,
      0 ≤ s ∧ s ≤ 1 ∧
      b ≤ s * (δ / semiMinor) ∧
      p0TubeFieldGap M (sweep M) ≤ 288 * s * δ / semiMinor ∧
      p0TubeInteractionGap M (sweep M) ≤ 3 * b

structure P0TubeTransferCertificate (δ : ℝ) where
  leaves : TubeMergedLeafBundle
  omega : ℂ → Measure ℂ
  sweep : P0TubeAdmissibleMeasures δ → P0AdmissibleMeasures
  sweep_kappa : ∀ M, (sweep M).kappa = M.kappa
  sweep_nu : ∀ M, (sweep M).nu = sweptMeasure M.nu omega
  sweep_mu : ∀ M, (sweep M).mu = M.mu
  sweep_finite : ∀ M, p0TubeFiniteEnergyCondition M →
    P0FiniteEnergyCondition (sweep M)
  energy : P0TubeEnergyComparisonObligations δ omega sweep

/-! ## Order-theoretic infimum passage

The next theorem is the complete `WithTop` infimum step.  It retains the
actual atomless/finite-energy hypotheses through `sweep_finite`; competitors
outside the finite-energy domain have extended energy `+∞` and are handled
without an informal `∞ - ∞` subtraction.
-/

theorem p0TubeAlpha_ge_of_transfer
    {δ alpha : ℝ}
    (hδ : 0 < δ) (_hδmax : δ ≤ tubeRadiusMax)
    (hNonempty : Nonempty (P0TubeAdmissibleMeasures δ))
    (certificate : P0TubeTransferCertificate δ)
    (hGammaBdd : BddBelow (Set.range p0ExtendedEnergy))
    (halpha : (alpha : WithTop ℝ) ≤ alphaGamma) :
    ((alpha - 300 * δ : ℝ) : WithTop ℝ) ≤ p0TubeAlpha δ := by
  unfold p0TubeAlpha
  apply le_csInf
  · rcases hNonempty with ⟨M⟩
    exact ⟨p0TubeExtendedEnergy M, M, rfl⟩
  · intro y hy
    rcases hy with ⟨M, rfl⟩
    by_cases hM : p0TubeFiniteEnergyCondition M
    · have hfiniteSweep := certificate.sweep_finite M hM
      have hGammaLe : alphaGamma ≤ p0ExtendedEnergy (certificate.sweep M) := by
        change (sInf (Set.range p0ExtendedEnergy)) ≤ _
        have hSweepMem : p0ExtendedEnergy (certificate.sweep M) ∈
            Set.range p0ExtendedEnergy :=
          Set.mem_range_self (certificate.sweep M)
        exact csInf_le hGammaBdd hSweepMem
      have hAlphaValue : alpha ≤ p0RegularizedEnergyValue (certificate.sweep M) := by
        have hcast : (alpha : WithTop ℝ) ≤
            (p0RegularizedEnergyValue (certificate.sweep M) : WithTop ℝ) := by
          calc
            (alpha : WithTop ℝ) ≤ alphaGamma := halpha
            _ ≤ p0ExtendedEnergy (certificate.sweep M) := hGammaLe
            _ = (p0RegularizedEnergyValue (certificate.sweep M) : WithTop ℝ) :=
              p0ExtendedEnergy_eq_value_of_finite (certificate.sweep M) hfiniteSweep
        exact_mod_cast hcast
      rcases certificate.energy.cost_ledger M hM with
        ⟨s, b, hs0, hs1, hb, hF, hI⟩
      have hcomparison := p0Tube_energy_comparison_of_costs hδ
        M (certificate.sweep) hs0 hs1 hb hF hI
      have hTubeValue : alpha - 300 * δ ≤ p0TubeRegularizedEnergyValue M := by
        linarith
      rw [p0TubeExtendedEnergy_eq_value_of_finite M hM]
      exact_mod_cast hTubeValue
    · rw [show p0TubeExtendedEnergy M = ⊤ by
      unfold p0TubeExtendedEnergy
      simp [hM]]
      exact le_top

/-! ## Paper-facing `300 δ` statement

`hAlphaEq` is the explicit real-valued finiteness bridge for the paper's
`alpha_Gamma`.  The theorem below therefore states exactly the desired real
transfer once the genuine continuum energy comparison and a real infimum
representation are supplied.
-/

def p0TubeEnergyInfimum (energy : ℝ → ℝ) (δ : ℝ) : Prop :=
  (energy δ : WithTop ℝ) = p0TubeAlpha δ

theorem p0Tube_transfer_statement_of_certificate
    (energy : ℝ → ℝ) (alphaGammaReal : ℝ)
    (hAlphaEq : alphaGamma = (alphaGammaReal : WithTop ℝ))
    (hEnergy : ∀ δ, p0TubeEnergyInfimum energy δ)
    (hGammaBdd : BddBelow (Set.range p0ExtendedEnergy))
    (hCertificate : ∀ {δ : ℝ}, 0 < δ → δ ≤ tubeRadiusMax →
      P0TubeTransferCertificate δ) :
    tubeTransferStatement energy alphaGammaReal := by
  intro δ hδ hδmax
  have hbound := p0TubeAlpha_ge_of_transfer hδ hδmax
    (p0TubeAdmissibleMeasures_nonempty δ) (hCertificate hδ hδmax) hGammaBdd
    (show (alphaGammaReal : WithTop ℝ) ≤ alphaGamma by rw [hAlphaEq])
  rw [← hEnergy δ] at hbound
  exact_mod_cast hbound

end
end Li2Lean.P0
