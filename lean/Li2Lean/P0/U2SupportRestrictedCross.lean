/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6CrossEnergy
import Li2Lean.P0.Mu0Cap
import Li2Lean.P0.U2NegativeAxisCap

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0.L6Admissible
noncomputable section

open Li2Lean.P0.L6Variations

private theorem cross_pos_finite_of_right_ae_bound
    (μ ν : Measure ℂ) {C : ENNReal} [SFinite μ] [SFinite ν]
    (hC : ∀ᵐ z ∂μ, (∫⁻ w, l6PosKernel z w ∂ν) ≤ C)
    (hCtop : C ≠ ⊤) (hμtop : μ univ ≠ ⊤) :
    (∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top (ENNReal.mul_ne_top hCtop hμtop)
  rw [lintegral_prod _ measurable_l6PosKernel.aemeasurable]
  calc
    (∫⁻ z, ∫⁻ w, l6PosKernel (z, w).1 (z, w).2 ∂ν ∂μ) ≤
        ∫⁻ _z, C ∂μ := by
      apply lintegral_mono_ae
      simpa using hC
    _ = C * μ univ := lintegral_const _

private theorem cross_pos_finite_of_left_ae_bound
    (μ ν : Measure ℂ) {C : ENNReal} [SFinite μ] [SFinite ν]
    (hC : ∀ᵐ z ∂ν, (∫⁻ w, l6PosKernel z w ∂μ) ≤ C)
    (hCtop : C ≠ ⊤) (hνtop : ν univ ≠ ⊤) :
    (∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν)) ≠ ⊤ := by
  have hswap := cross_pos_finite_of_right_ae_bound ν μ (C := C) hC hCtop hνtop
  intro htop
  apply hswap
  rw [← lintegral_prod_swap (fun x : ℂ × ℂ => l6PosKernel x.1 x.2)] at htop
  have hsymm : (fun x : ℂ × ℂ => l6PosKernel x.swap.1 x.swap.2) =
      (fun x : ℂ × ℂ => l6PosKernel x.1 x.2) := by
    funext x
    simpa [Prod.swap] using (l6PosKernel_comm x.2 x.1)
  rw [hsymm] at htop
  exact htop

/-- Support-local bridge. Sη and Sφ are support sets on which the reference
positive-kernel potentials are capped. Their AE support transfers are explicit
for all four source marginals, so no global-in-z cap is hidden. -/
theorem p0L6CrossEnergy_of_support_restricted_of_admissible
    (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M)
    (hfin₀ : P0FiniteEnergyCondition M₀)
    {Sη Sφ : Set ℂ} {Cη Cφ : ENNReal}
    (hηcap : ∀ z ∈ Sη, (∫⁻ w, l6PosKernel z w ∂M₀.eta) ≤ Cη)
    (hφcap : ∀ z ∈ Sφ,
      (∫⁻ w, l6PosKernel z w ∂(p0FrequencyMeasure M₀)) ≤ Cφ)
    (hηM : ∀ᵐ z ∂M.eta, z ∈ Sη)
    (hηφM : ∀ᵐ z ∂(p0FrequencyMeasure M), z ∈ Sη)
    (hφM : ∀ᵐ z ∂M.eta, z ∈ Sφ)
    (hφφM : ∀ᵐ z ∂(p0FrequencyMeasure M), z ∈ Sφ)
    (hCη : Cη ≠ ⊤) (hCφ : Cφ ≠ ⊤) :
    P0L6CrossEnergy M M₀ := by
  have hηtop : M.eta univ ≠ ⊤ := by simp [show M.eta univ = 1 from M.companion_mass]
  have hη₀top : M₀.eta univ ≠ ⊤ := by simp [show M₀.eta univ = 1 from M₀.companion_mass]
  have hφtop : (p0FrequencyMeasure M) univ ≠ ⊤ := by
    simp [p0AdmissibleFrequencyMeasure_mass]
  have hηMb : ∀ᵐ z ∂M.eta, (∫⁻ w, l6PosKernel z w ∂M₀.eta) ≤ Cη :=
    hηM.mono (fun z hz => hηcap z hz)
  have hηφMb : ∀ᵐ z ∂(p0FrequencyMeasure M),
      (∫⁻ w, l6PosKernel z w ∂M₀.eta) ≤ Cη :=
    hηφM.mono (fun z hz => hηcap z hz)
  have hφMb : ∀ᵐ z ∂M.eta,
      (∫⁻ w, l6PosKernel z w ∂(p0FrequencyMeasure M₀)) ≤ Cφ :=
    hφM.mono (fun z hz => hφcap z hz)
  have hφφMb : ∀ᵐ z ∂(p0FrequencyMeasure M),
      (∫⁻ w, l6PosKernel z w ∂(p0FrequencyMeasure M₀)) ≤ Cφ :=
    hφφM.mono (fun z hz => hφcap z hz)
  have hp1 := cross_pos_finite_of_right_ae_bound M.eta M₀.eta hηMb hCη hηtop
  have hp2 := cross_pos_finite_of_right_ae_bound (p0FrequencyMeasure M)
      (p0FrequencyMeasure M₀) hφφMb hCφ hφtop
  have hp3 := cross_pos_finite_of_right_ae_bound M.eta
      (p0FrequencyMeasure M₀) hφMb hCφ hηtop
  have hp4 := cross_pos_finite_of_left_ae_bound M₀.eta
      (p0FrequencyMeasure M) hηφMb hCη hφtop
  exact p0L6CrossEnergy_of_split M M₀ hfin hfin₀
    (p0_admissible_eta_log_moment M) (p0_admissible_eta_log_moment M₀)
    hp1 hp2 hp3 hp4

end
end Li2Lean.P0.L6Admissible
