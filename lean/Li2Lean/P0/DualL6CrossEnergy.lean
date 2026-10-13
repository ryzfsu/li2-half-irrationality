/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Admissible
import Li2Lean.P0.TubeCollarVariance
import Li2Lean.P0.TubeVarianceSupport

open MeasureTheory Set Filter

namespace Li2Lean.P0.L6Admissible

noncomputable section

open Li2Lean.P0.L6Variations


/-- Every admissible companion has a logarithmic norm moment: its pinned
part lies in the compact interval , while its contour part is
carried by the compact ellipse . -/
theorem p0_admissible_eta_log_moment (M : P0AdmissibleMeasures) :
    Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M.eta := by
  let fκ : ℝ → ℝ := fun t => Real.log (1 + ‖(t : ℂ)‖)
  have hκmeas : Measurable fκ := by
    apply Real.measurable_log.comp
    fun_prop
  have hκcont : Continuous fκ := by
    unfold fκ
    have hc : Continuous (fun t : ℝ => (1 : ℝ) + ‖(t : ℂ)‖) := by
      fun_prop
    exact hc.log (by intro t; positivity)
  have hκbase : Integrable fκ (volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))) := by
    exact hκcont.continuousOn.integrableOn_compact isCompact_Icc
  have hκ : Integrable (fun z : ℂ => Real.log (1 + ‖z‖))
      (Measure.map Complex.ofReal M.kappa) := by
    have hf : Measurable (fun z : ℂ => Real.log (1 + ‖z‖)) := by
      apply Real.measurable_log.comp
      fun_prop
    rw [integrable_map_measure hf.aestronglyMeasurable
      Complex.measurable_ofReal.aemeasurable]
    have hκ' : Integrable fκ M.kappa := hκbase.mono_measure M.kappa_le_density
    simpa [fκ, Function.comp_def, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg] using hκ'
  have hνtop : M.nu univ ≠ ⊤ := by
    have hle : M.nu ≤ p0CompanionMeasure M.kappa M.nu := by
      exact Measure.le_add_left le_rfl
    have hle' := (Measure.le_iff.mp hle) Set.univ MeasurableSet.univ
    rw [M.companion_mass] at hle'
    exact ne_top_of_le_ne_top (by simp) hle'
  letI : IsFiniteMeasure M.nu := ⟨(lt_top_iff_ne_top.mpr hνtop)⟩
  have hνae : ∀ᵐ z ∂M.nu, z ∈ Gamma := by
    filter_upwards [Measure.support_mem_ae (μ := M.nu)] with z hz
    exact M.nu_supported hz
  have hν : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M.nu := by
    apply Li2Lean.P0.TubeVariance.continuous_integrable M.nu hνae
    have hc : Continuous (fun z : ℂ => (1 : ℝ) + ‖z‖) := by fun_prop
    exact hc.log (by intro z; positivity)
  simpa [P0AdmissibleMeasures.eta, p0CompanionMeasure] using hκ.add_measure hν

/-- The positive L6 kernel is symmetric, including its collision value. -/
theorem l6PosKernel_comm (z w : ℂ) :
    l6PosKernel z w = l6PosKernel w z := by
  by_cases h : z = w
  · simp [h]
  · simp [l6PosKernel, h, Ne.symm h, norm_sub_rev]

private theorem cross_pos_finite_of_right_bound
    {C : ENNReal}
    (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (hC : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂ν ≤ C)
    (hCtop : C ≠ ⊤) (hμtop : μ univ ≠ ⊤) :
    (∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν)) ≠ ⊤ := by
  apply ne_top_of_le_ne_top
    (ENNReal.mul_ne_top hCtop hμtop)
  exact lintegral_posKernel_prod_le hC

/-- Swapping the factors reduces a left-oriented cross integral to the
right-potential bound. -/
private theorem cross_pos_finite_of_left_bound
    {C : ENNReal}
    (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (hC : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂μ ≤ C)
    (hCtop : C ≠ ⊤) (hνtop : ν univ ≠ ⊤) :
    (∫⁻ x, l6PosKernel x.1 x.2 ∂(μ.prod ν)) ≠ ⊤ := by
  have hswap := cross_pos_finite_of_right_bound ν μ (C := C) (by
    intro z
    simpa only [l6PosKernel_comm] using hC z) hCtop hνtop
  intro htop
  apply hswap
  rw [← lintegral_prod_swap (fun x : ℂ × ℂ => l6PosKernel x.1 x.2)] at htop
  have hsymm : (fun x : ℂ × ℂ => l6PosKernel x.swap.1 x.swap.2) =
      (fun x : ℂ × ℂ => l6PosKernel x.1 x.2) := by
    funext x
    simpa [Prod.swap] using (l6PosKernel_comm x.2 x.1)
  rw [hsymm] at htop
  exact htop

/-- The four cross integrabilities follow once the two reference marginals
have finite uniformly bounded positive potentials.  The orientation of the
fourth term is handled by the kernel symmetry and product swap. -/
theorem p0L6CrossEnergy_of_uniform_reference_potential
    (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) (hfin₀ : P0FiniteEnergyCondition M₀)
    (hη : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M.eta)
    (hη₀ : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M₀.eta)
    {Cη Cφ : ENNReal}
    (hηbound : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂M₀.eta ≤ Cη)
    (hφbound : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂(p0FrequencyMeasure M₀) ≤ Cφ)
    (hCη : Cη ≠ ⊤) (hCφ : Cφ ≠ ⊤) :
    P0L6CrossEnergy M M₀ := by
  have hφ := freq_log_moment M hfin
  have hφ₀ := freq_log_moment M₀ hfin₀
  have hηtop : M.eta univ ≠ ⊤ := by
    simp [show M.eta univ = 1 from M.companion_mass]
  have hη₀top : M₀.eta univ ≠ ⊤ := by
    simp [show M₀.eta univ = 1 from M₀.companion_mass]
  have hφtop : (p0FrequencyMeasure M) univ ≠ ⊤ := by
    simp [p0AdmissibleFrequencyMeasure_mass]
  have hp1 : (∫⁻ x, l6PosKernel x.1 x.2 ∂(M.eta.prod M₀.eta)) ≠ ⊤ :=
    cross_pos_finite_of_right_bound M.eta M₀.eta hηbound hCη hηtop
  have hp2 : (∫⁻ x, l6PosKernel x.1 x.2 ∂((p0FrequencyMeasure M).prod
      (p0FrequencyMeasure M₀))) ≠ ⊤ :=
    cross_pos_finite_of_right_bound (p0FrequencyMeasure M)
      (p0FrequencyMeasure M₀) hφbound hCφ hφtop
  have hp3 : (∫⁻ x, l6PosKernel x.1 x.2 ∂(M.eta.prod
      (p0FrequencyMeasure M₀))) ≠ ⊤ :=
    cross_pos_finite_of_right_bound M.eta (p0FrequencyMeasure M₀)
      hφbound hCφ hηtop
  have hp4 : (∫⁻ x, l6PosKernel x.1 x.2 ∂(M₀.eta.prod
      (p0FrequencyMeasure M))) ≠ ⊤ :=
    cross_pos_finite_of_left_bound M₀.eta (p0FrequencyMeasure M)
      hηbound hCη hφtop
  exact p0L6CrossEnergy_of_split M M₀ hfin hfin₀ hη hη₀ hp1 hp2 hp3 hp4


/-- Convenience form with the two companion logarithmic moments discharged
from admissibility itself. -/
theorem p0L6CrossEnergy_of_uniform_reference_potential_of_admissible
    (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M) (hfin₀ : P0FiniteEnergyCondition M₀)
    {Cη Cφ : ENNReal}
    (hηbound : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂M₀.eta ≤ Cη)
    (hφbound : ∀ z : ℂ, ∫⁻ w, l6PosKernel z w ∂(p0FrequencyMeasure M₀) ≤ Cφ)
    (hCη : Cη ≠ ⊤) (hCφ : Cφ ≠ ⊤) :
    P0L6CrossEnergy M M₀ := by
  exact p0L6CrossEnergy_of_uniform_reference_potential M M₀ hfin hfin₀
    (p0_admissible_eta_log_moment M) (p0_admissible_eta_log_moment M₀)
    hηbound hφbound hCη hCφ

end
end Li2Lean.P0.L6Admissible
