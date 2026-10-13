/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Admissible
import Li2Lean.P0.ConfigContourMeasure
import Li2Lean.P0.ConfigSegment
import Li2Lean.P0.ConfigContourKernel
import Li2Lean.P0.TubeEnergyGain
import Li2Lean.P0.TubeInteriorSweep

open MeasureTheory Set Filter
open scoped ENNReal

namespace Li2Lean.P0

noncomputable section

open L6Admissible
open L6Variations
open ConfigContourMeasure
open ConfigContourKernel

/-- The four literal measures used by the v10 reference pair. -/
def kappa0 : Measure ℝ := ConfigSegment.pinnedReferenceMeasure
def nu0 : Measure ℂ := ConfigContourMeasure.contourReferenceMeasure
def mu0 : Measure ℝ := ConfigSegment.frequencyReferenceMeasure

/-- Fejér/Joukowski chord lower bound.  It is the quantitative input used to
control the logarithmic diagonal of the contour reference. -/
theorem fejer_contour_chord_lower (u v : ℝ) :
    contourScale * (1 - contourRatio) * ‖ConfigContourKernel.phase u -
      ConfigContourKernel.phase v‖ ≤
      ‖Li2Lean.p0EllipsePoint 1 u - Li2Lean.p0EllipsePoint 1 v‖ := by
  rw [ConfigContourKernel.ellipse_difference_factorization, norm_mul, norm_mul]
  have hs : ‖(contourScale : ℂ)‖ = contourScale := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos contourScale_pos]
  let q : ℂ := (contourRatio : ℂ) /
      (ConfigContourKernel.phase u * ConfigContourKernel.phase v)
  have hqnorm : ‖q‖ = contourRatio := by
    dsimp [q]
    rw [norm_div, norm_mul, norm_phase, norm_phase,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg contourRatio_nonneg]
    simp
  have hq : 1 - contourRatio ≤ ‖1 - q‖ := by
    have htri : ‖(1 : ℂ)‖ ≤ ‖1 - q‖ + ‖q‖ := by
      calc
        ‖(1 : ℂ)‖ = ‖(1 - q) + q‖ := by congr 1 <;> ring
        _ ≤ ‖1 - q‖ + ‖q‖ := norm_add_le _ _
    rw [norm_one, hqnorm] at htri
    linarith
  rw [hs]
  have hh := mul_le_mul_of_nonneg_left hq
    (mul_nonneg contourScale_pos.le
      (norm_nonneg (ConfigContourKernel.phase u - ConfigContourKernel.phase v)))
  convert hh using 1 <;> ring
/-- Data needed to turn the three literal measures into an admissible finite
energy reference.  The fields are explicit proof obligations: no positivity
or finite-energy claim is hidden behind a declaration. -/
structure P0ReferenceFiniteEnergyData where
  kappa_le_density : kappa0 ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
  nu_supported : Measure.support nu0 ⊆ Gamma
  companion_mass : p0CompanionMeasure kappa0 nu0 Set.univ = 1
  mu_le_density : mu0 ≤ volume.restrict (Set.Ici (1 / 2 : ℝ))
  frequency_mass : mu0 Set.univ = 1
  finite_energy : P0FiniteEnergyCondition {
    kappa := kappa0
    nu := nu0
    mu := mu0
    kappa_le_density := kappa_le_density
    nu_supported := nu_supported
    companion_mass := companion_mass
    mu_le_density := mu_le_density
    frequency_mass := frequency_mass }

/-- Package `κ₀,ν₀,μ₀` as a finite-energy `P0AdmissibleMeasures`. -/
def p0ReferenceMeasures (h : P0ReferenceFiniteEnergyData) : P0AdmissibleMeasures := {
  kappa := kappa0
  nu := nu0
  mu := mu0
  kappa_le_density := h.kappa_le_density
  nu_supported := h.nu_supported
  companion_mass := h.companion_mass
  mu_le_density := h.mu_le_density
  frequency_mass := h.frequency_mass }

theorem p0ReferenceMeasures_finite_energy (h : P0ReferenceFiniteEnergyData) :
    P0FiniteEnergyCondition (p0ReferenceMeasures h) := h.finite_energy

/-- Cross-energy finiteness from four positive-part bounds.  The four bounds
are exactly the M/M₀, reflected-frequency, and mixed entries of the dual
quadratic expansion. -/
theorem p0Reference_cross_energy
    (h : P0ReferenceFiniteEnergyData)
    (M : P0AdmissibleMeasures) (hM : P0FiniteEnergyCondition M)
    (hη : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) M.eta)
    (hη₀ : Integrable (fun z : ℂ => Real.log (1 + ‖z‖)) (p0ReferenceMeasures h).eta)
    {p1 p2 p3 p4 : ℝ≥0∞}
    (hp1 : ∫⁻ x, L6Variations.l6PosKernel x.1 x.2 ∂(M.eta.prod (p0ReferenceMeasures h).eta) ≤ p1)
    (hp2 : ∫⁻ x, L6Variations.l6PosKernel x.1 x.2 ∂((p0FrequencyMeasure M).prod
      (p0FrequencyMeasure (p0ReferenceMeasures h))) ≤ p2)
    (hp3 : ∫⁻ x, L6Variations.l6PosKernel x.1 x.2 ∂(M.eta.prod
      (p0FrequencyMeasure (p0ReferenceMeasures h))) ≤ p3)
    (hp4 : ∫⁻ x, L6Variations.l6PosKernel x.1 x.2 ∂((p0ReferenceMeasures h).eta.prod
      (p0FrequencyMeasure M)) ≤ p4)
    (hfinite1 : p1 ≠ ⊤) (hfinite2 : p2 ≠ ⊤)
    (hfinite3 : p3 ≠ ⊤) (hfinite4 : p4 ≠ ⊤) :
    P0L6CrossEnergy M (p0ReferenceMeasures h) := by
  apply p0L6CrossEnergy_of_split M (p0ReferenceMeasures h) hM h.finite_energy hη hη₀
  · intro htop
    apply hfinite1
    apply top_unique
    simpa [htop] using hp1
  · intro htop
    apply hfinite2
    apply top_unique
    simpa [htop] using hp2
  · intro htop
    apply hfinite3
    apply top_unique
    simpa [htop] using hp3
  · intro htop
    apply hfinite4
    apply top_unique
    simpa [htop] using hp4

/-- Concrete W-field bookkeeping for the regularized dual energy.  The two
caps are kept as explicit hypotheses (`h_eta-P` and `h_mu-T`); all L6
quadratic terms are discharged by `p0_dualLower_regularizedQuadratic_ge`. -/
theorem p0_dualLower_energyValue_ge
    (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M)
    (hfin₀ : P0FiniteEnergyCondition M₀)
    (hcross : P0L6CrossEnergy M M₀)
    (h_eta P h_mu T C : ℝ)
    (hC : C = (9 / 2 : ℝ) - 2 * ell)
    (hEtaCap : h_eta - P ≤
      (∫ z, p0CompanionField z ∂M.eta) +
      (∫ z, (-2 * L6Variations.l6LogPotential M₀.eta z -
        L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z) ∂M.eta))
    (hMuCap : h_mu - T ≤
      (∫ t, p0RegularizedFrequencyField t ∂M.mu) +
      3 * (∫ t, Real.log (1 + t) ∂M.mu) +
      (∫ z, (-2 * L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z -
        L6Variations.l6LogPotential M₀.eta z) ∂(p0FrequencyMeasure M))) :
    C + L6Variations.l6QLog M₀.eta (p0FrequencyMeasure M₀) + h_eta + h_mu - P - T ≤
      p0RegularizedEnergyValue M := by
  have hquad := p0_dualLower_regularizedQuadratic_ge M M₀ hfin hfin₀ hcross
  unfold p0RegularizedEnergyValue
  rw [hC]
  linear_combination hquad + hEtaCap + hMuCap

end
end Li2Lean.P0

namespace Li2Lean.P0

open MeasureTheory Set Filter
open scoped ENNReal

namespace L6Variations

/-- Pointwise conversion from a positive distance to a finite `l6PosKernel`
cap.  This is the generic ENNReal/log-distance interface used by the literal
reference bounds below. -/
theorem l6PosKernel_le_of_dist_lower {d : ℝ} (hd : 0 < d) {z w : ℂ}
    (h : d ≤ ‖z - w‖) :
    l6PosKernel z w ≤ ENNReal.ofReal (Real.posLog d⁻¹) := by
  have hnorm : 0 < ‖z - w‖ := lt_of_lt_of_le hd h
  have hne : z ≠ w := by
    intro hzw
    subst w
    simpa using hnorm
  have hinv : ‖z - w‖⁻¹ ≤ d⁻¹ := by
    simpa [one_div] using (one_div_le_one_div_of_le hd h)
  have hlog : Real.posLog ‖z - w‖⁻¹ ≤ Real.posLog d⁻¹ := by
    exact Real.posLog_le_posLog (by linarith [inv_nonneg.mpr (norm_nonneg (z - w))]) hinv
  simp [l6PosKernel, hne]
  exact ENNReal.ofReal_le_ofReal hlog

end L6Variations

namespace U2PinnedReference

open L6Variations
open ConfigContourMeasure

/-- The literal contour reference is carried by the ellipse `Gamma`. -/
theorem nu0_ae_mem_Gamma : ∀ᵐ w ∂nu0, w ∈ Gamma := by
  rw [nu0, contourReferenceMeasure]
  apply (ae_map_iff continuous_ellipse.aemeasurable
    TubeInterior.measurable_Gamma).2
  filter_upwards [] with u
  change Config.baseEllipse u ∈ Gamma
  rw [← TubeEnergy.gammaPoint_eq_baseEllipse]
  exact ⟨u, rfl⟩

/-- Uniform positive-part cap for a pinned real point against the literal
contour reference.  The only geometric input is the proved `751/5000`
source-to-ellipse clearance. -/
theorem pinned_l6PosKernel_bound {x : ℝ}
    (hx : x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) :
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂nu0) ≤
      ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ := by
  letI : IsFiniteMeasure nu0 := by
    unfold nu0
    infer_instance
  have hx02 : (x : ℂ).re ∈ Set.Icc (0 : ℝ) 2 := by
    simp only [Complex.ofReal_re]
    constructor <;> linarith [hx.1, hx.2]
  have hdist : ∀ᵐ w ∂nu0, (751 / 5000 : ℝ) ≤ ‖(x : ℂ) - w‖ := by
    filter_upwards [nu0_ae_mem_Gamma] with w hw
    have h := TubeEnergy.positive_source_norm_sub_ge hx02 (by simp) hw
    simpa [norm_sub_rev] using h
  calc
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂nu0) ≤
        ∫⁻ _w : ℂ, ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) ∂nu0 := by
      apply lintegral_mono_ae
      filter_upwards [hdist] with w hw
      exact l6PosKernel_le_of_dist_lower (by norm_num) hw
    _ = ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ :=
      lintegral_const _

/-- Reference cross-energy interface for a pinned source measure.  It is
stated with an explicit almost-everywhere support premise so it can be used
for a mapped or swept pinned measure without hiding a support transfer. -/
theorem pinned_cross_l6PosKernel_bound
    (κc : Measure ℂ) [SFinite κc]
    (hκ : ∀ᵐ z ∂κc,
      ∃ x : ℝ, x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ) ∧ z = (x : ℂ)) :
    (∫⁻ p, l6PosKernel p.1 p.2 ∂(κc.prod nu0)) ≤
      ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * κc Set.univ * nu0 Set.univ := by
  letI : IsFiniteMeasure nu0 := by
    unfold nu0
    infer_instance
  rw [lintegral_prod _ measurable_l6PosKernel.aemeasurable]
  have hinner : ∀ᵐ z ∂κc,
      (∫⁻ w, l6PosKernel z w ∂nu0) ≤
        ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ := by
    filter_upwards [hκ] with z hz
    obtain ⟨x, hx, rfl⟩ := hz
    exact pinned_l6PosKernel_bound hx
  have hinner' : ∀ᵐ z ∂κc,
      (∫⁻ w, l6PosKernel (z, w).1 (z, w).2 ∂nu0) ≤
        ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ := by
    simpa using hinner
  calc
    (∫⁻ z, ∫⁻ w, l6PosKernel (z, w).1 (z, w).2 ∂nu0 ∂κc) ≤
        ∫⁻ _z, ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * nu0 Set.univ ∂κc :=
      lintegral_mono_ae hinner'
    _ = ENNReal.ofReal (Real.posLog (751 / 5000 : ℝ)⁻¹) * κc Set.univ * nu0 Set.univ := by
      rw [lintegral_const]
      ac_rfl
