/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorBoundary

/-! # Actual exterior two-sweep logarithmic energy -/

open MeasureTheory Complex Filter

namespace Li2Lean.P0

noncomputable section

/-- A coarse compactness bound used only to establish absolute integrability. -/
theorem norm_le_three_of_mem_Gamma {x : ℂ} (hx : x ∈ Gamma) : ‖x‖ ≤ 3 := by
  rcases hx with ⟨θ, rfl⟩
  rw [← joukowski_circleMap_eq_gammaPoint θ]
  have h := (norm_add_le ((center : ℂ) + ellipseC * circleMap 0 1 θ)
    (ellipseD * (circleMap 0 1 θ)⁻¹)).trans
      (add_le_add (norm_add_le (center : ℂ) (ellipseC * circleMap 0 1 θ)) le_rfl)
  simp only [norm_mul, norm_inv, norm_circleMap_zero, abs_one, inv_one, mul_one,
    ellipseC_norm, ellipseD_norm] at h
  norm_num [joukowski, center, semiMajor, semiMinor] at h ⊢
  linarith

/-- Symmetry of the finite-valued logarithmic kernel. -/
theorem exterior_realLogKernel_comm (z w : ℂ) : realLogKernel z w = realLogKernel w z := by
  simp only [realLogKernel, norm_sub_rev]

/-- A lower bound for the boundary kernel controls its absolute value by its signed value. -/
theorem norm_realLogKernel_le_on_Gamma {x y : ℂ} (hx : x ∈ Gamma) (hy : y ∈ Gamma) :
    ‖realLogKernel x y‖ ≤ 12 + realLogKernel x y := by
  have hdist : ‖x - y‖ ≤ 6 :=
    (norm_sub_le x y).trans (by linarith [norm_le_three_of_mem_Gamma hx, norm_le_three_of_mem_Gamma hy])
  have hlog : Real.log ‖x - y‖ ≤ 6 := (Real.log_le_self (norm_nonneg _)).trans hdist
  rw [realLogKernel, Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith, by linarith⟩

/-- The constructed exterior measures are carried by the entire boundary. -/
theorem exteriorSweep_ae_mem_Gamma (z : ℂ) : ∀ᵐ y ∂exteriorSweep z, y ∈ Gamma := by
  rw [ae_iff]
  exact exteriorSweep_boundary_support z

/-- A genuine L1 bound for every boundary logarithmic slice of the actual exterior law. -/
theorem integral_norm_exteriorSweep_boundary {z x : ℂ} (hz : ellipseLevel z < 0)
    (hx : x ∈ Gamma) :
    (∫ y, ‖realLogKernel y x‖ ∂exteriorSweep z) ≤
      12 + realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
  let : IsProbabilityMeasure (exteriorSweep z) := ⟨exteriorSweep_univ hz⟩
  have hi := exteriorSweep_integrable_logKernel hz x
  calc
    (∫ y, ‖realLogKernel y x‖ ∂exteriorSweep z) ≤
        ∫ y, (12 + realLogKernel y x) ∂exteriorSweep z := by
      apply integral_mono_ae hi.norm ((integrable_const 12).add hi)
      filter_upwards [exteriorSweep_ae_mem_Gamma z] with y hy
      exact norm_realLogKernel_le_on_Gamma hy hx
    _ = 12 + realLogKernel z x + exteriorCorrection ellipseExteriorInverse z := by
      rw [integral_add (integrable_const 12) hi, integral_const,
        exteriorSweep_boundary_source hz hx]
      simp only [Measure.real, exteriorSweep_univ hz, ENNReal.toReal_one, one_smul]
      ring

/-- Joint absolute integrability for two actual exterior sweeps, including coincident centers.
No product-integrability or boundary-separation premise is assumed. -/
theorem integrable_exteriorSweep_prod {z w : ℂ} (hz : ellipseLevel z < 0)
    (hw : ellipseLevel w < 0) :
    Integrable (fun q : ℂ × ℂ => realLogKernel q.1 q.2)
      ((exteriorSweep z).prod (exteriorSweep w)) := by
  let : IsProbabilityMeasure (exteriorSweep z) := ⟨exteriorSweep_univ hz⟩
  let : IsProbabilityMeasure (exteriorSweep w) := ⟨exteriorSweep_univ hw⟩
  have hmeas : AEStronglyMeasurable (fun q : ℂ × ℂ => realLogKernel q.1 q.2)
      ((exteriorSweep z).prod (exteriorSweep w)) := by
    apply Measurable.aestronglyMeasurable
    unfold realLogKernel
    fun_prop
  apply (integrable_prod_iff hmeas).mpr
  constructor
  · apply ae_of_all
    intro x
    simpa only [exterior_realLogKernel_comm] using exteriorSweep_integrable_logKernel hw x
  · have hb : Integrable
        (fun x => 12 + realLogKernel x w + exteriorCorrection ellipseExteriorInverse w)
        (exteriorSweep z) :=
      ((integrable_const 12).add (exteriorSweep_integrable_logKernel hz w)).add (integrable_const _)
    apply hb.mono' hmeas.norm.integral_prod_right'
    filter_upwards [exteriorSweep_ae_mem_Gamma z] with x hx
    rw [Real.norm_of_nonneg (integral_nonneg (fun _ => norm_nonneg _))]
    have h := integral_norm_exteriorSweep_boundary hw hx
    simpa only [exterior_realLogKernel_comm] using h

/-- Fubini and the full boundary-source identity give the exact two-sweep potential reduction. -/
theorem integral_exteriorSweep_prod_eq {z w : ℂ} (hz : ellipseLevel z < 0)
    (hw : ellipseLevel w < 0) :
    (∫ q : ℂ × ℂ, realLogKernel q.1 q.2 ∂((exteriorSweep z).prod (exteriorSweep w))) =
      (∫ y, realLogKernel y w ∂exteriorSweep z) + exteriorCorrection ellipseExteriorInverse w := by
  let : IsProbabilityMeasure (exteriorSweep z) := ⟨exteriorSweep_univ hz⟩
  let : IsProbabilityMeasure (exteriorSweep w) := ⟨exteriorSweep_univ hw⟩
  rw [integral_prod _ (integrable_exteriorSweep_prod hz hw)]
  calc
    (∫ x, ∫ y, realLogKernel x y ∂exteriorSweep w ∂exteriorSweep z) =
        ∫ x, (realLogKernel x w + exteriorCorrection ellipseExteriorInverse w) ∂exteriorSweep z := by
      apply integral_congr_ae
      filter_upwards [exteriorSweep_ae_mem_Gamma z] with x hx
      have h := exteriorSweep_boundary_source hw hx
      convert h using 1 <;> simp only [exterior_realLogKernel_comm]
    _ = _ := by
      rw [integral_add (exteriorSweep_integrable_logKernel hz w) (integrable_const _), integral_const]
      simp only [Measure.real, exteriorSweep_univ hz, ENNReal.toReal_one, one_smul]

/-- The exterior/exterior part of v10 `tube-green` for the actual measures.
The diagonal exclusion is solely the source kernel's finite-valued convention; the product integral
above remains absolutely integrable on the diagonal as well. -/
theorem exteriorSweep_two_sweep {z w : ℂ} (hz : ellipseLevel z < 0)
    (hw : ellipseLevel w < 0) (hzw : z ≠ w) :
    (∫ q : ℂ × ℂ, realLogKernel q.1 q.2 ∂((exteriorSweep z).prod (exteriorSweep w))) ≤
      realLogKernel z w + exteriorCorrection ellipseExteriorInverse z +
        exteriorCorrection ellipseExteriorInverse w := by
  rw [integral_exteriorSweep_prod_eq hz hw]
  exact add_le_add (exteriorSweep_point_green hz hw.ne hzw) le_rfl

end
end Li2Lean.P0
