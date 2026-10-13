/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.DualL6Reference
import Li2Lean.P0.ContourEnergyLowerBound
import Li2Lean.P0.U2NegativeAxisCap
import Li2Lean.P0.TubeEnergyGain

open MeasureTheory Set Filter
open scoped ENNReal BigOperators

namespace Li2Lean.P0.U2NegativeEtaL6Cap

noncomputable section

open Li2Lean.P0.L6Variations
open Li2Lean.P0.L6Admissible
open Li2Lean.P0.EnergyLowerBound
open Li2Lean.P0.U2GlobalFejer
open Li2Lean.P0.ConfigContourMeasure
open Li2Lean.P0.ConfigContourTail

private theorem l6PosKernel_le_of_dist_lower
    {z w : ℂ} {d : ℝ} (hd : 0 < d) (h : d ≤ ‖z - w‖) :
    l6PosKernel z w ≤ ENNReal.ofReal (Real.posLog d⁻¹) := by
  have hne : z ≠ w := by
    intro hzw
    subst w
    simp at h
    linarith
  simp only [l6PosKernel, hne, ↓reduceIte]
  apply ENNReal.ofReal_le_ofReal
  apply Real.posLog_le_posLog
  · exact le_trans (by norm_num) (inv_nonneg.mpr (norm_nonneg _))
  · have hn : ‖z - w‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
    simpa [one_div] using one_div_le_one_div_of_le hd h

/-- The negative-axis clearance from `x ≤ -1/2` to the literal reference eta
support (the pinned interval and the contour) is `1749/5000`. -/
def negativeEtaClearance : ℝ := 1749 / 5000

private theorem negativeEtaClearance_pos : 0 < negativeEtaClearance := by
  norm_num [negativeEtaClearance]

/-- Almost every point of the literal reference eta is at least the explicit
negative-axis clearance away from any `x ≤ -1/2`. -/
theorem reference_eta_negative_distance_ae
    (hRef : P0ReferenceFiniteEnergyData) {x : ℝ} (hx : x ≤ -(1 / 2 : ℝ)) :
    ∀ᵐ w ∂(p0ReferenceMeasures hRef).eta,
      negativeEtaClearance ≤ ‖(x : ℂ) - w‖ := by
  let M : P0AdmissibleMeasures := p0ReferenceMeasures hRef
  have hset : MeasurableSet {w : ℂ |
      negativeEtaClearance ≤ ‖(x : ℂ) - w‖} := by
    exact (isClosed_le continuous_const
      (continuous_norm.comp (continuous_const.sub continuous_id))).measurableSet
  change ∀ᵐ w ∂(Measure.map Complex.ofReal M.kappa + M.nu),
      negativeEtaClearance ≤ ‖(x : ℂ) - w‖
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff Complex.measurable_ofReal.aemeasurable hset]
    filter_upwards [EnergyLowerBound.kappa_ae_mem M] with t ht
    have hxt : x ≤ t := by linarith [ht.1]
    rw [show ‖(x : ℂ) - (t : ℂ)‖ = |x - t| by
      rw [← Complex.ofReal_sub]
      simp only [Complex.norm_real, Real.norm_eq_abs]]
    rw [abs_of_nonpos (sub_nonpos.mpr hxt)]
    norm_num [negativeEtaClearance]
    linarith [ht.1]
  · filter_upwards [EnergyLowerBound.nu_ae_mem_Gamma M] with w hw
    obtain ⟨u, rfl⟩ := hw
    have htx : (1 / 2 : ℝ) ≤ -x := by linarith
    have h := negativeAxis_distance_lower htx u
    have hd : negativeEtaClearance ≤ (-x : ℝ) - leftClearance := by
      norm_num [negativeEtaClearance, ConfigContourTail.leftClearance]
      linarith
    have hrewrite : -(((-x : ℝ) : ℂ)) = (x : ℂ) := by
      push_cast
      ring
    rw [hrewrite] at h
    change -x - leftClearance ≤ ‖(x : ℂ) - Config.baseEllipse u‖ at h
    rw [← TubeEnergy.gammaPoint_eq_baseEllipse u] at h
    exact hd.trans h

/-- Explicit finite local positive-kernel cap for the reference eta on the
negative half-line. -/
theorem reference_eta_l6PosKernel_bound_on_negative_axis
    (hRef : P0ReferenceFiniteEnergyData) {x : ℝ}
    (hx : x ≤ -(1 / 2 : ℝ)) :
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂(p0ReferenceMeasures hRef).eta) ≤
      ENNReal.ofReal (Real.posLog negativeEtaClearance⁻¹) := by
  have hdist := reference_eta_negative_distance_ae hRef hx
  have hpoint : ∀ᵐ w ∂(p0ReferenceMeasures hRef).eta,
      l6PosKernel (x : ℂ) w ≤
        ENNReal.ofReal (Real.posLog negativeEtaClearance⁻¹) := by
    filter_upwards [hdist] with w hw
    exact l6PosKernel_le_of_dist_lower negativeEtaClearance_pos hw
  calc
    (∫⁻ w, l6PosKernel (x : ℂ) w ∂(p0ReferenceMeasures hRef).eta) ≤
        ∫⁻ _w : ℂ, ENNReal.ofReal (Real.posLog negativeEtaClearance⁻¹) ∂
          (p0ReferenceMeasures hRef).eta :=
      lintegral_mono_ae hpoint
    _ = ENNReal.ofReal (Real.posLog negativeEtaClearance⁻¹) *
          (p0ReferenceMeasures hRef).eta Set.univ := by rw [lintegral_const]
    _ = ENNReal.ofReal (Real.posLog negativeEtaClearance⁻¹) := by
      rw [show (p0ReferenceMeasures hRef).eta Set.univ = 1 by
        exact (p0ReferenceMeasures hRef).companion_mass]
      simp

end
end Li2Lean.P0.U2NegativeEtaL6Cap
