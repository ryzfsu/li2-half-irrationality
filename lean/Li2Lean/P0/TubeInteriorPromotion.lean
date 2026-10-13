/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorMean
import Li2Lean.P0.TubeInteriorEndpoint
import Li2Lean.P0.TubeInteriorVarianceBridge
import Li2Lean.P0.TubeInteriorPotential

open MeasureTheory ProbabilityTheory Filter Metric
open scoped Topology

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-! ## The concrete logarithmic Jensen bridge

The truncation parameter is retained in the statement.  This is deliberate:
it records the positive distance needed before replacing the finite Jensen
functional by the genuine logarithmic kernel.  No compactness or source
separation assertion is hidden in this bridge.
-/

/-- The actual Cauchy sweep obeys the untruncated logarithmic Jensen bound
whenever one fixed truncation is already below the centre and every point of
the original contour. -/
theorem interiorSweep_logKernel_jensen {z x : ℂ}
    (hz : z ∈ ellipseInterior) {ε : ℝ} (hε : 0 < ε)
    (hcentre : ε ≤ ‖z - x‖)
    (hboundary : ∀ y ∈ Gamma, ε ≤ ‖y - x‖) :
    (∫ y, realLogKernel y x ∂interiorSweep z) ≤ realLogKernel z x := by
  have htr := interiorSweep_truncated_jensen (z := z) (x := x) hz hε
  rw [truncatedLogNorm, max_eq_right hcentre] at htr
  have hsupport : ∀ᵐ y ∂interiorSweep z, y ∈ Gamma := by
    rw [ae_iff]
    exact interiorSweep_boundary_support z
  have hneg :
      (fun y => realLogKernel y x) =ᵐ[interiorSweep z]
        (fun y => -truncatedLogNorm ε (y - x)) := by
    filter_upwards [hsupport] with y hy
    simp only [realLogKernel, truncatedLogNorm]
    rw [max_eq_right (hboundary y hy)]
  calc
    (∫ y, realLogKernel y x ∂interiorSweep z) =
        ∫ y, -truncatedLogNorm ε (y - x) ∂interiorSweep z :=
      integral_congr_ae hneg
    _ = -∫ y, truncatedLogNorm ε (y - x) ∂interiorSweep z := by
      rw [integral_neg]
    _ ≤ -Real.log ‖z - x‖ := neg_le_neg htr
    _ = realLogKernel z x := by simp only [realLogKernel]

/-! ## Paper-facing promotion

This structure is an adapter, rather than a new harmonic-measure
construction.  Every field names the concrete object or theorem that the
paper uses.  The final field keeps the source separation premise explicit;
the finite configuration transfer, exterior sweep, pair-Green, barrier, and
energy estimates remain outside this interior promotion.
-/

structure ActualInteriorSweepPaperAdapter : Prop where
  disk_cover_mem_interior :
    ∀ {z u : ℂ}, z ∈ ellipseInterior → ‖u‖ < 1 → interiorDiskMap z u ∈ ellipseInterior
  disk_cover_center :
    ∀ {z : ℂ}, z ∈ ellipseInterior → interiorDiskMap z 0 = z
  finite_radius_jensen :
    ∀ {z x : ℂ} {R ε : ℝ}, z ∈ ellipseInterior → 0 < R → R < 1 → 0 < ε →
      truncatedLogNorm ε (z - x) ≤
        Real.circleAverage (fun u => truncatedLogNorm ε (interiorDiskMap z u - x)) 0 R
  sweep_measurable : Measurable interiorSweep
  sweep_probability : ∀ z : ℂ, IsProbabilityMeasure (interiorSweep z)
  sweep_mass : ∀ z : ℂ, interiorSweep z Set.univ = 1
  sweep_boundary_support : ∀ z : ℂ, interiorSweep z Gammaᶜ = 0
  boundary_dirac : ∀ {z : ℂ}, z ∈ Gamma → interiorSweep z = Measure.dirac z
  actual_truncated_jensen :
    ∀ {z x : ℂ}, z ∈ ellipseInterior → ∀ {ε : ℝ}, 0 < ε →
      truncatedLogNorm ε (z - x) ≤
        ∫ y, truncatedLogNorm ε (y - x) ∂interiorSweep z
  actual_log_kernel_jensen :
    ∀ {z x : ℂ}, z ∈ ellipseInterior → ∀ {ε : ℝ}, 0 < ε →
      ε ≤ ‖z - x‖ → (∀ y ∈ Gamma, ε ≤ ‖y - x‖) →
      (∫ y, realLogKernel y x ∂interiorSweep z) ≤ realLogKernel z x
  barycenter :
    ∀ {z : ℂ}, z ∈ ellipseInterior → (∫ y, y ∂interiorSweep z) = z
  variance :
    ∀ {z : ℂ}, z ∈ ellipseInterior →
      (∫ y, ‖y - z‖ ^ 2 ∂interiorSweep z) ≤ semiMajor ^ 2 * ellipseLevel z
  interior_positive_source_point_green :
    ∀ {z x : ℂ}, z ∈ ellipseInterior → x ∈ ellipseInterior →
      x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 → z ≠ x →
      ∀ {ε : ℝ}, 0 < ε → ε ≤ ‖z - x‖ → (∀ y ∈ Gamma, ε ≤ ‖y - x‖) →
      (∫ y, realLogKernel y x ∂interiorSweep z) ≤ realLogKernel z x

/-- The concrete disk cover, Cauchy sweep and endpoint laws instantiate the
paper adapter without changing the sweep family. -/
def actualInteriorSweepPaperAdapter : ActualInteriorSweepPaperAdapter := by
  refine
    { disk_cover_mem_interior := ?_
      disk_cover_center := ?_
      finite_radius_jensen := ?_
      sweep_measurable := measurable_interiorSweep
      sweep_probability := fun z => interiorSweep_isProbability z
      sweep_mass := interiorSweep_mass
      sweep_boundary_support := interiorSweep_boundary_support
      boundary_dirac := fun hz => interiorSweep_eq_dirac_of_mem_Gamma hz
      actual_truncated_jensen := ?_
      actual_log_kernel_jensen := ?_
      barycenter := ?_
      variance := ?_
      interior_positive_source_point_green := ?_ }
  · intro z u hz hu
    exact interiorDiskMap_mem_interior hz hu
  · intro z hz
    exact interiorDiskMap_zero hz
  · intro z x R ε hz hR hR1 hε
    exact truncatedLogNorm_interiorDiskMap hz hR hR1 hε
  · intro z x hz ε hε
    exact interiorSweep_truncated_jensen hz hε
  · intro z x hz ε hε hcentre hboundary
    exact interiorSweep_logKernel_jensen hz hε hcentre hboundary
  · intro z hz
    exact interiorSweep_barycenter hz
  · intro z hz
    exact interiorSweep_variance_le hz
  · intro z x hz hx hxre hxim hzx ε hε hcentre hboundary
    exact interiorSweep_logKernel_jensen hz hε hcentre hboundary

end
end Li2Lean.P0.TubeInterior
