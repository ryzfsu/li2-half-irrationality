/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourSelfPotential

/-!
# Literal pinned-field endpoint identity

This file records the semantic endpoint reduction of the *actual* C-A
`Weta` callback on the real axis.  It uses only the fixed Appendix A segment
measures and their endpoint primitives.  The contour self-potential is kept
as an explicit term: replacing it by the finite Fourier expression requires
`ContourSelfPotentialFourierObligation`, which is not asserted here.
-/

open MeasureTheory

namespace Li2Lean.P0.ConfigContourSelfPotential

noncomputable section

open ConfigReferenceSymmetry ConfigSegment ConfigContourReference
open Li2Lean.LogSegment

/-! ## Real-axis endpoint expansion -/

theorem pinnedWeta_ofReal_eq_endpoint_source (x : ℝ) :
    pinnedWeta x =
      (primitive (x - 1 / 4) - primitive (x - 5 / 4) +
        (primitive x - primitive (x - 2)))
      - (x * Real.log 2 +
        (primitive (x + 1 / 2) - primitive x) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))
      - 2 * (pinnedReferencePotential x + contourReferencePotential (x : ℂ))
      - frequencyReferencePotential (-x) := by
  unfold pinnedWeta Config.Weta ConfigReferenceSymmetry.actualReference
  change Config.A0 (x : ℂ) - Config.phi (x : ℂ) -
      2 * (ConfigSegment.pinnedReferenceComplexPotential (x : ℂ) +
        ConfigContourReference.contourReferencePotential (x : ℂ)) -
      ConfigReferenceSymmetry.reflectedFrequencyPotential (x : ℂ) = _
  rw [ConfigSegment.A0_ofReal_eq_endpoints,
    ConfigSegment.phi_ofReal_eq_endpoints,
    ConfigSegment.pinnedReferenceComplexPotential_ofReal,
    ConfigReferenceSymmetry.reflectedFrequencyPotential_eq_mixed]
  -- The mixed integral at a real point is the real frequency potential at `-x`.
  have hfreq :
      (∫ t, Real.log ‖(x : ℂ) + (t : ℂ)‖
          ∂ConfigSegment.frequencyReferenceMeasure) =
        frequencyReferencePotential (-x) := by
    unfold frequencyReferencePotential
    apply integral_congr_ae
    filter_upwards [] with t
    simp only [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    have ht : -x - t = -(x + t) := by ring
    rw [ht, abs_neg]
  rw [hfreq]

theorem pinnedWeta_ofReal_eq_explicit_endpoint_source (x : ℝ) :
    pinnedWeta x =
      (primitive (x - 1 / 4) - primitive (x - 5 / 4) +
        (primitive x - primitive (x - 2)))
      - (x * Real.log 2 +
        (primitive (x + 1 / 2) - primitive x) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))
      - 2 * ((∑ j ∈ Finset.range 32,
          referenceDensity ConfigData.pinnedMassUnits j *
            (primitive (x - referenceCellLeft (1 / 4) j) -
              primitive (x - referenceCellRight (1 / 4) j))) +
        contourReferencePotential (x : ℂ))
      - frequencyReferencePotential (-x) := by
  rw [pinnedWeta_ofReal_eq_endpoint_source,
    ConfigSegment.pinnedReferencePotential_eq_endpoints]

end

end Li2Lean.P0.ConfigContourSelfPotential
