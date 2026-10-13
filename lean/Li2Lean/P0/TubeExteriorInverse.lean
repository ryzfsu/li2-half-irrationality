/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExterior
import Li2Lean.P0.TubeInterior

/-! # A measurable exterior inverse for the literal v10 ellipse -/

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

open TubeInterior

/-- The second quadratic preimage is `d/(c*w)`. -/
def joukowskiOtherPreimage (w : ℂ) : ℂ := ellipseD / (ellipseC * w)

/-- Both nonzero quadratic roots have exactly the same Joukowski image. -/
theorem joukowski_otherPreimage {w : ℂ} (hw : w ≠ 0) :
    joukowski (joukowskiOtherPreimage w) = joukowski w := by
  have hc : ellipseC ≠ 0 := by norm_num [ellipseC, semiMajor, semiMinor]
  have hd : ellipseD ≠ 0 := by norm_num [ellipseD, semiMajor, semiMinor]
  unfold joukowskiOtherPreimage joukowski
  field_simp
  ring

/-- The product of the preimage moduli is the exact annulus ratio. -/
theorem norm_joukowskiOtherPreimage (w : ℂ) :
    ‖joukowskiOtherPreimage w‖ = annulusRatio / ‖w‖ := by
  rw [joukowskiOtherPreimage, norm_div, norm_mul, ellipseC_norm, ellipseD_norm]
  norm_num [annulusRatio, semiMajor, semiMinor]
  ring

/-- Measurable explicit exterior root choice, including every boundary point. -/
def ellipseExteriorInverse (z : ℂ) : ℂ :=
  if 1 ≤ ‖interiorPreimage z‖ then interiorPreimage z
  else joukowskiOtherPreimage (interiorPreimage z)

/-- Borel measurability of the literal root choice used for exterior sweeping. -/
theorem measurable_ellipseExteriorInverse : Measurable ellipseExteriorInverse := by
  unfold ellipseExteriorInverse
  apply Measurable.ite
    (measurableSet_le measurable_const measurable_interiorPreimage.norm)
    measurable_interiorPreimage
  exact measurable_const.div (measurable_const.mul measurable_interiorPreimage)

/-- The explicit selected root is globally a right inverse of the Joukowski map. -/
theorem joukowski_ellipseExteriorInverse (z : ℂ) :
    joukowski (ellipseExteriorInverse z) = z := by
  unfold ellipseExteriorInverse
  split_ifs
  · exact joukowski_interiorPreimage z
  · rw [joukowski_otherPreimage (interiorPreimage_ne_zero z), joukowski_interiorPreimage]

/-- Every exterior or boundary point has a selected root outside the open disk. -/
theorem ellipseExteriorInverse_norm_ge_one {z : ℂ} (hz : ellipseLevel z ≤ 0) :
    1 ≤ ‖ellipseExteriorInverse z‖ := by
  unfold ellipseExteriorInverse
  split_ifs with h
  · exact h
  · have hr : ‖interiorPreimage z‖ ≤ annulusRatio := by
      by_contra hbad
      have hin : joukowski (interiorPreimage z) ∈ ellipseInterior :=
        (joukowski_mem_interior_iff _ (interiorPreimage_ne_zero z)).mpr
          ⟨lt_of_not_ge hbad, lt_of_not_ge h⟩
      rw [joukowski_interiorPreimage] at hin
      exact (not_lt_of_ge hz) hin
    rw [norm_joukowskiOtherPreimage]
    exact (one_le_div (norm_pos_iff.mpr (interiorPreimage_ne_zero z))).2 hr

/-- The inverse law requested by `TubeTransferObligations`, now without an inverse premise. -/
theorem ellipseExteriorInverse_spec (z : ℂ) (hz : ellipseLevel z ≤ 0) :
    1 ≤ ‖ellipseExteriorInverse z‖ ∧ joukowski (ellipseExteriorInverse z) = z :=
  ⟨ellipseExteriorInverse_norm_ge_one hz, joukowski_ellipseExteriorInverse z⟩

/-- Exterior injectivity makes the chosen measurable root the actual inverse. -/
theorem ellipseExteriorInverse_joukowski {w : ℂ} (hw : 1 ≤ ‖w‖) :
    ellipseExteriorInverse (joukowski w) = w := by
  have hw0 : w ≠ 0 := by intro h; norm_num [h] at hw
  have hz : ellipseLevel (joukowski w) ≤ 0 := by
    by_contra h
    have hin : joukowski w ∈ ellipseInterior := lt_of_not_ge h
    have hlt := ((joukowski_mem_interior_iff w hw0).mp hin).2
    exact (not_lt_of_ge hw) hlt
  exact joukowski_injective_exterior (ellipseExteriorInverse_norm_ge_one hz) hw
    (joukowski_ellipseExteriorInverse _)

/-- Exact exterior-distance control in the literal v10 tube. -/
theorem ellipseExteriorInverse_distance_lower (z : ℂ) (hz : ellipseLevel z ≤ 0) :
    semiMinor * (‖ellipseExteriorInverse z‖ - 1) ≤ Metric.infDist z Gamma :=
  exterior_distance_lower_bound_of_inverse ellipseExteriorInverse ellipseExteriorInverse_spec z hz

/-- Eq. `tube-e` with a constructed measurable inverse and the original point quantifier. -/
theorem ellipseExteriorCorrection_bound {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ}
    (hz : z ∈ tube δ) :
    0 ≤ exteriorCorrection ellipseExteriorInverse z ∧
      exteriorCorrection ellipseExteriorInverse z ≤ δ / semiMinor :=
  exteriorCorrection_bound_of_inverse ellipseExteriorInverse ellipseExteriorInverse_spec hδ hz

end
end Li2Lean.P0
