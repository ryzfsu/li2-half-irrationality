/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourReference
import Li2Lean.P0.ConfigSegment

/-!
# The actual reference and the half-contour reduction

All callback fields below are defined by the literal Appendix A measures.
This file discharges `CAReceipt.contour_reduction` for that reference.  It
does not assert the cell inequalities, energy enclosure, or tail estimate.
-/

open MeasureTheory

namespace Li2Lean.P0.ConfigReferenceSymmetry

noncomputable section

open ConfigContourReference

/-- Integration against `eta_0 = kappa_0 + nu_0`, with the actual Appendix A
pinned measure and the exact Fejer contour mixture. -/
def etaReferenceIntegral (f : ℂ → ℝ) : ℝ :=
  (∫ x, f (x : ℂ) ∂ConfigSegment.pinnedReferenceMeasure) +
    contourReferenceIntegral f

/-- The logarithmic potential of the actual combined reference. -/
def etaReferencePotential (z : ℂ) : ℝ :=
  ConfigSegment.pinnedReferenceComplexPotential z +
    contourReferencePotential z

/-- The reflected frequency potential in the actual first variation. -/
def reflectedFrequencyPotential (z : ℂ) : ℝ :=
  ConfigSegment.frequencyReferenceComplexPotential (-z)

/-- The reflected callback is exactly the mixed positive-axis logarithmic
potential in v10 (5.1), including the sign in `z+t`. -/
theorem reflectedFrequencyPotential_eq_mixed (z : ℂ) :
    reflectedFrequencyPotential z =
      ∫ t, Real.log ‖z + (t : ℂ)‖ ∂ConfigSegment.frequencyReferenceMeasure := by
  unfold reflectedFrequencyPotential ConfigSegment.frequencyReferenceComplexPotential
  apply MeasureTheory.integral_congr_ae
  filter_upwards [] with t
  rw [show -z - (t : ℂ) = -(z + (t : ℂ)) by ring, norm_neg]

def qEtaEta : ℝ := etaReferenceIntegral etaReferencePotential

def qMuMu : ℝ := ∫ t, ConfigSegment.frequencyReferencePotential t
  ∂ConfigSegment.frequencyReferenceMeasure

def qEtaMu : ℝ := etaReferenceIntegral reflectedFrequencyPotential

/-- The v10 reference callbacks, now assigned to real integrals of the exact
arrays.  No numerical enclosure or admissibility assertion is stored here. -/
def actualReference : Config.DualReferencePotentials where
  Leta := etaReferencePotential
  Lmu := ConfigSegment.frequencyReferencePotential
  LmuNegative := reflectedFrequencyPotential
  QetaEta := qEtaEta
  QmuMu := qMuMu
  QetaMu := qEtaMu
  qLog := qEtaEta + qMuMu + qEtaMu
  qLog_eq := rfl

/-- The callback used in `Weta` is a mixed potential of the same literal
frequency measure, not a free function attached to the numerical tables. -/
theorem actualReference_LmuNegative (z : ℂ) :
    actualReference.LmuNegative z =
      ∫ t, Real.log ‖z + (t : ℂ)‖ ∂ConfigSegment.frequencyReferenceMeasure :=
  reflectedFrequencyPotential_eq_mixed z

theorem norm_conj_sub_real (z : ℂ) (x : ℝ) :
    ‖(starRingEnd ℂ) z - (x : ℂ)‖ = ‖z - (x : ℂ)‖ := by
  simpa only [map_sub, Complex.conj_ofReal] using
    Complex.norm_conj (z - (x : ℂ))

theorem norm_conj_add_real (z : ℂ) (x : ℝ) :
    ‖(starRingEnd ℂ) z + (x : ℂ)‖ = ‖z + (x : ℂ)‖ := by
  simpa only [map_add, Complex.conj_ofReal] using
    Complex.norm_conj (z + (x : ℂ))

theorem A0_conj (z : ℂ) :
    Config.A0 ((starRingEnd ℂ) z) = Config.A0 z := by
  simp only [Config.A0, norm_conj_sub_real]

theorem phi_conj (z : ℂ) :
    Config.phi ((starRingEnd ℂ) z) = Config.phi z := by
  simp only [Config.phi, Complex.conj_re, norm_conj_add_real]

theorem etaReferencePotential_conj (z : ℂ) :
    etaReferencePotential ((starRingEnd ℂ) z) =
      etaReferencePotential z := by
  simp only [etaReferencePotential,
    ConfigSegment.pinnedReferenceComplexPotential_conj,
    contourReferencePotential_conj]

theorem reflectedFrequencyPotential_conj (z : ℂ) :
    reflectedFrequencyPotential ((starRingEnd ℂ) z) =
      reflectedFrequencyPotential z := by
  unfold reflectedFrequencyPotential
  rw [← map_neg (starRingEnd ℂ),
    ConfigSegment.frequencyReferenceComplexPotential_conj]

/-- Conjugation symmetry of the literal v10 first-variation field. -/
theorem actual_Weta_conj (z : ℂ) :
    Config.Weta actualReference ((starRingEnd ℂ) z) =
      Config.Weta actualReference z := by
  simp only [Config.Weta, actualReference, A0_conj, phi_conj,
    etaReferencePotential_conj, reflectedFrequencyPotential_conj]

/-- Every point of the paper's exact ellipse is a point of its upper half
or the conjugate of such a point. -/
theorem ellipse_half_reduction (u : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧
      (Li2Lean.p0EllipsePoint 1 u =
        Li2Lean.p0EllipsePoint 1 (Real.pi * v) ∨
       Li2Lean.p0EllipsePoint 1 u =
        (starRingEnd ℂ) (Li2Lean.p0EllipsePoint 1 (Real.pi * v))) := by
  let a := Real.arccos (Real.cos u)
  have ha0 : 0 ≤ a := Real.arccos_nonneg _
  have hapi : a ≤ Real.pi := Real.arccos_le_pi _
  have hc : Real.cos a = Real.cos u :=
    Real.cos_arccos (Real.neg_one_le_cos u) (Real.cos_le_one u)
  have hs : Real.sin u ^ 2 = Real.sin a ^ 2 := by
    have ha := Real.sin_sq_add_cos_sq a
    rw [hc] at ha
    nlinarith [Real.sin_sq_add_cos_sq u]
  refine ⟨a / Real.pi, div_nonneg ha0 Real.pi_pos.le, ?_, ?_⟩
  · exact (div_le_one Real.pi_pos).mpr hapi
  · have hp : Real.pi * (a / Real.pi) = a := by
      field_simp
    rw [hp]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with hsin | hsin
    · left
      simp only [Li2Lean.p0EllipsePoint, hc, ← hsin]
    · right
      rw [← ellipse_reflect]
      simp only [Li2Lean.p0EllipsePoint, Real.cos_two_pi_sub,
        Real.sin_two_pi_sub, hc, hsin]

/-- The actual-reference instance of `CAReceipt.contour_reduction`.
Its statement has no supplied symmetry, Fourier-evaluation, or numerical
premise: all measures and all 64 mixture weights are fixed above. -/
theorem actualReference_contour_reduction (u : ℝ) :
    ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧
      Config.Weta actualReference (Li2Lean.p0EllipsePoint 1 u) =
        Config.Weta actualReference
          (Li2Lean.p0EllipsePoint 1 (Real.pi * v)) := by
  obtain ⟨v, hv0, hv1, h | h⟩ := ellipse_half_reduction u
  · exact ⟨v, hv0, hv1, congrArg (Config.Weta actualReference) h⟩
  · refine ⟨v, hv0, hv1, ?_⟩
    rw [h, actual_Weta_conj]

end

end Li2Lean.P0.ConfigReferenceSymmetry
