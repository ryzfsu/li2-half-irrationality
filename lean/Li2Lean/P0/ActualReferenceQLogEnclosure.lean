/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.FourierConst
import Li2Lean.P0.ConfigLogEnclosures

/-!
# Exact energy enclosures for the literal C-A reference

The arithmetic certificates below are evaluated by `decide +kernel` over
rational intervals. Their soundness is transported to the fixed degree-48
Fejer/Joukowski coefficients by the existing Fourier coefficient theorem.
No floating point value or numerical model answer is a proof input.
-/

namespace Li2Lean.P0.ActualReferenceQLogEnclosure

open Li2Lean.P0.CA.Contour
open Li2Lean.P0.CA.Contour.QI
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourKernel

set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

/-- Rational conversion from the squared potential coefficient to the
corresponding contour self-energy coefficient. -/
def energyFactor (n : ℕ) : ℚ :=
  (n + 1 : ℚ) / (1 + (1333 / 24233 : ℚ) ^ (n + 1))

/-- One self-energy summand, rounded outwards after exact rational arithmetic. -/
def selfEnergyTermI (n : ℕ) : QI :=
  rnd (smul (energyFactor n)
    (mul (bLit.getD n ⟨0, 0⟩) (bLit.getD n ⟨0, 0⟩)))

/-- The already proved rational enclosure of the literal Joukowski scale. -/
def logScaleI : QI :=
  ⟨191983067064 / 1000000000000, 191983067065 / 1000000000000⟩

theorem logScaleI_mem : logScaleI.mem (Real.log contourScale) := by
  simpa only [logScaleI, QI.mem, contourScale, Rat.cast_div, Rat.cast_ofNat] using
    ConfigLogEnclosures.log_referenceScale_enclosure_v10

/-- A finite, purely rational enclosure of the Fourier self-energy. -/
def selfEnergyI : QI :=
  sub (smul ((267885951940 / 1000000000000 : ℚ) ^ 2) logScaleI)
    (sumIdx 48 selfEnergyTermI)

theorem energyFactor_eq (n : ℕ) :
    (energyFactor n : ℝ) * bR n ^ 2 =
      (1 + contourRatio ^ (n + 1)) *
        contourFourierMoment (n + 1) ^ 2 / (n + 1 : ℝ) := by
  have hnp : (0 : ℝ) < n + 1 := by positivity
  have hq : 0 ≤ contourRatio ^ (n + 1) :=
    pow_nonneg contourRatio_nonneg _
  have hqp : (0 : ℝ) < 1 + contourRatio ^ (n + 1) := by linarith
  unfold energyFactor bR
  push_cast
  change ((n + 1 : ℝ) / (1 + contourRatio ^ (n + 1))) *
    ((1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) /
      (n + 1 : ℝ)) ^ 2 = _
  field_simp [hnp.ne', hqp.ne']

theorem selfEnergyTermI_mem {n : ℕ} (hn : n < 48) :
    (selfEnergyTermI n).mem
      ((1 + contourRatio ^ (n + 1)) *
        contourFourierMoment (n + 1) ^ 2 / (n + 1 : ℝ)) := by
  rw [← energyFactor_eq]
  unfold selfEnergyTermI
  have hb := bLit_mem hn
  simpa only [pow_two] using mem_rnd (mem_smul (energyFactor n) (mem_mul hb hb))

/-- The finite rational self-energy enclosure encloses the actual Fourier
expression with the exact Appendix A mass and all 48 nonzero frequencies. -/
theorem selfEnergyI_mem : selfEnergyI.mem contourSelfEnergyFourier := by
  have hsum := mem_sumIdx (fun n hn => selfEnergyTermI_mem hn)
  have hmass := mem_smul ((267885951940 / 1000000000000 : ℚ) ^ 2) logScaleI_mem
  unfold selfEnergyI contourSelfEnergyFourier contourMass
  push_cast at hmass
  exact mem_sub hmass hsum

/-- A compact exact certificate for the contour contribution. Its precision
is stronger than the final `-11/25` qLog margin requires. -/
theorem selfEnergyI_certificate :
    QI.sub_le selfEnergyI
      ⟨-660895 / 10000000, -660894 / 10000000⟩ = true := by
  decide +kernel

/-- Unconditional rational enclosure of the literal contour Fourier energy. -/
theorem contourSelfEnergyFourier_enclosure :
    (-660895 / 10000000 : ℝ) ≤ contourSelfEnergyFourier ∧
      contourSelfEnergyFourier ≤ (-660894 / 10000000 : ℝ) := by
  have h := QI.mem_of_sub_le selfEnergyI_certificate selfEnergyI_mem
  norm_num only [QI.mem, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] at h ⊢
  exact h


/-- The rational margin used after the six literal energy components have
been identified and bounded. Each component is retained with its true sign,
and the pinned-contour interaction is counted twice. -/
theorem qLog_margin_of_component_bounds
    {pinnedSelf frequencySelf pinnedFrequency pinnedContour contourSelf frequencyContour : ℝ}
    (hpp : (-90874 / 100000 : ℝ) ≤ pinnedSelf)
    (hff : (-54305 / 100000 : ℝ) ≤ frequencySelf)
    (hpf : (57429 / 100000 : ℝ) ≤ pinnedFrequency)
    (hpc : (7740 / 100000 : ℝ) ≤ pinnedContour)
    (hcc : (-6610 / 100000 : ℝ) ≤ contourSelf)
    (hfc : (35040 / 100000 : ℝ) ≤ frequencyContour) :
    (-11 / 25 : ℝ) < pinnedSelf + frequencySelf + pinnedFrequency +
      2 * pinnedContour + contourSelf + frequencyContour := by
  linarith

end Li2Lean.P0.ActualReferenceQLogEnclosure

#print axioms Li2Lean.P0.ActualReferenceQLogEnclosure.selfEnergyI_mem
#print axioms Li2Lean.P0.ActualReferenceQLogEnclosure.selfEnergyI_certificate
#print axioms Li2Lean.P0.ActualReferenceQLogEnclosure.contourSelfEnergyFourier_enclosure
