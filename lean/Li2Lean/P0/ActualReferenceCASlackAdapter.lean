/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Receipt
import Li2Lean.P0.CA.Receipt.Bridge
import Li2Lean.P0.ActualReferenceDual
import Li2Lean.P0.ActualReferenceWetaRegularity

/-!
# Actual positive-part penalties from the C-A slack receipt

This adapter uses `CA.Receipt.CAReceiptSlackActual` and the literal reference
fields. Its penalty record contains the two actual positive-part integrals
and their integrability witnesses. The alpha bound is proved independently
from `CA.Receipt.ActualReferenceLinearization`; it is not a record field.

The spent slack certificate proves the floor `199/100` and the paper target
`397/200`. The legacy floor `Config.alphaFloor = 1.992909` is not claimed:
it is above the spent certificate value `1.990536...`.
-/

open MeasureTheory Set Filter

namespace Li2Lean.P0

open ConfigReferenceSymmetry CA.Receipt
open ConfigSegment ConfigContourReference ConfigContourTail
open Li2Lean.LogSegment

noncomputable section

private theorem continuous_actualReference_psi : Continuous Config.psi := by
  unfold Config.psi
  exact (((Real.continuous_mul_log.sub
    (Real.continuous_mul_log.comp (continuous_id.sub continuous_const))).sub
      continuous_const).sub (continuous_id.mul continuous_const))

private theorem continuous_minus_reference_sum (start : ℝ) (count : ℕ)
    (units : List ℕ) :
    Continuous (fun t : ℝ =>
      ∑ j ∈ Finset.range count,
        referenceDensity units j *
          (primitive (t - referenceCellLeft start j) -
            primitive (t - referenceCellRight start j))) := by
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    ((continuous_primitive.comp (continuous_id.sub continuous_const)).sub
      (continuous_primitive.comp (continuous_id.sub continuous_const)))

private theorem continuous_plus_reference_sum (start : ℝ) (count : ℕ)
    (units : List ℕ) :
    Continuous (fun t : ℝ =>
      ∑ j ∈ Finset.range count,
        referenceDensity units j *
          (primitive (t + referenceCellRight start j) -
            primitive (t + referenceCellLeft start j))) := by
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
      (continuous_primitive.comp (continuous_id.add continuous_const)))

/-- Continuity of the literal frequency field on its whole admissible ray,
including the reference density endpoints and `t = 1/2`. -/
theorem actualReference_Wmu_continuousOn_halfline :
    ContinuousOn (Config.Wmu actualReference) (Ici (1 / 2 : ℝ)) := by
  have hbase : Continuous
      (fun t : ℝ =>
        primitive (t + 5 / 4) - primitive (t + 1 / 4) +
          (primitive (t + 2) - primitive t)) :=
    ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
      (continuous_primitive.comp (continuous_id.add continuous_const))).add
      ((continuous_primitive.comp (continuous_id.add continuous_const)).sub
        (continuous_primitive.comp continuous_id))
  have hfreq := continuous_minus_reference_sum (1 / 2) 160 ConfigData.frequencyMassUnits
  have hpin := continuous_plus_reference_sum (1 / 4) 32 ConfigData.pinnedMassUnits
  have hcontour : ContinuousOn
      (fun t : ℝ => contourReferencePotential (-(t : ℂ))) (Ici (1 / 2 : ℝ)) := by
    intro t ht
    have hclear : leftClearance < t := by
      unfold leftClearance
      linarith [mem_Ici.mp ht]
    exact (hasDerivAt_contourReferencePotential_neg hclear).continuousAt.continuousWithinAt
  have hf := ((((hbase.sub continuous_actualReference_psi).sub
    (hfreq.const_mul 2)).sub hpin).continuousOn).sub hcontour
  exact hf.congr (fun t _ => ConfigSlackSemanticIdentity.actualWmu_eq_endpoints t)

/-- The positive part of a continuous field is integrable on a compact interval. -/
theorem actualReference_positivePart_integrable_Icc
    {f : ℝ → ℝ} {a b h : ℝ}
    (hcont : ContinuousOn f (Icc a b)) :
    IntegrableOn (fun t => max (h - f t) 0) (Icc a b) := by
  have hc : ContinuousOn (fun t => max (h - f t) 0) (Icc a b) := by
    simpa only [Pi.sub_apply] using
      (continuousOn_const.sub hcont).sup (continuousOn_const :
        ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Icc a b))
  exact hc.integrableOn_Icc

/-- A compact continuous field above threshold on the tail has an integrable
positive-part penalty on the complete halfline. -/
theorem actualReference_positivePart_integrable_Ici_of_tail_floor
    {f : ℝ → ℝ} {a b h : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Icc a b))
    (hfloor : ∀ s, b ≤ s → h ≤ f s) :
    IntegrableOn (fun t => max (h - f t) 0) (Ici a) := by
  have hcompact := actualReference_positivePart_integrable_Icc (h := h) hcont
  have htail : IntegrableOn (fun t => max (h - f t) 0) (Ici b) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
      (g := fun t => max (h - f t) 0) (s := Ici b)
      (μ := volume) integrableOn_zero ?_ measurableSet_Ici
    intro t ht
    have hle : h - f t ≤ 0 := by linarith [hfloor t (mem_Ici.mp ht)]
    exact (max_eq_right hle).symm
  simpa only [Icc_union_Ici_eq_Ici hab] using hcompact.union htail

/-- The completed contour floor, with no legacy receipt or duality field. -/
theorem caReceipt_eta_lower (R : CAReceiptSlackActual) :
    ∀ z ∈ Gamma, ((hEtaQ : ℚ) : ℝ) ≤ Config.Weta actualReference z :=
  R.contour_lower_all

/-- Integrability of the actual frequency positive part from the proved
literal continuity and the receipt's proved tail threshold. -/
theorem caReceipt_frequency_positivePart_integrable (R : CAReceiptSlackActual) :
    IntegrableOn
      (fun t => max (((hMuQ : ℚ) : ℝ) - Config.Wmu actualReference t) 0)
      (Ici (1 / 2 : ℝ)) := by
  apply actualReference_positivePart_integrable_Ici_of_tail_floor
    (a := (1 / 2 : ℝ)) (b := (81 / 10 : ℝ)) (by norm_num)
    (actualReference_Wmu_continuousOn_halfline.mono (fun _ ht => ht.1))
  intro t ht
  exact R.frequency_tail_threshold ht

/-- The two literal positive-part penalties from a valid slack receipt.
Both literal field regularity witnesses are proved, including their density
endpoints; no continuity or differentiability premise remains. -/
def actualReferencePenaltyCertificate_of_caReceipt
    (R : CAReceiptSlackActual) : ActualReferencePenaltyCertificate :=
  actualReferencePenaltyCertificate_of_max
    (hEta := ((hEtaQ : ℚ) : ℝ)) (hMu := ((hMuQ : ℚ) : ℝ))
    (caReceipt_eta_lower R)
    (actualReference_positivePart_integrable_Icc actualReference_Weta_continuousOn_pinned)
    (caReceipt_frequency_positivePart_integrable R)

/-- The actual pinned penalty is at most the spent slack row penalty. -/
theorem caReceipt_pinned_actualPenalty_le (R : CAReceiptSlackActual)
    :
    (actualReferencePenaltyCertificate_of_caReceipt R).P ≤
      (pinnedPenaltyQ : ℝ) := by
  change (∫ x in Icc (1 / 4 : ℝ) (5 / 4),
    max (((hEtaQ : ℚ) : ℝ) - Config.Weta actualReference (x : ℂ)) 0) ≤ _
  apply le_trans (b := pinnedPenalty) ?_ pinnedPenalty_le
  apply integral_mono_ae
    (actualReference_positivePart_integrable_Icc actualReference_Weta_continuousOn_pinned)
    (stepMajorant_integrableOn _ _ _ _)
  filter_upwards [ae_restrict_mem measurableSet_Icc] with x hx
  exact max_le (R.pinned_dominated x hx) (stepMajorant_nonneg _ _ _ x)

/-- The actual frequency penalty is at most the spent slack row penalty. -/
theorem caReceipt_frequency_actualPenalty_le (R : CAReceiptSlackActual)
    :
    (actualReferencePenaltyCertificate_of_caReceipt R).T ≤
      (frequencyPenaltyQ : ℝ) := by
  change (∫ t in Ici (1 / 2 : ℝ),
    max (((hMuQ : ℚ) : ℝ) - Config.Wmu actualReference t) 0) ≤ _
  apply le_trans (b := frequencyPenalty) ?_ frequencyPenalty_le
  apply integral_mono_ae (caReceipt_frequency_positivePart_integrable R)
    (stepMajorant_integrableOn _ _ _ _)
  filter_upwards [ae_restrict_mem measurableSet_Ici] with t ht
  exact max_le (R.frequency_dominated t ht) (stepMajorant_nonneg _ _ _ t)

/-- The actual positive-part certificate gives the spent rational lower bound. -/
theorem actualReference_alphaCertificate_lt_of_caReceipt (R : CAReceiptSlackActual) :
    (((CAReceiptSlackActual.certificateValue : ℚ) : ℝ) : WithTop ℝ) < alphaGamma := by
  let C := actualReferencePenaltyCertificate_of_caReceipt R
  have hdual := actualReference_alphaGamma_lower_qLog C
  change ((Config.cAConstant + actualReference.qLog + ((hEtaQ : ℚ) : ℝ) +
    ((hMuQ : ℚ) : ℝ) - C.P - C.T : ℝ) : WithTop ℝ) ≤ alphaGamma at hdual
  have hm := CAReceiptSlackActual.margin R.analytic.qLog_lower
    (caReceipt_pinned_actualPenalty_le R) (caReceipt_frequency_actualPenalty_le R)
  have hc : (((CAReceiptSlackActual.certificateValue : ℚ) : ℝ) : WithTop ℝ) <
      ((Config.cAConstant + actualReference.qLog + ((hEtaQ : ℚ) : ℝ) +
        ((hMuQ : ℚ) : ℝ) - C.P - C.T : ℝ) : WithTop ℝ) := by
    exact_mod_cast hm
  exact lt_of_lt_of_le hc hdual

/-- Every real target at most the spent certificate is below the actual
variational infimum. -/
theorem actualReference_alpha_lt_of_caReceipt (R : CAReceiptSlackActual)
    {alpha : ℝ} (halpha : alpha ≤ ((CAReceiptSlackActual.certificateValue : ℚ) : ℝ)) :
    (alpha : WithTop ℝ) < alphaGamma :=
  lt_of_le_of_lt (WithTop.coe_le_coe.mpr halpha)
    (actualReference_alphaCertificate_lt_of_caReceipt R)

/-- Replacement floor: `199/100`, explicitly narrowed from the legacy
`Config.alphaFloor` to the floor supported by the spent slack certificate. -/
theorem actualReference_alphaFloor_lt_of_caReceipt (R : CAReceiptSlackActual) :
    ((199 / 100 : ℝ) : WithTop ℝ) < alphaGamma := by
  apply actualReference_alpha_lt_of_caReceipt R
  norm_num [CAReceiptSlackActual.certificateValue]

/-- The paper-preserving target `397/200` is below the actual infimum. -/
theorem actualReference_alpha397_lt_of_caReceipt (R : CAReceiptSlackActual) :
    ((397 / 200 : ℝ) : WithTop ℝ) < alphaGamma := by
  apply actualReference_alpha_lt_of_caReceipt R
  norm_num [CAReceiptSlackActual.certificateValue]

/-- Non-row analytic inputs from the proved literal U2 finite-energy and
cross-energy producer, leaving only the independent qLog enclosure. -/
theorem caAnalyticInputs_of_qLog (hq : (-11 / 25 : ℝ) < actualReference.qLog) :
    CAAnalyticInputs := by
  refine ⟨CA.Receipt.actualReferenceLinearization_of_L6
    p0ReferenceFiniteEnergyData_literal ?_, ?_⟩
  · intro M hM
    exact p0L6CrossEnergy_actual_reference M hM
  · simpa only [qLogSlackLower, Rat.cast_neg, Rat.cast_div, Rat.cast_ofNat] using hq

/-- The completed actual slack receipt from the three proved regional inputs
and the independent qLog enclosure. The central row build may supply
`CA.Wire.caRowInputs` without replaying the rows in this adapter's closure. -/
theorem caReceiptSlackActual_of_caRows (rows : CARowInputs)
    (hq : (-11 / 25 : ℝ) < actualReference.qLog) : CAReceiptSlackActual :=
  ⟨rows, caAnalyticInputs_of_qLog hq⟩

/-- Alpha bound with exactly the row and qLog obligations exposed. -/
theorem actualReference_alpha397_lt_of_caRows (rows : CARowInputs)
    (hq : (-11 / 25 : ℝ) < actualReference.qLog) :
    ((397 / 200 : ℝ) : WithTop ℝ) < alphaGamma :=
  actualReference_alpha397_lt_of_caReceipt (caReceiptSlackActual_of_caRows rows hq)

end

end Li2Lean.P0
