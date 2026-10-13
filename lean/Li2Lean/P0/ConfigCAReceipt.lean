/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigReferenceSymmetry
import Li2Lean.P0.Contour
import Li2Lean.P0.Config
import Li2Lean.P0.ConfigThreshold

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

open Li2Lean.P0.ConfigReferenceSymmetry

/-! The C-A directed-cell receipt is locked to the Appendix A reference
measures and to the paper's variational value `alpha_Gamma`. -/
structure CAReceipt where
  contourCells : List Li2Lean.F_L8.ReceiptCell
  pinnedCells : List Li2Lean.F_L8.ReceiptCell
  frequencyCells : List Li2Lean.F_L8.ReceiptCell
  contour_data_exact : contourCells = ConfigData.contourCells
  pinned_data_exact : pinnedCells = ConfigData.pinnedCells
  frequency_data_exact : frequencyCells = ConfigData.frequencyCells
  contour_reduction : ∀ u : ℝ, ∃ v : ℝ, 0 ≤ v ∧ v ≤ 1 ∧
    Weta actualReference (Li2Lean.p0EllipsePoint 1 u) =
      Weta actualReference (Li2Lean.p0EllipsePoint 1 (Real.pi * v))
  contour_cell_bounds : ∀ c ∈ contourCells, ∀ hwidth : c.lo ≤ c.hi,
    c.modelRemainderValid
      (fun u => Weta actualReference (Li2Lean.p0EllipsePoint 1 (Real.pi * u)))
      hwidth
  pinned_cell_bounds : ∀ c ∈ pinnedCells, ∀ hwidth : c.lo ≤ c.hi,
    c.modelRemainderValid
      (fun x => Weta actualReference (Complex.ofReal x)) hwidth
  frequency_cell_bounds : ∀ c ∈ frequencyCells, ∀ hwidth : c.lo ≤ c.hi,
    c.modelRemainderValid (Wmu actualReference) hwidth
  pPenalty : ℝ
  tPenalty : ℝ
  pPenalty_aggregation :
    pPenalty = ∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ),
      max (hEta - Weta actualReference (Complex.ofReal x)) 0
  tPenalty_aggregation :
    tPenalty = ∫ t in Set.Ici (1 / 2 : ℝ),
      max (hMu - Wmu actualReference t) 0
  pPenalty_bound : pPenalty ≤ pPenaltyUpper
  tPenalty_bound : tPenalty ≤ tPenaltyUpper
  qLog_bound : qLogLower < actualReference.qLog
  logTwo_enclosure :
    (693 / 1000 : ℝ) < Real.log 2 ∧ Real.log 2 < 6931473 / 10000000
  tail_value : hMu < Wmu actualReference (81 / 10)
  tail_derivative : ∀ t : ℝ, (81 / 10 : ℝ) ≤ t →
    (28975217729 / 991618303000 : ℝ) ≤ deriv (Wmu actualReference) t
  duality_lower :
    ((cAConstant + actualReference.qLog + hEta + hMu -
      pPenalty - tPenalty : ℝ) : WithTop ℝ) ≤ Li2Lean.P0.alphaGamma

namespace CAReceipt

theorem contour_lower (R : CAReceipt) {u : ℝ}
    (hlo : (0 : ℝ) ≤ u) (hhi : u ≤ 1) :
    hEta ≤ Weta actualReference (Li2Lean.p0EllipsePoint 1 (Real.pi * u)) := by
  have hcover : Li2Lean.F_L8.ExactChain R.contourCells 0 1 := by
    rw [R.contour_data_exact]
    exact ConfigData.contourCells_exactChain
  obtain ⟨c, hmem, hbound⟩ :=
    Li2Lean.F_L8.exactChain_sound hcover
      (fun c hmem hwidth => R.contour_cell_bounds c hmem hwidth)
      (x := u) (by simpa using hlo) (by simpa using hhi)
  have hmem' : c ∈ ConfigData.contourCells := by
    rw [← R.contour_data_exact]
    exact hmem
  have hq := Li2Lean.P0.ConfigThreshold.contourCells_lower_floor hmem'
  have hqR : (-669 / 200 : ℝ) ≤ (c.lower : ℝ) := by exact_mod_cast hq
  have hthreshold : hEta ≤ (c.lower : ℝ) := by
    calc
      hEta = (-669 / 200 : ℝ) := by norm_num [hEta]
      _ ≤ (c.lower : ℝ) := hqR
  exact le_trans hthreshold hbound

theorem contour_lower_all (R : CAReceipt) (u : ℝ) :
    hEta ≤ Weta actualReference (Li2Lean.p0EllipsePoint 1 u) := by
  obtain ⟨v, hv0, hv1, hsymm⟩ := R.contour_reduction u
  rw [hsymm]
  exact R.contour_lower hv0 hv1

theorem pinned_lower (R : CAReceipt) {x : ℝ}
    (hlo : (1 / 4 : ℝ) ≤ x) (hhi : x ≤ 5 / 4) :
    ∃ c, c ∈ R.pinnedCells ∧
      (c.lower : ℝ) ≤ Weta actualReference (Complex.ofReal x) := by
  have hcover :
      Li2Lean.F_L8.ExactChain R.pinnedCells (1 / 4) (5 / 4) := by
    rw [R.pinned_data_exact]
    exact ConfigData.pinnedCells_exactChain
  exact Li2Lean.F_L8.exactChain_sound hcover
    (fun c hmem hwidth => R.pinned_cell_bounds c hmem hwidth)
    (x := x) (by simpa using hlo) (by simpa using hhi)

theorem frequency_lower (R : CAReceipt) {t : ℝ}
    (hlo : (1 / 2 : ℝ) ≤ t) (hhi : t ≤ 81 / 10) :
    ∃ c, c ∈ R.frequencyCells ∧
      (c.lower : ℝ) ≤ Wmu actualReference t := by
  have hcover :
      Li2Lean.F_L8.ExactChain R.frequencyCells (1 / 2) (81 / 10) := by
    rw [R.frequency_data_exact]
    exact ConfigData.frequencyCells_exactChain
  exact Li2Lean.F_L8.exactChain_sound hcover
    (fun c hmem hwidth => R.frequency_cell_bounds c hmem hwidth)
    (x := t) (by simpa using hlo) (by simpa using hhi)

/-- Parameterized C-A conclusion: every target `alpha ≤ alphaFloor` is
strictly below the actual variational value `alpha_Gamma`. -/
theorem alpha_bound_of_le (R : CAReceipt) {alpha : ℝ} (halpha : alpha ≤ alphaFloor) :
    (alpha : WithTop ℝ) < Li2Lean.P0.alphaGamma := by
  have hlog := R.logTwo_enclosure.2
  have hq := R.qLog_bound
  have hp := R.pPenalty_bound
  have ht := R.tPenalty_bound
  have hrational : alpha < cAAlphaFloorExpression := cA_rational_margin_of_le halpha
  have hmodel : cAAlphaFloorExpression <
      cAConstant + actualReference.qLog + hEta + hMu - R.pPenalty - R.tPenalty := by
    unfold cAAlphaFloorExpression cAConstant
    nlinarith
  have hreal : alpha <
      cAConstant + actualReference.qLog + hEta + hMu - R.pPenalty - R.tPenalty :=
    lt_trans hrational hmodel
  have hcast : (alpha : WithTop ℝ) <
      ((cAConstant + actualReference.qLog + hEta + hMu -
        R.pPenalty - R.tPenalty : ℝ) : WithTop ℝ) := by
    exact_mod_cast hreal
  exact lt_of_lt_of_le hcast R.duality_lower

/-- The paper instance `alpha = alphaFloor = 1992909/10^6`. -/
theorem alpha_bound (R : CAReceipt) :
    (alphaFloor : WithTop ℝ) < Li2Lean.P0.alphaGamma :=
  R.alpha_bound_of_le le_rfl

end CAReceipt

end

end Li2Lean.P0.Config

#print axioms Li2Lean.P0.Config.CAReceipt.contour_lower
#print axioms Li2Lean.P0.Config.CAReceipt.pinned_lower
#print axioms Li2Lean.P0.Config.CAReceipt.frequency_lower
#print axioms Li2Lean.P0.Config.CAReceipt.alpha_bound
#print axioms Li2Lean.P0.Config.CAReceipt.alpha_bound_of_le

namespace Li2Lean.P0.Config.CAReceipt

/-- The tail derivative receipt gives the full tail floor once continuity and
 differentiability of the literal W_mu field are supplied. These regularity
 hypotheses are kept explicit because a derivative lower bound alone does not
 imply monotonicity. -/
theorem frequency_lower_tail_of_deriv
    (R : CAReceipt)
    (hcont : ContinuousOn
      (Config.Wmu ConfigReferenceSymmetry.actualReference)
      (Set.Ici (81 / 10 : ℝ)))
    (hdiff : DifferentiableOn ℝ
      (Config.Wmu ConfigReferenceSymmetry.actualReference)
      (Set.Ioi (81 / 10 : ℝ)))
    {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    Config.hMu ≤ Config.Wmu ConfigReferenceSymmetry.actualReference t := by
  have hmono : MonotoneOn
      (Config.Wmu ConfigReferenceSymmetry.actualReference)
      (Set.Ici (81 / 10 : ℝ)) :=
    monotoneOn_of_deriv_nonneg (convex_Ici (81 / 10 : ℝ)) hcont
      (by simpa [interior_Ici] using hdiff) (by
      intro x hx
      have hx' : (81 / 10 : ℝ) < x := by simpa using hx
      have hd := R.tail_derivative x (le_of_lt hx')
      have hc : (0 : ℝ) ≤ 28975217729 / 991618303000 := by norm_num
      exact hc.trans hd)
  have hbase : Config.Wmu ConfigReferenceSymmetry.actualReference (81 / 10 : ℝ) ≤
      Config.Wmu ConfigReferenceSymmetry.actualReference t :=
    hmono (by simp) (by exact ht) ht
  exact (le_of_lt R.tail_value).trans hbase

end Li2Lean.P0.Config.CAReceipt

namespace Li2Lean.P0.Config.CAReceipt

/-- The positive part of a continuous frequency field is integrable on the
finite C-A interval. -/
theorem positivePart_integrable_Icc
    {f : ℝ → ℝ} {a b h : ℝ}
    (hcont : ContinuousOn f (Set.Icc a b)) :
    IntegrableOn (fun t => max (h - f t) 0) (Set.Icc a b) := by
  have hc : ContinuousOn (fun t => max (h - f t) 0) (Set.Icc a b) := by
    have hsub : ContinuousOn (fun t => h - f t) (Set.Icc a b) :=
      continuousOn_const.sub hcont
    have hzero : ContinuousOn (fun _ : ℝ => (0 : ℝ)) (Set.Icc a b) :=
      continuousOn_const
    have hs := hsub.sup hzero
    simpa [max_def] using hs
  exact hc.integrableOn_Icc

/-- If the tail starts above the threshold, its positive part vanishes. -/
theorem positivePart_eq_zero_of_tail_floor
    {f : ℝ → ℝ} {h b t : ℝ}
    (hfloor : ∀ s, b ≤ s → h ≤ f s)
    (ht : b ≤ t) : max (h - f t) 0 = 0 := by
  rw [max_eq_right]
  linarith [hfloor t ht]

end Li2Lean.P0.Config.CAReceipt

namespace Li2Lean.P0.Config.CAReceipt

/-- Compact positive-part integrability plus the zero tail gives integrability
on the full half-line. -/
theorem positivePart_integrable_Ici_of_tail_floor
    {f : ℝ → ℝ} {a b h : ℝ} (hab : a ≤ b)
    (hcont : ContinuousOn f (Set.Icc a b))
    (hfloor : ∀ s, b ≤ s → h ≤ f s) :
    IntegrableOn (fun t => max (h - f t) 0) (Set.Ici a) := by
  have hcompact := positivePart_integrable_Icc (h := h) hcont
  have htail : IntegrableOn (fun t => max (h - f t) 0) (Set.Ici b) := by
    refine IntegrableOn.congr_fun (f := fun _ : ℝ => (0 : ℝ))
      (g := fun t => max (h - f t) 0) (s := Set.Ici b)
      (μ := volume) integrableOn_zero ?_ measurableSet_Ici
    intro t ht
    exact (positivePart_eq_zero_of_tail_floor hfloor ht).symm
  have hunion := hcompact.union htail
  simpa [Set.Icc_union_Ici_eq_Ici hab] using hunion

end Li2Lean.P0.Config.CAReceipt

namespace Li2Lean.P0.Config.CAReceipt

/-- The receipt's frequency positive part is integrable on the complete
half-line once the literal field's tail regularity is supplied. -/
theorem actual_frequency_positivePart_integrable
    (R : CAReceipt)
    (hcontCompact : ContinuousOn
      (Config.Wmu ConfigReferenceSymmetry.actualReference)
      (Set.Icc (1 / 2 : ℝ) (81 / 10 : ℝ)))
    (hcontTail : ContinuousOn
      (Config.Wmu ConfigReferenceSymmetry.actualReference)
      (Set.Ici (81 / 10 : ℝ)))
    (hdiffTail : DifferentiableOn ℝ
      (Config.Wmu ConfigReferenceSymmetry.actualReference)
      (Set.Ioi (81 / 10 : ℝ))) :
    IntegrableOn
      (fun t => max (Config.hMu -
        Config.Wmu ConfigReferenceSymmetry.actualReference t) 0)
      (Set.Ici (1 / 2 : ℝ)) := by
  apply positivePart_integrable_Ici_of_tail_floor (a := (1 / 2 : ℝ))
    (b := (81 / 10 : ℝ)) (h := Config.hMu) (by norm_num) hcontCompact
  intro s hs
  exact frequency_lower_tail_of_deriv R hcontTail hdiffTail hs

end Li2Lean.P0.Config.CAReceipt
