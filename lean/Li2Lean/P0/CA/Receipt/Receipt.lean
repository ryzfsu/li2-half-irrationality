/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Duality
import Li2Lean.P0.CA.Receipt.Tail
import Li2Lean.P0.ConfigSlackReceipt
import Li2Lean.P0.ConfigAnalytic

/-!
# The C-A 397/200 receipt bound to the actual reference

`CAReceiptSlackActual` collects exactly the inputs that are not yet proved:
the three regional row inputs (`RowInputs.lean`), the L6 linearization at the
actual reference (`Duality.lean`), and the reference-energy enclosure
`-11/25 < actualReference.qLog`. Every other field of the old `CAReceipt`
is a theorem here, proved from source for the slack tables:

* `contour_lower_all`: `h_η ≤ W_η` on all of `Γ`;
* `pinned_penalty_le` / `frequency_penalty_le`: the step-majorant penalties
  `P`, `T` are at most the exact spent rational masses;
* `frequency_tail_threshold`: `h_μ ≤ W_μ(t)` for every `t ≥ 81/10`
  (monotonicity from the proved (5.8) derivative envelope);
* `duality_lower`: `cAConstant + Q_log + h_η + h_μ - P - T ≤ alphaGamma`;
* `alpha_bound_floor`, `alpha_bound`: `199/100 < alphaGamma` and
  `397/200 < alphaGamma`.

The penalties are those of the SPENT rows `lower - allowance`
(`1/2000` contour, `1/10000` pinned/frequency); the original row bounds
supplied by the inputs imply them. The certificate value is
`815323602118761/409600000000000 = 1.99053613...` (with `Q_log > -11/25`;
`1.99220143...` with the v10 enclosure), above the `1.990` floor.
-/

open MeasureTheory Set

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.F_L8
open Li2Lean.P0.ConfigReferenceSymmetry

noncomputable section

/-- The pinned penalty `P` of the slack receipt: the integral of the step
majorant of the spent pinned rows below `h_η`. -/
def pinnedPenalty : ℝ :=
  ∫ x in Icc (1 / 4 : ℝ) (5 / 4), stepMajorant hEtaQ realAllowance Data.pinnedRows x

/-- The frequency penalty `T` of the slack receipt. -/
def frequencyPenalty : ℝ :=
  ∫ t in Ici (1 / 2 : ℝ), stepMajorant hMuQ realAllowance Data.frequencyRows t

theorem pinnedPenalty_le : pinnedPenalty ≤ (pinnedPenaltyQ : ℝ) := by
  have h := integral_stepMajorant_le hEtaQ realAllowance (Icc (1 / 4 : ℝ) (5 / 4))
    Data.pinnedRows (exactChain_widths Data.pinnedRows_chain)
  rw [Data.pinnedRows_penalty] at h
  exact h

theorem frequencyPenalty_le : frequencyPenalty ≤ (frequencyPenaltyQ : ℝ) := by
  have h := integral_stepMajorant_le hMuQ realAllowance (Ici (1 / 2 : ℝ))
    Data.frequencyRows (exactChain_widths Data.frequencyRows_chain)
  rw [Data.frequencyRows_penalty] at h
  exact h

theorem gammaPoint_eq_ellipse (u : ℝ) :
    gammaPoint u = Li2Lean.p0EllipsePoint 1 u := by
  simp [gammaPoint, Li2Lean.p0EllipsePoint, center, semiMajor, semiMinor]

/-- The reference-energy lower bound needed by the slack receipt. It is
weaker than the v10 enclosure `Config.qLogLower = -0.438334707` by about
`1.67e-3` (the true value is `-0.43833470604...`); the slack absorbs the
difference. -/
def qLogSlackLower : ℚ := -11 / 25

theorem qLogSlackLower_le_v10 : ((qLogSlackLower : ℚ) : ℝ) ≤ Config.qLogLower := by
  norm_num [qLogSlackLower, Config.qLogLower]

/-- The legacy `CAReceiptSlack.pinned_floor` field cannot hold for the
generated pinned table: the pinned rows near `x = 5/4` lie below the common
floor `-1673/500`. Pinned rows only enter through the penalty `P`. -/
theorem pinnedRows_not_above_slackFloor :
    ¬ ∀ c ∈ Data.pinnedRows, P0.caSlackFloor ≤ c.lower := by
  intro h
  have hsub : ∀ c ∈ Data.pinnedRows03, P0.caSlackFloor ≤ c.lower :=
    fun c hc => h c (by
      unfold Data.pinnedRows
      exact List.mem_append_right _ hc)
  have hcheck := floorCheck_complete hsub
  have hfalse : floorCheck P0.caSlackFloor Data.pinnedRows03 = false := by
    decide +kernel
  rw [hcheck] at hfalse
  exact Bool.noConfusion hfalse

/-- The non-row inputs of the receipt. -/
structure CAAnalyticInputs : Prop where
  /-- L6 linearization at the actual reference. -/
  linearization : ActualReferenceLinearization
  /-- Reference-energy enclosure `Q_log > -11/25`. -/
  qLog_lower : ((qLogSlackLower : ℚ) : ℝ) < actualReference.qLog

/-- The completed C-A slack receipt: only the unproved inputs are fields. -/
structure CAReceiptSlackActual : Prop where
  rows : CARowInputs
  analytic : CAAnalyticInputs

namespace CAReceiptSlackActual

variable (R : CAReceiptSlackActual)

include R in
theorem contour_lower_param {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    ((hEtaQ : ℚ) : ℝ) ≤ contourFunction v := by
  have hw := exactChain_widths Data.contourRows_chain
  obtain ⟨c, hmem, _, hlo, hhi⟩ :=
    exactChain_covers Data.contourRows_chain v (by simpa using hv0) (by simpa using hv1)
  have hrow := row_lower_of_valid R.rows.contour hw c hmem v hlo hhi
  have hfloor := Data.contourRows_floor c hmem
  have ha : (0 : ℚ) ≤ contourAllowance := by norm_num [contourAllowance]
  have hq : hEtaQ ≤ c.lower := by linarith
  have hqR : ((hEtaQ : ℚ) : ℝ) ≤ (c.lower : ℝ) := by exact_mod_cast hq
  linarith

include R in
/-- `h_η ≤ W_η` on the whole ellipse `Γ`. -/
theorem contour_lower_all :
    ∀ z ∈ Gamma, ((hEtaQ : ℚ) : ℝ) ≤ Config.Weta actualReference z := by
  rintro z ⟨u, rfl⟩
  rw [gammaPoint_eq_ellipse]
  obtain ⟨v, hv0, hv1, hsymm⟩ := actualReference_contour_reduction u
  rw [hsymm]
  exact R.contour_lower_param hv0 hv1

include R in
theorem pinned_dominated :
    ∀ x ∈ Icc (1 / 4 : ℝ) (5 / 4),
      ((hEtaQ : ℚ) : ℝ) - Config.Weta actualReference (x : ℂ) ≤
        stepMajorant hEtaQ realAllowance Data.pinnedRows x := by
  intro x hx
  have hw := exactChain_widths Data.pinnedRows_chain
  have horig := row_lower_of_valid R.rows.pinned hw
  have hspent := spent_of_original (a := realAllowance)
    (by norm_num [realAllowance]) horig
  exact sub_le_stepMajorant Data.pinnedRows_chain hEtaQ realAllowance hspent
    (by simpa using hx.1) (by simpa using hx.2)

include R in
/-- `h_μ ≤ W_μ` at the right endpoint `81/10`. -/
theorem frequency_endpoint_threshold :
    ((hMuQ : ℚ) : ℝ) ≤ frequencyFunction (81 / 10) := by
  have hw := exactChain_widths Data.frequencyRows_chain
  obtain ⟨c, hmem, _, hlo, hhi⟩ :=
    exactChain_covers Data.frequencyRows_chain (81 / 10) (by norm_num) (by norm_num)
  have hrow := row_lower_of_valid R.rows.frequency hw c hmem (81 / 10) hlo hhi
  have hhiq : (81 / 10 : ℚ) ≤ c.hi := by
    have hR : (((81 / 10 : ℚ)) : ℝ) ≤ (c.hi : ℝ) := by push_cast; exact hhi
    exact_mod_cast hR
  have hend := Data.frequencyRows_endpoint c hmem hhiq
  have ha : (0 : ℚ) ≤ realAllowance := by norm_num [realAllowance]
  have hq : hMuQ ≤ c.lower := by linarith
  have hqR : ((hMuQ : ℚ) : ℝ) ≤ (c.lower : ℝ) := by exact_mod_cast hq
  linarith

include R in
/-- `h_μ ≤ W_μ(t)` on the whole tail `t ≥ 81/10`. -/
theorem frequency_tail_threshold {t : ℝ} (ht : (81 / 10 : ℝ) ≤ t) :
    ((hMuQ : ℚ) : ℝ) ≤ Config.Wmu actualReference t :=
  le_trans R.frequency_endpoint_threshold (frequencyFunction_tail_ge ht)

include R in
theorem frequency_dominated :
    ∀ t ∈ Ici (1 / 2 : ℝ),
      ((hMuQ : ℚ) : ℝ) - Config.Wmu actualReference t ≤
        stepMajorant hMuQ realAllowance Data.frequencyRows t := by
  intro t ht
  by_cases hle : t ≤ 81 / 10
  · have hw := exactChain_widths Data.frequencyRows_chain
    have horig := row_lower_of_valid R.rows.frequency hw
    have hspent := spent_of_original (a := realAllowance)
      (by norm_num [realAllowance]) horig
    exact sub_le_stepMajorant Data.frequencyRows_chain hMuQ realAllowance hspent
      (by simpa using (mem_Ici.mp ht)) (by simpa using hle)
  · have htail := R.frequency_tail_threshold (le_of_lt (lt_of_not_ge hle))
    have h0 := stepMajorant_nonneg hMuQ realAllowance Data.frequencyRows t
    linarith

include R in
/-- The duality field: `cAConstant + Q_log + h_η + h_μ - P - T ≤ alphaGamma`. -/
theorem duality_lower :
    ((Config.cAConstant + actualReference.qLog + ((hEtaQ : ℚ) : ℝ) +
        ((hMuQ : ℚ) : ℝ) - pinnedPenalty - frequencyPenalty : ℝ) : WithTop ℝ) ≤
      alphaGamma :=
  actual_duality_lower R.analytic.linearization R.contour_lower_all
    (fun x _ => stepMajorant_nonneg _ _ _ x) R.pinned_dominated
    (stepMajorant_integrableOn _ _ _ _)
    (fun t _ => stepMajorant_nonneg _ _ _ t) R.frequency_dominated
    (stepMajorant_integrableOn _ _ _ _)

/-- The exact rational certificate value with spent allowances. -/
def certificateValue : ℚ := 815323602118761 / 409600000000000

/-- Margin lemma: the rational enclosures give the certificate value, which
is above the `1.990` floor and the `397/200` target. -/
theorem margin {q P T : ℝ} (hq : ((qLogSlackLower : ℚ) : ℝ) < q)
    (hP : P ≤ (pinnedPenaltyQ : ℝ)) (hT : T ≤ (frequencyPenaltyQ : ℝ)) :
    ((certificateValue : ℚ) : ℝ) <
      Config.cAConstant + q + ((hEtaQ : ℚ) : ℝ) + ((hMuQ : ℚ) : ℝ) - P - T := by
  have hlog := ConfigAnalytic.logTwoEnclosure_v10.2
  unfold Config.cAConstant
  simp only [certificateValue, qLogSlackLower, hEtaQ, hMuQ, pinnedPenaltyQ, frequencyPenaltyQ] at hq hP hT ⊢
  push_cast at hq hP hT ⊢
  linarith

theorem certificateValue_gt_floor : (199 / 100 : ℚ) < certificateValue := by
  norm_num [certificateValue]

theorem floor_gt_target : (397 / 200 : ℚ) < 199 / 100 := by norm_num

include R in
/-- `certificateValue < alphaGamma`. -/
theorem alpha_bound_certificate :
    (((certificateValue : ℚ) : ℝ) : WithTop ℝ) < alphaGamma := by
  have hm := margin R.analytic.qLog_lower pinnedPenalty_le frequencyPenalty_le
  have hcast : (((certificateValue : ℚ) : ℝ) : WithTop ℝ) <
      ((Config.cAConstant + actualReference.qLog + ((hEtaQ : ℚ) : ℝ) +
        ((hMuQ : ℚ) : ℝ) - pinnedPenalty - frequencyPenalty : ℝ) : WithTop ℝ) := by
    exact_mod_cast hm
  exact lt_of_lt_of_le hcast R.duality_lower

include R in
/-- Every target at most the certificate value is strictly below `alphaGamma`. -/
theorem alpha_bound_of_le {alpha : ℝ} (h : alpha ≤ ((certificateValue : ℚ) : ℝ)) :
    (alpha : WithTop ℝ) < alphaGamma :=
  lt_of_le_of_lt (by exact_mod_cast h) R.alpha_bound_certificate

include R in
/-- The `1.990` floor: `199/100 < alphaGamma`. -/
theorem alpha_bound_floor : (((199 / 100 : ℚ) : ℝ) : WithTop ℝ) < alphaGamma :=
  R.alpha_bound_of_le (by exact_mod_cast certificateValue_gt_floor.le)

include R in
/-- The narrowed C-A target: `397/200 < alphaGamma`. -/
theorem alpha_bound :
    (((P0.caSlackAlphaTarget : ℚ) : ℝ) : WithTop ℝ) < alphaGamma :=
  R.alpha_bound_of_le (by
    have : P0.caSlackAlphaTarget ≤ certificateValue := by
      norm_num [P0.caSlackAlphaTarget, certificateValue]
    exact_mod_cast this)

end CAReceiptSlackActual

end

end Li2Lean.P0.CA.Receipt
