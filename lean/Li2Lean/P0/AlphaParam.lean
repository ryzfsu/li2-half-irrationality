/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.IntegerizationTables
import Li2Lean.P0.Dual
import Li2Lean.P0.ConfigCAReceipt
import Li2Lean.P0.ConfigSlackReceipt

/-!
# The alpha-parameterized analytic chain

The P0 endpoint argument needs only `p0TauSharp 2 < alpha` for the decay rate
`alpha` of `P0AnalyticEstimateAt alpha`. This file

* proves `p0TauSharp 2 ≤ p0BasicIntegerizerRateClaim < 1979/1000` from the
  audited integerization tables (the exact constant `p0K` equals the sum of the
  three table claims, and the 30-term atanh partial sum is below `log 2`);
* defines admissibility `P0AlphaAdmissible alpha := p0TauSharp 2 < alpha` and
  proves it for the paper target `1992909/10^6` and for the slack target
  `397/200`;
* assembles an `EndpointCertificate` from `P0AnalyticEstimateAt alpha`, the
  integerizer bound, the fixed `32 * 83^k` nonvanishing tower, and
  admissibility, for any `alpha`;
* links the slack target to the existing C-A receipt and dual certificate.

None of the open inputs (`P0AnalyticEstimateAt`, `P0IntegerizerBound`,
`P0A2NonvanishingStatement`, the receipts) is proved here.
-/

namespace Li2Lean

noncomputable section

/-! ## The sharp integerizer rate at `a = 2` -/

/-- The 30-term atanh partial sum `p0LogTwoLower` is a lower bound for `log 2`. -/
theorem p0LogTwoLower_le_log_two :
    ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) ≤ Real.log 2 := by
  have hsum := Real.hasSum_log_one_add_inv (a := (1 : ℝ)) one_pos
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
      (1 / (2 * (1 : ℝ) + 1)) ^ (2 * k + 1) := by
    intro k
    positivity
  have hle := sum_le_hasSum (Finset.range 30) (fun k _ => hnn k) hsum
  have heq : ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) =
      ∑ k ∈ Finset.range 30, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
        (1 / (2 * (1 : ℝ) + 1)) ^ (2 * k + 1) := by
    unfold IntegerizationTables.p0LogTwoLower
    push_cast
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ Real.log (1 + (1 : ℝ)⁻¹) := hle
    _ = Real.log 2 := by norm_num

/-- The exact rational `K` of docs/6379 H2 is the sum of the three audited
integerization-table claims. -/
theorem p0K_eq_table_claims :
    p0K = ((IntegerizationTables.p0LowIntegralClaim +
      IntegerizationTables.p0SmallPrimeTailClaim +
      IntegerizationTables.p0HighIntegralClaim : ℚ) : ℝ) := by
  unfold p0K IntegerizationTables.p0LowIntegralClaim
    IntegerizationTables.p0SmallPrimeTailClaim
    IntegerizationTables.p0HighIntegralClaim
  push_cast
  norm_num

/-- At `a = 2`, `tau_sharp = K - (13/16) log 2`. -/
theorem p0TauSharp_two_eq : p0TauSharp 2 = p0K - 13 / 16 * Real.log 2 := by
  unfold p0TauSharp
  norm_num

/-- `tau_sharp(2)` is at most the audited basic integerizer-rate claim. -/
theorem p0TauSharp_two_le_rateClaim :
    p0TauSharp 2 ≤
      ((IntegerizationTables.p0BasicIntegerizerRateClaim : ℚ) : ℝ) := by
  rw [p0TauSharp_two_eq, p0K_eq_table_claims]
  have h := p0LogTwoLower_le_log_two
  unfold IntegerizationTables.p0BasicIntegerizerRateClaim
  push_cast
  linarith

/-- The proved sharp-rate bound `tau_sharp(2) < 1979/1000`. -/
theorem p0TauSharp_two_lt_1979_over_1000 :
    p0TauSharp 2 < (1979 / 1000 : ℝ) := by
  have h1 := p0TauSharp_two_le_rateClaim
  have h2 : ((IntegerizationTables.p0BasicIntegerizerRateClaim : ℚ) : ℝ) <
      ((1979 / 1000 : ℚ) : ℝ) := by
    exact_mod_cast IntegerizationTables.p0BasicIntegerizerRate_lt_1979_over_1000
  have h3 : ((1979 / 1000 : ℚ) : ℝ) = (1979 / 1000 : ℝ) := by norm_num
  rw [h3] at h2
  exact lt_of_le_of_lt h1 h2

/-! ## Admissible decay rates -/

/-- A rational decay rate is admissible when it beats the sharp integerizer rate. -/
def P0AlphaAdmissible (alpha : ℚ) : Prop :=
  p0TauSharp 2 < (alpha : ℝ)

/-- Every rational target at least `1979/1000` is admissible. -/
theorem p0AlphaAdmissible_of_ge {alpha : ℚ} (h : 1979 / 1000 ≤ alpha) :
    P0AlphaAdmissible alpha := by
  have hR : (1979 / 1000 : ℝ) ≤ (alpha : ℝ) := by
    have : ((1979 / 1000 : ℚ) : ℝ) ≤ (alpha : ℝ) := by exact_mod_cast h
    simpa using this
  exact lt_of_lt_of_le p0TauSharp_two_lt_1979_over_1000 hR

/-- The paper target `1992909/10^6` is admissible. -/
theorem p0PaperAlphaTarget_admissible : P0AlphaAdmissible p0PaperAlphaTarget :=
  p0AlphaAdmissible_of_ge (by norm_num [p0PaperAlphaTarget])

/-- The slack target `397/200` exceeds the proved bound on `tau_sharp(2)`. -/
theorem caSlackAlphaTarget_admissible : P0AlphaAdmissible P0.caSlackAlphaTarget :=
  p0AlphaAdmissible_of_ge (by norm_num [P0.caSlackAlphaTarget])

/-- The target carried by any slack receipt is admissible. -/
theorem CAReceiptSlack_target_admissible (R : P0.CAReceiptSlack) :
    P0AlphaAdmissible R.alphaTarget := by
  rw [R.alphaTarget_eq]
  exact caSlackAlphaTarget_admissible

/-! ## Endpoint certificate for an arbitrary admissible rate -/

/--
Assembly of the L1 endpoint certificate at an arbitrary decay rate `alpha`
with `p0TauSharp 2 < alpha`, along the fixed tower `m = 32 * 83^k`. The open
inputs are the hypotheses; nothing about them is proved here.
-/
theorem p0EndpointCertificate_of_alpha (F : P0Family) (hbase : F.a = 2)
    {alpha : ℝ} (hadm : p0TauSharp 2 < alpha)
    (hA : P0AnalyticEstimateAt alpha F) (hI : P0IntegerizerBound F)
    (hN : P0A2NonvanishingStatement F) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) := by
  obtain ⟨D, hDpos, hdeg, hpoly, hrate⟩ := hI
  have hpow : ∀ k : ℕ, 1 ≤ 83 ^ k := fun k => Nat.one_le_pow _ _ (by norm_num)
  have hidx_pos : ∀ k : ℕ, 0 < 32 * 83 ^ k := fun k => by positivity
  have hidx4 : ∀ k : ℕ, 4 ∣ 32 * 83 ^ k :=
    fun k => Dvd.dvd.mul_right (by norm_num) _
  have hidx8 : ∀ k : ℕ, 8 ≤ 32 * 83 ^ k := fun k => by
    have := hpow k
    omega
  have hmono : StrictMono (fun k : ℕ => 32 * 83 ^ k) := by
    intro i j hij
    have : 83 ^ i < 83 ^ j := Nat.pow_lt_pow_right (by norm_num) hij
    show 32 * 83 ^ i < 32 * 83 ^ j
    omega
  have hrate' : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k, k₀ ≤ k →
      Real.log (D (32 * 83 ^ k) : ℝ) / ((32 * 83 ^ k : ℕ) : ℝ) ^ 2 ≤
        p0TauSharp 2 + ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hrate ε hε
    refine ⟨M, fun k hk => ?_⟩
    have hk' : M ≤ 32 * 83 ^ k := by
      have : k < 83 ^ k := Nat.lt_pow_self (by norm_num)
      omega
    have := hM _ hk' (hidx_pos k) (hidx4 k)
    rw [hbase] at this
    exact this
  exact ⟨{
    index := fun k => 32 * 83 ^ k
    G := F.G
    D := D
    alpha := alpha
    tau := p0TauSharp 2
    cLog := 10
    cLinear := 56
    cConst := 301
    index_strictMono := hmono
    index_multiple_four := hidx4
    index_ge_eight := hidx8
    alpha_gt_tau := hadm
    degree_bound := fun k => hdeg _ (hidx_pos k) (hidx4 k)
    integerizer_pos := fun k => hDpos _ (hidx_pos k) (hidx4 k)
    integerizer_poly := fun k => hpoly _ (hidx_pos k) (hidx4 k)
    analytic_bound := fun k => hA hbase _ (hidx8 k) (hidx4 k)
    integerizer_rate := hrate'
    nonzero_at_rationals := hN hbase }⟩

/-- Rational-target form: an admissible rational target suffices. -/
theorem p0EndpointCertificate_of_admissible (F : P0Family) (hbase : F.a = 2)
    {alpha : ℚ} (hadm : P0AlphaAdmissible alpha)
    (hA : P0AnalyticEstimateAt (alpha : ℝ) F) (hI : P0IntegerizerBound F)
    (hN : P0A2NonvanishingStatement F) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) :=
  p0EndpointCertificate_of_alpha F hbase hadm hA hI hN

/-- Paper instance: the estimate at `1992909/10^6`. -/
theorem p0EndpointCertificate_of_paperEstimate (F : P0Family) (hbase : F.a = 2)
    (hA : P0AnalyticEstimate F) (hI : P0IntegerizerBound F)
    (hN : P0A2NonvanishingStatement F) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) :=
  p0EndpointCertificate_of_admissible F hbase p0PaperAlphaTarget_admissible
    ((p0AnalyticEstimate_iff_at_paperTarget F).1 hA) hI hN

/-- Slack instance: the estimate at `397/200` already suffices. -/
theorem p0EndpointCertificate_of_slackEstimate (F : P0Family) (hbase : F.a = 2)
    (hA : P0AnalyticEstimateAt ((P0.caSlackAlphaTarget : ℚ) : ℝ) F)
    (hI : P0IntegerizerBound F) (hN : P0A2NonvanishingStatement F) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) :=
  p0EndpointCertificate_of_admissible F hbase caSlackAlphaTarget_admissible
    hA hI hN

/-! ## The slack target against the existing paper-target pieces -/

/-- `397/200 < 1992909/10^6`. -/
theorem caSlackAlphaTarget_lt_paperTarget :
    P0.caSlackAlphaTarget < p0PaperAlphaTarget := by
  norm_num [P0.caSlackAlphaTarget, p0PaperAlphaTarget]

/-- The real slack target is below `alphaFloor`. -/
theorem caSlackAlphaTarget_le_alphaFloor :
    ((P0.caSlackAlphaTarget : ℚ) : ℝ) ≤ P0.Config.alphaFloor := by
  rw [P0.Config.alphaFloor_eq_paperTarget]
  exact_mod_cast caSlackAlphaTarget_lt_paperTarget.le

/-- The paper estimate implies the slack estimate. -/
theorem p0AnalyticEstimate_slack_of_paper {F : P0Family}
    (hA : P0AnalyticEstimate F) :
    P0AnalyticEstimateAt ((P0.caSlackAlphaTarget : ℚ) : ℝ) F := by
  have h := (p0AnalyticEstimate_iff_at_paperTarget F).1 hA
  refine P0AnalyticEstimateAt.mono ?_ h
  exact_mod_cast caSlackAlphaTarget_lt_paperTarget.le

/-- The existing C-A receipt (old tables) certifies `397/200 < alpha_Gamma`. -/
theorem CAReceipt_slack_alpha_bound (R : P0.Config.CAReceipt) :
    (((P0.caSlackAlphaTarget : ℚ) : ℝ) : WithTop ℝ) < P0.alphaGamma :=
  R.alpha_bound_of_le caSlackAlphaTarget_le_alphaFloor

/-- A typed L8 dual certificate certifies `397/200 < alphaGamma`. -/
theorem p0DualCertificate_slack_alpha_lower {F : P0Family}
    (certificate : P0DualCertificate F) :
    ((P0.caSlackAlphaTarget : ℚ) : ℝ) < certificate.alphaGamma := by
  refine p0DualCertificate_alpha_lower_of_le ?_ certificate
  rw [p0DualRationalLower_exact]
  norm_num [P0.caSlackAlphaTarget]

end

end Li2Lean
