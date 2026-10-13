/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.AlphaParam
import Li2Lean.P0.IntegerizerRate

namespace Li2Lean

noncomputable section

open P0.Integerization

/-! Endpoint assembly using an explicit integerizer rate.  This is the
weakened interface needed when the arithmetic proof supplies any rate below
the analytic target, rather than exactly `p0TauSharp 2`. -/
theorem p0EndpointCertificate_of_rate
    (F : P0Family) (hbase : F.a = 2)
    {alpha rate : ℝ} (hrate : rate < alpha)
    (hA : P0AnalyticEstimateAt alpha F)
    (hI : P0IntegerizerBoundAt F rate)
    (hN : P0A2NonvanishingStatement F) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) := by
  obtain ⟨D, hDpos, hdeg, hpoly, hrateBound⟩ := hI
  have hpow : ∀ k : ℕ, 1 ≤ 83 ^ k := fun k =>
    Nat.one_le_pow _ _ (by norm_num)
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
      Real.log (D (32 * 83 ^ k) : ℝ) /
          ((32 * 83 ^ k : ℕ) : ℝ) ^ 2 ≤ rate + ε := by
    intro ε hε
    obtain ⟨M, hM⟩ := hrateBound ε hε
    refine ⟨M, fun k hk => ?_⟩
    have hk' : M ≤ 32 * 83 ^ k := by
      have : k < 83 ^ k := Nat.lt_pow_self (by norm_num)
      omega
    exact hM _ hk' (hidx_pos k) (hidx4 k)
  exact ⟨{
    index := fun k => 32 * 83 ^ k
    G := F.G
    D := D
    alpha := alpha
    tau := rate
    cLog := 10
    cLinear := 56
    cConst := 301
    index_strictMono := hmono
    index_multiple_four := hidx4
    index_ge_eight := hidx8
    alpha_gt_tau := hrate
    degree_bound := fun k => hdeg _ (hidx_pos k) (hidx4 k)
    integerizer_pos := fun k => hDpos _ (hidx_pos k) (hidx4 k)
    integerizer_poly := fun k => hpoly _ (hidx_pos k) (hidx4 k)
    analytic_bound := fun k => hA hbase _ (hidx8 k) (hidx4 k)
    integerizer_rate := hrate'
    nonzero_at_rationals := hN hbase }⟩

theorem p0EndpointCertificate_of_rate_below_caSlack
    (F : P0Family) (hbase : F.a = 2) (rate : ℝ)
    (hrate : rate < ((397 / 200 : ℚ) : ℝ))
    (hA : P0AnalyticEstimateAt ((397 / 200 : ℚ) : ℝ) F)
    (hI : P0IntegerizerBoundAt F rate)
    (hN : P0A2NonvanishingStatement F) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) := by
  apply p0EndpointCertificate_of_rate F hbase ?_ hA hI hN
  exact hrate

end

end Li2Lean
