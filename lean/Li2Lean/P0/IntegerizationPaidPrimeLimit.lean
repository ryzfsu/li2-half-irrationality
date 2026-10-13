/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFiniteTailLimit
import Li2Lean.P0.IntegerizationChain

/-! The entire paid finite-profile budget has a strict rate below 397/200.
This module retains the two-adic feature subtraction and pays a finite
64-cell tail majorant. Relating this explicit budget to the determinant is
a separate finite coefficient/geometry theorem, not a PNT hypothesis. -/
namespace Li2Lean.P0.Integerization
noncomputable section
open Filter Topology
open IntegerizationTables

/-- A standalone copy of the short log-series argument in AlphaParam,
so this arithmetic module does not import the C-A receipt dependency DAG. -/
theorem p0PaidRate_logTwoLower_le : (p0LogTwoLower : ℝ) ≤ Real.log 2 := by
  have hsum := Real.hasSum_log_one_add_inv (a := (1 : ℝ)) one_pos
  have hnn : ∀ k : ℕ, 0 ≤ (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
      (1 / (2 * (1 : ℝ) + 1)) ^ (2 * k + 1) := by
    intro k
    positivity
  have hle := sum_le_hasSum (Finset.range 30) (fun k _ => hnn k) hsum
  have heq : (p0LogTwoLower : ℝ) =
      ∑ k ∈ Finset.range 30, (2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) *
        (1 / (2 * (1 : ℝ) + 1)) ^ (2 * k + 1) := by
    unfold p0LogTwoLower
    push_cast
    refine Finset.sum_congr rfl ?_
    intro k _
    ring
  rw [heq]
  calc
    _ ≤ Real.log (1 + (1 : ℝ)⁻¹) := hle
    _ = Real.log 2 := by norm_num

def p0FinitePaidRateConstant : ℝ :=
  (p0LowIntegralClaim : ℝ) + 287 / 192 +
    ((p0FiniteTailIntegral : ℝ) + 3 / 256) - (13 / 16) * Real.log 2

def p0FinitePaidProfileBudget (m : ℕ) : ℝ :=
  weightedPrimeSum p0A2LowProfile m / (m : ℝ) +
    weightedPrimeSum p0A2HighProfile m / (m : ℝ) +
    p0FiniteTailBudget m - ((13 / 16) - 1 / (m : ℝ)) * Real.log 2

theorem p0FinitePaidProfileBudget_tendsto :
    Tendsto p0FinitePaidProfileBudget atTop (𝓝 p0FinitePaidRateConstant) := by
  have hi : Tendsto (fun m : ℕ => 1 / (m : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    simpa only [one_div, Function.comp_def] using
      (tendsto_inv_atTop_zero.comp
        (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop))
  have hf : Tendsto (fun m : ℕ => ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2)
      atTop (𝓝 ((13 / 16 : ℝ) * Real.log 2)) := by
    simpa using (tendsto_const_nhds.sub hi).mul_const (Real.log 2)
  have hh := p0A2HighProfile_weightedPrime_limit_value.comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  exact ((p0A2LowProfile_weightedPrime_nat_limit.add hh).add
    p0FiniteTailBudget_tendsto).sub hf

set_option maxHeartbeats 1000000 in
theorem p0FinitePaidRateConstant_lt : p0FinitePaidRateConstant < (248 / 125 : ℝ) := by
  have ht0 : ((p0FiniteTailIntegral + 3 / 256 : ℚ) : ℝ) < ((1 / 50 : ℚ) : ℝ) := by
    exact_mod_cast p0FiniteTail_total_lt
  have ht : (p0FiniteTailIntegral : ℝ) + 3 / 256 < (1 / 50 : ℝ) := by
    push_cast at ht0
    exact ht0
  have hn : (p0LowIntegralClaim : ℝ) + 287 / 192 + 1 / 50 -
      (13 / 16 : ℝ) * (p0LogTwoLower : ℝ) < 248 / 125 := by
    norm_num [p0LowIntegralClaim, p0LogTwoLower, Finset.sum_range_succ]
  have hl := p0PaidRate_logTwoLower_le
  unfold p0FinitePaidRateConstant
  linarith

theorem p0FinitePaidRate_lt_caSlack : (248 / 125 : ℝ) < 397 / 200 := by norm_num

/-- For any fixed finite collection of rational walls, the normalized
O(m log m) payment tends to zero. The caller supplies its concrete count. -/
def p0FiniteWallBudget (wallCount m : ℕ) : ℝ :=
  (3 * wallCount : ℕ) * Real.log (3 * (m : ℝ)) / (m : ℝ)

theorem p0FiniteWallBudget_tendsto_zero (wallCount : ℕ) :
    Tendsto (p0FiniteWallBudget wallCount) atTop (𝓝 (0 : ℝ)) := by
  have hscale : Tendsto (fun m : ℕ => (3 : ℝ) * m) atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num)
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hscale
  have hh := hlog.const_mul ((3 * wallCount : ℕ) * (3 : ℝ))
  have he : (fun m : ℕ => ((3 * wallCount : ℕ) * (3 : ℝ)) *
      (Real.log (3 * (m : ℝ)) / (3 * (m : ℝ)))) =
      p0FiniteWallBudget wallCount := by
    funext m
    unfold p0FiniteWallBudget
    simp only [div_eq_mul_inv, mul_inv_rev]
    ring
  simp only [Function.comp_apply, id_eq, mul_zero] at hh
  rw [he] at hh
  exact hh

/-- The explicit profile budget, arbitrary vanishing square-root-prime cost,
and finite-wall cost have the same computed limit. This statement is about
the actual budget expression and does not assume an integerizer rate. -/
theorem p0FinitePaidBudget_with_error_tendsto
    (smallCost : ℕ → ℝ)
    (hsmall : Tendsto (fun m : ℕ => smallCost m / (m : ℝ)^2) atTop (𝓝 0))
    (wallCount : ℕ) :
    Tendsto (fun m : ℕ => p0FinitePaidProfileBudget m +
      smallCost m / (m : ℝ)^2 + p0FiniteWallBudget wallCount m)
      atTop (𝓝 p0FinitePaidRateConstant) := by
  simpa using (p0FinitePaidProfileBudget_tendsto.add hsmall).add
    (p0FiniteWallBudget_tendsto_zero wallCount)

/-- Once finite primewise arithmetic places a scalar below the paid budget,
its rate follows. The finite inequality is kept explicit; no baseline sharp
rate and no hidden actual feature-divisibility witness is assumed. -/
theorem p0Scalar_rate_of_finitePaidBudget
    (D : ℕ → ℚ) (smallCost : ℕ → ℝ) (wallCount : ℕ)
    (hsmall : Tendsto (fun m : ℕ => smallCost m / (m : ℝ)^2) atTop (𝓝 0))
    (hfinite : ∀ m : ℕ, 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ)^2 ≤ p0FinitePaidProfileBudget m +
        smallCost m / (m : ℝ)^2 + p0FiniteWallBudget wallCount m) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ)^2 ≤ (248 / 125 : ℝ) := by
  have ht := p0FinitePaidBudget_with_error_tendsto smallCost hsmall wallCount
  have he := (tendsto_order.mp ht).2 (248 / 125) p0FinitePaidRateConstant_lt
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp he
  refine ⟨M, ?_⟩
  intro m hm hp h4
  exact le_trans (hfinite m hp h4) (hM m hm).le

end
end Li2Lean.P0.Integerization
#print axioms Li2Lean.P0.Integerization.p0FinitePaidProfileBudget_tendsto
#print axioms Li2Lean.P0.Integerization.p0FinitePaidRateConstant_lt
#print axioms Li2Lean.P0.Integerization.p0FiniteWallBudget_tendsto_zero
#print axioms Li2Lean.P0.Integerization.p0Scalar_rate_of_finitePaidBudget
