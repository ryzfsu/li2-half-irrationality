/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourAnalytic
import Li2Lean.P0.ConfigContourSelfPotential

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigContourExternalPOC

noncomputable section

open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential

def externalTerm (q : ℝ) (n : ℕ) (v u : ℝ) : ℝ :=
  -((q : ℝ) ^ (n + 1) * Real.cos ((n + 1) * (u + v)) / (n + 1))

def externalTermBound (q : ℝ) (n : ℕ) (u : ℝ) : ℝ :=
  |q| ^ (n + 1) * |contourDensity u|

theorem contourDensity_continuous : Continuous contourDensity := by
  unfold contourDensity
  apply continuous_finsetSum
  intro j hj
  exact continuous_const.mul
    (Li2Lean.P0.ConfigFejerMass.continuous_fejer48.comp
      (continuous_id.sub continuous_const))

private theorem abs_q_lt_one {q : ℝ} (hq : ‖(q : ℂ)‖ < 1) : |q| < 1 := by
  simpa [Complex.norm_real, Real.norm_eq_abs] using hq

private theorem geom_succ_summable {q : ℝ} (hq : |q| < 1) :
    Summable (fun n : ℕ => |q| ^ (n + 1)) := by
  have h := summable_geometric_of_lt_one (abs_nonneg q) hq
  have h' := h.mul_left |q|
  simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using h'

private theorem externalTerm_norm_bound (q : ℝ) (n : ℕ) (v u : ℝ) :
    ‖externalTerm q n v u‖ ≤ |q| ^ (n + 1) := by
  have hden : 1 ≤ ((n + 1 : ℕ) : ℝ) := by
    exact_mod_cast (Nat.succ_le_succ (Nat.zero_le n))
  have hden0 : 0 < ((n + 1 : ℕ) : ℝ) := lt_of_lt_of_le zero_lt_one hden
  have hcos : |Real.cos ((n + 1) * (u + v))| ≤ 1 :=
    Real.abs_cos_le_one _
  rw [externalTerm, Real.norm_eq_abs, abs_neg, abs_div, abs_mul, abs_pow]
  rw [show |(↑n + 1 : ℝ)| = (↑n + 1 : ℝ) from
    abs_of_nonneg (by positivity)]
  have hqnon : 0 ≤ |q| ^ (n + 1) := pow_nonneg (abs_nonneg q) _
  have hmul : |q| ^ (n + 1) * |Real.cos ((n + 1) * (u + v))| ≤
      |q| ^ (n + 1) * ((n + 1 : ℕ) : ℝ) := by
    calc
      |q| ^ (n + 1) *
          |Real.cos ((n + 1) * (u + v))| ≤
          |q| ^ (n + 1) * 1 := mul_le_mul_of_nonneg_left hcos hqnon
      _ ≤ |q| ^ (n + 1) * ((n + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hqnon
  simpa only [Nat.cast_add, Nat.cast_one] using
    (div_le_iff₀ hden0).2 hmul

theorem externalLogKernel_integral_tsum (q v : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * externalLogKernel q u v) =
      ∑' n : ℕ, ∫ u in (0 : ℝ)..(2 * Real.pi),
        contourDensity u * externalTerm q n v u := by
  let r : ℝ := |q|
  have hr : r < 1 := by exact abs_q_lt_one hq
  have hgeom : Summable (fun n : ℕ => r ^ (n + 1)) := by
    simpa [r] using geom_succ_summable hr
  let F : ℕ → ℝ → ℝ := fun n u => contourDensity u * externalTerm q n v u
  let B : ℕ → ℝ → ℝ := fun n u => externalTermBound q n u
  have hterm (u : ℝ) : HasSum (fun n => externalTerm q n v u)
      (externalLogKernel q u v) := by
    have hsum : Summable (fun n : ℕ =>
        q ^ (n + 1) * Real.cos ((n + 1) * (u + v)) / (n + 1)) := by
      refine hgeom.of_norm_bounded ?_
      intro n
      have hbound := externalTerm_norm_bound q n v u
      simpa [externalTerm, r, Real.norm_eq_abs, abs_neg] using hbound
    rw [externalLogKernel_eq_tsum q u v hq]
    simpa [externalTerm] using hsum.hasSum.neg
  have hlim : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      HasSum (fun n => F n u) (contourDensity u * externalLogKernel q u v) := by
    filter_upwards [] with u hu
    exact (hterm u).mul_left (contourDensity u)
  have hmeas (n : ℕ) : AEStronglyMeasurable (F n)
      (volume.restrict (Set.uIoc (0 : ℝ) (2 * Real.pi))) := by
    apply (contourDensity_continuous.mul ?_).aestronglyMeasurable
    unfold externalTerm
    fun_prop
  have hbound (n : ℕ) : ∀ᵐ u ∂volume, u ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) →
      ‖F n u‖ ≤ B n u := by
    filter_upwards [] with u hu
    dsimp [F, B, externalTermBound]
    rw [abs_mul]
    have hterm := externalTerm_norm_bound q n v u
    have hterm' : |externalTerm q n v u| ≤ |q| ^ (n + 1) := by
      simpa [Real.norm_eq_abs] using hterm
    calc
      |contourDensity u| * |externalTerm q n v u| ≤
          |contourDensity u| * |q| ^ (n + 1) :=
            mul_le_mul_of_nonneg_left hterm' (abs_nonneg _)
      _ = |q| ^ (n + 1) * |contourDensity u| := mul_comm _ _
  have hboundSummable : ∀ᵐ u ∂volume,
      u ∈ Set.uIoc (0 : ℝ) (2 * Real.pi) → Summable (fun n => B n u) := by
    filter_upwards [] with u hu
    dsimp [B, externalTermBound]
    exact hgeom.mul_right _
  have hboundInt : IntervalIntegrable (fun u => ∑' n : ℕ, B n u)
      volume 0 (2 * Real.pi) := by
    have heq (u : ℝ) : (∑' n : ℕ, B n u) =
        (∑' n : ℕ, r ^ (n + 1)) * |contourDensity u| := by
      dsimp [B, externalTermBound]
      rw [Summable.tsum_mul_right _ hgeom]
    have hcont : Continuous (fun u : ℝ =>
        (∑' n : ℕ, r ^ (n + 1)) * |contourDensity u|) :=
      continuous_const.mul (continuous_abs.comp contourDensity_continuous)
    exact (hcont.congr fun u => (heq u).symm).intervalIntegrable _ _
  have hseries := intervalIntegral.hasSum_integral_of_dominated_convergence
    (a := (0 : ℝ)) (b := 2 * Real.pi) (μ := volume) (F := F)
    (bound := B) hmeas hbound hboundSummable hboundInt hlim
  simpa only [F] using hseries.tsum_eq.symm

end

end Li2Lean.P0.ConfigContourExternalPOC
