/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Agents.G_L7

open MeasureTheory Filter

namespace Li2Lean
namespace P0

noncomputable section

/-- The literal double-circle interaction in v10 `sec-tube`, reduced using
the already proved L7 circle mean. This identity also covers intersecting
and coincident circles; no separation or integrability hypothesis is added. -/
theorem circlePairEnergy_eq_neg_circleAverage_log_max (z w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    circlePairEnergy z w r =
      -Real.circleAverage (fun x : ℂ => Real.log (max r ‖x - w‖)) z r := by
  have hperiod : (2 : ℝ) * Real.pi ≠ 0 :=
    mul_ne_zero two_ne_zero Real.pi_ne_zero
  have hinner (u : ℝ) :
      (∫ v in (0 : ℝ)..(2 * Real.pi),
        realLogKernel (circlePoint z r u) (circlePoint w r v)) =
      -(Real.log (max r ‖circlePoint z r u - w‖) * (2 * Real.pi)) := by
    have h := g_l7_circle_average (circlePoint z r u) w r hr
    change (∫ v in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖circlePoint z r u - circlePoint w r v‖) / (2 * Real.pi) =
        Real.log (max r ‖circlePoint z r u - w‖) at h
    rw [div_eq_iff hperiod] at h
    simpa only [realLogKernel, intervalIntegral.integral_neg] using congrArg Neg.neg h
  unfold circlePairEnergy
  simp_rw [hinner]
  rw [intervalIntegral.integral_neg, intervalIntegral.integral_mul_const]
  simp_rw [ContourKit.p0CirclePoint_eq_circleMap]
  rw [Real.circleAverage_def, smul_eq_mul]
  field_simp

/-- Exact diagonal correction in v10 `eq:tube-circle`: the self-energy of
the probability arclength measure on a radius-`r` circle is `log (1/r)`. -/
theorem circlePairEnergy_self (z : ℂ) {r : ℝ} (hr : 0 < r) :
    circlePairEnergy z z r = Real.log (1 / r) := by
  rw [circlePairEnergy_eq_neg_circleAverage_log_max z z hr]
  have hmean :
      Real.circleAverage (fun x : ℂ => Real.log (max r ‖x - z‖)) z r =
        Real.log r := by
    apply Real.circleAverage_const_on_circle
    intro x hx
    have hxnorm : ‖x - z‖ = r := by
      simpa only [Metric.mem_sphere, dist_eq_norm, abs_of_pos hr] using hx
    simp only [hxnorm, max_self]
  rw [hmean]
  simp only [one_div, Real.log_inv]

/-- Monotonicity against the truncated logarithm, with the single logarithmic
singularity removed by Mathlib's codiscrete congruence theorem. In particular,
the proof does not misuse the finite convention `Real.log 0 = 0`. -/
theorem log_max_center_le_circleAverage_log_max (z w : ℂ) {r : ℝ}
    (hr : 0 < r) :
    Real.log (max r ‖z - w‖) ≤
      Real.circleAverage (fun x : ℂ => Real.log (max r ‖x - w‖)) z r := by
  have hcont : Continuous (fun x : ℂ => Real.log (max r ‖x - w‖)) := by
    apply Continuous.log (continuous_const.max ((continuous_id.sub continuous_const).norm))
    intro x
    exact ne_of_gt (lt_of_lt_of_le hr (le_max_left r ‖x - w‖))
  have hbase : CircleIntegrable (fun x : ℂ => Real.log ‖x - w‖) z r :=
    circleIntegrable_log_norm_sub_const r
  have heq :
      (fun x : ℂ => Real.log ‖x - w‖) =ᶠ[codiscreteWithin (Metric.sphere z |r|)]
        (fun x : ℂ => min (Real.log ‖x - w‖) (Real.log (max r ‖x - w‖))) := by
    filter_upwards [compl_singleton_mem_codiscreteWithin w] with x hx
    have hxw : x ≠ w := by simpa only [Set.mem_compl_iff, Set.mem_singleton_iff] using hx
    have hpos : 0 < ‖x - w‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxw)
    exact (min_eq_left (Real.log_le_log hpos (le_max_right r ‖x - w‖))).symm
  calc
    Real.log (max r ‖z - w‖) =
        Real.circleAverage (fun x : ℂ => Real.log ‖x - w‖) z r :=
      (ContourKit.circleAverage_log_norm_sub_const_eq_log_max w z hr).symm
    _ = Real.circleAverage
        (fun x : ℂ => min (Real.log ‖x - w‖) (Real.log (max r ‖x - w‖))) z r :=
      Real.circleAverage_congr_codiscreteWithin heq hr.ne'
    _ ≤ Real.circleAverage (fun x : ℂ => Real.log (max r ‖x - w‖)) z r := by
      exact Real.circleAverage_mono
        (CircleIntegrable.congr_codiscreteWithin heq hbase)
        hcont.continuousOn.circleIntegrable' (fun _ _ => min_le_right _ _)

/-- The double-circle upper bound used in v10 `eq:tube-circle`, in its stronger
truncated-kernel form. It holds for all centers, including intersecting circles. -/
theorem circlePairEnergy_le_neg_log_max (z w : ℂ) {r : ℝ} (hr : 0 < r) :
    circlePairEnergy z w r ≤ -Real.log (max r ‖z - w‖) := by
  rw [circlePairEnergy_eq_neg_circleAverage_log_max z w hr]
  exact neg_le_neg (log_max_center_le_circleAverage_log_max z w hr)

/-- Away from a collision of centers, circular smoothing decreases the pair
energy in v10 `eq:tube-circle`. The circles themselves may intersect. -/
theorem circlePairEnergy_le_realLogKernel (z w : ℂ) {r : ℝ} (hr : 0 < r)
    (hzw : z ≠ w) : circlePairEnergy z w r ≤ realLogKernel z w := by
  calc
    circlePairEnergy z w r ≤ -Real.log (max r ‖z - w‖) :=
      circlePairEnergy_le_neg_log_max z w hr
    _ ≤ realLogKernel z w := by
      apply neg_le_neg
      exact Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hzw))
        (le_max_right r ‖z - w‖)

/-- v10 `eq:tube-circle`, before dividing by `m²`: all diagonal terms are
exactly `log (1/r)`, and no separation of smoothing circles is required. -/
theorem finite_configuration_transfer_distinct : finiteConfigurationTransferDistinct := by
  intro d z r hr hz
  have hsum :
      (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) ≤
      (∑ i : Fin d, ∑ j : Fin d,
        if i = j then 0 else realLogKernel (z i) (z j)) +
        (d : ℝ) * Real.log (1 / r) := by
    calc
      (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) ≤
          ∑ i : Fin d, ∑ j : Fin d,
            ((if i = j then 0 else realLogKernel (z i) (z j)) +
              (if i = j then Real.log (1 / r) else 0)) := by
        apply Finset.sum_le_sum
        intro i hi
        apply Finset.sum_le_sum
        intro j hj
        by_cases hij : i = j
        · subst j
          simp [circlePairEnergy_self (z i) hr]
        · simpa only [ite_eq_right hij, add_zero] using
            circlePairEnergy_le_realLogKernel (z i) (z j) hr (hz i j hij)
      _ = (∑ i : Fin d, ∑ j : Fin d,
          if i = j then 0 else realLogKernel (z i) (z j)) +
          (d : ℝ) * Real.log (1 / r) := by
        simp [Finset.sum_add_distrib]
  linarith

/-- The normalized finite-configuration form of v10 `eq:tube-circle`.
The denominator is the literal `m²` used by the empirical contour measure. -/
theorem finite_configuration_transfer_normalized {d : ℕ} (z : Fin d → ℂ)
    {r : ℝ} (hr : 0 < r) (hz : ∀ i j, i ≠ j → z i ≠ z j) (m : ℕ) :
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else realLogKernel (z i) (z j)) / (m : ℝ) ^ 2 ≥
    (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) / (m : ℝ) ^ 2 -
      (d : ℝ) / (m : ℝ) ^ 2 * Real.log (1 / r) := by
  have h := finite_configuration_transfer_distinct d z r hr hz
  have hscaled := div_le_div_of_nonneg_right h (sq_nonneg (m : ℝ))
  convert hscaled using 1
  ring

/-- At the paper's smoothing radius `m⁻²`, every diagonal term costs exactly
`2 log m`, as stated after v10 `eq:tube-circle`. -/
theorem circlePairEnergy_self_inverse_sq (z : ℂ) {m : ℝ} (hm : 0 < m) :
    circlePairEnergy z z (m ^ 2)⁻¹ = 2 * Real.log m := by
  rw [circlePairEnergy_self z (inv_pos.mpr (sq_pos_of_pos hm))]
  simp [Real.log_pow]

/-- The exact unnormalized smoothing cost `2 d log m` from v10 `sec-tube`.
The later tube-transfer theorem supplies the separate additive cost `300`. -/
theorem finite_configuration_transfer_inverse_sq {d : ℕ} (z : Fin d → ℂ)
    {m : ℝ} (hm : 0 < m) (hz : ∀ i j, i ≠ j → z i ≠ z j) :
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else realLogKernel (z i) (z j)) ≥
    (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) (m ^ 2)⁻¹) -
      2 * (d : ℝ) * Real.log m := by
  have h := finite_configuration_transfer_distinct d z (m ^ 2)⁻¹
    (inv_pos.mpr (sq_pos_of_pos hm)) hz
  have hlog : Real.log (1 / (m ^ 2)⁻¹) = 2 * Real.log m := by
    simp [Real.log_pow]
  rw [hlog] at h
  convert h using 1
  ring

/-- v10 `eq:tube-circle` on every nonzero Vandermonde configuration. -/
theorem l7_vandermonde_configuration_transfer : l7VandermondeConfigurationTransfer :=
  l7_vandermonde_transfer_of_distinct finite_configuration_transfer_distinct

/-- v10 `eq:tube-circle` with its required zero-Vandermonde collision branch. -/
theorem l7_collision_split : l7CollisionSplit :=
  l7_collision_split_of_distinct_transfer finite_configuration_transfer_distinct

end
end P0

/-- The L7 finite-configuration interface is discharged from the exact v10
circle smoothing estimate, retaining the collision/Vandermonde split. -/
theorem g_l7_finite_configuration_transfer : L7FiniteConfigurationTransfer :=
  P0.l7_collision_split

end Li2Lean
