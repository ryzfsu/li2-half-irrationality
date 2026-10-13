/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Defs

/-!
# Circle averages and cell displacements for the cell inequality

Generic tools for `CellBound/CirclePieces.lean`:

* the logarithm is `1/c`-Lipschitz on `[c, ∞)`;
* a function that is `L`-Lipschitz from an endpoint of a cell differs from
  its endpoint value times the cell length by at most `L h^2 / 2`;
* integrals against `circleProbability` are angular averages, and the
  average of `log ‖x - w‖` over a circle is `log (max r ‖x - z‖)`;
* the same for the empirical circle measure `ν_δ`.
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

/-- The logarithm is `1/c`-Lipschitz on `[c, ∞)`. -/
theorem abs_log_sub_log_le {u v c : ℝ} (hc : 0 < c) (hu : c ≤ u) (hv : c ≤ v) :
    |Real.log u - Real.log v| ≤ |u - v| / c := by
  have hu0 : 0 < u := lt_of_lt_of_le hc hu
  have hv0 : 0 < v := lt_of_lt_of_le hc hv
  have h1 : Real.log u - Real.log v ≤ (u - v) / v := by
    rw [← Real.log_div hu0.ne' hv0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hu0 hv0)
    rw [sub_div, div_self hv0.ne']
    exact this
  have h2 : Real.log v - Real.log u ≤ (v - u) / u := by
    rw [← Real.log_div hv0.ne' hu0.ne']
    have := Real.log_le_sub_one_of_pos (div_pos hv0 hu0)
    rw [sub_div, div_self hu0.ne']
    exact this
  have h3 : (u - v) / v ≤ |u - v| / c :=
    (div_le_div_of_nonneg_right (le_abs_self _) hv0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hv)
  have h4 : (v - u) / u ≤ |u - v| / c := by
    have : v - u ≤ |u - v| := by rw [abs_sub_comm]; exact le_abs_self _
    exact (div_le_div_of_nonneg_right this hu0.le).trans
      (div_le_div_of_nonneg_left (abs_nonneg _) hc hu)
  rw [abs_le]
  constructor <;> linarith

/-- Cell against its left endpoint. -/
theorem cell_left_endpoint {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hL : ∀ x ∈ Set.Icc a b, |f x - f a| ≤ L * (x - a)) :
    |(∫ x in Set.Ico a b, f x) - (b - a) * f a| ≤ L * (b - a) ^ 2 / 2 := by
  have hint : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have heq : (∫ x in a..b, f x) - (b - a) * f a = ∫ x in a..b, (f x - f a) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp [intervalIntegral.integral_const, smul_eq_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hb : (∫ x in a..b, L * (x - a)) = L * (b - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x => x)]
    simp [integral_id]
    ring
  rw [← hb]
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · exact ae_of_all _ (fun x hx => by
      rw [Real.norm_eq_abs]; exact hL x ⟨hx.1.le, hx.2⟩)
  · exact (continuous_const.mul (continuous_id.sub continuous_const)).intervalIntegrable _ _

/-- Cell against its right endpoint. -/
theorem cell_right_endpoint {f : ℝ → ℝ} {a b L : ℝ} (hab : a ≤ b)
    (hf : ContinuousOn f (Set.Icc a b))
    (hL : ∀ x ∈ Set.Icc a b, |f x - f b| ≤ L * (b - x)) :
    |(∫ x in Set.Ico a b, f x) - (b - a) * f b| ≤ L * (b - a) ^ 2 / 2 := by
  have hint : IntervalIntegrable f volume a b := hf.intervalIntegrable_of_Icc hab
  rw [integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  have heq : (∫ x in a..b, f x) - (b - a) * f b = ∫ x in a..b, (f x - f b) := by
    rw [intervalIntegral.integral_sub hint intervalIntegrable_const]
    simp [intervalIntegral.integral_const, smul_eq_mul]
  rw [heq, ← Real.norm_eq_abs]
  have hb : (∫ x in a..b, L * (b - x)) = L * (b - a) ^ 2 / 2 := by
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_left (fun x => x)]
    simp [integral_id]
    ring
  rw [← hb]
  apply intervalIntegral.norm_integral_le_of_norm_le hab
  · exact ae_of_all _ (fun x hx => by
      rw [Real.norm_eq_abs]; exact hL x ⟨hx.1.le, hx.2⟩)
  · exact (continuous_const.mul (continuous_const.sub continuous_id)).intervalIntegrable _ _

/-! ## Circle probability -/

theorem integral_circleProbability_eq {f : ℂ → ℝ} (hf : StronglyMeasurable f)
    (z : ℂ) (r : ℝ) :
    ∫ w, f w ∂(circleProbability z r) =
      (2 * Real.pi)⁻¹ * ∫ t, f (circlePoint z r t) ∂circleAngleMeasure := by
  rw [circleProbability, integral_smul_measure,
    ENNReal.toReal_ofReal (inv_nonneg.mpr Real.two_pi_pos.le),
    integral_map (continuous_circlePoint z r).aemeasurable hf.aestronglyMeasurable,
    smul_eq_mul]

theorem integrable_circleProbability_of {f : ℂ → ℝ} (hf : StronglyMeasurable f)
    (z : ℂ) (r : ℝ)
    (h : Integrable (fun t => f (circlePoint z r t)) circleAngleMeasure) :
    Integrable f (circleProbability z r) := by
  rw [circleProbability]
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  exact (integrable_map_measure hf.aestronglyMeasurable
    (continuous_circlePoint z r).aemeasurable).mpr h

theorem measurable_log_norm_sub (x : ℂ) : Measurable (fun w : ℂ => Real.log ‖x - w‖) := by
  fun_prop

theorem integrable_log_norm_sub_circleProbability (x z : ℂ) (r : ℝ) :
    Integrable (fun w : ℂ => Real.log ‖x - w‖) (circleProbability z r) := by
  apply integrable_circleProbability_of (measurable_log_norm_sub x).stronglyMeasurable
  have h := (integrable_realLogKernel_circlePoint x z r).neg
  refine h.congr (ae_of_all _ (fun t => ?_))
  simp [realLogKernel]

/-- Circle average of `log ‖x - w‖`. -/
theorem integral_log_norm_sub_circleProbability (x z : ℂ) {r : ℝ} (hr : 0 < r) :
    ∫ w, Real.log ‖x - w‖ ∂(circleProbability z r) = Real.log (max r ‖x - z‖) := by
  rw [integral_circleProbability_eq (measurable_log_norm_sub x).stronglyMeasurable]
  have h := integral_realLogKernel_circlePoint x z hr
  simp only [realLogKernel, integral_neg] at h
  have h2 : (∫ t, Real.log ‖x - circlePoint z r t‖ ∂circleAngleMeasure) =
      Real.log (max r ‖x - z‖) * (2 * Real.pi) := by linarith
  rw [h2]
  field_simp

/-! ## The empirical circle measure -/

theorem integrable_log_norm_sub_circleEmpirical {d : ℕ} (z : Fin d → ℂ) (r : ℝ) (m : ℕ)
    (x : ℂ) :
    Integrable (fun w : ℂ => Real.log ‖x - w‖) (circleEmpiricalMeasure z r m) := by
  unfold circleEmpiricalMeasure
  apply Integrable.smul_measure _ ENNReal.ofReal_ne_top
  rw [Measure.sum_fintype]
  apply integrable_finsetSum_measure.mpr
  intro i _
  exact integrable_log_norm_sub_circleProbability x (z i) r

theorem integral_log_norm_sub_circleEmpirical {d : ℕ} (z : Fin d → ℂ) {r : ℝ}
    (hr : 0 < r) (m : ℕ) (x : ℂ) :
    ∫ w, Real.log ‖x - w‖ ∂(circleEmpiricalMeasure z r m) =
      (m : ℝ)⁻¹ * ∑ i : Fin d, Real.log (max r ‖x - z i‖) := by
  unfold circleEmpiricalMeasure
  rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg m)),
    Measure.sum_fintype, integral_finsetSum_measure (fun i _ =>
      integrable_log_norm_sub_circleProbability x (z i) r), smul_eq_mul]
  congr 1
  apply Finset.sum_congr rfl
  intro i _
  exact integral_log_norm_sub_circleProbability x (z i) hr

end

end Li2Lean.P0.CellBound
