/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.LogSegment
import Mathlib.MeasureTheory.Integral.Prod

open MeasureTheory

namespace Li2Lean.LogSegment

noncomputable section

/-- The literal v10 second primitive, with its continuous value `H(0)=0`. -/
def secondPrimitive (v : ℝ) : ℝ :=
  v ^ 2 * Real.log |v| / 2 - 3 * v ^ 2 / 4

@[simp] theorem secondPrimitive_zero : secondPrimitive 0 = 0 := by
  simp [secondPrimitive]

theorem secondPrimitive_eq (v : ℝ) :
    secondPrimitive v = v * (v * Real.log v) / 2 - (3 / 4 : ℝ) * v ^ 2 := by
  simp only [secondPrimitive, Real.log_abs]
  ring

theorem continuous_secondPrimitive : Continuous secondPrimitive := by
  simp_rw [funext secondPrimitive_eq]
  exact ((continuous_id.mul Real.continuous_mul_log).div_const 2).sub
    ((continuous_id.pow 2).const_mul (3 / 4))

/-- The second primitive is differentiated away from zero. Its continuous
value at zero is sufficient for the endpoint form of the fundamental theorem. -/
theorem hasDerivAt_secondPrimitive {v : ℝ} (hv : v ≠ 0) :
    HasDerivAt secondPrimitive (primitive v) v := by
  have h := (((hasDerivAt_id v).mul (Real.hasDerivAt_mul_log hv)).div_const 2).sub
    (((hasDerivAt_id v).pow 2).const_mul (3 / 4 : ℝ))
  convert! h using 1
  · funext x
    exact secondPrimitive_eq x
  · rw [primitive_eq]
    simp only [id_eq]
    ring

/-- The exact integral of `F` from zero, including a negative upper endpoint. -/
theorem integral_primitive_from_zero (b : ℝ) :
    (∫ x in (0 : ℝ)..b, primitive x) = secondPrimitive b := by
  by_cases hb : 0 ≤ b
  · have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb
      continuous_secondPrimitive.continuousOn
      (fun x hx => hasDerivAt_secondPrimitive (ne_of_gt hx.1))
      (continuous_primitive.intervalIntegrable 0 b)
    simpa only [secondPrimitive_zero, sub_zero] using h
  · have hb' : b ≤ 0 := le_of_not_ge hb
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hb'
      continuous_secondPrimitive.continuousOn
      (fun x hx => hasDerivAt_secondPrimitive (ne_of_lt hx.2))
      (continuous_primitive.intervalIntegrable b 0)
    rw [intervalIntegral.integral_symm]
    simpa only [secondPrimitive_zero, zero_sub, neg_neg] using congrArg Neg.neg h

/-- The endpoint formula for integrating `F`, valid across zero and without
an ordering hypothesis on the endpoints. -/
theorem integral_primitive (a b : ℝ) :
    (∫ x in a..b, primitive x) = secondPrimitive b - secondPrimitive a := by
  have h := intervalIntegral.integral_add_adjacent_intervals
    (continuous_primitive.intervalIntegrable (μ := volume) 0 a)
    (continuous_primitive.intervalIntegrable (μ := volume) a b)
  rw [integral_primitive_from_zero, integral_primitive_from_zero] at h
  linarith

/-- Exact logarithmic rectangle energy, including overlapping or touching
segments and all zero differences. This is the `H` rule in v10 C-A. -/
theorem integral_integral_log_abs_sub (a b c d : ℝ) :
    (∫ x in a..b, ∫ y in c..d, Real.log |x - y|) =
      secondPrimitive (b - c) - secondPrimitive (a - c) -
        secondPrimitive (b - d) + secondPrimitive (a - d) := by
  simp_rw [integral_log_abs_sub]
  have hc : Continuous (fun x : ℝ => primitive (x - c)) :=
    continuous_primitive.comp (continuous_id.sub continuous_const)
  have hd : Continuous (fun x : ℝ => primitive (x - d)) :=
    continuous_primitive.comp (continuous_id.sub continuous_const)
  rw [intervalIntegral.integral_sub (hc.intervalIntegrable a b) (hd.intervalIntegrable a b)]
  rw [intervalIntegral.integral_comp_sub_right primitive c,
    intervalIntegral.integral_comp_sub_right primitive d,
    integral_primitive, integral_primitive]
  ring

/-- Primitive of the absolute logarithm, used only to prove absolute
integrability on rectangles before applying Fubini. -/
def absLogPrimitive (v : ℝ) : ℝ := ∫ x in (0 : ℝ)..v, ‖Real.log x‖

theorem continuous_absLogPrimitive : Continuous absLogPrimitive := by
  exact intervalIntegral.continuous_primitive
    (fun a b => (intervalIntegral.intervalIntegrable_log' (a := a) (b := b)).norm) 0

/-- The integral of the absolute logarithm over a translated half-open cell
is a difference of continuous primitives. -/
theorem integral_Ico_norm_log_abs_sub (x : ℝ) {c d : ℝ} (hcd : c ≤ d) :
    (∫ y in Set.Ico c d, ‖Real.log |x - y|‖) =
      absLogPrimitive (x - c) - absLogPrimitive (x - d) := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hcd]
  simp_rw [Real.log_abs]
  rw [intervalIntegral.integral_comp_sub_left (fun z => ‖Real.log z‖) x]
  have h := intervalIntegral.integral_add_adjacent_intervals
    ((intervalIntegral.intervalIntegrable_log' (a := 0) (b := x - d)).norm)
    ((intervalIntegral.intervalIntegrable_log' (a := x - d) (b := x - c)).norm)
  unfold absLogPrimitive
  linarith

/-- Absolute integrability of the real log kernel on every bounded rectangle.
There is no disjointness or endpoint-separation premise. -/
theorem integrable_log_abs_sub_rectangle {a b c d : ℝ} (hcd : c ≤ d) :
    Integrable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|)
      ((volume.restrict (Set.Ico a b)).prod (volume.restrict (Set.Ico c d))) := by
  have hsub : Measurable (fun p : ℝ × ℝ => p.1 - p.2) :=
    measurable_fst.sub measurable_snd
  have hm : Measurable (fun p : ℝ × ℝ => Real.log |p.1 - p.2|) := by
    simpa only [Real.log_abs, Function.comp_def] using Real.measurable_log.comp hsub
  apply (integrable_prod_iff hm.aestronglyMeasurable).mpr
  constructor
  · filter_upwards [] with x
    exact integrableOn_Ico_log_abs_sub x hcd
  · have heq : (fun x => ∫ y in Set.Ico c d, ‖Real.log |x - y|‖) =
        (fun x => absLogPrimitive (x - c) - absLogPrimitive (x - d)) := by
      funext x
      exact integral_Ico_norm_log_abs_sub x hcd
    rw [heq]
    exact (((continuous_absLogPrimitive.comp (continuous_id.sub continuous_const)).sub
      (continuous_absLogPrimitive.comp (continuous_id.sub continuous_const))).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self

/-- The half-open-cell product measure has exactly the same endpoint energy
as the oriented rectangle integral. -/
theorem integral_log_abs_sub_rectangle {a b c d : ℝ} (hab : a ≤ b) (hcd : c ≤ d) :
    (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂((volume.restrict (Set.Ico a b)).prod (volume.restrict (Set.Ico c d)))) =
      secondPrimitive (b - c) - secondPrimitive (a - c) -
        secondPrimitive (b - d) + secondPrimitive (a - d) := by
  rw [integral_prod _ (integrable_log_abs_sub_rectangle hcd)]
  simp_rw [integral_Ico_log_abs_sub _ hcd]
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab]
  rw [← integral_integral_log_abs_sub]
  simp_rw [integral_log_abs_sub]


/-- Integrating one endpoint primitive over an actual half-open cell. -/
theorem integral_Ico_primitive_sub (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Ico a b, primitive (x - c)) =
      secondPrimitive (b - c) - secondPrimitive (a - c) := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_sub_right primitive c, integral_primitive]

/-- The reflected endpoint primitive for pinned-frequency interaction. -/
theorem integral_Ico_primitive_add (c : ℝ) {a b : ℝ} (hab : a ≤ b) :
    (∫ x in Set.Ico a b, primitive (x + c)) =
      secondPrimitive (b + c) - secondPrimitive (a + c) := by
  rw [MeasureTheory.integral_Ico_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
    intervalIntegral.integral_comp_add_right primitive c, integral_primitive]

end

end Li2Lean.LogSegment
