/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Config
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

/-!
# Pinned one-body variation: `∫_E |(φ₂ - A₀)'| ≤ log 168`

Paper v13, `p0-analytic.tex` (pinned quadrature paragraph): "Direct integration
of the explicit derivatives gives `∫_E |(φ₂ - A₀)'| ≤ log 6 + 2 log 2 + log 7
= log 168`. Consequently pinned quadrature costs at most `m log 336`."

`PinnedFieldVariationBound` states this against the canonical `Config.phi`
(the base-2 contour field `φ₂`), `Config.A0` and `Config.p0SupportE = E`,
with the derivative taken by `deriv` of the real restriction.  The proof
evaluates both fields in closed form, shows `(φ₂ - A₀)'` is nonnegative on
`(1/4, 1]` and nonpositive on `[1, 5/4)`, and integrates exactly:
`∫_E |(φ₂ - A₀)'| = (1/2) log (84375/512) ≈ 2.5524 < log 168 ≈ 5.1240`.
-/

/-- The real restriction of `φ₂ - A₀`. -/
def pinnedFieldGap (x : ℝ) : ℝ := phi (x : ℂ) - A0 (x : ℂ)

/-- Paper v13: `∫_E |(φ₂ - A₀)'| ≤ log 168`, with `E = [1/4, 5/4]`. -/
def PinnedFieldVariationBound : Prop :=
  ∫ x in p0SupportE, |deriv pinnedFieldGap x| ≤ Real.log 168

/-- `t log t - t`, the primitive of `log` (Mathlib's `Real.log` is even). -/
def pvXlx (t : ℝ) : ℝ := t * Real.log t - t

theorem pvXlx_continuous : Continuous pvXlx := by
  unfold pvXlx
  exact Real.continuous_mul_log.sub continuous_id

theorem pvXlx_hasDerivAt {t : ℝ} (ht : t ≠ 0) :
    HasDerivAt pvXlx (Real.log t) t := by
  have h := (Real.hasDerivAt_mul_log ht).sub (hasDerivAt_id' t)
  rw [show Real.log t = Real.log t + 1 - 1 by ring]
  exact h

theorem pvXlx_neg (t : ℝ) : pvXlx (-t) = -pvXlx t := by
  unfold pvXlx
  rw [Real.log_neg_eq_log]
  ring

/-- `∫_a^b log |c - y| dy = X(c - a) - X(c - b)`. -/
theorem pv_integral_log_sub (c a b : ℝ) :
    (∫ y in a..b, Real.log |c - y|) = pvXlx (c - a) - pvXlx (c - b) := by
  have h := intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.log |x|)
    (a := a) (b := b) c
  rw [h]
  simp_rw [Real.log_abs]
  rw [integral_log]
  unfold pvXlx
  ring

/-- `∫_a^b log |c + s| ds = X(c + b) - X(c + a)`. -/
theorem pv_integral_log_add (c a b : ℝ) :
    (∫ s in a..b, Real.log |c + s|) = pvXlx (c + b) - pvXlx (c + a) := by
  have h := intervalIntegral.integral_comp_add_left (fun x : ℝ => Real.log |x|)
    (a := a) (b := b) c
  rw [h]
  simp_rw [Real.log_abs]
  rw [integral_log]
  unfold pvXlx
  ring

/-- Closed form of `φ₂ - A₀` on the real line. -/
def pinnedGapClosed (x : ℝ) : ℝ :=
  x * Real.log 2 + (pvXlx (x + 1 / 2) - pvXlx x) + 1 / 2 -
      (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) -
    ((pvXlx (x - 1 / 4) - pvXlx (x - 5 / 4)) + (pvXlx x - pvXlx (x - 2)))

theorem pinnedFieldGap_eq : pinnedFieldGap = pinnedGapClosed := by
  funext x
  unfold pinnedFieldGap pinnedGapClosed phi A0
  have hA : ∀ y : ℝ, Real.log ‖(x : ℂ) - (y : ℂ)‖ = Real.log |x - y| := by
    intro y
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have hP : ∀ s : ℝ, Real.log ‖(x : ℂ) + (s : ℂ)‖ = Real.log |x + s| := by
    intro s
    rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [hA, hP]
  rw [pv_integral_log_sub, pv_integral_log_sub, pv_integral_log_add]
  simp only [Complex.ofReal_re, add_zero]
  ring_nf

/-- The explicit derivative of `φ₂ - A₀` on the real line. -/
def pinnedGapDeriv (x : ℝ) : ℝ :=
  Real.log 2 + (Real.log (x + 1 / 2) - Real.log x) -
    ((Real.log (x - 1 / 4) - Real.log (x - 5 / 4)) +
      (Real.log x - Real.log (x - 2)))

theorem pinnedGapClosed_hasDerivAt {x : ℝ} (h0 : x ≠ 0) (h1 : x + 1 / 2 ≠ 0)
    (h2 : x - 1 / 4 ≠ 0) (h3 : x - 5 / 4 ≠ 0) (h4 : x - 2 ≠ 0) :
    HasDerivAt pinnedGapClosed (pinnedGapDeriv x) x := by
  have dX := pvXlx_hasDerivAt h0
  have dA := (pvXlx_hasDerivAt h1).comp_add_const x (1 / 2)
  have dB := (pvXlx_hasDerivAt h2).comp_sub_const x (1 / 4)
  have dC := (pvXlx_hasDerivAt h3).comp_sub_const x (5 / 4)
  have dD := (pvXlx_hasDerivAt h4).comp_sub_const x 2
  have dL : HasDerivAt (fun y : ℝ => y * Real.log 2) (Real.log 2) x := by
    simpa using (hasDerivAt_id x).mul_const (Real.log 2)
  have h := ((((dL.add (dA.sub dX)).add_const (1 / 2)).sub_const
    ((1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))).sub ((dB.sub dC).add (dX.sub dD)))
  unfold pinnedGapClosed pinnedGapDeriv
  exact h

theorem deriv_pinnedFieldGap {x : ℝ} (hx : x ∈ Set.Ioo (1 / 4 : ℝ) (5 / 4)) :
    deriv pinnedFieldGap x = pinnedGapDeriv x := by
  rw [pinnedFieldGap_eq]
  obtain ⟨h1, h2⟩ := hx
  exact (pinnedGapClosed_hasDerivAt (by linarith) (by linarith) (by linarith)
    (by linarith) (by linarith)).deriv

/-- Product form of the derivative on `(1/4, 5/4)`. -/
theorem pinnedGapDeriv_eq {x : ℝ} (hx : x ∈ Set.Ioo (1 / 4 : ℝ) (5 / 4)) :
    pinnedGapDeriv x =
      Real.log (2 * (x + 1 / 2) * (5 / 4 - x) * (2 - x)) -
        Real.log (x * x * (x - 1 / 4)) := by
  obtain ⟨h1, h2⟩ := hx
  have e1 : Real.log (x - 5 / 4) = Real.log (5 / 4 - x) := by
    rw [← Real.log_neg_eq_log]; ring_nf
  have e2 : Real.log (x - 2) = Real.log (2 - x) := by
    rw [← Real.log_neg_eq_log]; ring_nf
  unfold pinnedGapDeriv
  rw [e1, e2, Real.log_mul (by positivity) (by linarith),
    Real.log_mul (by positivity) (by linarith),
    Real.log_mul (by norm_num) (by linarith),
    Real.log_mul (by positivity) (by linarith),
    Real.log_mul (by linarith) (by linarith)]
  ring

theorem pinnedGapDeriv_nonneg {x : ℝ} (h1 : 1 / 4 < x) (h2 : x ≤ 1) :
    0 ≤ pinnedGapDeriv x := by
  rw [pinnedGapDeriv_eq ⟨h1, by linarith⟩, sub_nonneg]
  apply Real.log_le_log
  · have : 0 < x - 1 / 4 := by linarith
    have : 0 < x := by linarith
    positivity
  · nlinarith [mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1.le),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h2) (sub_nonneg.2 h1.le))
        (sub_nonneg.2 h1.le)]

theorem pinnedGapDeriv_nonpos {x : ℝ} (h1 : 1 ≤ x) (h2 : x < 5 / 4) :
    pinnedGapDeriv x ≤ 0 := by
  rw [pinnedGapDeriv_eq ⟨by linarith, h2⟩, sub_nonpos]
  apply Real.log_le_log
  · have : 0 < 5 / 4 - x := by linarith
    have : 0 < 2 - x := by linarith
    have : 0 < x + 1 / 2 := by linarith
    positivity
  · nlinarith [mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2.le),
      mul_nonneg (mul_nonneg (sub_nonneg.2 h1) (sub_nonneg.2 h2.le))
        (sub_nonneg.2 h1)]

theorem pv_log_affine_integrable (c a b : ℝ) :
    IntervalIntegrable (fun x => Real.log (x + c)) volume a b := by
  have h := (intervalIntegral.intervalIntegrable_log' (a := a + c) (b := b + c)).comp_add_right c
  simpa using h

theorem pinnedGapDeriv_integrable (a b : ℝ) :
    IntervalIntegrable pinnedGapDeriv volume a b := by
  have hl : ∀ c : ℝ, IntervalIntegrable (fun x => Real.log (x + c)) volume a b :=
    fun c => pv_log_affine_integrable c a b
  have h0 : IntervalIntegrable (fun x => Real.log x) volume a b :=
    intervalIntegral.intervalIntegrable_log'
  have hm : ∀ c : ℝ, IntervalIntegrable (fun x => Real.log (x - c)) volume a b := by
    intro c
    simpa [sub_eq_add_neg] using hl (-c)
  have h := ((intervalIntegrable_const (c := Real.log 2)).add
    ((hl (1 / 2)).sub h0)).sub (((hm (1 / 4)).sub (hm (5 / 4))).add (h0.sub (hm 2)))
  unfold pinnedGapDeriv
  exact h

theorem pinnedGapClosed_continuous : Continuous pinnedGapClosed := by
  have hX := pvXlx_continuous
  unfold pinnedGapClosed
  fun_prop

/-- The exact total variation of `φ₂ - A₀` on `E`. -/
theorem pinnedFieldVariation_eq :
    (∫ x in p0SupportE, |deriv pinnedFieldGap x|) =
      2 * pinnedGapClosed 1 - pinnedGapClosed (1 / 4) - pinnedGapClosed (5 / 4) := by
  unfold p0SupportE
  rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by norm_num)]
  have hI := pinnedGapDeriv_integrable
  -- integrability of `|deriv|` on each half, via agreement on the open interval
  have hL : IntervalIntegrable (fun x => |deriv pinnedFieldGap x|) volume (1 / 4) 1 := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
      (hI (1 / 4) 1)).congr_fun ?_ measurableSet_Ioo
    intro x hx
    show pinnedGapDeriv x = |deriv pinnedFieldGap x|
    rw [deriv_pinnedFieldGap ⟨hx.1, by linarith [hx.2]⟩,
      abs_of_nonneg (pinnedGapDeriv_nonneg hx.1 hx.2.le)]
  have hR : IntervalIntegrable (fun x => |deriv pinnedFieldGap x|) volume 1 (5 / 4) := by
    rw [intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)]
    refine ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
      (hI 1 (5 / 4)).neg).congr_fun ?_ measurableSet_Ioo
    intro x hx
    show -pinnedGapDeriv x = |deriv pinnedFieldGap x|
    rw [deriv_pinnedFieldGap ⟨by linarith [hx.1], hx.2⟩,
      abs_of_nonpos (pinnedGapDeriv_nonpos hx.1.le hx.2)]
  rw [← intervalIntegral.integral_add_adjacent_intervals hL hR]
  have eL : (∫ x in (1 / 4 : ℝ)..1, |deriv pinnedFieldGap x|) =
      ∫ x in (1 / 4 : ℝ)..1, pinnedGapDeriv x := by
    apply intervalIntegral.integral_congr_ae
    refine Filter.Eventually.of_forall (fun x hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    rw [deriv_pinnedFieldGap ⟨hx.1, by linarith [hx.2]⟩,
      abs_of_nonneg (pinnedGapDeriv_nonneg hx.1 hx.2)]
  have eR : (∫ x in (1 : ℝ)..(5 / 4), |deriv pinnedFieldGap x|) =
      ∫ x in (1 : ℝ)..(5 / 4), -pinnedGapDeriv x := by
    apply intervalIntegral.integral_congr_ae
    refine (Measure.ae_ne volume (5 / 4 : ℝ)).mono (fun x hne hx => ?_)
    rw [Set.uIoc_of_le (by norm_num)] at hx
    have hlt : x < 5 / 4 := lt_of_le_of_ne hx.2 hne
    rw [deriv_pinnedFieldGap ⟨by linarith [hx.1], hlt⟩,
      abs_of_nonpos (pinnedGapDeriv_nonpos hx.1.le hlt)]
  have hcont := pinnedGapClosed_continuous
  have ftc : ∀ a b : ℝ, a ≤ b → 1 / 4 ≤ a → b ≤ 5 / 4 →
      (∫ x in a..b, pinnedGapDeriv x) = pinnedGapClosed b - pinnedGapClosed a := by
    intro a b hab ha hb
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hab hcont.continuousOn
    · intro x hx
      exact pinnedGapClosed_hasDerivAt (by linarith [hx.1]) (by linarith [hx.1])
        (by linarith [hx.1]) (by linarith [hx.2]) (by linarith [hx.2])
    · exact hI a b
  rw [eL, eR, intervalIntegral.integral_neg, ftc (1 / 4) 1 (by norm_num) le_rfl (by norm_num),
    ftc 1 (5 / 4) (by norm_num) (by norm_num) le_rfl]
  ring

/-- Value of the exact variation: `(9/2)` coefficients in `log 2, log 3, log 5`. -/
theorem pinnedFieldVariation_value :
    2 * pinnedGapClosed 1 - pinnedGapClosed (1 / 4) - pinnedGapClosed (5 / 4) =
      -(9 / 2) * Real.log 2 + (3 / 2) * Real.log 3 + (5 / 2) * Real.log 5 := by
  have hdiv : ∀ p q : ℝ, 0 < p → 0 < q → Real.log (p / q) = Real.log p - Real.log q :=
    fun p q hp hq => Real.log_div hp.ne' hq.ne'
  have h4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; norm_num
  simp only [pinnedGapClosed, pvXlx]
  norm_num
  rw [hdiv 3 2 (by norm_num) (by norm_num), hdiv 1 2 (by norm_num) (by norm_num),
    hdiv 3 4 (by norm_num) (by norm_num), hdiv 1 4 (by norm_num) (by norm_num),
    hdiv 7 4 (by norm_num) (by norm_num), hdiv 5 4 (by norm_num) (by norm_num),
    Real.log_one, h4]
  ring

theorem pinnedFieldVariationBound : PinnedFieldVariationBound := by
  unfold PinnedFieldVariationBound
  rw [pinnedFieldVariation_eq, pinnedFieldVariation_value]
  have key : Real.log (3 * 5 ^ 5) ≤ Real.log (2 ^ 15 * 7 ^ 2) :=
    Real.log_le_log (by norm_num) (by norm_num)
  have h168 : Real.log 168 = 3 * Real.log 2 + Real.log 3 + Real.log 7 := by
    rw [show (168 : ℝ) = 2 ^ 3 * 3 * 7 by norm_num, Real.log_mul (by norm_num) (by norm_num),
      Real.log_mul (by norm_num) (by norm_num), Real.log_pow]
    norm_num
  rw [Real.log_mul (by norm_num) (by norm_num), Real.log_mul (by norm_num) (by norm_num),
    Real.log_pow, Real.log_pow, Real.log_pow] at key
  rw [h168]
  push_cast at key
  linarith

/-- The pinned quadrature cost constant: the variation `log 168` plus the
`J_m` endpoint loss `log 2` is the `log 336` consumed by `cStar`. -/
theorem pinnedQuadratureCost_log336 : Real.log 168 + Real.log 2 = Real.log 336 := by
  rw [← Real.log_mul (by norm_num) (by norm_num)]
  norm_num

end

end Li2Lean.P0.Config
