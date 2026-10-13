/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigRealTail
import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

/-!
  The frequency mixed-cell estimate used in the finite configuration
  envelope.  This file first records the analytic part of the estimate:
  the entropy field is increasing on the positive-variation interval and
  decreasing afterwards.  The endpoint variation is exactly `log 2 / 2`.
  The finite-family sum is kept as a separate theorem so that the discrete
  cell bookkeeping is visible in the final coefficient proof.
-/

theorem psi_continuous : Continuous Config.psi := by
  unfold Config.psi
  have hmul : Continuous (fun x : ℝ => x * Real.log x) := Real.continuous_mul_log
  have hshift : Continuous (fun x : ℝ =>
      (x - (1 / 2 : ℝ)) * Real.log (x - (1 / 2 : ℝ))) := by
    exact hmul.comp (continuous_id.sub continuous_const)
  have hlin : Continuous (fun x : ℝ => x * Real.log 2) :=
    continuous_id.mul continuous_const
  exact ((hmul.sub hshift).sub continuous_const).sub hlin

private theorem psi_deriv_nonneg_half_one {t : ℝ}
    (ht : (1 / 2 : ℝ) < t) (ht1 : t ≤ 1) :
    0 ≤ deriv Config.psi t := by
  have hderiv := (ConfigRealTail.psi_hasDerivAt ht).deriv
  rw [hderiv]
  have ht0 : 0 < t := by linarith
  have hv0 : 0 < t - 1 / 2 := by linarith
  have hratio : 1 ≤ t / (t - 1 / 2) := by
    apply (le_div_iff₀ hv0).2
    linarith
  have hratio2 : (2 : ℝ) ≤ t / (t - 1 / 2) := by
    apply (le_div_iff₀ hv0).2
    linarith
  have hlog : Real.log 2 ≤ Real.log (t / (t - 1 / 2)) := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by norm_num)
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact hratio2
  rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hv0)] at hlog
  linarith

private theorem psi_deriv_nonpos_one_inf {t : ℝ} (ht : (1 : ℝ) < t) :
    deriv Config.psi t ≤ 0 := by
  have hderiv := (ConfigRealTail.psi_hasDerivAt
    (by linarith : (1 / 2 : ℝ) < t)).deriv
  rw [hderiv]
  have ht0 : 0 < t := by linarith
  have hv0 : 0 < t - 1 / 2 := by linarith
  have hratio : t / (t - 1 / 2) ≤ (2 : ℝ) := by
    apply (div_le_iff₀ hv0).2
    linarith
  have hlog : Real.log (t / (t - 1 / 2)) ≤ Real.log 2 := by
    apply Real.strictMonoOn_log.monotoneOn
    · exact Set.mem_Ioi.mpr (by positivity)
    · exact Set.mem_Ioi.mpr (by norm_num)
    · exact hratio
  rw [Real.log_div (ne_of_gt ht0) (ne_of_gt hv0)] at hlog
  linarith

theorem psi_monotoneOn_half_one :
    MonotoneOn Config.psi (Set.Icc (1 / 2 : ℝ) 1) := by
  apply monotoneOn_of_deriv_nonneg (convex_Icc _ _)
  · exact psi_continuous.continuousOn
  · intro x hx
    exact (ConfigRealTail.psi_hasDerivAt (by
      have hx' : x ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
        simpa only [interior_Icc] using hx
      exact hx'.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioo (1 / 2 : ℝ) 1 := by
      simpa only [interior_Icc] using hx
    exact psi_deriv_nonneg_half_one hx'.1 hx'.2.le

theorem psi_antitoneOn_one_top :
    AntitoneOn Config.psi (Set.Ici (1 : ℝ)) := by
  apply antitoneOn_of_deriv_nonpos (convex_Ici _)
  · exact psi_continuous.continuousOn
  · intro x hx
    have hxt : (1 / 2 : ℝ) < x := by
      have hx' : x ∈ Set.Ioi (1 : ℝ) := by
        simpa only [interior_Ici] using hx
      exact lt_trans (by norm_num) hx'
    exact (ConfigRealTail.psi_hasDerivAt hxt).differentiableAt.differentiableWithinAt
  · intro x hx
    have hx' : x ∈ Set.Ioi (1 : ℝ) := by
      simpa only [interior_Ici] using hx
    exact psi_deriv_nonpos_one_inf hx'

theorem psi_half_value : Config.psi (1 / 2 : ℝ) = -(Real.log 2) / 2 := by
  unfold Config.psi
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hcombo : Real.log (1 / 2 : ℝ) * (-1 / 2 : ℝ) +
      Real.log 2 * (-1 / 2 : ℝ) = 0 := by
    rw [hlog]
    ring
  simp only [sub_self, Real.log_zero, zero_mul, mul_zero]
  norm_num at hcombo ⊢
  ring

theorem psi_one_value : Config.psi 1 = 0 := by
  unfold Config.psi
  have hlog : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, Real.log_inv]
  have hcombo : Real.log (1 / 2 : ℝ) * (-1 / 2 : ℝ) +
      Real.log 2 * (-1 / 2 : ℝ) = 0 := by
    rw [hlog]
    ring
  simp only [Real.log_one, sub_self, Real.log_zero, zero_mul, mul_zero]
  norm_num at hcombo ⊢
  linarith

theorem psi_positive_variation_half_one :
    Config.psi 1 - Config.psi (1 / 2 : ℝ) = Real.log 2 / 2 := by
  rw [psi_one_value, psi_half_value]
  ring

/-! A single right-endpoint cell has no larger error than its endpoint
variation on an increasing interval, and has nonpositive error on a
decreasing interval.  These are the analytic mixed-cell inequalities used
by the finite-family estimate. -/

theorem psi_right_endpoint_error_le_of_monotone
    {a b : ℝ} (hab : a ≤ b) (hmono : MonotoneOn Config.psi (Set.Icc a b)) :
    (b - a) * Config.psi b - (∫ t in a..b, Config.psi t) ≤
      (b - a) * (Config.psi b - Config.psi a) := by
  have hcont : ContinuousOn Config.psi (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using psi_continuous.continuousOn
  have hint : IntervalIntegrable Config.psi volume a b :=
    hcont.intervalIntegrable
  have hlow : (∫ t in a..b, Config.psi a) ≤
      (∫ t in a..b, Config.psi t) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
    intro x hx
    apply hmono
    · exact ⟨le_rfl, hab⟩
    · exact hx
    · exact hx.1
  rw [intervalIntegral.integral_const] at hlow
  norm_num [smul_eq_mul] at hlow
  linarith

theorem psi_right_endpoint_error_nonpos_of_antitone
    {a b : ℝ} (hab : a ≤ b) (hmono : AntitoneOn Config.psi (Set.Icc a b)) :
    (b - a) * Config.psi b - (∫ t in a..b, Config.psi t) ≤ 0 := by
  have hcont : ContinuousOn Config.psi (Set.uIcc a b) := by
    simpa [Set.uIcc_of_le hab] using psi_continuous.continuousOn
  have hint : IntervalIntegrable Config.psi volume a b :=
    hcont.intervalIntegrable
  have hlow : (∫ t in a..b, Config.psi b) ≤
      (∫ t in a..b, Config.psi t) := by
    apply intervalIntegral.integral_mono_on hab intervalIntegrable_const hint
    intro x hx
    apply hmono
    · exact hx
    · exact ⟨hab, le_rfl⟩
    · exact hx.2
  rw [intervalIntegral.integral_const] at hlow
  norm_num [smul_eq_mul] at hlow
  linarith

def frequencyEndpointError (m r : ℕ) : ℝ :=
  (m : ℝ) * Config.psi ((r : ℝ) / (m : ℝ)) -
    (m : ℝ) ^ 2 *
      (∫ t in ((r - 1 : ℕ) : ℝ) / (m : ℝ)..(r : ℝ) / (m : ℝ),
        Config.psi t)

private lemma frequency_cell_endpoints {m r : ℕ} (hm : 0 < m) (hr : 0 < r) :
    ((r - 1 : ℕ) : ℝ) / (m : ℝ) ≤ (r : ℝ) / (m : ℝ) ∧
      (r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ) = 1 / (m : ℝ) := by
  have hrsub : r - 1 + 1 = r := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hr.ne')
  have hcast : ((r - 1 : ℕ) : ℝ) + 1 = (r : ℝ) := by
    exact_mod_cast hrsub
  constructor
  · apply div_le_div_of_nonneg_right _ (by positivity)
    linarith
  · field_simp
    linarith

theorem frequencyEndpointError_le_variation
    {m r : ℕ} (hm : 0 < m) (h4 : 4 ∣ m)
    (hr : m / 2 + 1 ≤ r) (hrm : r ≤ m) :
    frequencyEndpointError m r ≤
      (m : ℝ) * (Config.psi ((r : ℝ) / (m : ℝ)) -
        Config.psi (((r - 1 : ℕ) : ℝ) / (m : ℝ))) := by
  have hrpos : 0 < r := by omega
  obtain ⟨hab, hwidth⟩ := frequency_cell_endpoints hm hrpos
  let a : ℝ := ((r - 1 : ℕ) : ℝ) / (m : ℝ)
  let b : ℝ := (r : ℝ) / (m : ℝ)
  have ha : (1 / 2 : ℝ) ≤ a := by
    have hnat : m / 2 ≤ r - 1 := by omega
    obtain ⟨k, hk⟩ := h4
    have hnat2 : m ≤ 2 * (r - 1) := by omega
    have hcast : (m : ℝ) ≤ 2 * ((r - 1 : ℕ) : ℝ) := by
      exact_mod_cast hnat2
    dsimp [a]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < m)).2
    nlinarith
  have hb : b ≤ 1 := by
    dsimp [b]
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < m)).2
    have hcast : (r : ℝ) ≤ (m : ℝ) := by exact_mod_cast hrm
    nlinarith
  have hmono : MonotoneOn Config.psi (Set.Icc a b) := by
    exact psi_monotoneOn_half_one.mono (by
      intro x hx
      exact ⟨le_trans ha hx.1, le_trans hx.2 hb⟩)
  have hbase := psi_right_endpoint_error_le_of_monotone hab hmono
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hwidth' :
      (r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ) = 1 / (m : ℝ) := hwidth
  have hm2 := mul_le_mul_of_nonneg_left hbase (sq_nonneg (m : ℝ))
  have hrewrite : frequencyEndpointError m r = (m : ℝ) ^ 2 *
        ((r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ)) *
          Config.psi ((r : ℝ) / (m : ℝ)) -
        (m : ℝ) ^ 2 * (∫ t in ((r - 1 : ℕ) : ℝ) / (m : ℝ)..
          (r : ℝ) / (m : ℝ), Config.psi t) := by
    unfold frequencyEndpointError
    rw [hwidth']
    field_simp [ne_of_gt hmpos]
  rw [hrewrite]
  have hm2' :
      (m : ℝ) ^ 2 * ((r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ)) *
          Config.psi ((r : ℝ) / (m : ℝ)) -
        (m : ℝ) ^ 2 * (∫ t in ((r - 1 : ℕ) : ℝ) / (m : ℝ)..
          (r : ℝ) / (m : ℝ), Config.psi t) ≤
      (m : ℝ) ^ 2 *
        (((r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ)) *
          (Config.psi ((r : ℝ) / (m : ℝ)) -
            Config.psi (((r - 1 : ℕ) : ℝ) / (m : ℝ)))) := by
    convert hm2 using 1 <;> ring
  calc
    _ ≤ (m : ℝ) ^ 2 *
        (((r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ)) *
          (Config.psi ((r : ℝ) / (m : ℝ)) -
            Config.psi (((r - 1 : ℕ) : ℝ) / (m : ℝ)))) := hm2'
    _ = (m : ℝ) * (Config.psi ((r : ℝ) / (m : ℝ)) -
        Config.psi (((r - 1 : ℕ) : ℝ) / (m : ℝ))) := by
          rw [hwidth']
          field_simp [ne_of_gt hmpos]

theorem frequencyEndpointError_nonpos_of_antitone
    {m r : ℕ} (hm : 0 < m) (hr : m < r) :
    frequencyEndpointError m r ≤ 0 := by
  have hrpos : 0 < r := by omega
  obtain ⟨hab, hwidth⟩ := frequency_cell_endpoints hm hrpos
  let a : ℝ := ((r - 1 : ℕ) : ℝ) / (m : ℝ)
  let b : ℝ := (r : ℝ) / (m : ℝ)
  have ha : (1 : ℝ) ≤ a := by
    have hnat : m ≤ r - 1 := by omega
    dsimp [a]
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < m)).2
    have hcast : (m : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by exact_mod_cast hnat
    nlinarith
  have hmono : AntitoneOn Config.psi (Set.Icc a b) := by
    exact psi_antitoneOn_one_top.mono (by
      intro x hx
      exact le_trans ha hx.1)
  have hbase := psi_right_endpoint_error_nonpos_of_antitone hab hmono
  have hmpos : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  have hm2 := mul_le_mul_of_nonneg_left hbase (sq_nonneg (m : ℝ))
  have hrewrite : frequencyEndpointError m r = (m : ℝ) ^ 2 *
        ((r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ)) *
          Config.psi ((r : ℝ) / (m : ℝ)) -
        (m : ℝ) ^ 2 * (∫ t in ((r - 1 : ℕ) : ℝ) / (m : ℝ)..
          (r : ℝ) / (m : ℝ), Config.psi t) := by
    unfold frequencyEndpointError
    rw [hwidth]
    field_simp [ne_of_gt hmpos]
  rw [hrewrite]
  have hm2' :
      (m : ℝ) ^ 2 * ((r : ℝ) / (m : ℝ) - ((r - 1 : ℕ) : ℝ) / (m : ℝ)) *
          Config.psi ((r : ℝ) / (m : ℝ)) -
        (m : ℝ) ^ 2 * (∫ t in ((r - 1 : ℕ) : ℝ) / (m : ℝ)..
          (r : ℝ) / (m : ℝ), Config.psi t) ≤ (m : ℝ) ^ 2 * 0 := by
    convert hm2 using 1 <;> ring
  exact hm2'.trans_eq (by ring)

end

end Li2Lean.P0.Config

#print axioms Li2Lean.P0.Config.psi_monotoneOn_half_one
#print axioms Li2Lean.P0.Config.psi_antitoneOn_one_top
#print axioms Li2Lean.P0.Config.psi_positive_variation_half_one
#print axioms Li2Lean.P0.Config.psi_right_endpoint_error_le_of_monotone
#print axioms Li2Lean.P0.Config.frequencyEndpointError_le_variation
#print axioms Li2Lean.P0.Config.frequencyEndpointError_nonpos_of_antitone
