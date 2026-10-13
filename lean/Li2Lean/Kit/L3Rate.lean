/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces

open Filter
open Topology

namespace Li2Lean

/-- A one-piece constant profile for a positive ratio interval. -/
def constantPrimeAffineProfile (a b c : ℚ) (ha : 0 < a) (hab : a < b) :
    PrimeAffineProfile where
  pieces :=
    [{ lo := a
       hi := b
       slope := 0
       intercept := c
       lo_pos := ha
       lo_lt_hi := hab }]

/-- Evaluation of the one-piece profile, with the interface's half-open wall convention. -/
theorem constantPrimeAffineProfile_eval (a b c : ℚ) (ha : 0 < a) (hab : a < b)
    (x : ℝ) :
    (constantPrimeAffineProfile a b c ha hab).eval x =
      if (a : ℝ) ≤ x ∧ x < (b : ℝ) then (c : ℝ) else 0 := by
  simp [constantPrimeAffineProfile, PrimeAffineProfile.eval]

/-- The Lebesgue integral of the constant profile is its interval width times its height. -/
theorem constantPrimeAffineProfile_integral (a b c : ℚ) (ha : 0 < a) (hab : a < b) :
    (∫ t : ℝ, (constantPrimeAffineProfile a b c ha hab).eval t) =
      (c : ℝ) * ((b : ℝ) - (a : ℝ)) := by
  have heq :
      (fun t : ℝ => (constantPrimeAffineProfile a b c ha hab).eval t) =
        Set.indicator (Set.Ico (a : ℝ) (b : ℝ)) (fun _ : ℝ => (c : ℝ)) := by
    funext t
    by_cases h : (a : ℝ) ≤ t ∧ t < (b : ℝ)
    · simp [constantPrimeAffineProfile, PrimeAffineProfile.eval, h]
    · simp [constantPrimeAffineProfile, PrimeAffineProfile.eval,
        h]
  rw [heq, MeasureTheory.integral_indicator_const _ measurableSet_Ico]
  have hab' : (a : ℝ) ≤ (b : ℝ) := by exact_mod_cast hab.le
  simp [Real.volume_real_Ico, max_eq_left (sub_nonneg.mpr hab'), smul_eq_mul,
    mul_comm]

/-- Rescaling the explicit Chebyshev PNT input by a fixed positive factor. -/
theorem hPNT_theta_scaled (hpnt : hPNT) (c : ℝ) (hc : 0 < c) :
    Tendsto (fun x : ℝ => Chebyshev.theta (c * x) / x) atTop (𝓝 c) := by
  have hscale : Tendsto (fun x : ℝ => c * x) atTop atTop :=
    Filter.tendsto_id.const_mul_atTop hc
  have hratio : Tendsto
      (fun x : ℝ => Chebyshev.theta (c * x) / (c * x)) atTop (𝓝 1) :=
    hpnt.comp hscale
  have hconst : Tendsto (fun _ : ℝ => c) atTop (𝓝 c) := tendsto_const_nhds
  have hprod := hratio.mul hconst
  have hfun :
      (fun x : ℝ => Chebyshev.theta (c * x) / x) =
        (fun x : ℝ => Chebyshev.theta (c * x) / (c * x) * c) := by
    funext x
    by_cases hx : x = 0
    · subst x
      simp [Chebyshev.theta]
    · field_simp [hx, hc.ne']
  rw [hfun]
  simpa using hprod

/--
The weighted prime mass in the Chebyshev interval `(a*x, b*x]` has its
expected first-order limit under `hPNT`. This interval increment is a single
constant-weight rate leaf; it does not establish the general affine-profile
limit `L3WeightedPrimeLimit`.
-/
theorem hPNT_theta_interval_rate (hpnt : hPNT) (a b : ℝ)
    (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun x : ℝ => (Chebyshev.theta (b * x) - Chebyshev.theta (a * x)) / x)
      atTop (𝓝 (b - a)) := by
  have hb := hPNT_theta_scaled hpnt b (lt_trans ha hab)
  have ha' := hPNT_theta_scaled hpnt a ha
  have hdiff : Tendsto
      (fun x : ℝ => Chebyshev.theta (b * x) / x -
        Chebyshev.theta (a * x) / x)
      atTop (𝓝 (b - a)) := by
    simpa using hb.sub ha'
  have heq :
      (fun x : ℝ =>
        (Chebyshev.theta (b * x) - Chebyshev.theta (a * x)) / x) =ᶠ[atTop]
      (fun x : ℝ => Chebyshev.theta (b * x) / x -
        Chebyshev.theta (a * x) / x) := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    field_simp [hx.ne']
  exact hdiff.congr' heq.symm

/--
The corresponding one-piece constant profile has the matching Chebyshev
proxy rate. The proxy is deliberately written with a theta increment rather
than `weightedPrimeSum`; the finite-sum identification and endpoint audit
remain separate obligations for the full L3 interface.
-/
theorem hPNT_constant_profile_theta_rate (hpnt : hPNT)
    (a b c : ℚ) (ha : 0 < a) (hab : a < b) :
    Tendsto
      (fun x : ℝ => (c : ℝ) *
        (Chebyshev.theta ((b : ℝ) * x) - Chebyshev.theta ((a : ℝ) * x)) / x)
      atTop
      (𝓝 (∫ t : ℝ, (constantPrimeAffineProfile a b c ha hab).eval t)) := by
  have hmass := hPNT_theta_interval_rate hpnt (a : ℝ) (b : ℝ)
    (by exact_mod_cast ha) (by exact_mod_cast hab)
  have hc : Tendsto (fun _ : ℝ => (c : ℝ)) atTop (𝓝 (c : ℝ)) := tendsto_const_nhds
  have hscaled := hc.mul hmass
  rw [constantPrimeAffineProfile_integral a b c ha hab]
  simpa only [div_eq_mul_inv, mul_assoc] using hscaled

end Li2Lean
