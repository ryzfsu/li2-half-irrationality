/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateFinite
import Li2Lean.P0.IntegerizationS08Lift

/-!
# Unconditional P0 integerizer bound at `a = 2`

The settled primewise integerizer of `IntegerizationSettledPrimeLimit` with the
concrete moving-prime exponent `p0RateW`:

* two-adic feature divisibility: `S08.p0A2_feature_divisibility`;
* odd-prime coefficient valuations: `p0Rate_odd_valuation`;
* finite prime-sum majorant: `p0Rate_finite_profile`.

The resulting rate `248/125` is below the C-A slack `397/200`, which is the
input of `p0EndpointCertificate_of_rate_below_caSlack`.
-/

namespace Li2Lean.P0.Integerization

theorem p0A2_actual_two_feature (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    P0A2ActualTwoFeatureDivisibility m := by
  obtain ⟨P, hdiv, hmap⟩ := S08.p0A2_feature_divisibility p0A2CanonicalFamily rfl m hm h4
  exact p0A2ActualTwoFeatureDivisibility_of_real_witness m h4 P hdiv hmap

/-- The P0 integerizer bound for the canonical `a = 2` family, with no premise. -/
theorem p0A2_integerizer_bound_at_unconditional :
    P0IntegerizerBoundAt p0A2CanonicalFamily (248 / 125 : ℝ) :=
  p0A2_integerizer_bound_at_of_finite_profile p0RateW p0RateWallCount
    p0A2_actual_two_feature (fun m hm h4 => p0Rate_odd_valuation m hm h4)
    p0Rate_finite_profile

theorem p0A2_integerizer_rate_lt_caSlack : (248 / 125 : ℝ) < ((397 / 200 : ℚ) : ℝ) := by
  norm_num

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0A2_actual_two_feature
#print axioms Li2Lean.P0.Integerization.p0A2_integerizer_bound_at_unconditional
#print axioms Li2Lean.P0.Integerization.p0A2_integerizer_rate_lt_caSlack
