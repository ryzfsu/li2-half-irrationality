/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateMain
import Li2Lean.P0.AlphaParamWeak

/-!
# Endpoint wiring with the unconditional integerizer

The integerizer input of `p0EndpointCertificate_of_rate_below_caSlack` is now a
theorem.  The remaining inputs of the endpoint certificate are exactly the
analytic estimate at `397/200` and the nonvanishing statement.
-/

namespace Li2Lean

theorem p0A2_endpoint_certificate_of_analytic_nonvanishing
    (hA : P0AnalyticEstimateAt ((397 / 200 : ℚ) : ℝ) p0A2CanonicalFamily)
    (hN : P0A2NonvanishingStatement p0A2CanonicalFamily) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) :=
  p0EndpointCertificate_of_rate_below_caSlack p0A2CanonicalFamily rfl (248 / 125)
    P0.Integerization.p0A2_integerizer_rate_lt_caSlack hA
    P0.Integerization.p0A2_integerizer_bound_at_unconditional hN

end Li2Lean

#print axioms Li2Lean.p0A2_endpoint_certificate_of_analytic_nonvanishing
