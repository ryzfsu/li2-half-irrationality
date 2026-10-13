/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Main
import Li2Lean.P0.EnvMain
import Li2Lean.P0.RateEndpoint
import Li2Lean.Main

namespace Li2Lean

open P0.CoefficientAssembly

/- The cell and integerizer producers are unconditional.  This is the final
   analytic interface: only the signed coefficient envelope remains visible. -/
theorem li2_half_irrational_of_envelope_v2
    (henv : P0SignedCoefficientEnvelope) :
    Irrational (li2InvValue (2 : ℤ)) := by
  have hA :
      P0AnalyticEstimateAt ((397 / 200 : ℚ) : ℝ) p0A2CanonicalFamily :=
    p0AnalyticEstimateAt_all_of_envelope henv p0A2CanonicalFamily
  obtain ⟨certificate⟩ :=
    p0EndpointCertificate_of_rate_below_caSlack
      p0A2CanonicalFamily rfl (248 / 125 : ℝ)
      P0.Integerization.p0A2_integerizer_rate_lt_caSlack hA
      P0.Integerization.p0A2_integerizer_bound_at_unconditional
      (P0.ScaledLucas.p0A2_nonvanishing p0A2CanonicalFamily)
  exact li2_half_irrational_of_endpoint_certificate certificate

/- The preceding producer discharges the last visible premise. -/
theorem li2_half_irrational_unconditional :
    Irrational (li2InvValue (2 : ℤ)) :=
  li2_half_irrational_of_envelope_v2
    P0.CoefficientAssembly.p0SignedCoefficientEnvelope_proved

end Li2Lean

#print axioms Li2Lean.li2_half_irrational_of_envelope_v2
#print axioms Li2Lean.li2_half_irrational_unconditional
