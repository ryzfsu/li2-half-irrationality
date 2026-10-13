/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.L1
import Li2Lean.P0.Source
import Li2Lean.P0.Config
import Li2Lean.P0.JoukowskiPoleRange
import Li2Lean.P0.TwoPreimageResidue
import Li2Lean.P0.AlphaParam
import Li2Lean.P0.NonvanishingScaledLucas

namespace Li2Lean

/-- The fixed `a = 2` family from the literal determinant definition. -/
noncomputable def p0A2CanonicalFamily : P0Family where
  a := 2
  base_abs_ge_two := by norm_num
  G := fun m => (p0CanonicalPolynomial 2 m).map (algebraMap ℚ ℝ)
  G_source := by
    intro m hm
    rfl

/-- The source normalization at `a = 2` is the target series. -/
theorem sourceBeta_two_eq_li2InvValue_two :
    sourceBeta 2 = li2InvValue (2 : ℤ) := by
  unfold sourceBeta li2InvValue
  apply tsum_congr
  intro k
  norm_num

/-- The endpoint criterion gives the half-value conclusion from its full certificate. -/
theorem li2_half_irrational_of_endpoint_certificate
    (certificate : EndpointCertificate (li2InvValue (2 : ℤ))) :
    Irrational (li2InvValue (2 : ℤ)) :=
  l1_endpoint_criterion (li2InvValue (2 : ℤ)) certificate

/--
The actual `a = 2` family has an unconditional fixed Frobenius tower. Given
the paper's analytic estimate and the full integerizer bound, these inputs
construct the endpoint certificate used by L1.
-/
theorem p0A2_endpoint_certificate_of_remaining_inputs
    (hAnalytic : P0AnalyticEstimateAt
      ((P0.caSlackAlphaTarget : ℚ) : ℝ) p0A2CanonicalFamily)
    (hIntegerizer : P0IntegerizerBound p0A2CanonicalFamily) :
    Nonempty (EndpointCertificate (li2InvValue (2 : ℤ))) := by
  exact p0EndpointCertificate_of_slackEstimate p0A2CanonicalFamily rfl
    hAnalytic hIntegerizer (P0.ScaledLucas.p0A2_nonvanishing p0A2CanonicalFamily)

/--
Conditional Main assembly with only the two unresolved P0 inputs exposed:
the analytic estimate from the contour/configuration argument and the full
integerizer rate. The seed/Frobenius nonvanishing block is supplied by its
proved construction above.
-/
theorem li2_half_irrational_of_remaining_p0_inputs
    (hAnalytic : P0AnalyticEstimateAt
      ((P0.caSlackAlphaTarget : ℚ) : ℝ) p0A2CanonicalFamily)
    (hIntegerizer : P0IntegerizerBound p0A2CanonicalFamily) :
    Irrational (li2InvValue (2 : ℤ)) := by
  rcases p0A2_endpoint_certificate_of_remaining_inputs hAnalytic hIntegerizer
    with ⟨certificate⟩
  exact li2_half_irrational_of_endpoint_certificate certificate

/--
The two verified Joukowski leaves package the preimage location and its
normalized unit-circle residue for every paper pole in the strict range.
-/
theorem p0_scaled_pole_residue_summary (m i : ℕ) (hm : 0 < m)
    (hi : i < 2 * m) :
    P0ContourLeaf.P0PolePreimageCondition m i ∧
      (∮ z in C(0, 1),
        P0ContourLeaf.affineJoukowskiDeriv
            (P0ContourLeaf.alphaScaled m : ℂ)
            (P0ContourLeaf.betaScaled m : ℂ) z /
          (P0ContourLeaf.affineJoukowski
              (P0ContourLeaf.xiScaled m : ℂ)
              (P0ContourLeaf.alphaScaled m : ℂ)
              (P0ContourLeaf.betaScaled m : ℂ) z - (i : ℂ))) =
        2 * (Real.pi : ℂ) * Complex.I := by
  constructor
  · exact P0ContourLeaf.p0_pole_preimage_condition m i hm hi
  · exact P0ContourLeaf.p0_scaled_pole_residue m i hm hi

/--
Conditional Main summary: the target is irrational if an `EndpointCertificate`
for the fixed value is supplied. The endpoint certificate still carries the
integerization, quadratic decay, and rational-point nonvanishing obligations;
this wrapper constructs none of them.
-/
theorem li2_half_main_summary
    (certificate : EndpointCertificate (li2InvValue (2 : ℤ))) :
    Irrational (li2InvValue (2 : ℤ)) ∧
      sourceBeta 2 = li2InvValue (2 : ℤ) := by
  exact ⟨li2_half_irrational_of_endpoint_certificate certificate,
    sourceBeta_two_eq_li2InvValue_two⟩

/--
Remaining paper-level contour obligations. The residue leaves above do not
prove the exact P0 contour identity (3.1) or the Andréief determinant step.
-/
def HalfContourKitObligations : Prop :=
  P0ContourIdentityStatement ∧ L5AndreiefStatement

end Li2Lean
