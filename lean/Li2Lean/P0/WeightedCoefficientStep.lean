/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.P0CoefficientStep
import Li2Lean.P0.FrequencyLimit

open scoped BigOperators

namespace Li2Lean.P0

open Li2Lean.P0.Config
open Li2Lean.P0.FrequencyLimit

noncomputable section

/--
The finite weighted coefficient mass from docs/6333 (3.4)--(3.6), with the
frequency cutoff made explicit.  `E` is the literal finite sum over pinned
sets `S`; each summand is a `d = m - S.card`-fold product contour integral,
and its inner sum is over the bounded increasing frequency tuples
`r : TruncatedFrequencyTuple (m / 2) m H`.  Thus this abbreviation does not
replace the continuous contour integral by a finite configuration list.
-/
noncomputable def weightedCoefficientMass
    (m H : ℕ) (h4 : 4 ∣ m) : ℝ :=
  E m H h4

/-- The abbreviation exposes the exact finite `(S,R)`/contour definition. -/
theorem weightedCoefficientMass_eq_E (m H : ℕ) (h4 : 4 ∣ m) :
    weightedCoefficientMass m H h4 = E m H h4 :=
  rfl

/-!
This is the paper-faithful replacement for the old direct
`coefficient_mass_bound` field.  It keeps L5/L7 and the literal C-A bound in
the record, but asks for the actual finite-cutoff contour mass and its
uniform decay estimate as two separate obligations.  Neither obligation is
proved here: this file only gives their exact types and the sound assembly
theorem below.
-/
structure P0WeightedCoefficientStepAt (alpha : ℝ) (F : P0Family) where
  base_eq_two : F.a = 2
  l5_contour : P0ContourIdentityStatement
  l5_andreief : L5AndreiefStatement
  l7_circle_average : L7CircleAverageStatement
  l7_configuration : L7FiniteConfigurationTransfer
  config_final_bound :
    ConfigFinalBoundLiteral ((caSlackAlphaTarget : ℚ) : ℝ)
  /-- Absolute coefficient mass is bounded by the literal finite cutoff mass. -/
  weighted_mass_bound :
    ∀ (m H : ℕ) (hm : 8 ≤ m) (h4 : 4 ∣ m), 20 * m ≤ H →
      |(F.G m).eval (li2InvValue (2 : ℤ))| ≤
        weightedCoefficientMass m H h4
  /-- The finite cutoff mass already includes the paper's tail/count budget. -/
  weighted_decay_bound :
    ∀ (m H : ℕ) (hm : 8 ≤ m) (h4 : 4 ∣ m), 20 * m ≤ H →
      weightedCoefficientMass m H h4 ≤
        Real.exp (-alpha * (m : ℝ) ^ 2 +
          10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301)

/--
The weighted interface implies the existing parameterized analytic estimate.
This is only order-theoretic assembly; all contour, Andreief, frequency and
C-A arithmetic obligations remain explicit fields above.
-/
theorem p0AnalyticEstimateAt_of_weightedCoefficientStep
    {alpha : ℝ} {F : P0Family} (S : P0WeightedCoefficientStepAt alpha F) :
    P0AnalyticEstimateAt alpha F := by
  intro _ m hm h4
  have hcut : 20 * m ≤ 20 * m := le_rfl
  exact le_trans
    (S.weighted_mass_bound m (20 * m) hm h4 hcut)
    (S.weighted_decay_bound m (20 * m) hm h4 hcut)

/-- The narrowed target keeps the old Main conclusion type unchanged. -/
theorem p0AnalyticEstimateAt_of_weightedCoefficientStep_slack
    {F : P0Family} (S : P0WeightedCoefficientStepAt
      ((caSlackAlphaTarget : ℚ) : ℝ) F) :
    P0AnalyticEstimateAt ((caSlackAlphaTarget : ℚ) : ℝ) F :=
  p0AnalyticEstimateAt_of_weightedCoefficientStep S

end

end Li2Lean.P0

#print axioms Li2Lean.P0.p0AnalyticEstimateAt_of_weightedCoefficientStep
#print axioms Li2Lean.P0.p0AnalyticEstimateAt_of_weightedCoefficientStep_slack
