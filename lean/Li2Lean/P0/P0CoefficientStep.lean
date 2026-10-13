/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigLiteralWeight
import Li2Lean.P0.AlphaParam

open scoped BigOperators

namespace Li2Lean.P0

open Li2Lean.P0.Config

noncomputable section

/-- The finite configuration weight summed by the coefficient step.  It is
the literal `contourQValue` reconstructed from one paper configuration; no
free function-valued weight is accepted by this interface. -/
def coefficientConfigurationSum (S : Finset FiniteConfiguration) : ℝ :=
  ∑ C ∈ S, literalConfigQWeight C

/--
The paper-level S7 coefficient step.  The first four fields are the actual
L5/L7 obligations used to derive the finite configuration expansion.  The
last two fields are the remaining, explicitly typed outputs of that
derivation: a coefficient mass bound and a configuration-count bound.  They
are stated separately from the target exponential estimate, so this record
cannot be inhabited by supplying the conclusion under a renamed field.

`config_final_bound` is the literal C-A bound for the reconstructed
`contourQValue`; `config_m_eq` prevents configurations for another `m` from
being inserted into the sum. The decay target is fixed to the regenerated
`397/200` slack target used by Main. -/
structure P0CoefficientStep (F : P0Family) where
  base_eq_two : F.a = 2
  l5_contour : P0ContourIdentityStatement
  l5_andreief : L5AndreiefStatement
  l7_circle_average : L7CircleAverageStatement
  l7_configuration : L7FiniteConfigurationTransfer
  config_final_bound :
    ConfigFinalBoundLiteral ((caSlackAlphaTarget : ℚ) : ℝ)
  configurations : ℕ → Finset FiniteConfiguration
  config_m_eq : ∀ (m : ℕ) (C : FiniteConfiguration),
    C ∈ configurations m → C.m = m
  coefficient_mass_bound : ∀ (m : ℕ), 8 ≤ m → 4 ∣ m →
    |(F.G m).eval (li2InvValue (2 : ℤ))| ≤
      coefficientConfigurationSum (configurations m)
  configuration_count_bound : ∀ (m : ℕ), 8 ≤ m → 4 ∣ m →
    ((configurations m).card : ℝ) ≤
      Real.exp ((56 - Config.cStar) * (m : ℝ) + (2 / 3 : ℝ))

/-- Per-configuration energy bridge used by the Andreief/sup coefficient step.
The configuration weight is the literal `Q_m` reconstruction, and the only
input is the source-locked C-A final bound.  In particular this theorem does
not quantify over a free weight function, a free `Q`, or a receipt field for
`alphaGamma`. -/
theorem literalConfigQWeight_le_exp_of_final_bound
    {alpha : ℝ} (hfinal : ConfigFinalBoundLiteral alpha)
    {m : ℕ} {C : FiniteConfiguration} (hCm : C.m = m) :
    literalConfigQWeight C ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) + Config.cStar * (m : ℝ) +
        300 + 1 / 3) := by
  rcases hfinal C with hzero | ⟨hpos, hlog⟩
  · rw [hzero]
    positivity
  · have hq : literalConfigQWeight C =
        Real.exp (Real.log (literalConfigQWeight C)) := by
      rw [Real.exp_log hpos]
    rw [hq, ← hCm]
    exact Real.exp_le_exp.mpr hlog

private theorem coefficientConfigurationSum_le_exp
    {alpha : ℝ} {m : ℕ} {S : Finset FiniteConfiguration}
    (hfinal : ConfigFinalBoundLiteral alpha)
    (hCm : ∀ C ∈ S, C.m = m)
    (hcard : (S.card : ℝ) ≤
      Real.exp ((56 - Config.cStar) * (m : ℝ) + (2 / 3 : ℝ))) :
    coefficientConfigurationSum S ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301) := by
  let base : ℝ :=
    -alpha * (m : ℝ) ^ 2 +
      10 * (m : ℝ) * Real.log (m : ℝ) + Config.cStar * (m : ℝ) +
      300 + 1 / 3
  let delta : ℝ := (56 - Config.cStar) * (m : ℝ) + (2 / 3 : ℝ)
  have hterm : ∀ C ∈ S, literalConfigQWeight C ≤ Real.exp base := by
    intro C hC
    simpa [base] using literalConfigQWeight_le_exp_of_final_bound hfinal (hCm C hC)
  have hsum : coefficientConfigurationSum S ≤ (S.card : ℝ) * Real.exp base := by
    unfold coefficientConfigurationSum
    calc
      (∑ C ∈ S, literalConfigQWeight C) ≤ ∑ _C ∈ S, Real.exp base := by
        exact Finset.sum_le_sum (fun C hC => hterm C hC)
      _ = (S.card : ℝ) * Real.exp base := by
        simp [nsmul_eq_mul]
  have hexp : 0 ≤ Real.exp base := (Real.exp_pos base).le
  have hprod : (S.card : ℝ) * Real.exp base ≤
      Real.exp delta * Real.exp base :=
    mul_le_mul_of_nonneg_right hcard hexp
  calc
    coefficientConfigurationSum S ≤ (S.card : ℝ) * Real.exp base := hsum
    _ ≤ Real.exp delta * Real.exp base := hprod
    _ = Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301) := by
      rw [← Real.exp_add]
      congr 1
      dsimp [base, delta]
      ring

/-- The typed S7 output has exactly the shape consumed by L1. -/
theorem p0AnalyticEstimateAt_of_coefficientStep
    {F : P0Family} (S : P0CoefficientStep F) :
    P0AnalyticEstimateAt ((caSlackAlphaTarget : ℚ) : ℝ) F := by
  intro _ m hm h4
  exact le_trans (S.coefficient_mass_bound m hm h4)
    (coefficientConfigurationSum_le_exp S.config_final_bound
      (fun C hC => S.config_m_eq m C hC)
      (S.configuration_count_bound m hm h4))

end

end Li2Lean.P0

#print axioms Li2Lean.P0.p0AnalyticEstimateAt_of_coefficientStep
