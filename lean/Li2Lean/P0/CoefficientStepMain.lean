/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CoefficientStepAssembly
import Li2Lean.P0.AlphaUnconditional
import Li2Lean.Main

/-!
# Coefficient step at `397/200`: the remaining analytic leaves

`CoefficientStepAssembly` reduces `P0AnalyticEstimateAt alpha F` to

* `P0SignedCoefficientEnvelope`: `‖G_m(β)‖ ≤ EInfinity m` (paper v13
  ll. 40--93 and l. 629, Cauchy--Binet plus triangle inequality), and
* `ConfigFinalBoundLiteralHead alpha`: the literal per-configuration bound on
  the retained frequency head.

This file removes the C-A/tube part of the second input.  Using the
premise-free `AlphaUnconditional.alphaGamma_gt_397_200` and the proved tube
sweep comparison `TubeGap.p0Tube_energy_comparison_actual`, the head bound at
`397/200` follows from the discrete-to-continuum cell comparison
`ConfigEnergyComparisonHead` (paper v13 ll. 257--473: "Finite configurations
and cell estimates", ending with the displayed bound
`log Q ≤ -m^2 E(κ_S + ν_δ, μ_R) + 10 m log m + c_* m + 1/3`, `δ = m^{-2}`).

So the coefficient step is reduced to exactly two analytic statements,
neither of which contains a decay rate or `alphaGamma`.
-/

open MeasureTheory

namespace Li2Lean.P0.CoefficientAssembly

open Li2Lean.P0
open Li2Lean.P0.Config

noncomputable section

/-! ## Tube lower bound for one finite-energy competitor -/

/-- Every finite-energy tube competitor has energy at least `397/200 - 300 δ`
(premise-free: `alphaGamma_gt_397_200` and the proved sweep comparison). -/
theorem tube_value_ge_397_200 {δ : ℝ} (hδ : 0 < δ) (hδmax : δ ≤ tubeRadiusMax)
    (M : P0TubeAdmissibleMeasures δ) (hM : p0TubeFiniteEnergyCondition M) :
    397 / 200 - 300 * δ ≤ p0TubeRegularizedEnergyValue M := by
  have hfin := p0TubeSweep_finite hδ.le hδmax M hM
  have hGammaLe : alphaGamma ≤ p0ExtendedEnergy (p0TubeSweep M) := by
    change (sInf (Set.range p0ExtendedEnergy)) ≤ _
    exact csInf_le EnergyLowerBound.p0ExtendedEnergy_bddBelow
      (Set.mem_range_self (p0TubeSweep M))
  have hvalue : (397 / 200 : ℝ) ≤ p0RegularizedEnergyValue (p0TubeSweep M) := by
    have hcast : ((397 / 200 : ℝ) : WithTop ℝ) ≤
        (p0RegularizedEnergyValue (p0TubeSweep M) : WithTop ℝ) := by
      calc ((397 / 200 : ℝ) : WithTop ℝ) ≤ alphaGamma :=
            AlphaUnconditional.alphaGamma_gt_397_200.le
        _ ≤ p0ExtendedEnergy (p0TubeSweep M) := hGammaLe
        _ = (p0RegularizedEnergyValue (p0TubeSweep M) : WithTop ℝ) :=
          p0ExtendedEnergy_eq_value_of_finite (p0TubeSweep M) hfin
    exact_mod_cast hcast
  have hcmp := TubeGap.p0Tube_energy_comparison_actual hδ hδmax M hM
  linarith

/-! ## The discrete-to-continuum cell comparison (remaining leaf) -/

/-- Paper v13 ll. 257--473 at base `2` with tube radius `δ = m^{-2}`: every
retained configuration with positive literal weight admits a finite-energy
tube competitor (in the paper, `κ_S + ν_δ`, `μ_R`) whose regularized energy
controls `log Q_m` up to `10 m log m + c_* m + 1/3`.  The base-`2` diagonal
factor `|S| log log 2 < 0` is dropped (l. 464).  This is the only remaining
input of the head bound; it contains no `alphaGamma` and no decay rate. -/
def ConfigEnergyComparisonHead : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    0 < literalConfigQWeight C →
    ∃ M : P0TubeAdmissibleMeasures (1 / (C.m : ℝ) ^ 2),
      p0TubeFiniteEnergyCondition M ∧
      Real.log (literalConfigQWeight C) ≤
        -(C.m : ℝ) ^ 2 * p0TubeRegularizedEnergyValue M +
          10 * (C.m : ℝ) * Real.log (C.m : ℝ) + cStar * (C.m : ℝ) + 1 / 3

/-- The head bound at `397/200` from the cell comparison and the tube lower
bound (v13 ll. 729--733 with the Lean tube cost `300 δ`). -/
theorem configFinalBoundLiteralHead_397_200
    (hcmp : ConfigEnergyComparisonHead) :
    ConfigFinalBoundLiteralHead (397 / 200) := by
  intro C hhead
  rcases (show 0 ≤ literalConfigQWeight C by
      rw [literalConfigQWeight_is_literal_contourQValue]
      unfold contourQValue UReal frequencyWeightReal
      have hell : 0 ≤ ell := Real.log_nonneg (by norm_num)
      positivity).eq_or_lt with hzero | hpos
  · exact Or.inl hzero.symm
  · refine Or.inr ⟨hpos, ?_⟩
    obtain ⟨M, hM, hlog⟩ := hcmp C hhead hpos
    have hm8 := C.m_ge_eight
    have hmpos : (0 : ℝ) < C.m := by exact_mod_cast (show 0 < C.m by omega)
    have hδ : 0 < 1 / (C.m : ℝ) ^ 2 := by positivity
    have hδmax : 1 / (C.m : ℝ) ^ 2 ≤ tubeRadiusMax := by
      unfold tubeRadiusMax
      have h8 : (8 : ℝ) ≤ C.m := by exact_mod_cast hm8
      rw [div_le_div_iff₀ (by positivity) (by norm_num)]
      nlinarith
    have hV := tube_value_ge_397_200 hδ hδmax M hM
    have hm2 : (C.m : ℝ) ^ 2 * (1 / (C.m : ℝ) ^ 2) = 1 := by
      field_simp
    have hmul : -(C.m : ℝ) ^ 2 * p0TubeRegularizedEnergyValue M ≤
        -(397 / 200 : ℝ) * (C.m : ℝ) ^ 2 + 300 := by
      have := mul_le_mul_of_nonneg_left hV (by positivity : (0 : ℝ) ≤ (C.m : ℝ) ^ 2)
      nlinarith
    unfold configExponent
    linarith

/-! ## The corrected coefficient record and its consumer -/

/-- The paper's signed envelope, `|G_m(β)| ≤ E_m(∞)` (v13 l. 629). -/
def P0SignedCoefficientEnvelope : Prop :=
  ∀ (m : ℕ), 8 ≤ m → ∀ h4 : 4 ∣ m, ‖GmBeta m‖ ≤ FrequencyLimit.EInfinity m h4

/-- `signedContourStatement` plus the triangle/Tonelli envelope of
`signedContourRhs` give the signed envelope. -/
theorem signedCoefficientEnvelope_of_signedContour
    (hsigned : signedContourStatement)
    (henv : ∀ (m : ℕ) (_hm : 0 < m) (h4 : 4 ∣ m),
      ‖signedContourRhs m‖ ≤ FrequencyLimit.EInfinity m h4) :
    P0SignedCoefficientEnvelope := by
  intro m hm8 h4
  rw [(hsigned m (by omega) h4).2]
  exact henv m (by omega) h4

/-- Corrected coefficient-step record.  Compared with
`P0WeightedCoefficientStepAt`, the field `weighted_mass_bound`
(`|G_m(β)| ≤ E m H` for each finite `H ≥ 20m`) is replaced by the paper's
`|G_m(β)| ≤ E_m(∞)`; the finite-`H` form does not follow from the paper,
which only gives `E_m(∞) ≤ (1 + 3/160·2^{-m}) E_m(20m)`. -/
structure P0CoefficientStepActual (F : P0Family) : Prop where
  base_eq_two : F.a = 2
  signed_envelope : P0SignedCoefficientEnvelope
  cell_comparison : ConfigEnergyComparisonHead

/-- Assembly for an arbitrary decay rate. -/
theorem p0AnalyticEstimateAt_of_envelope_head {alpha : ℝ} (F : P0Family)
    (henv : P0SignedCoefficientEnvelope) (hhead : ConfigFinalBoundLiteralHead alpha) :
    P0AnalyticEstimateAt alpha F := by
  intro hbase m hm8 h4
  rw [← norm_GmBeta_eq_eval_abs hbase h4]
  exact (henv m hm8 h4).trans (EInfinity_le_of_head hhead hm8 h4)

/-- The coefficient step at the slack target `397/200`. -/
theorem p0AnalyticEstimateAt_of_coefficientStepActual {F : P0Family}
    (S : P0CoefficientStepActual F) :
    P0AnalyticEstimateAt ((caSlackAlphaTarget : ℚ) : ℝ) F := by
  have htarget : ((caSlackAlphaTarget : ℚ) : ℝ) = 397 / 200 := by
    norm_num [caSlackAlphaTarget]
  rw [htarget]
  exact p0AnalyticEstimateAt_of_envelope_head F S.signed_envelope
    (configFinalBoundLiteralHead_397_200 S.cell_comparison)

/-- The same two inputs give the estimate for every family (the canonical
`G_source` fixes the polynomial once `F.a = 2`); this is the universally
quantified form consumed by `CA.Receipt.P0CoefficientStep`. -/
theorem p0AnalyticEstimateAt_all_of_inputs
    (henv : P0SignedCoefficientEnvelope) (hcmp : ConfigEnergyComparisonHead) :
    ∀ F : P0Family, P0AnalyticEstimateAt ((caSlackAlphaTarget : ℚ) : ℝ) F := by
  intro F
  by_cases hbase : F.a = 2
  · exact p0AnalyticEstimateAt_of_coefficientStepActual ⟨hbase, henv, hcmp⟩
  · intro h
    exact absurd h hbase

/-- The weighted record's decay field, produced from the cell comparison. -/
theorem weighted_decay_bound_397_200 (hcmp : ConfigEnergyComparisonHead) :
    ∀ (m H : ℕ) (_hm : 8 ≤ m) (h4 : 4 ∣ m), 20 * m ≤ H →
      weightedCoefficientMass m H h4 ≤
        Real.exp (-(397 / 200 : ℝ) * (m : ℝ) ^ 2 +
          10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301) :=
  weighted_decay_bound_of_head (configFinalBoundLiteralHead_397_200 hcmp)

end

end Li2Lean.P0.CoefficientAssembly

namespace Li2Lean

open Li2Lean.P0.CoefficientAssembly

/-- Main consumer: the `Li2(1/2)` irrationality from the two coefficient
leaves and the integerizer bound.  The C-A target `397/200 < alphaGamma` and
the tube transfer are already premise-free inside the proof. -/
theorem li2_half_irrational_of_coefficient_leaves
    (henv : P0SignedCoefficientEnvelope) (hcmp : ConfigEnergyComparisonHead)
    (hIntegerizer : P0IntegerizerBound p0A2CanonicalFamily) :
    Irrational (li2InvValue (2 : ℤ)) :=
  li2_half_irrational_of_remaining_p0_inputs
    (p0AnalyticEstimateAt_all_of_inputs henv hcmp p0A2CanonicalFamily) hIntegerizer

end Li2Lean
