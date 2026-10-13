/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Caps
import Li2Lean.P0.CA.Receipt.RowInputs
import Li2Lean.P0.DualAlgebra
import Li2Lean.P0.ContourEnergyLowerBound

/-!
# The C-A duality step at the actual reference

`ActualReferenceLinearization` is the L6 quadratic lower bound of v10
`lem:dual-lower` at the literal reference `actualReference`: for every
finite-energy admissible pair `M`, the two first variations are integrable
and

  `cAConstant + Q_log + ∫ W_η dη + ∫ W_μ dμ ≤ E(M)`.

It is the mass-zero positivity `E(M) - linearization = I(M - M₀) ≥ 0`, not a
statement about `alphaGamma` or any cap. From it, the caps of `Caps.lean`
and the infimum convention of `p0ExtendedEnergy`, this file proves the
duality field

  `cAConstant + Q_log + h_η + h_μ - P - T ≤ alphaGamma`

for every threshold pair and every pair of integrable nonnegative penalty
majorants.
-/

open MeasureTheory Set

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.P0.ConfigReferenceSymmetry

noncomputable section

/-- The L6 linearization at the actual reference (v10 `lem:dual-lower`,
quadratic step). -/
def ActualReferenceLinearization : Prop :=
  ∀ M : P0AdmissibleMeasures, P0FiniteEnergyCondition M →
    Integrable (Config.Weta actualReference) M.eta ∧
    Integrable (Config.Wmu actualReference) M.mu ∧
    Config.cAConstant + actualReference.qLog +
        (∫ z, Config.Weta actualReference z ∂M.eta) +
        (∫ t, Config.Wmu actualReference t ∂M.mu) ≤
      p0RegularizedEnergyValue M

/-- The duality field of the C-A receipt, for arbitrary thresholds and
penalty majorants. -/
theorem actual_duality_lower (hLin : ActualReferenceLinearization)
    {hη hμ : ℝ} {p q : ℝ → ℝ}
    (hΓ : ∀ z ∈ Gamma, hη ≤ Config.Weta actualReference z)
    (hp0 : ∀ x ∈ Icc (1 / 4 : ℝ) (5 / 4), 0 ≤ p x)
    (hpW : ∀ x ∈ Icc (1 / 4 : ℝ) (5 / 4),
      hη - Config.Weta actualReference (x : ℂ) ≤ p x)
    (hpInt : IntegrableOn p (Icc (1 / 4 : ℝ) (5 / 4)))
    (hq0 : ∀ t ∈ Ici (1 / 2 : ℝ), 0 ≤ q t)
    (hqW : ∀ t ∈ Ici (1 / 2 : ℝ), hμ - Config.Wmu actualReference t ≤ q t)
    (hqInt : IntegrableOn q (Ici (1 / 2 : ℝ))) :
    ((Config.cAConstant + actualReference.qLog + hη + hμ -
        (∫ x in Icc (1 / 4 : ℝ) (5 / 4), p x) -
        (∫ t in Ici (1 / 2 : ℝ), q t) : ℝ) : WithTop ℝ) ≤ alphaGamma := by
  classical
  unfold alphaGamma
  apply Li2Lean.p0DualExtendedInfimum_ge_of_finiteCases p0ExtendedEnergy
    P0FiniteEnergyCondition p0RegularizedEnergyValue _ EnergyLowerBound.p0AdmissibleMeasures_nonempty
  · intro M
    unfold p0ExtendedEnergy
    split_ifs <;> rfl
  · intro M hM
    obtain ⟨hWη, hWμ, hlin⟩ := hLin M hM
    have hcapη := eta_cap M hWη hΓ hp0 hpW hpInt
    have hcapμ := mu_cap M hWμ hq0 hqW hqInt
    linarith

end

end Li2Lean.P0.CA.Receipt
