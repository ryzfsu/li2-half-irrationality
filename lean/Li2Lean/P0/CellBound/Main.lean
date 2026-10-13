/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Assembly
import Li2Lean.P0.CellBound.LogQ
import Li2Lean.P0.CellBound.EnergyDecomp
import Li2Lean.P0.CellBound.CirclePieces
import Li2Lean.P0.CellBound.RealPieces
import Li2Lean.P0.CellBound.GridPieces

/-!
# `ConfigWitnessCellBound`, premise-free

Paper v13 `p0-analytic.tex` ll. 257-431, display ll. 425-431, for the fixed
competitor `configTubeWitness C = (κ_S, ν_δ, μ_R)`, `δ = m^{-2}`, against the
canonical `p0TubeRegularizedEnergyValue`.
-/

namespace Li2Lean.P0.CellBound

open Li2Lean.P0.CoefficientAssembly

/-- The discrete-to-continuum cell inequality for the configuration witness. -/
theorem configWitnessCellBound : ConfigWitnessCellBound :=
  configWitnessCellBound_of_components logQIdentity qPosFacts energyDecomposition
    pinFieldPiece contFieldPiece freqFieldPiece kkPiece kNuPiece nuNuPiece muMuPiece
    kMuPiece nuMuPiece pinFieldLower contFieldLower freqFieldLower fixedVBound
    oneBodyBound

end Li2Lean.P0.CellBound

namespace Li2Lean

open Li2Lean.P0.CoefficientAssembly

/-- `P0AnalyticEstimateAt (397/200)` for every family from the signed envelope
alone (the cell inequality is now proved). -/
theorem p0AnalyticEstimateAt_all_of_envelope
    (henv : P0SignedCoefficientEnvelope) :
    ∀ F : P0Family, P0AnalyticEstimateAt ((Li2Lean.P0.caSlackAlphaTarget : ℚ) : ℝ) F :=
  p0AnalyticEstimateAt_all_of_envelope_cellBound henv
    Li2Lean.P0.CellBound.configWitnessCellBound

/-- Main consumer: irrationality of `Li2(1/2)` from the signed coefficient
envelope and the integerizer bound. -/
theorem li2_half_irrational_of_envelope
    (henv : P0SignedCoefficientEnvelope)
    (hIntegerizer : P0IntegerizerBound p0A2CanonicalFamily) :
    Irrational (li2InvValue (2 : ℤ)) :=
  li2_half_irrational_of_envelope_cellBound henv
    Li2Lean.P0.CellBound.configWitnessCellBound hIntegerizer

end Li2Lean
