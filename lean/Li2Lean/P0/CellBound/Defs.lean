/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigWitnessFiniteEnergy
import Li2Lean.P0.ConfigOneBodyEntropy
import Li2Lean.P0.ConfigFgBound
import Li2Lean.P0.ConfigSelfCells

/-!
# Cell inequality for the configuration witness: definitions

Paper v13 `p0-analytic.tex` ll. 257-431.  For a finite configuration
`C = (S, R, Z)` at scale `m` we name

* the discrete logarithmic sums in scaled coordinates `x_s = s/m`,
  `ζ_a = C.contour a`, `t_r = r/m` that make up `log Q` after the three
  Cauchy determinants are expanded and the deleted fixed-grid factors are
  restored (`LogQIdentity`), and
* the pieces of the regularized energy of the fixed witness
  `configTubeWitness C = (κ_S, ν_δ, μ_R)` (`EnergyDecomposition`).

The component statements are `Prop`s proved in the sibling files; the
assembly is in `CellBound/Assembly.lean`.
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

variable (C : FiniteConfiguration)

/-! ## Discrete sums (scaled coordinates) -/

/-- Ordered pinned pairs `∑_{s ≠ t} log |x_s - x_t|`. -/
def pinPin : ℝ := latticeOffDiagonalLogSum C.m C.pinned

/-- Ordered frequency pairs `∑_{r ≠ q} log |t_r - t_q|`. -/
def freqFreq : ℝ := latticeOffDiagonalLogSum C.m C.frequency

/-- Ordered contour pairs `∑_{a ≠ b} log |ζ_a - ζ_b|`. -/
def contCont : ℝ :=
  ∑ a : Fin C.contourCount, ∑ b : Fin C.contourCount,
    if a = b then 0 else Real.log ‖C.contour a - C.contour b‖

/-- `∑_{s, a} log |x_s - ζ_a|`. -/
def pinCont : ℝ :=
  ∑ s ∈ C.pinned, ∑ a : Fin C.contourCount,
    Real.log ‖(((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖

/-- `∑_{s, r} log (x_s + t_r)`. -/
def pinFreq : ℝ :=
  ∑ s ∈ C.pinned, ∑ r ∈ C.frequency,
    Real.log ((s : ℝ) / (C.m : ℝ) + (r : ℝ) / (C.m : ℝ))

/-- `∑_{a, r} log |ζ_a + t_r|`. -/
def contFreq : ℝ :=
  ∑ a : Fin C.contourCount, ∑ r ∈ C.frequency,
    Real.log ‖C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖

/-- The fixed-grid field at the pinned sites, the site itself omitted. -/
def pinField : ℝ :=
  ∑ s ∈ C.pinned,
    ((∑ i ∈ pinnedUniverse C.m,
        if i = s then 0 else Real.log |(s : ℝ) / (C.m : ℝ) - (i : ℝ) / (C.m : ℝ)|) +
      ∑ j ∈ frequencyUniverse C.m,
        if j = s then 0 else Real.log |(s : ℝ) / (C.m : ℝ) - (j : ℝ) / (C.m : ℝ)|)

/-- The fixed-grid field at the contour points. -/
def contField : ℝ :=
  ∑ a : Fin C.contourCount,
    ((∑ i ∈ pinnedUniverse C.m,
        Real.log ‖C.contour a - (((i : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖) +
      ∑ j ∈ frequencyUniverse C.m,
        Real.log ‖C.contour a - (((j : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖)

/-- The fixed-grid field at the frequencies. -/
def freqField : ℝ :=
  ∑ r ∈ C.frequency, fixedLatticeLogSum C.m ((r : ℝ) / (C.m : ℝ))

/-- The fixed Vandermonde `log |Δ(I)|^2 |Δ(J)|` in scaled coordinates. -/
def fixedV : ℝ :=
  latticeOffDiagonalLogSum C.m (pinnedUniverse C.m) +
    (1 / 2 : ℝ) * latticeOffDiagonalLogSum C.m (frequencyUniverse C.m)

/-- The one-body factors of `Q`. -/
def oneBody : ℝ :=
  (∑ s ∈ C.pinned, Real.log (ell * UReal (C.m / 2) s)) +
    (∑ r ∈ C.frequency, Real.log (frequencyWeightReal (C.m / 2) r)) +
    ∑ a : Fin C.contourCount,
      Real.log ‖p0Entire (C.m / 2) (Complex.ofReal (C.m : ℝ) * C.contour a)‖

/-- The exact expansion of `log Q` (three Cauchy determinants, restoration
of the deleted fixed-grid factors, scaling by `m`). -/
def LogQIdentity : Prop :=
  ∀ C : FiniteConfiguration, 0 < literalConfigQWeight C →
    Real.log (literalConfigQWeight C) =
      oneBody C + fixedV C + pinPin C + 2 * pinCont C + contCont C + freqFreq C +
        pinFreq C + contFreq C - pinField C - contField C - freqField C -
        (2 * (C.m : ℝ) + 2 * (C.contourCount : ℝ)) * Real.log (C.m : ℝ)

/-- Nonvanishing consequences of `Q > 0` used by the bounds. -/
def QPosFacts : Prop :=
  ∀ C : FiniteConfiguration, 0 < literalConfigQWeight C →
    (∀ a b : Fin C.contourCount, a ≠ b → C.contour a ≠ C.contour b) ∧
      ∀ a : Fin C.contourCount,
        p0Entire (C.m / 2) (Complex.ofReal (C.m : ℝ) * C.contour a) ≠ 0

/-! ## Energy pieces of the witness -/

/-- `κ_S`. -/
abbrev wκ : Measure ℝ := pinnedMeasure C.m C.pinned
/-- `ν_δ`. -/
abbrev wν : Measure ℂ := configContourMeasure C
/-- `μ_R`. -/
abbrev wμ : Measure ℝ := frequencyMeasure C.m C.frequency

def ePk : ℝ := ∫ x : ℝ, p0CompanionField (x : ℂ) ∂(wκ C)
def ePν : ℝ := ∫ z : ℂ, p0CompanionField z ∂(wν C)
def eBμ : ℝ := ∫ t : ℝ, P0.B0 t ∂(wμ C)
def eΨμ : ℝ := ∫ t : ℝ, P0.psi t ∂(wμ C)
def eIkk : ℝ := -∫ p : ℝ × ℝ, Real.log |p.1 - p.2| ∂((wκ C).prod (wκ C))
def eIkν : ℝ :=
  ∫ p : ℂ × ℂ, li2LogKernel p.1 p.2 ∂((Measure.map Complex.ofReal (wκ C)).prod (wν C))
def eIνν : ℝ := li2LogInteraction (wν C) (wν C)
def eLLμ : ℝ := ∫ p : ℝ × ℝ, Real.log |p.1 - p.2| ∂((wμ C).prod (wμ C))
def eMkμ : ℝ := ∫ p : ℝ × ℝ, Real.log (p.1 + p.2) ∂((wκ C).prod (wμ C))
def eMνμ : ℝ := ∫ p : ℂ × ℝ, Real.log ‖p.1 + (p.2 : ℂ)‖ ∂((wν C).prod (wμ C))

/-- The regularized energy of the witness split into its pieces; the
`log (1 + t)` regularizers cancel (`-3 + 2 + 1 = 0`). -/
def EnergyDecomposition : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    p0TubeRegularizedEnergyValue (configTubeWitness C) =
      ((9 / 2 : ℝ) - 2 * ell) + ePk C + ePν C + eBμ C - eΨμ C + eIkk C +
        2 * eIkν C + eIνν C - eLLμ C - eMkμ C - eMνμ C

/-! ## Piece bounds -/

/-- Pinned field: cell average against the left endpoint (variation `log 168`). -/
def PinFieldPiece : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) ^ 2 * ePk C ≤
      (C.m : ℝ) * (∑ s ∈ C.pinned, p0CompanionField (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) +
        (C.m : ℝ) * Real.log 168

/-- Contour field: circle average (`A_0` harmonic, `φ` subharmonic). -/
def ContFieldPiece : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) ^ 2 * ePν C ≤
      (C.m : ℝ) * ∑ a : Fin C.contourCount, p0CompanionField (C.contour a)

/-- Frequency field: `B_0` increasing, `ψ` quadrature. -/
def FreqFieldPiece : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    (C.m : ℝ) ^ 2 * (eBμ C - eΨμ C) ≤
      (C.m : ℝ) * (∑ r ∈ C.frequency,
        (P0.B0 ((r : ℝ) / (C.m : ℝ)) - P0.psi ((r : ℝ) / (C.m : ℝ)))) +
        (C.m : ℝ) / 2 * Real.log 2

/-- Pinned self-energy (`eq:config-self` on `S`). -/
def KKPiece : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) ^ 2 * eIkk C ≤
      -pinPin C + (C.pinned.card : ℝ) * (Real.log (C.m : ℝ) + Real.log (2 * Real.pi))

/-- Pinned-contour interaction (circle average, displacement `1/d_+`). -/
def KNuPiece : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) ^ 2 * eIkν C ≤ -pinCont C + (C.m : ℝ) / (2 * dPlus)

/-- Contour self-energy (circle smoothing `2 d log m`). -/
def NuNuPiece : Prop :=
  ∀ C : FiniteConfiguration,
    (∀ a b : Fin C.contourCount, a ≠ b → C.contour a ≠ C.contour b) →
    (C.m : ℝ) ^ 2 * eIνν C ≤
      -contCont C + 2 * (C.contourCount : ℝ) * Real.log (C.m : ℝ)

/-- Frequency self-energy (`eq:config-self` on `R - 1`). -/
def MuMuPiece : Prop :=
  ∀ C : FiniteConfiguration,
    -((C.m : ℝ) ^ 2 * eLLμ C) ≤
      -freqFreq C + (C.m : ℝ) * (Real.log (C.m : ℝ) + Real.log (2 * Real.pi))

/-- Pinned-frequency interaction (cell displacement, crude `4/(3m)` per pair). -/
def KMuPiece : Prop :=
  ∀ C : FiniteConfiguration,
    -((C.m : ℝ) ^ 2 * eMkμ C) ≤ -pinFreq C + 4 * (C.m : ℝ) / 3

/-- Contour-frequency interaction (circle average, displacement `1/(2 d_-)`). -/
def NuMuPiece : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    -((C.m : ℝ) ^ 2 * eMνμ C) ≤ -contFreq C + (C.m : ℝ) / (2 * dMinus)

/-! ## Fixed-grid fields and fixed Vandermonde -/

/-- `eq:config-pinned`: the `I_m` part is nonnegative, the `J_m` part `≥ -log 2`. -/
def PinFieldLower : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) * (∑ s ∈ C.pinned, P0.A0 (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) -
      (C.pinned.card : ℝ) * Real.log 2 ≤ pinField C

/-- Fixed contour denominators (displacement `3/(2 d_+)` per contour point). -/
def ContFieldLower : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) * (∑ a : Fin C.contourCount, P0.A0 (C.contour a)) -
      (C.contourCount : ℝ) * (3 / (2 * dPlus)) ≤ contField C

/-- `eq:config-Bzero` summed over the frequencies. -/
def FreqFieldLower : Prop :=
  ∀ C : FiniteConfiguration,
    (C.m : ℝ) * (∑ r ∈ C.frequency, P0.B0 ((r : ℝ) / (C.m : ℝ))) -
      (C.m : ℝ) * Real.log (35 / 3 : ℝ) ≤ freqField C

/-- Fixed Vandermonde normalization `C_0 = 9/2 - 2 log 2`. -/
def FixedVBound : Prop :=
  ∀ C : FiniteConfiguration,
    fixedV C ≤ -(C.m : ℝ) ^ 2 * ((9 / 2 : ℝ) - 2 * Real.log 2) +
      2 * (C.m : ℝ) * (Real.log (C.m : ℝ) + Real.log (2 * Real.pi))

/-- Binomial entropy and the finite contour product. -/
def OneBodyBound : Prop :=
  ∀ C : FiniteConfiguration,
    (∀ a : Fin C.contourCount,
        p0Entire (C.m / 2) (Complex.ofReal (C.m : ℝ) * C.contour a) ≠ 0) →
    oneBody C ≤
      (C.m : ℝ) * (∑ s ∈ C.pinned, P0.phi (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) +
        (C.m : ℝ) * (∑ r ∈ C.frequency, P0.psi ((r : ℝ) / (C.m : ℝ))) +
        (C.m : ℝ) * (∑ a : Fin C.contourCount, P0.phi (C.contour a)) +
        (C.contourCount : ℝ) * b C.m

end

end Li2Lean.P0.CellBound
