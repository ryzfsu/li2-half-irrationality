/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.Agents.F_L8.Types
import Li2Lean.P0.ConfigData
import Li2Lean.P0.ConfigThreshold

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

def pinnedUniverse (m : ℕ) : Finset ℕ := Finset.Ico (m / 4) (5 * m / 4)

def frequencyUniverse (m : ℕ) : Finset ℕ := Finset.range (2 * m)

/-- The half-open pinned cell `P_i`, docs/6333, v10 `eq:config-cells`. -/
def pinnedCell (m i : ℕ) : Set ℝ :=
  Set.Ico ((i : ℝ) / (m : ℝ)) (((i + 1 : ℕ) : ℝ) / (m : ℝ))

/-- The half-open frequency cell `Q_r`, docs/6333, v10 `eq:config-cells`. -/
def frequencyCell (m r : ℕ) : Set ℝ :=
  Set.Ico (((r - 1 : ℕ) : ℝ) / (m : ℝ)) ((r : ℝ) / (m : ℝ))

/-- The selected pinned cells with unit density, as in `eq:config-cells`. -/
def pinnedMeasure (m : ℕ) (S : Finset ℕ) : Measure ℝ :=
  ∑ i ∈ S, volume.restrict (pinnedCell m i)

/-- The selected frequency cells with unit density, as in `eq:config-cells`. -/
def frequencyMeasure (m : ℕ) (R : Finset ℕ) : Measure ℝ :=
  ∑ r ∈ R, volume.restrict (frequencyCell m r)

def baseEllipse (u : ℝ) : ℂ := Li2Lean.p0EllipsePoint 1 u

def baseEllipseSet : Set ℂ := Set.range baseEllipse

/-- A finite configuration occurring in `Q_m(S,R,Z)`, docs/6333, §5. -/
structure FiniteConfiguration where
  m : ℕ
  m_ge_eight : 8 ≤ m
  four_dvd_m : 4 ∣ m
  pinned : Finset ℕ
  frequency : Finset ℕ
  pinned_subset : pinned ⊆ pinnedUniverse m
  frequency_lower : ∀ r ∈ frequency, m / 2 + 1 ≤ r
  frequency_card : frequency.card = m
  contourCount : ℕ
  contour : Fin contourCount → ℂ
  contour_mem : ∀ a, contour a ∈ baseEllipseSet
  mass_balance : contourCount + pinned.card = m

def FiniteConfiguration.kappa (C : FiniteConfiguration) : Measure ℝ :=
  pinnedMeasure C.m C.pinned

def FiniteConfiguration.mu (C : FiniteConfiguration) : Measure ℝ :=
  frequencyMeasure C.m C.frequency

def p0SupportE : Set ℝ := Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)

/-- Exact density caps and masses for the cell measures in `eq:config-cells`.
This remains a separate measure-theoretic obligation until its cell lemmas are
proved. -/
def CellMeasureContracts (C : FiniteConfiguration) : Prop :=
  C.kappa ≤ volume.restrict p0SupportE ∧
    C.mu ≤ volume.restrict (Set.Ici (1 / 2 : ℝ)) ∧
    C.kappa Set.univ = ENNReal.ofReal ((C.pinned.card : ℝ) / (C.m : ℝ)) ∧
    C.mu Set.univ = 1

/-- The continuum pinned field `A_0`, docs/6333, §3, equation (3.6). -/
def A0 (z : ℂ) : ℝ :=
  (∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ),
      Real.log ‖z - Complex.ofReal x‖) +
    (∫ x in (0 : ℝ)..2, Real.log ‖z - Complex.ofReal x‖)

/-- The continuum contour field `φ`, docs/6333, §3, equation (3.6). -/
def phi (z : ℂ) : ℝ :=
  z.re * Real.log 2 +
    (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + Complex.ofReal s‖) +
    1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)

/-- The continuum frequency field `ψ`, docs/6333, §3, equation (3.6). -/
def psi (t : ℝ) : ℝ :=
  t * Real.log t - (t - 1 / 2) * Real.log (t - 1 / 2) -
    (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) - t * Real.log 2

/-- The fixed frequency field `B_0`, docs/6333, §3, equation (3.6). -/
def B0 (t : ℝ) : ℝ :=
  (∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ), Real.log (t + x)) +
    (∫ x in (0 : ℝ)..2, Real.log (t + x))

/-- Endpoint lattice sum in `eq:config-Bzero`. -/
def fixedLatticeLogSum (m : ℕ) (t : ℝ) : ℝ :=
  (∑ i ∈ pinnedUniverse m, Real.log (t + (i : ℝ) / (m : ℝ))) +
    (∑ j ∈ frequencyUniverse m, Real.log (t + (j : ℝ) / (m : ℝ)))

/-- The one-sided scalar-weight quadrature assertion `eq:config-psi`. -/
def PsiQuadratureBound (C : FiniteConfiguration) : Prop :=
  (C.m : ℝ) *
      (∑ r ∈ C.frequency, psi ((r : ℝ) / (C.m : ℝ))) -
      (C.m : ℝ) ^ 2 * (∫ t, psi t ∂C.mu) ≤
    (C.m : ℝ) / 2 * Real.log 2

/-- The fixed-lattice monotone quadrature assertion `eq:config-Bzero`. -/
def BzeroQuadratureBound : Prop :=
  ∀ m : ℕ, 8 ≤ m → 4 ∣ m → ∀ t : ℝ, (1 / 2 : ℝ) ≤ t →
    0 ≤ (m : ℝ) * B0 t - fixedLatticeLogSum m t ∧
      (m : ℝ) * B0 t - fixedLatticeLogSum m t ≤ Real.log (35 / 3 : ℝ)

def rightOmittedCount (a N i : ℕ) : ℕ := a + N - 1 - i

/-- The two-sided pinned logarithmic quadrature assertion `eq:config-pinned`. -/
def PinnedQuadratureBound : Prop :=
  ∀ m a N i : ℕ, 0 < m → 0 < N → a ≤ i → i < a + N →
    Real.log (Nat.factorial (i - a) : ℝ) +
      Real.log (Nat.factorial (rightOmittedCount a N i) : ℝ) -
      ((N - 1 : ℕ) : ℝ) * Real.log (m : ℝ) -
      (m : ℝ) *
        (∫ y in ((a : ℝ) / (m : ℝ))..(((a + N : ℕ) : ℝ) / (m : ℝ)),
          Real.log |(i : ℝ) / (m : ℝ) - y|) ≥
      Real.log ((m : ℝ) / ((rightOmittedCount a N i + 1 : ℕ) : ℝ))

/-- The union-of-cell measure `λ` used in `eq:config-self`. -/
def latticeCellMeasure (m : ℕ) (sites : Finset ℕ) : Measure ℝ :=
  ∑ i ∈ sites, volume.restrict (pinnedCell m i)

/-- The ordered off-diagonal lattice logarithm in `eq:config-self`. -/
def latticeOffDiagonalLogSum (m : ℕ) (sites : Finset ℕ) : ℝ :=
  ∑ i ∈ sites, ∑ j ∈ sites,
    if i = j then 0 else
      Real.log |(i : ℝ) / (m : ℝ) - (j : ℝ) / (m : ℝ)|

/-- The real self-cell comparison `eq:config-self`. -/
def SelfCellBound : Prop :=
  ∀ m : ℕ, 0 < m → ∀ sites : Finset ℕ,
    latticeOffDiagonalLogSum m sites ≤
      (m : ℝ) ^ 2 *
        (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
          ∂((latticeCellMeasure m sites).prod (latticeCellMeasure m sites))) +
      (sites.card : ℝ) * (Real.log (m : ℝ) + Real.log (2 * Real.pi))

def dPlus : ℝ := 751 / 5000

def dMinus : ℝ := 1749 / 5000

/-- The exact mixed-cell clearance inequalities from docs/6333, v10 §5. -/
def MixedCellClearance : Prop :=
  (∀ z ∈ baseEllipseSet, ∀ x ∈ Set.Icc (0 : ℝ) 2,
      dPlus ≤ ‖z - Complex.ofReal x‖) ∧
  (∀ z ∈ baseEllipseSet, ∀ t : ℝ, (1 / 2 : ℝ) ≤ t →
      dMinus ≤ ‖z + Complex.ofReal t‖)

/-- The finite-product error term `b_m` in `eq:config-Fg`. -/
def b (m : ℕ) : ℝ :=
  5 * (1 + 2 * Real.log 2) +
    4 * (1 + Real.log ((m / 2 + 1 : ℕ) : ℝ))

/-- The finite contour-product bound `eq:config-Fg`, including its zero case. -/
def FgBound : Prop :=
  ∀ m : ℕ, 8 ≤ m → 4 ∣ m → ∀ z : ℂ,
    let v := Li2Lean.p0Entire (m / 2)
      (Complex.ofReal (m : ℝ) * z)
    v = 0 ∨ Real.log ‖v‖ ≤ (m : ℝ) * phi z + b m

/-- The explicit linear constant in `eq:config-cstar`. -/
def cStar : ℝ :=
  4 * Real.log (2 * Real.pi) + 9 + (21 / 2 : ℝ) * Real.log 2 +
    Real.log 336 + Real.log (35 / 3 : ℝ) +
    5 / (2 * dPlus) + 1 / (2 * dMinus)

/-- The rational-series numerical obligation in `eq:config-cstar`. -/
def CstarRoundedBound : Prop := cStar < (49979 / 1000 : ℝ)

/-- The paper's C-A alpha floor, the instance `p0PaperAlphaTarget` of the
parameterized chain (see `alphaFloor_eq_paperTarget`). -/
def alphaFloor : ℝ := 1992909 / 1000000

/-- `alphaFloor` is the real cast of the shared paper target. -/
theorem alphaFloor_eq_paperTarget :
    alphaFloor = ((Li2Lean.p0PaperAlphaTarget : ℚ) : ℝ) := by
  norm_num [alphaFloor, Li2Lean.p0PaperAlphaTarget]

/-- The abstract final configuration inequality `eq:config-final`, for a
nonnegative configuration weight `Q`. The public literal interface is defined
in `ConfigLiteralWeight`, where `Q` is fixed to the actual `Q_m` expression.
A zero term is handled without taking its logarithm. -/
def ConfigFinalBound (alpha : ℝ) (Q : FiniteConfiguration → ℝ) : Prop :=
  ∀ C : FiniteConfiguration,
    Q C = 0 ∨
      (0 < Q C ∧
        Real.log (Q C) ≤
          -alpha * (C.m : ℝ) ^ 2 +
            10 * (C.m : ℝ) * Real.log (C.m : ℝ) +
            cStar * (C.m : ℝ) + 300 + 1 / 3)

/-- Inputs for the three logarithmic-energy components in C-A, docs/6333 §5.
This is a contract type: the fields are not yet computed from the finite
reference arrays in `certificates/dual/reference.json`. -/
structure DualReferencePotentials where
  Leta : ℂ → ℝ
  Lmu : ℝ → ℝ
  LmuNegative : ℂ → ℝ
  QetaEta : ℝ
  QmuMu : ℝ
  QetaMu : ℝ
  qLog : ℝ
  qLog_eq : qLog = QetaEta + QmuMu + QetaMu

def Weta (D : DualReferencePotentials) (z : ℂ) : ℝ :=
  A0 z - phi z - 2 * D.Leta z - D.LmuNegative z

def Wmu (D : DualReferencePotentials) (t : ℝ) : ℝ :=
  B0 t - psi t - 2 * D.Lmu t - D.Leta (Complex.ofReal (-t))

def hEta : ℝ := -(669 / 200 : ℝ)

def hMu : ℝ := 71 / 25

def pPenaltyUpper : ℝ := 6905963574153 / 81920000000000

def tPenaltyUpper : ℝ := 38158094390353 / 409600000000000

def qLogLower : ℝ := -(438334707 / 1000000000 : ℝ)

def cAConstant : ℝ := 9 / 2 - 2 * Real.log 2

def cAAlphaFloorExpression : ℝ :=
  9 / 2 - 2 * (6931473 / 10000000 : ℝ) + qLogLower + hEta + hMu -
    pPenaltyUpper - tPenaltyUpper

/-- Rational margin arithmetic used in the C-A aggregation. -/
theorem cA_rational_margin : alphaFloor < cAAlphaFloorExpression := by
  norm_num [alphaFloor, cAAlphaFloorExpression, qLogLower, hEta, hMu,
    pPenaltyUpper, tPenaltyUpper]

/-- Parameterized rational margin: every target `alpha ≤ alphaFloor`
(e.g. the slack target `397/200`) lies below the C-A expression. -/
theorem cA_rational_margin_of_le {alpha : ℝ} (h : alpha ≤ alphaFloor) :
    alpha < cAAlphaFloorExpression :=
  lt_of_le_of_lt h cA_rational_margin

/-! The C-A directed-cell receipt is defined in ConfigCAReceipt, after the
actual reference and variational value are available. -/

end

end Li2Lean.P0.Config
