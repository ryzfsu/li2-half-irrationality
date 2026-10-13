/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigFejerMass
import Li2Lean.P0.ConfigReferenceSymmetry
import Li2Lean.P0.ConfigContourKernel
import Li2Lean.P0.ConfigThreshold
import Li2Lean.Agents.F_L8.Types

/-!
# The closed contour potential interface

The contour reference is the literal degree-48 Fejer mixture from Appendix A.
This file separates the finite source algebra from the singular analytic step
which identifies the logarithmic contour integral with its Fourier formula.
The latter is retained as an explicit obligation: an off-diagonal pointwise
factorization alone does not justify an integral across the collision set.

The checker below acts on the full `Weta` field of the actual reference.  In
particular, its contour rows do not silently drop the pinned reference term.
The pinned row obligations are carried alongside the contour rows for later
assembly into `CAReceipt`.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigContourSelfPotential

noncomputable section

open ConfigContourReference ConfigFejerMass ConfigReferenceSymmetry
open Li2Lean.F_L8

/-! ## The literal finite kernel -/

/-- The ungrouped finite Fourier kernel coming from the 49 Fejer summands. -/
def K48 (u : ℝ) : ℂ :=
  (49 : ℂ)⁻¹ * ∑ r ∈ Finset.range 49, ∑ s ∈ Finset.range 49,
    fourierChar ((r : ℤ) - (s : ℤ)) u

/-- The triangular coefficient of the degree-48 Fejer kernel. -/
def K48Coeff (n : ℕ) : ℝ :=
  if n ≤ 48 then 1 - (n : ℝ) / 49 else 0

/-- The actual cosine moment of the 64 weighted Fejer mixture. -/
def contourFourierMoment (n : ℕ) : ℝ :=
  K48Coeff n * ∑ j : Fin 64,
    contourWeight j * Real.cos ((n : ℝ) * contourAngle j)

theorem fejer48_eq_K48 (u : ℝ) :
    (fejer48 u : ℂ) = K48 u := by
  unfold fejer48 K48
  rw [Complex.ofReal_div, exp_sum_norm_sq]
  norm_num only [Complex.ofReal_ofNat]
  ring

theorem K48_eq_fejer48 (u : ℝ) :
    K48 u = (fejer48 u : ℂ) := (fejer48_eq_K48 u).symm

theorem K48_real_nonneg (u : ℝ) : 0 ≤ fejer48 u := fejer48_nonneg u

theorem K48Coeff_zero : K48Coeff 0 = 1 := by
  norm_num [K48Coeff]

theorem K48Coeff_pos {n : ℕ} (hn48 : n ≤ 48) :
    0 < K48Coeff n := by
  simp only [K48Coeff, if_pos hn48]
  have hnlt : n < 49 := lt_of_le_of_lt hn48 (by norm_num)
  have hnltR : (n : ℝ) < 49 := by exact_mod_cast hnlt
  linarith

/-! ## Source and Fourier forms of the contour potential -/

/-- Total mass of the literal contour reference. -/
def contourMass : ℝ := 267885951940 / 1000000000000

/-- The actual logarithmic potential evaluated at a contour parameter. -/
def contourSelfPotential (u : ℝ) : ℝ :=
  contourReferencePotential (Li2Lean.p0EllipsePoint 1 u)

/-- The finite degree-48 expression in (5.5). -/
def contourSelfPotentialFourier (u : ℝ) : ℝ :=
  contourMass * Real.log ConfigContourKernel.contourScale -
    ∑ n ∈ Finset.range 48,
      ((1 + ConfigContourKernel.contourRatio ^ (n + 1)) *
        contourFourierMoment (n + 1) / (n + 1 : ℝ)) *
        Real.cos ((n + 1 : ℝ) * u)

/-- The corresponding finite expression for the contour self-energy. -/
def contourSelfEnergyFourier : ℝ :=
  contourMass ^ 2 * Real.log ConfigContourKernel.contourScale -
    ∑ n ∈ Finset.range 48,
      ((1 + ConfigContourKernel.contourRatio ^ (n + 1)) *
        (contourFourierMoment (n + 1)) ^ 2 / (n + 1 : ℝ))

theorem contourMass_eq_source :
    contourMass = ∑ j : Fin 64, contourWeight j := by
  unfold contourMass
  exact ConfigFejerMass.contourWeight_sum.symm

theorem contourSelfPotential_eq_source_integral (u : ℝ) :
    contourSelfPotential u =
      (2 * Real.pi)⁻¹ * ∫ v in (0 : ℝ)..(2 * Real.pi),
        contourDensity v *
          Real.log ‖Li2Lean.p0EllipsePoint 1 u -
            Li2Lean.p0EllipsePoint 1 v‖ := by
  rfl

/-- The finite Fourier identity still requiring the collision-null and
integrability argument for the logarithmic kernel. -/
def ContourSelfPotentialFourierObligation : Prop :=
  ∀ u : ℝ, contourSelfPotential u = contourSelfPotentialFourier u

/-- Parameter square on which the contour logarithm is singular on the
diagonal. -/
def contourParameterSquare : Set (ℝ × ℝ) :=
  Set.Icc (0 : ℝ) (2 * Real.pi) ×ˢ Set.Icc (0 : ℝ) (2 * Real.pi)

/-- The exact collision locus of the ellipse parameterization. -/
def contourPointCollisionSet : Set (ℝ × ℝ) :=
  {p | Li2Lean.p0EllipsePoint 1 p.1 = Li2Lean.p0EllipsePoint 1 p.2}

/-- The scalar logarithmic kernel used by the double contour integral. -/
def contourLogDistanceKernel (p : ℝ × ℝ) : ℝ :=
  Real.log ‖Li2Lean.p0EllipsePoint 1 p.1 -
    Li2Lean.p0EllipsePoint 1 p.2‖

/-- Analytic premises needed before the off-diagonal factorization can be
integrated.  They are deliberately separate from the finite source algebra. -/
def ContourSelfPotentialAnalyticObligation : Prop :=
  (volume.prod volume) (contourPointCollisionSet ∩ contourParameterSquare) = 0 ∧
    Integrable contourLogDistanceKernel
      ((volume.prod volume).restrict contourParameterSquare) ∧
    ContourSelfPotentialFourierObligation

theorem contourSelfPotential_fourier_of_obligation
    (h : ContourSelfPotentialFourierObligation) (u : ℝ) :
    contourSelfPotential u = contourSelfPotentialFourier u := h u

/-! ## Full `Weta` source expansion -/

/-- The actual full first-variation field along the contour half-parameter. -/
def contourWeta (x : ℝ) : ℝ :=
  Config.Weta actualReference (Li2Lean.p0EllipsePoint 1 (Real.pi * x))

/-- The pinned real-axis field is retained as a separate full-`Weta` callback. -/
def pinnedWeta (x : ℝ) : ℝ :=
  Config.Weta actualReference (Complex.ofReal x)

/-- Source expansion of the full field, conditional only on the finite Fourier
identity for the actual contour potential.  The pinned term is explicit. -/
theorem contourWeta_eq_actual_source (x : ℝ) :
    contourWeta x =
      Config.A0 (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
        Config.phi (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
        2 * ConfigSegment.pinnedReferenceComplexPotential
          (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
        2 * contourSelfPotential (Real.pi * x) -
        reflectedFrequencyPotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) := by
  unfold contourWeta Config.Weta actualReference
  change Config.A0 (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
      Config.phi (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
      2 * (ConfigSegment.pinnedReferenceComplexPotential
        (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) +
        contourReferencePotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x))) -
      reflectedFrequencyPotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) = _
  simp only [contourSelfPotential]
  ring

/-- Source expansion of the full field, conditional only on the finite Fourier
identity for the actual contour potential.  The pinned term is explicit. -/
theorem contourWeta_eq_full_source
    (h : ContourSelfPotentialFourierObligation) (x : ℝ) :
    contourWeta x =
      Config.A0 (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
        Config.phi (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
        2 * ConfigSegment.pinnedReferenceComplexPotential
          (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
        2 * contourSelfPotentialFourier (Real.pi * x) -
        reflectedFrequencyPotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) := by
  have hp : contourReferencePotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) =
      contourSelfPotentialFourier (Real.pi * x) := by
    simpa only [contourSelfPotential] using h (Real.pi * x)
  unfold contourWeta Config.Weta actualReference
  change Config.A0 (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
      Config.phi (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) -
      2 * (ConfigSegment.pinnedReferenceComplexPotential
        (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) +
        contourReferencePotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x))) -
      reflectedFrequencyPotential (Li2Lean.p0EllipsePoint 1 (Real.pi * x)) = _
  rw [hp]
  ring

/-- Full-`Weta` cell-bound obligations for the contour and pinned rows.  This
is an interface, not an analytic proof of either family of bounds. -/
structure FullWetaCellObligations where
  contour_cells : List ReceiptCell
  pinned_cells : List ReceiptCell
  contour_data_exact : contour_cells = ConfigData.contourCells
  pinned_data_exact : pinned_cells = ConfigData.pinnedCells
  contour_cell_bounds : ∀ c ∈ contour_cells, ∀ hwidth : c.lo ≤ c.hi,
    c.modelRemainderValid contourWeta hwidth
  pinned_cell_bounds : ∀ c ∈ pinned_cells, ∀ hwidth : c.lo ≤ c.hi,
    c.modelRemainderValid pinnedWeta hwidth

/-! ## Soundness of the finite directed checker -/

/-- Semantic interface for a finite contour lower-bound checker. -/
def ContourCellChecker (cells : List ReceiptCell) (f : ℝ → ℝ) : Prop :=
  ExactChain cells 0 1 ∧
    ∀ c ∈ cells, ∀ hwidth : c.lo ≤ c.hi,
      c.modelRemainderValid f hwidth

/-- A checker with an explicit rational floor on every source row. -/
def ContourCellCheckerWithFloor (cells : List ReceiptCell) (f : ℝ → ℝ)
    (lower : ℚ) : Prop :=
  ContourCellChecker cells f ∧ ∀ c, c ∈ cells → lower ≤ c.lower

/-- Exact-chain coverage plus cell remainders imply the checker bound. -/
theorem contourCellChecker_sound {cells : List ReceiptCell} {f : ℝ → ℝ}
    (hchecker : ContourCellChecker cells f) {x : ℝ}
    (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    ∃ c, c ∈ cells ∧ (c.lower : ℝ) ≤ f x := by
  rcases hchecker with ⟨hchain, hrem⟩
  exact exactChain_sound hchain hrem (by simpa using hx0) (by simpa using hx1)

/-- The floor checker implies a global lower bound on the whole covered
interval; no numerical or transcendental fact is hidden in this implication. -/
theorem contourCellCheckerWithFloor_sound
    {cells : List ReceiptCell} {f : ℝ → ℝ} {lower : ℚ}
    (hchecker : ContourCellCheckerWithFloor cells f lower)
    {x : ℝ} (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    (lower : ℝ) ≤ f x := by
  obtain ⟨c, hmem, hbound⟩ := contourCellChecker_sound hchecker.1 hx0 hx1
  have hfloor : lower ≤ c.lower := hchecker.2 c hmem
  exact le_trans (by exact_mod_cast hfloor) hbound

/-- The specialized full-`Weta` checker preserves the literal contour rows
and exposes its sound lower-bound consequence on `[0,1]`. -/
theorem fullWeta_contour_checker_sound (O : FullWetaCellObligations)
    {x : ℝ} (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    ∃ c, c ∈ O.contour_cells ∧ (c.lower : ℝ) ≤ contourWeta x := by
  have hchain : ExactChain O.contour_cells 0 1 := by
    rw [O.contour_data_exact]
    exact ConfigData.contourCells_exactChain
  exact exactChain_sound hchain O.contour_cell_bounds
    (by simpa using hx0) (by simpa using hx1)

theorem fullWeta_contour_floor_sound (O : FullWetaCellObligations)
    {x : ℝ} (hx0 : (0 : ℝ) ≤ x) (hx1 : x ≤ 1) :
    Config.hEta ≤ contourWeta x := by
  obtain ⟨c, hmem, hbound⟩ := fullWeta_contour_checker_sound O hx0 hx1
  have hmem' : c ∈ ConfigData.contourCells := by
    rw [← O.contour_data_exact]
    exact hmem
  have hfloor := ConfigThreshold.contourCells_lower_floor hmem'
  have hfloorR : (-669 / 200 : ℝ) ≤ (c.lower : ℝ) := by
    exact_mod_cast hfloor
  exact le_trans (by norm_num [Config.hEta]) (hfloorR.trans hbound)

theorem fullWeta_pinned_checker_sound (O : FullWetaCellObligations)
    {x : ℝ} (hx0 : (1 / 4 : ℝ) ≤ x) (hx1 : x ≤ 5 / 4) :
    ∃ c, c ∈ O.pinned_cells ∧ (c.lower : ℝ) ≤ pinnedWeta x := by
  have hchain : ExactChain O.pinned_cells (1 / 4) (5 / 4) := by
    rw [O.pinned_data_exact]
    exact ConfigData.pinnedCells_exactChain
  exact exactChain_sound hchain O.pinned_cell_bounds
    (by simpa using hx0) (by simpa using hx1)

end

end Li2Lean.P0.ConfigContourSelfPotential
