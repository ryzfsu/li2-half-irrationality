/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourPotentialActual
import Li2Lean.P0.ConfigSlackSemanticIdentity

/-!
# Closed form of the actual `Weta` on the contour

For a point `z = X + i Y` with `Y ≠ 0`, every real segment potential of the
actual reference has the elementary primitive
`G(s,Y) = s (log (s^2+Y^2)/2 - 1) + Y * arctan (s/Y)`.  With Lean's
conventions `G(s,0)` is the real primitive `s (log |s| - 1)`, so one formula
covers the whole contour, including the two real points `θ = 0, π`.
The contour self-potential is the exact Fejer/Joukowski Fourier polynomial
(`contourSelfPotential_eq_fourier`).  No numerical input enters this file.
-/

open MeasureTheory

namespace Li2Lean.P0.CA.Contour

noncomputable section

open Li2Lean.LogSegment
open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigReferenceSymmetry

/-- The complex segment primitive. -/
def Gr (s Y : ℝ) : ℝ :=
  s * (Real.log (s ^ 2 + Y ^ 2) / 2 - 1) + Y * Real.arctan (s / Y)

theorem Gr_zero (s : ℝ) : Gr s 0 = primitive s := by
  simp only [Gr, primitive, div_zero, Real.arctan_zero, mul_zero, add_zero]
  congr 1
  rw [show s ^ 2 + 0 ^ 2 = s ^ 2 by ring, Real.log_pow, Real.log_abs]
  push_cast
  ring

theorem hasDerivAt_Gr {Y : ℝ} (hY : Y ≠ 0) (s : ℝ) :
    HasDerivAt (fun v => Gr v Y) (Real.log (s ^ 2 + Y ^ 2) / 2) s := by
  have hpos : 0 < s ^ 2 + Y ^ 2 := by positivity
  have h1 : HasDerivAt (fun v : ℝ => v ^ 2 + Y ^ 2) (2 * s) s := by
    simpa using (hasDerivAt_pow 2 s).add_const (Y ^ 2)
  have hlog := h1.log hpos.ne'
  have hA := (hasDerivAt_id s).mul ((hlog.div_const 2).sub_const 1)
  have hq : HasDerivAt (fun v : ℝ => v / Y) (1 / Y) s := by
    simpa using (hasDerivAt_id s).div_const Y
  have hB := (hq.arctan).const_mul Y
  have h := hA.add hB
  convert h using 1
  · funext v; simp [Gr]
  · simp only [id]
    field_simp
    ring

theorem continuous_logsq {Y : ℝ} (hY : Y ≠ 0) :
    Continuous (fun s : ℝ => Real.log (s ^ 2 + Y ^ 2) / 2) := by
  apply Continuous.div_const
  apply Continuous.log (by fun_prop)
  intro s
  positivity

theorem log_norm_eq (X Y x : ℝ) :
    Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (x : ℂ)‖ =
      Real.log ((X - x) ^ 2 + Y ^ 2) / 2 := by
  have : ((X : ℂ) + (Y : ℂ) * Complex.I) - (x : ℂ) =
      ((X - x : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]

theorem log_norm_add_eq (X Y x : ℝ) :
    Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (x : ℂ)‖ =
      Real.log ((X + x) ^ 2 + Y ^ 2) / 2 := by
  have : ((X : ℂ) + (Y : ℂ) * Complex.I) + (x : ℂ) =
      ((X + x : ℝ) : ℂ) + (Y : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I, Real.log_sqrt (by positivity)]

/-- Segment potential at a non-real point. -/
theorem integral_log_norm_sub {X Y : ℝ} (hY : Y ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (x : ℂ)‖) =
      Gr (X - a) Y - Gr (X - b) Y := by
  simp_rw [log_norm_eq]
  rw [intervalIntegral.integral_comp_sub_left
    (fun s => Real.log (s ^ 2 + Y ^ 2) / 2) X]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => Gr v Y) (fun s _ => hasDerivAt_Gr hY s)
    ((continuous_logsq hY).intervalIntegrable _ _)]

/-- Reflected segment potential at a non-real point. -/
theorem integral_log_norm_add {X Y : ℝ} (hY : Y ≠ 0) (a b : ℝ) :
    (∫ x in a..b, Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (x : ℂ)‖) =
      Gr (X + b) Y - Gr (X + a) Y := by
  simp_rw [log_norm_add_eq]
  rw [intervalIntegral.integral_comp_add_left
    (fun s => Real.log (s ^ 2 + Y ^ 2) / 2) X]
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt
    (f := fun v => Gr v Y) (fun s _ => hasDerivAt_Gr hY s)
    ((continuous_logsq hY).intervalIntegrable _ _)]

theorem continuous_log_norm_sub {X Y : ℝ} (hY : Y ≠ 0) :
    Continuous (fun x : ℝ =>
      Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (x : ℂ)‖) := by
  simp_rw [log_norm_eq]
  exact (continuous_logsq hY).comp (continuous_const.sub continuous_id)

theorem continuous_log_norm_add {X Y : ℝ} (hY : Y ≠ 0) :
    Continuous (fun x : ℝ =>
      Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (x : ℂ)‖) := by
  simp_rw [log_norm_add_eq]
  exact (continuous_logsq hY).comp (continuous_const.add continuous_id)

/-- Complex potential of a piecewise-uniform reference measure. -/
theorem referenceComplexPotential_eq {X Y : ℝ} (hY : Y ≠ 0)
    (start : ℝ) (count : ℕ) (units : List ℕ) :
    (∫ y, Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (y : ℂ)‖
        ∂referenceMeasure start count units) =
      ∑ j ∈ Finset.range count, referenceDensity units j *
        (Gr (X - referenceCellLeft start j) Y -
          Gr (X - referenceCellRight start j) Y) := by
  unfold referenceMeasure
  have hint : ∀ j ∈ Finset.range count, Integrable
      (fun y : ℝ => Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) - (y : ℂ)‖)
      (ENNReal.ofReal (referenceDensity units j) •
        volume.restrict (Set.Ico (referenceCellLeft start j)
          (referenceCellRight start j))) := by
    intro j hj
    exact (((continuous_log_norm_sub hY).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure hint]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_measure, ENNReal.toReal_ofReal (referenceDensity_nonneg units j),
    MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (referenceCellLeft_le_right start j),
    integral_log_norm_sub hY]
  rfl

/-- Reflected complex potential of a piecewise-uniform reference measure. -/
theorem referenceComplexPotential_add_eq {X Y : ℝ} (hY : Y ≠ 0)
    (start : ℝ) (count : ℕ) (units : List ℕ) :
    (∫ y, Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (y : ℂ)‖
        ∂referenceMeasure start count units) =
      ∑ j ∈ Finset.range count, referenceDensity units j *
        (Gr (X + referenceCellRight start j) Y -
          Gr (X + referenceCellLeft start j) Y) := by
  unfold referenceMeasure
  have hint : ∀ j ∈ Finset.range count, Integrable
      (fun y : ℝ => Real.log ‖((X : ℂ) + (Y : ℂ) * Complex.I) + (y : ℂ)‖)
      (ENNReal.ofReal (referenceDensity units j) •
        volume.restrict (Set.Ico (referenceCellLeft start j)
          (referenceCellRight start j))) := by
    intro j hj
    exact (((continuous_log_norm_add hY).integrableOn_Icc).mono_set
      Set.Ico_subset_Icc_self).smul_measure ENNReal.ofReal_ne_top
  rw [integral_finsetSum_measure hint]
  apply Finset.sum_congr rfl
  intro j hj
  rw [integral_smul_measure, ENNReal.toReal_ofReal (referenceDensity_nonneg units j),
    MeasureTheory.integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (referenceCellLeft_le_right start j),
    integral_log_norm_add hY]
  rfl

/-! ## The contour closed form -/

def ellX (θ : ℝ) : ℝ := 11281 / 10000 + 12783 / 10000 * Real.cos θ

def ellY (θ : ℝ) : ℝ := 229 / 200 * Real.sin θ

theorem ellipse_eq (θ : ℝ) :
    Li2Lean.p0EllipsePoint 1 θ = ((ellX θ : ℝ) : ℂ) + ((ellY θ : ℝ) : ℂ) * Complex.I := by
  simp only [Li2Lean.p0EllipsePoint, ellX, ellY, Nat.cast_one, Complex.ofReal_one, one_mul]
  ring

/-- The segment part of `Weta` at `X + iY`, written with `Gr`. -/
def segForm (X Y : ℝ) : ℝ :=
  (Gr (X - 1 / 4) Y - Gr (X - 5 / 4) Y + (Gr (X - 0) Y - Gr (X - 2) Y)) -
    (X * Real.log 2 + (Gr (X + 1 / 2) Y - Gr (X + 0) Y) +
      1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
    2 * (∑ j ∈ Finset.range 32,
      referenceDensity ConfigData.pinnedMassUnits j *
        (Gr (X - referenceCellLeft (1 / 4) j) Y -
          Gr (X - referenceCellRight (1 / 4) j) Y)) -
    (∑ j ∈ Finset.range 160,
      referenceDensity ConfigData.frequencyMassUnits j *
        (Gr (X + referenceCellRight (1 / 2) j) Y -
          Gr (X + referenceCellLeft (1 / 2) j) Y))

/-- The full closed form of the actual `Weta` along the contour. -/
def Wform (θ : ℝ) : ℝ :=
  segForm (ellX θ) (ellY θ) -
    2 * ConfigContourSelfPotential.contourSelfPotentialFourier θ

theorem segForm_zero (X : ℝ) :
    segForm X 0 =
      (primitive (X - 1 / 4) - primitive (X - 5 / 4) +
        (primitive X - primitive (X - 2))) -
      (X * Real.log 2 + (primitive (X + 1 / 2) - primitive X) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
      2 * (∑ j ∈ Finset.range 32,
          referenceDensity ConfigData.pinnedMassUnits j *
            (primitive (X - referenceCellLeft (1 / 4) j) -
              primitive (X - referenceCellRight (1 / 4) j))) -
      (∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits j *
          (primitive (X + referenceCellRight (1 / 2) j) -
            primitive (X + referenceCellLeft (1 / 2) j))) := by
  simp only [segForm, Gr_zero, sub_zero, add_zero]

theorem segForm_eq {X Y : ℝ} (hY : Y ≠ 0) :
    Config.A0 ((X : ℂ) + (Y : ℂ) * Complex.I) -
        Config.phi ((X : ℂ) + (Y : ℂ) * Complex.I) -
        2 * pinnedReferenceComplexPotential ((X : ℂ) + (Y : ℂ) * Complex.I) -
        reflectedFrequencyPotential ((X : ℂ) + (Y : ℂ) * Complex.I) =
      segForm X Y := by
  have hA0 : Config.A0 ((X : ℂ) + (Y : ℂ) * Complex.I) =
      Gr (X - 1 / 4) Y - Gr (X - 5 / 4) Y + (Gr (X - 0) Y - Gr (X - 2) Y) := by
    simp only [Config.A0]
    rw [integral_log_norm_sub hY, integral_log_norm_sub hY]
  have hphi : Config.phi ((X : ℂ) + (Y : ℂ) * Complex.I) =
      X * Real.log 2 + (Gr (X + 1 / 2) Y - Gr (X + 0) Y) +
        1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) := by
    simp only [Config.phi]
    rw [integral_log_norm_add hY]
    simp
  have hpin : pinnedReferenceComplexPotential ((X : ℂ) + (Y : ℂ) * Complex.I) =
      ∑ j ∈ Finset.range 32,
        referenceDensity ConfigData.pinnedMassUnits j *
          (Gr (X - referenceCellLeft (1 / 4) j) Y -
            Gr (X - referenceCellRight (1 / 4) j) Y) := by
    unfold pinnedReferenceComplexPotential pinnedReferenceMeasure
    exact referenceComplexPotential_eq hY _ _ _
  have hfreq : reflectedFrequencyPotential ((X : ℂ) + (Y : ℂ) * Complex.I) =
      ∑ j ∈ Finset.range 160,
        referenceDensity ConfigData.frequencyMassUnits j *
          (Gr (X + referenceCellRight (1 / 2) j) Y -
            Gr (X + referenceCellLeft (1 / 2) j) Y) := by
    rw [reflectedFrequencyPotential_eq_mixed]
    unfold frequencyReferenceMeasure
    exact referenceComplexPotential_add_eq hY _ _ _
  rw [hA0, hphi, hpin, hfreq]
  rfl

/-- The actual `Weta` on the whole contour equals the closed form. -/
theorem weta_ellipse_eq_Wform (θ : ℝ) :
    Config.Weta actualReference (Li2Lean.p0EllipsePoint 1 θ) = Wform θ := by
  have hcont : ConfigContourReference.contourReferencePotential
      (Li2Lean.p0EllipsePoint 1 θ) =
      ConfigContourSelfPotential.contourSelfPotentialFourier θ :=
    ConfigContourPotentialActual.contourSelfPotential_eq_fourier θ
  by_cases hY : ellY θ = 0
  · have hz : Li2Lean.p0EllipsePoint 1 θ = ((ellX θ : ℝ) : ℂ) := by
      rw [ellipse_eq, hY]; simp
    have hc := hcont
    rw [hz] at hc ⊢
    rw [ConfigSlackSemanticIdentity.actualWeta_ofReal_eq_endpoints, hc]
    unfold Wform
    rw [hY, segForm_zero]
    ring
  · rw [ConfigSlackSemanticIdentity.actualWeta_eq_source, hcont]
    unfold Wform
    rw [← segForm_eq hY, ← ellipse_eq]
    ring

end

end Li2Lean.P0.CA.Contour

#print axioms Li2Lean.P0.CA.Contour.weta_ellipse_eq_Wform
