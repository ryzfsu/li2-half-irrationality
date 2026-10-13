/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

open MeasureTheory

namespace Li2Lean
namespace P0

noncomputable section

/-- The center and semiaxes of the OUR P0 ellipse, docs/6333 §3. -/
def center : ℝ := (11281 : ℝ) / 10000
def semiMajor : ℝ := (12783 : ℝ) / 10000
def semiMinor : ℝ := (229 : ℝ) / 200

/-- Boundary parameterization of the unscaled ellipse Γ. -/
def gammaPoint (u : ℝ) : ℂ :=
  Complex.ofReal (center + semiMajor * Real.cos u) +
    Complex.I * Complex.ofReal (semiMinor * Real.sin u)

def Gamma : Set ℂ := Set.range gammaPoint

/-- The signed defining function q of the ellipse interior D. -/
def ellipseLevel (z : ℂ) : ℝ :=
  1 - ((z.re - center) / semiMajor) ^ 2 - (z.im / semiMinor) ^ 2

def ellipseInterior : Set ℂ := {z | 0 < ellipseLevel z}

theorem ellipseLevel_gammaPoint (u : ℝ) : ellipseLevel (gammaPoint u) = 0 := by
  have hre : (gammaPoint u).re = center + semiMajor * Real.cos u := by
    simp [gammaPoint, Complex.cos_ofReal_re]
  have him : (gammaPoint u).im = semiMinor * Real.sin u := by
    simp [gammaPoint, Complex.sin_ofReal_re]
  rw [ellipseLevel, hre, him]
  field_simp [semiMajor, semiMinor]
  nlinarith [Real.sin_sq_add_cos_sq u]

/-- Closed Euclidean δ-tube about the OUR ellipse Γ. -/
def tube (δ : ℝ) : Set ℂ := {z | Metric.infDist z Gamma ≤ δ}

def tubeRadiusMax : ℝ := 1 / 64

def ellipseC : ℂ := Complex.ofReal ((semiMajor + semiMinor) / 2)
def ellipseD : ℂ := Complex.ofReal ((semiMajor - semiMinor) / 2)

/-- Exterior Green correction `e(z)`, zero on D and `log ‖W(z)‖` off D. -/
def exteriorCorrection (W : ℂ → ℂ) (z : ℂ) : ℝ :=
  if 0 < ellipseLevel z then 0 else Real.log ‖W z‖

theorem exteriorCorrection_eq_zero_inside (W : ℂ → ℂ) {z : ℂ}
    (hz : z ∈ ellipseInterior) : exteriorCorrection W z = 0 := by
  change 0 < ellipseLevel z at hz
  by_cases h : 0 < ellipseLevel z
  · simp [exteriorCorrection, h]
  · exact False.elim (h hz)

/-- Joukowski map F(w)=ξ+cw+d/w for nonzero w. -/
def joukowski (w : ℂ) : ℂ :=
  Complex.ofReal center + ellipseC * w + ellipseD * w⁻¹

/-- OUR factorization F(w₁)-F(w₂), docs/6333 §4. -/
theorem joukowski_factorization (w₁ w₂ : ℂ) (hw₁ : w₁ ≠ 0) (hw₂ : w₂ ≠ 0) :
    joukowski w₁ - joukowski w₂ =
      (w₁ - w₂) * (ellipseC - ellipseD * (w₁ * w₂)⁻¹) := by
  have hinv : w₁⁻¹ - w₂⁻¹ = -((w₁ - w₂) * (w₁ * w₂)⁻¹) := by
    field_simp [hw₁, hw₂]
    ring_nf
  unfold joukowski
  calc
    (Complex.ofReal center + ellipseC * w₁ + ellipseD * w₁⁻¹) -
        (Complex.ofReal center + ellipseC * w₂ + ellipseD * w₂⁻¹) =
      ellipseC * (w₁ - w₂) + ellipseD * (w₁⁻¹ - w₂⁻¹) := by ring
    _ = (w₁ - w₂) * (ellipseC - ellipseD * (w₁ * w₂)⁻¹) := by
      rw [hinv]
      ring_nf

theorem ellipseC_norm_gt_ellipseD_norm : ‖ellipseD‖ < ‖ellipseC‖ := by
  norm_num [ellipseC, ellipseD, semiMajor, semiMinor]

/-- The Joukowski map sends the unit-circle parameter to OUR ellipse Γ. -/
theorem joukowski_unit_circle_eq_gammaPoint (u : ℝ) :
    joukowski (Complex.exp (Complex.I * Complex.ofReal u)) = gammaPoint u := by
  unfold joukowski gammaPoint ellipseC ellipseD
  have harg : Complex.I * Complex.ofReal u = Complex.ofReal u * Complex.I := by ring
  have hexp : Complex.exp (Complex.I * Complex.ofReal u) =
      Complex.ofReal (Real.cos u) + Complex.ofReal (Real.sin u) * Complex.I := by
    rw [harg]
    exact Complex.exp_ofReal_mul_I u
  have hargNeg : -(Complex.I * Complex.ofReal u) = Complex.ofReal (-u) * Complex.I := by
    calc
      -(Complex.I * Complex.ofReal u) = -(Complex.ofReal u * Complex.I) := by rw [harg]
      _ = Complex.ofReal (-u) * Complex.I := by
        rw [Complex.ofReal_neg]
        ring
  have hinv : (Complex.exp (Complex.I * Complex.ofReal u))⁻¹ =
      Complex.ofReal (Real.cos u) - Complex.ofReal (Real.sin u) * Complex.I := by
    rw [← Complex.exp_neg]
    rw [hargNeg, Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg, sub_eq_add_neg]
  rw [hinv, hexp]
  push_cast
  ring

/-- The factorization and `|d| < |c|` prove injectivity on `|w| ≥ 1`. -/
theorem joukowski_injective_exterior {w₁ w₂ : ℂ}
    (h₁ : 1 ≤ ‖w₁‖) (h₂ : 1 ≤ ‖w₂‖)
    (hF : joukowski w₁ = joukowski w₂) : w₁ = w₂ := by
  have hw₁ : w₁ ≠ 0 := by
    intro h
    subst w₁
    norm_num at h₁
  have hw₂ : w₂ ≠ 0 := by
    intro h
    subst w₂
    norm_num at h₂
  have hfac := joukowski_factorization w₁ w₂ hw₁ hw₂
  have hzero : (w₁ - w₂) * (ellipseC - ellipseD * (w₁ * w₂)⁻¹) = 0 := by
    rw [← hfac, hF, sub_self]
  rcases mul_eq_zero.mp hzero with hdiff | htail
  · exact sub_eq_zero.mp hdiff
  · have hproduct : w₁ * w₂ ≠ 0 := mul_ne_zero hw₁ hw₂
    have hratio : ellipseC = ellipseD * (w₁ * w₂)⁻¹ := sub_eq_zero.mp htail
    have hscale : ellipseC * (w₁ * w₂) = ellipseD := by
      calc
        ellipseC * (w₁ * w₂) =
            (ellipseD * (w₁ * w₂)⁻¹) * (w₁ * w₂) := by rw [hratio]
        _ = ellipseD := by field_simp [hproduct]
    have hnorm : ‖ellipseC‖ * ‖w₁ * w₂‖ = ‖ellipseD‖ := by
      calc
        ‖ellipseC‖ * ‖w₁ * w₂‖ = ‖ellipseC * (w₁ * w₂)‖ := (norm_mul _ _).symm
        _ = ‖ellipseD‖ := by rw [hscale]
    have hnormProduct : 1 ≤ ‖w₁ * w₂‖ := by
      rw [norm_mul]
      nlinarith [norm_nonneg w₁, norm_nonneg w₂]
    have hnormC_nonneg : 0 ≤ ‖ellipseC‖ := norm_nonneg _
    have hmul : ‖ellipseC‖ ≤ ‖ellipseC‖ * ‖w₁ * w₂‖ := by
      nlinarith [mul_nonneg hnormC_nonneg (sub_nonneg.mpr hnormProduct)]
    linarith [ellipseC_norm_gt_ellipseD_norm]

/-- The collision-faithful logarithmic kernel from docs/6333 §4 (4.5).
At a collision it is `+∞`; away from collisions it is the real logarithmic
kernel used in finite-energy integrals. -/
def extendedLogKernel (z w : ℂ) : WithTop ℝ :=
  if z = w then ⊤ else ((-Real.log ‖z - w‖ : ℝ) : WithTop ℝ)

theorem extendedLogKernel_eq_top_of_collision (z : ℂ) :
    extendedLogKernel z z = ⊤ := by
  simp [extendedLogKernel]

theorem extendedLogKernel_eq_real_of_ne {z w : ℂ} (h : z ≠ w) :
    extendedLogKernel z w = ((-Real.log ‖z - w‖ : ℝ) : WithTop ℝ) := by
  simp [extendedLogKernel, h]

/-- Finite-valued kernel, used only after collision cases have been removed. -/
def realLogKernel (z w : ℂ) : ℝ := -Real.log ‖z - w‖

/-- OUR circle parametrization and normalized pair energy, docs/6333 §4. -/
def circlePoint (z : ℂ) (r t : ℝ) : ℂ :=
  z + Complex.ofReal r * Complex.exp (Complex.I * Complex.ofReal t)

def circlePairEnergy (z w : ℂ) (r : ℝ) : ℝ :=
  (∫ u in (0 : ℝ)..(2 * Real.pi),
    ∫ v in (0 : ℝ)..(2 * Real.pi),
      realLogKernel (circlePoint z r u) (circlePoint w r v)) /
    (2 * Real.pi) ^ 2

/-- The Vandermonde in the increasing Fin-index order used in (3.5). -/
def vandermonde (d : ℕ) (z : Fin d → ℂ) : ℂ :=
  ∏ i : Fin d, ∏ j : Fin d,
    if i.val < j.val then z j - z i else 1

def vandermondeSq (d : ℕ) (z : Fin d → ℂ) : ℂ :=
  vandermonde d z ^ 2

theorem vandermonde_eq_zero_of_collision {d : ℕ} (z : Fin d → ℂ)
    {i j : Fin d} (hij : i ≠ j) (hz : z i = z j) :
    vandermonde d z = 0 := by
  have hval : i.val ≠ j.val := by
    intro h
    exact hij (Fin.ext h)
  rcases lt_or_gt_of_ne hval with hlt | hgt
  · unfold vandermonde
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    simp [hlt, hz]
  · unfold vandermonde
    apply Finset.prod_eq_zero (Finset.mem_univ j)
    apply Finset.prod_eq_zero (Finset.mem_univ i)
    simp [hgt, hz]

theorem vandermondeSq_eq_zero_of_collision {d : ℕ} (z : Fin d → ℂ)
    {i j : Fin d} (hij : i ≠ j) (hz : z i = z j) :
    vandermondeSq d z = 0 := by
  simp [vandermondeSq, vandermonde_eq_zero_of_collision z hij hz]

theorem pairwise_ne_of_vandermonde_ne_zero {d : ℕ} (z : Fin d → ℂ)
    (hV : vandermonde d z ≠ 0) :
    ∀ i j, i ≠ j → z i ≠ z j := by
  intro i j hij hz
  exact hV (vandermonde_eq_zero_of_collision z hij hz)

/-- Remaining factors of the signed configuration integrand multiply the
`Δ(Y)^2` factor displayed in docs/6333 §3 (3.5). -/
def weightedConfiguration (N : ℕ) (Y : Fin N → ℂ) (rest : ℂ) : ℂ :=
  vandermondeSq N Y * rest

theorem weightedConfiguration_eq_zero_of_collision {d : ℕ}
    (Y : Fin d → ℂ) (rest : ℂ) {i j : Fin d}
    (hij : i ≠ j) (hY : Y i = Y j) :
    weightedConfiguration d Y rest = 0 := by
  simp [weightedConfiguration, vandermondeSq_eq_zero_of_collision Y hij hY]

/-- The finite-valued form of (4.5), restricted to distinct centers. -/
def finiteConfigurationTransferDistinct : Prop :=
  ∀ d : ℕ, ∀ z : Fin d → ℂ, ∀ r : ℝ, 0 < r →
    (∀ i j, i ≠ j → z i ≠ z j) →
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else realLogKernel (z i) (z j)) ≥
    (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) -
      (d : ℝ) * Real.log (1 / r)

/-- L7 transfer on every nonzero Vandermonde configuration. -/
def l7VandermondeConfigurationTransfer : Prop :=
  ∀ d : ℕ, ∀ z : Fin d → ℂ, ∀ r : ℝ, 0 < r →
    vandermonde d z ≠ 0 →
    (∑ i : Fin d, ∑ j : Fin d,
      if i = j then 0 else realLogKernel (z i) (z j)) ≥
    (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) -
      (d : ℝ) * Real.log (1 / r)

theorem l7_vandermonde_transfer_of_distinct
    (htransfer : finiteConfigurationTransferDistinct) :
    l7VandermondeConfigurationTransfer := by
  intro d z r hr hV
  exact htransfer d z r hr (pairwise_ne_of_vandermonde_ne_zero z hV)

/-- Every configuration is split into the zero-Vandermonde collision branch
and the pairwise-distinct finite-transfer branch used by the integral proof. -/
def l7CollisionSplit : Prop :=
  ∀ d : ℕ, ∀ z : Fin d → ℂ, ∀ r : ℝ, 0 < r →
    vandermondeSq d z = 0 ∨
      ((∀ i j, i ≠ j → z i ≠ z j) ∧
        (∑ i : Fin d, ∑ j : Fin d,
          if i = j then 0 else realLogKernel (z i) (z j)) ≥
        (∑ i : Fin d, ∑ j : Fin d, circlePairEnergy (z i) (z j) r) -
          (d : ℝ) * Real.log (1 / r))

theorem l7_collision_split_of_distinct_transfer
    (htransfer : finiteConfigurationTransferDistinct) : l7CollisionSplit := by
  intro d z r hr
  by_cases hV : vandermonde d z = 0
  · left
    simp [vandermondeSq, hV]
  · right
    exact ⟨pairwise_ne_of_vandermonde_ne_zero z hV,
      htransfer d z r hr (pairwise_ne_of_vandermonde_ne_zero z hV)⟩

/-- Sweeping a finite measure by a family of harmonic measures is `Measure.bind`.
This uses the generic measure/integral packaging pattern from openai/math's
Catalan 005 project; the ellipse and sweep estimates remain OUR obligations.
Kernel measurability and the harmonic-measure laws are stated separately. -/
def sweptMeasure (ν : Measure ℂ) (ω : ℂ → Measure ℂ) : Measure ℂ :=
  Measure.bind ν ω

/-- Nonnegative disintegration for a sweep. This states no signed Fubini claim;
integrability is required separately for signed potentials. -/
def nonnegativeSweepDisintegration : Prop :=
  ∀ (ν : Measure ℂ) (ω : ℂ → Measure ℂ) (f : ℂ → ENNReal),
    AEMeasurable ω ν → AEMeasurable f (sweptMeasure ν ω) →
    (∫⁻ y, f y ∂sweptMeasure ν ω) =
      ∫⁻ z, (∫⁻ y, f y ∂ω z) ∂ν

theorem nonnegative_sweep_disintegration : nonnegativeSweepDisintegration := by
  intro ν ω f hω hf
  simpa [sweptMeasure] using Measure.lintegral_bind hω hf

/-- Signed sweep Fubini, only under explicit integrability of the inner and
outer integrals. -/
def signedSweepFubini : Prop :=
  ∀ (ν : Measure ℂ) (ω : ℂ → Measure ℂ) (f : ℂ → ℝ),
    AEMeasurable ω ν → AEMeasurable f (sweptMeasure ν ω) →
    (∀ z, Integrable f (ω z)) →
    Integrable (fun z => ∫ y, f y ∂ω z) ν →
    Integrable f (sweptMeasure ν ω) →
    (∫ y, f y ∂sweptMeasure ν ω) =
      ∫ z, (∫ y, f y ∂ω z) ∂ν

/-- The exact 300δ tube-transfer target, with the permitted radius and the
same contour-energy infimum supplied by the later L6/L8 assembly. -/
def tubeTransferStatement (energyInfimum : ℝ → ℝ) (alphaGamma : ℝ) : Prop :=
  ∀ δ : ℝ, 0 < δ → δ ≤ tubeRadiusMax →
    energyInfimum δ ≥ alphaGamma - 300 * δ

theorem tube_error_constant_margin :
    (291 : ℝ) / semiMinor < 300 := by
  norm_num [semiMinor]

theorem tube_error_cost_lt_300 {δ s : ℝ} (hδ : 0 < δ)
    (hs1 : s ≤ 1) :
    (291 : ℝ) * s * δ / semiMinor < 300 * δ := by
  have hminor : 0 < semiMinor := by norm_num [semiMinor]
  have hcoef : 0 ≤ (291 : ℝ) / semiMinor :=
    div_nonneg (by norm_num) hminor.le
  have hsδ : s * δ ≤ δ := by
    calc
      s * δ ≤ 1 * δ := mul_le_mul_of_nonneg_right hs1 hδ.le
      _ = δ := by ring
  calc
    (291 : ℝ) * s * δ / semiMinor =
        ((291 : ℝ) / semiMinor) * (s * δ) := by ring
    _ ≤ ((291 : ℝ) / semiMinor) * δ :=
      mul_le_mul_of_nonneg_left hsδ hcoef
    _ < 300 * δ := mul_lt_mul_of_pos_right tube_error_constant_margin hδ

/-- Green-function and field estimates needed to prove the 300δ statement.
These remain named obligations; they are not inferred from the circle-average
identity. -/
structure TubeTransferObligations (W : ℂ → ℂ) (ω : ℂ → Measure ℂ)
    (greenD : ℂ → ℂ → ℝ)
    (interiorCost exteriorCost energyCost : ℝ → ℝ → ℝ) : Prop where
  exterior_inverse : ∀ z, ellipseLevel z ≤ 0 →
    1 ≤ ‖W z‖ ∧ joukowski (W z) = z
  exterior_distance_lower_bound : ∀ z, ellipseLevel z ≤ 0 →
    semiMinor * (‖W z‖ - 1) ≤ Metric.infDist z Gamma
  correction_bound : ∀ δ z, 0 < δ → δ ≤ tubeRadiusMax → z ∈ tube δ →
    0 ≤ exteriorCorrection W z ∧ exteriorCorrection W z ≤ δ / semiMinor
  harmonic_probability : ∀ z, ω z Set.univ = 1
  harmonic_boundary_support : ∀ z, ω z Gammaᶜ = 0
  boundary_dirac : ∀ z, ellipseLevel z = 0 → ω z = Measure.dirac z
  tube_source_separation : ∀ δ z (x : ℂ), 0 < δ → δ ≤ tubeRadiusMax →
    z ∈ tube δ → x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 → z ≠ x
  point_green : ∀ δ z (x : ℂ), 0 < δ → δ ≤ tubeRadiusMax →
    z ∈ tube δ → x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 →
    Integrable (fun y => realLogKernel y x) (ω z) →
    (∫ y, realLogKernel y x ∂ω z) ≤
      realLogKernel z x + exteriorCorrection W z
  pair_green : ∀ z w, z ≠ w →
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) ((ω z).prod (ω w)) →
    (∫ p : ℂ × ℂ, realLogKernel p.1 p.2 ∂((ω z).prod (ω w))) ≤
      realLogKernel z w + exteriorCorrection W z + exteriorCorrection W w
  inner_tube_level : ∀ δ z, 0 < δ → δ ≤ tubeRadiusMax →
    z ∈ tube δ → z ∈ ellipseInterior → ellipseLevel z ≤ 2 * δ / semiMinor
  positive_source_level : ∀ (x : ℂ), x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 →
    1 / 5 < ellipseLevel x
  level_curve_separation : ∀ x, x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 →
    Metric.infDist x {z | ellipseLevel z = 1 / 8} > 1 / 32
  outer_barrier_bound : ∀ δ z x, 0 < δ → δ ≤ tubeRadiusMax →
    z ∈ tube δ → z ∈ ellipseInterior → x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 →
    greenD z x ≤ 48 * ellipseLevel z
  interior_green : ∀ δ z (x : ℂ), 0 < δ → δ ≤ tubeRadiusMax →
    z ∈ tube δ → z ∈ ellipseInterior →
      x.re ∈ Set.Icc (0 : ℝ) 2 → x.im = 0 →
      greenD z x ≤ 96 * δ / semiMinor
  interior_field_cost : ∀ δ s, 0 < δ → δ ≤ tubeRadiusMax → 0 ≤ s → s ≤ 1 →
    interiorCost δ s ≤ 288 * s * δ / semiMinor
  exterior_field_cost : ∀ δ s, 0 < δ → δ ≤ tubeRadiusMax → 0 ≤ s → s ≤ 1 →
    exteriorCost δ s ≤ 3 * s * δ / semiMinor
  total_energy_cost : ∀ δ s, 0 < δ → δ ≤ tubeRadiusMax → 0 ≤ s → s ≤ 1 →
    energyCost δ s ≤ 291 * s * δ / semiMinor

end

end P0
end Li2Lean
