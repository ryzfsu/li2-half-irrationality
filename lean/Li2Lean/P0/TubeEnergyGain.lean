/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorVarianceBridge
import Li2Lean.P0.TubeInteriorPotential
import Li2Lean.P0.MixedCellClearanceFull

/-! # Interior logarithmic gain on the inner tube collar

This file proves the paper's interior Green bound `g_D(z,x) ≤ 96 δ / B`
(v10 `eq:tube-gD`) for the actual Cauchy sweep, by the variance route:

* `log_gain_le_ellipseLevel` bounds the logarithmic gain by
  `A² q(z) / (2 |z-x|²)`;
* every positive source `x ∈ [0,2]` has distance at least `751/5000` from `Γ`
  (the proved mixed-cell clearance), hence `|z - x| ≥ d₀ = 5383/40000` for every
  `z` in a tube of radius at most `1/64`;
* `A² / (2 d₀²) < 48`;
* the concavity of `q` and `|∇q| ≤ 2/B` on `Γ` give `q(z) ≤ 2 dist(z,Γ)/B`.

No Green function, barrier or maximum principle is assumed.
-/

open MeasureTheory Metric

namespace Li2Lean.P0.TubeEnergy

noncomputable section

/-- The literal contour parametrization is the configuration ellipse `baseEllipse`. -/
theorem gammaPoint_eq_baseEllipse (u : ℝ) : gammaPoint u = Config.baseEllipse u := by
  apply Complex.ext <;>
    simp [gammaPoint, Config.baseEllipse, Li2Lean.p0EllipsePoint, center, semiMajor, semiMinor]

/-- Every positive source in `[0,2]` is at distance at least `751/5000` from `Γ`. -/
theorem positive_source_norm_sub_ge {x y : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) (hy : y ∈ Gamma) :
    (751 / 5000 : ℝ) ≤ ‖y - x‖ := by
  obtain ⟨u, rfl⟩ := hy
  have hxeq : x = Complex.ofReal x.re := by
    apply Complex.ext <;> simp [hxim]
  have h := Config.s2_mixed_left_candidate (Config.baseEllipse u) ⟨u, rfl⟩ x.re hx
  rw [gammaPoint_eq_baseEllipse, hxeq]
  simpa [Config.dPlus] using h

/-- Distance form of the positive-source clearance. -/
theorem positive_source_infDist_ge {x : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (751 / 5000 : ℝ) ≤ infDist x Gamma := by
  apply (le_infDist (Set.range_nonempty gammaPoint)).2
  intro y hy
  rw [dist_comm, dist_eq_norm]
  exact positive_source_norm_sub_ge hx hxim hy

/-- The collar separation `d₀ = 751/5000 - 1/64 = 5383/40000`. -/
theorem tube_positive_source_norm_sub_ge {δ : ℝ} (hδ : δ ≤ tubeRadiusMax)
    {z x : ℂ} (hz : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (5383 / 40000 : ℝ) ≤ ‖z - x‖ := by
  have hsrc := positive_source_infDist_ge hx hxim
  have htri := infDist_le_infDist_add_dist (x := x) (y := z) (s := Gamma)
  change infDist z Gamma ≤ δ at hz
  rw [dist_eq_norm, norm_sub_rev] at htri
  norm_num [tubeRadiusMax] at hδ
  linarith

/-- Concavity of `q` and the gradient bound `|∇q| ≤ 2/B` at a contour point. -/
theorem ellipseLevel_le_of_mem_Gamma {z y : ℂ} (hy : y ∈ Gamma) :
    ellipseLevel z ≤ 2 * ‖z - y‖ / semiMinor := by
  obtain ⟨u, rfl⟩ := hy
  set c := Real.cos u
  set s := Real.sin u
  have hcs : c ^ 2 + s ^ 2 = 1 := by
    simp only [c, s]; linarith [Real.sin_sq_add_cos_sq u]
  have hre : (gammaPoint u).re = center + semiMajor * c := by
    simp [gammaPoint, c, Complex.cos_ofReal_re]
  have him : (gammaPoint u).im = semiMinor * s := by
    simp [gammaPoint, s, Complex.sin_ofReal_re]
  set dr := z.re - (gammaPoint u).re with hdr
  set di := z.im - (gammaPoint u).im with hdi
  have hnorm : ‖z - gammaPoint u‖ ^ 2 = dr ^ 2 + di ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [dr, di]; ring
  have hA : semiMajor = 12783 / 10000 := rfl
  have hB : semiMinor = 229 / 200 := rfl
  have hBpos : 0 < semiMinor := by norm_num [hB]
  -- q(z) = -2 (c dr / A + s di / B) - (dr/A)^2 - (di/B)^2
  have hq : ellipseLevel z =
      -2 * (c * dr / semiMajor + s * di / semiMinor) -
        (dr / semiMajor) ^ 2 - (di / semiMinor) ^ 2 := by
    have hzr : z.re = center + semiMajor * c + dr := by rw [hdr, hre]; ring
    have hzi : z.im = semiMinor * s + di := by rw [hdi, him]; ring
    unfold ellipseLevel
    rw [hzr, hzi]
    field_simp [hA, hB]
    rw [hA, hB] at *
    nlinarith [hcs]
  -- Cauchy–Schwarz with `A ≥ B`.
  set X := c * dr / semiMajor + s * di / semiMinor
  have hX : X ^ 2 ≤ (dr ^ 2 + di ^ 2) / semiMinor ^ 2 := by
    have h1 : X ^ 2 ≤ (c ^ 2 + s ^ 2) * ((dr / semiMajor) ^ 2 + (di / semiMinor) ^ 2) := by
      have key : ∀ a b p q : ℝ, (a * p + b * q) ^ 2 ≤ (a ^ 2 + b ^ 2) * (p ^ 2 + q ^ 2) :=
        fun a b p q => by nlinarith [sq_nonneg (a * q - b * p)]
      have hXe : X = c * (dr / semiMajor) + s * (di / semiMinor) := by simp only [X]; ring
      rw [hXe]
      exact key _ _ _ _
    have h2 : (dr / semiMajor) ^ 2 ≤ (dr / semiMinor) ^ 2 := by
      rw [div_pow, div_pow]
      apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
      rw [hA, hB]; norm_num
    rw [hcs, one_mul] at h1
    calc X ^ 2 ≤ (dr / semiMinor) ^ 2 + (di / semiMinor) ^ 2 := by linarith
      _ = (dr ^ 2 + di ^ 2) / semiMinor ^ 2 := by ring
  have hN : 0 ≤ ‖z - gammaPoint u‖ := norm_nonneg _
  have hY : (-X) ^ 2 ≤ (‖z - gammaPoint u‖ / semiMinor) ^ 2 := by
    rw [neg_sq, div_pow, hnorm]; exact hX
  have hYnn : 0 ≤ ‖z - gammaPoint u‖ / semiMinor := div_nonneg hN hBpos.le
  have hnegX : -X ≤ ‖z - gammaPoint u‖ / semiMinor := by
    nlinarith [sq_nonneg (-X - ‖z - gammaPoint u‖ / semiMinor)]
  rw [hq]
  have : 2 * ‖z - gammaPoint u‖ / semiMinor = 2 * (‖z - gammaPoint u‖ / semiMinor) := by ring
  rw [this]
  nlinarith [sq_nonneg (dr / semiMajor), sq_nonneg (di / semiMinor)]

/-- `q(z) ≤ 2 dist(z,Γ) / B` for every point of the plane. -/
theorem interior_level_le_infDist (z : ℂ) :
    ellipseLevel z ≤ 2 * infDist z Gamma / semiMinor := by
  obtain ⟨y, hy, hyd⟩ :=
    TubeInterior.isCompact_Gamma.exists_infDist_eq_dist (Set.range_nonempty gammaPoint) z
  rw [hyd, dist_eq_norm]
  exact ellipseLevel_le_of_mem_Gamma hy

/-- In the inner collar, `q(z) ≤ 2 δ / B`. -/
theorem tube_level_le {δ : ℝ} {z : ℂ} (hz : z ∈ tube δ) :
    ellipseLevel z ≤ 2 * δ / semiMinor := by
  have hB : 0 < semiMinor := by norm_num [semiMinor]
  have h := interior_level_le_infDist z
  change infDist z Gamma ≤ δ at hz
  calc ellipseLevel z ≤ 2 * infDist z Gamma / semiMinor := h
    _ ≤ 2 * δ / semiMinor := by gcongr

/-- The constant of the variance route: `A² / (2 d₀²) ≤ 48`. -/
theorem variance_gain_constant_le :
    semiMajor ^ 2 / (2 * (5383 / 40000 : ℝ) ^ 2) ≤ 48 := by
  norm_num [semiMajor]

/-- Paper `48 q` barrier bound, proved for the actual Cauchy sweep:
the interior Green function `∫ log|y-x| dω_z - log|z-x|` is at most `48 q(z)`
on the collar `D ∩ T_δ`, for every positive source `x ∈ [0,2]`. -/
theorem interiorSweep_log_gain_le_48q {δ : ℝ} (hδ : δ ≤ tubeRadiusMax)
    {z x : ℂ} (hz : z ∈ ellipseInterior) (hzt : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (∫ y, Real.log ‖y - x‖ ∂TubeInterior.interiorSweep z) - Real.log ‖z - x‖ ≤
      48 * ellipseLevel z := by
  haveI : IsProbabilityMeasure (TubeInterior.interiorSweep z) :=
    TubeInterior.interiorSweep_isProbability z
  have hμ : ∀ᵐ y ∂TubeInterior.interiorSweep z, y ∈ Gamma := by
    rw [ae_iff]
    exact TubeInterior.interiorSweep_boundary_support z
  have hd0 := tube_positive_source_norm_sub_ge hδ hzt hx hxim
  have hd0pos : (0 : ℝ) < 5383 / 40000 := by norm_num
  have hzx : z ≠ x := by
    intro h; rw [h, sub_self, norm_zero] at hd0; linarith
  have hgain := TubeVariance.log_gain_le_ellipseLevel _ hμ
    (TubeInterior.interiorSweep_barycenter hz) hzx (d := 751 / 5000) (by norm_num)
    (fun y hy => positive_source_norm_sub_ge hx hxim hy)
  have hq : 0 ≤ ellipseLevel z := le_of_lt hz
  have hcoef : semiMajor ^ 2 / (2 * ‖z - x‖ ^ 2) ≤ 48 := by
    calc semiMajor ^ 2 / (2 * ‖z - x‖ ^ 2) ≤
          semiMajor ^ 2 / (2 * (5383 / 40000 : ℝ) ^ 2) := by
          apply div_le_div_of_nonneg_left (sq_nonneg _) (by positivity)
          gcongr
      _ ≤ 48 := variance_gain_constant_le
  calc _ ≤ (semiMajor ^ 2 / (2 * ‖z - x‖ ^ 2)) * ellipseLevel z := hgain
    _ ≤ 48 * ellipseLevel z := mul_le_mul_of_nonneg_right hcoef hq

/-- Paper `eq:tube-gD`: `g_D(z,x) ≤ 96 δ / B` on the inner collar. -/
theorem interiorSweep_log_gain_le_96 {δ : ℝ} (hδ : δ ≤ tubeRadiusMax)
    {z x : ℂ} (hz : z ∈ ellipseInterior) (hzt : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (∫ y, Real.log ‖y - x‖ ∂TubeInterior.interiorSweep z) - Real.log ‖z - x‖ ≤
      96 * δ / semiMinor := by
  have h := interiorSweep_log_gain_le_48q hδ hz hzt hx hxim
  have hl := tube_level_le hzt
  calc _ ≤ 48 * ellipseLevel z := h
    _ ≤ 48 * (2 * δ / semiMinor) := by linarith
    _ = 96 * δ / semiMinor := by ring

/-- Kernel form: sweeping a positive-source kernel lowers it by at most `96 δ / B`. -/
theorem interiorSweep_realLogKernel_ge {δ : ℝ} (hδ : δ ≤ tubeRadiusMax)
    {z x : ℂ} (hz : z ∈ ellipseInterior) (hzt : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    realLogKernel z x - 96 * δ / semiMinor ≤
      ∫ y, realLogKernel y x ∂TubeInterior.interiorSweep z := by
  have h := interiorSweep_log_gain_le_96 hδ hz hzt hx hxim
  simp only [realLogKernel, integral_neg]
  linarith

end
end Li2Lean.P0.TubeEnergy
