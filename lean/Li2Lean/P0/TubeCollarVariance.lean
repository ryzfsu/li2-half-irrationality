/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeCollarGeometry

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

def tubeCollarVarianceCoefficient : ℝ := semiMajor ^ 2

def tubeCollarClearance : ℝ := 5383 / 40000

def tubeCollarGreenCoefficient : ℝ := 1307240712 / 28976689

theorem tubeCollar_coefficients_exact :
    tubeCollarVarianceCoefficient / (2 * tubeCollarClearance ^ 2) =
      tubeCollarGreenCoefficient := by
  have hA : semiMajor ^ 2 = (163405089 : ℝ) / 100000000 := by
    norm_num [semiMajor]
  have hc : 2 * tubeCollarClearance ^ 2 =
      (28976689 : ℝ) / 800000000 := by
    norm_num [tubeCollarClearance]
  rw [tubeCollarVarianceCoefficient, hA, hc]
  norm_num [tubeCollarGreenCoefficient]

theorem tubeCollar_greenCoefficient_lt_48 : tubeCollarGreenCoefficient < 48 := by
  norm_num [tubeCollarGreenCoefficient]

/- The actual v10 source-to-collar clearance, derived from its level function. -/
set_option maxHeartbeats 1000000 in
theorem tubeCollar_source_boundary_distance {x : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0) (u : ℝ) :
    semiMajor - center ≤ dist x (gammaPoint u) := by
  let t := Real.cos u
  let v := center + semiMajor * t
  have ht : -1 ≤ t ∧ t ≤ 1 := ⟨Real.neg_one_le_cos u, Real.cos_le_one u⟩
  have hsin : Real.sin u ^ 2 = 1 - t ^ 2 := by
    dsimp [t]
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hre : (gammaPoint u).re = v := by
    simp [v, gammaPoint, t, Complex.cos_ofReal_re]
  have him' : (gammaPoint u).im = semiMinor * Real.sin u := by
    simp [gammaPoint, Complex.sin_ofReal_re]
  have hdistSq : dist x (gammaPoint u) ^ 2 =
      (v - x.re) ^ 2 + semiMinor ^ 2 * (1 - t ^ 2) := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.sub_re, Complex.sub_im, him, hre, him']
    rw [show (0 - semiMinor * Real.sin u) * (0 - semiMinor * Real.sin u) =
      semiMinor ^ 2 * (Real.sin u ^ 2) by ring, hsin]
    ring
  have hA : 0 < semiMajor := by norm_num [semiMajor]
  have hB : 0 < semiMinor := by norm_num [semiMinor]
  have hc : 0 < center := by norm_num [center]
  have hd : 0 < semiMajor - center := by norm_num [semiMajor, center]
  have hcoef : 0 < semiMajor ^ 2 - semiMinor ^ 2 := by
    norm_num [semiMajor, semiMinor]
  have hleftSlope : semiMajor ^ 2 - semiMinor ^ 2 < center * semiMajor := by
    norm_num [semiMajor, semiMinor, center]
  have hrightSlope : semiMajor ^ 2 - semiMinor ^ 2 < semiMajor * (2 - center) := by
    norm_num [semiMajor, semiMinor, center]
  have hmiddle : semiMinor ^ 2 * (1 - (center / semiMajor) ^ 2) ≥
      (semiMajor - center) ^ 2 := by
    norm_num [semiMajor, semiMinor, center]
  have hrightEnd : (center + semiMajor - 2) ^ 2 ≥
      (semiMajor - center) ^ 2 := by
    norm_num [semiMajor, center]
  have hdistLower : (semiMajor - center) ^ 2 ≤ dist x (gammaPoint u) ^ 2 := by
    by_cases hleft : v ≤ 0
    · have htplus : 0 ≤ t + 1 := by linarith [ht.1]
      have hfactor : 0 ≤ 2 * center * semiMajor +
          (semiMajor ^ 2 - semiMinor ^ 2) * (t - 1) := by
        have hterm : 0 ≤ (semiMajor ^ 2 - semiMinor ^ 2) * (t + 1) :=
          mul_nonneg hcoef.le htplus
        nlinarith [hleftSlope, hterm]
      have hpoly : (center + semiMajor * t) ^ 2 +
          semiMinor ^ 2 * (1 - t ^ 2) ≥ (semiMajor - center) ^ 2 := by
        have heq : (center + semiMajor * t) ^ 2 +
            semiMinor ^ 2 * (1 - t ^ 2) - (semiMajor - center) ^ 2 =
              (t + 1) * (2 * center * semiMajor +
                (semiMajor ^ 2 - semiMinor ^ 2) * (t - 1)) := by ring
        calc
          _ = (semiMajor - center) ^ 2 +
              (t + 1) * (2 * center * semiMajor +
                (semiMajor ^ 2 - semiMinor ^ 2) * (t - 1)) := by
                  linear_combination heq
          _ ≥ _ := by nlinarith [mul_nonneg htplus hfactor]
      have hx0 : 0 ≤ x.re := hx.1
      have hhor : v ^ 2 ≤ (v - x.re) ^ 2 := by
        have hv : v ≤ 0 := hleft
        have hfac : 0 ≤ x.re - 2 * v := by linarith
        have hprod : 0 ≤ x.re * (x.re - 2 * v) := mul_nonneg hx0 hfac
        have heq : (v - x.re) ^ 2 = v ^ 2 + x.re * (x.re - 2 * v) := by ring
        calc
          v ^ 2 ≤ v ^ 2 + x.re * (x.re - 2 * v) := le_add_of_nonneg_right hprod
          _ = (v - x.re) ^ 2 := heq.symm
      calc
        (semiMajor - center) ^ 2 ≤
            v ^ 2 + semiMinor ^ 2 * (1 - t ^ 2) := hpoly
        _ ≤ (v - x.re) ^ 2 + semiMinor ^ 2 * (1 - t ^ 2) :=
          by nlinarith [hhor]
        _ = dist x (gammaPoint u) ^ 2 := by rw [hdistSq]
    · by_cases hright : 2 ≤ v
      · have htminus : 0 ≤ 1 - t := by linarith [ht.2]
        have hfactor : 0 ≤ -(2 * semiMajor * (center - 2) +
            (semiMajor ^ 2 - semiMinor ^ 2) * (t + 1)) := by
          have hterm : 0 ≤ (semiMajor ^ 2 - semiMinor ^ 2) * (2 - (t + 1)) :=
            mul_nonneg hcoef.le (by linarith [ht.2])
          nlinarith [hrightSlope, hterm]
        have hpoly : (center + semiMajor * t - 2) ^ 2 +
            semiMinor ^ 2 * (1 - t ^ 2) ≥ (center + semiMajor - 2) ^ 2 := by
          have heq : (center + semiMajor * t - 2) ^ 2 +
              semiMinor ^ 2 * (1 - t ^ 2) - (center + semiMajor - 2) ^ 2 =
                (t - 1) * (2 * semiMajor * (center - 2) +
                  (semiMajor ^ 2 - semiMinor ^ 2) * (t + 1)) := by ring
          calc
            _ = (center + semiMajor - 2) ^ 2 +
                (t - 1) * (2 * semiMajor * (center - 2) +
                  (semiMajor ^ 2 - semiMinor ^ 2) * (t + 1)) := by
                    linear_combination heq
          _ ≥ _ := by
              have htm1 : t - 1 ≤ 0 := by linarith [ht.2]
              have hS : 2 * semiMajor * (center - 2) +
                  (semiMajor ^ 2 - semiMinor ^ 2) * (t + 1) ≤ 0 := by
                linarith [hfactor]
              have hprod := mul_nonneg_of_nonpos_of_nonpos htm1 hS
              nlinarith [hprod]
        have hx2 : x.re ≤ 2 := hx.2
        have hhor : (v - 2) ^ 2 ≤ (v - x.re) ^ 2 := by
          have hv : 0 ≤ v - 2 := sub_nonneg.mpr hright
          have hx' : 0 ≤ 2 - x.re := sub_nonneg.mpr hx2
          have hfac : 0 ≤ 2 * (v - 2) + (2 - x.re) :=
            add_nonneg (mul_nonneg (by norm_num) hv) hx'
          have hprod : 0 ≤ (2 - x.re) * (2 * (v - 2) + (2 - x.re)) :=
            mul_nonneg hx' hfac
          have heq : (v - x.re) ^ 2 = (v - 2) ^ 2 +
              (2 - x.re) * (2 * (v - 2) + (2 - x.re)) := by ring
          calc
            (v - 2) ^ 2 ≤ (v - 2) ^ 2 +
                (2 - x.re) * (2 * (v - 2) + (2 - x.re)) :=
              le_add_of_nonneg_right hprod
            _ = (v - x.re) ^ 2 := heq.symm
        calc
          (semiMajor - center) ^ 2 ≤ (center + semiMajor - 2) ^ 2 := hrightEnd
          _ ≤ (center + semiMajor * t - 2) ^ 2 +
              semiMinor ^ 2 * (1 - t ^ 2) := hpoly
          _ ≤ (v - x.re) ^ 2 + semiMinor ^ 2 * (1 - t ^ 2) :=
            by nlinarith [hhor]
          _ = dist x (gammaPoint u) ^ 2 := by
            rw [hdistSq]
      · have hvpos : 0 < v := lt_of_not_ge hleft
        have hvlt : v < 2 := lt_of_not_ge hright
        have htlo : -(center / semiMajor) < t := by
          rw [← neg_div]
          exact (div_lt_iff₀ hA).2 (by
            change 0 < center + semiMajor * t at hvpos
            linarith)
        have hthi : t < (2 - center) / semiMajor := by
          exact (lt_div_iff₀ hA).2 (by
            change center + semiMajor * t < 2 at hvlt
            linarith)
        have hratio : (2 - center) / semiMajor ≤ center / semiMajor := by
          exact (div_le_div_iff_of_pos_right hA).2 (by norm_num [center])
        have htl : -(center / semiMajor) ≤ t := le_of_lt htlo
        have htu : t ≤ center / semiMajor := (le_of_lt hthi).trans hratio
        have htsq : t ^ 2 ≤ (center / semiMajor) ^ 2 := by
          have hp : 0 ≤ (center / semiMajor - t) * (center / semiMajor + t) :=
            mul_nonneg (by linarith [htu]) (by linarith [htl])
          nlinarith [hp]
        have hvert : (semiMajor - center) ^ 2 ≤
            semiMinor ^ 2 * (1 - t ^ 2) := by
          have hinner : 1 - (center / semiMajor) ^ 2 ≤ 1 - t ^ 2 := by
            linarith [htsq]
          have hscaled := mul_le_mul_of_nonneg_left hinner (sq_nonneg semiMinor)
          exact le_trans hmiddle hscaled
        calc
          (semiMajor - center) ^ 2 ≤ semiMinor ^ 2 * (1 - t ^ 2) := hvert
          _ ≤ (v - x.re) ^ 2 + semiMinor ^ 2 * (1 - t ^ 2) :=
            le_add_of_nonneg_left (sq_nonneg (v - x.re))
          _ = dist x (gammaPoint u) ^ 2 := by rw [hdistSq]
  have hdistNonneg : 0 ≤ dist x (gammaPoint u) := dist_nonneg
  by_contra hnot
  have hlt : dist x (gammaPoint u) < semiMajor - center := lt_of_not_ge hnot
  have hprod : 0 < (semiMajor - center - dist x (gammaPoint u)) *
      (semiMajor - center + dist x (gammaPoint u)) := by
    apply mul_pos
    · linarith
    · linarith
  nlinarith [hdistLower, hprod]

theorem tube_collar_source_distance_clearance {δ : ℝ} {z x : ℂ}
    (hδ : δ ≤ tubeRadiusMax) (htube : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0) :
    tubeCollarClearance ≤ dist z x := by
  have hlow : semiMajor - center - dist z x ≤ Metric.infDist z Gamma := by
    apply (Metric.le_infDist gamma_nonempty_collar).2
    rintro w ⟨u, rfl⟩
    have hsource := tubeCollar_source_boundary_distance hx him u
    have htriangle := dist_triangle x z (gammaPoint u)
    rw [dist_comm x z] at htriangle
    linarith
  have ht : Metric.infDist z Gamma ≤ δ := htube
  have hδ' : δ ≤ (1 / 64 : ℝ) := by
    simpa [tubeRadiusMax] using hδ
  have hbound : semiMajor - center - δ ≤ dist z x := by
    have h' := le_trans hlow ht
    linarith
  have hconst : tubeCollarClearance = semiMajor - center - (1 / 64 : ℝ) := by
    norm_num [tubeCollarClearance, semiMajor, center]
  rw [hconst]
  linarith

/-- Pointwise logarithmic Taylor bound. The only singular cases are excluded
by the explicit nonzero hypotheses; no local small-displacement condition is used. -/
theorem log_norm_sub_le_re_displacement_add_sq {y z x : ℂ}
    (hyx : y ≠ x) (hzx : z ≠ x) :
    Real.log ‖y - x‖ - Real.log ‖z - x‖ ≤
      ((y - z) / (z - x)).re + ‖(y - z) / (z - x)‖ ^ 2 / 2 := by
  have hypos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  have hzpos : 0 < ‖z - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hzx)
  let u : ℂ := (y - z) / (z - x)
  have hquot : (y - x) / (z - x) = 1 + u := by
    dsimp [u]
    field_simp [hzx]
    ring
  have hnormquot : ‖y - x‖ / ‖z - x‖ = ‖1 + u‖ := by
    rw [← norm_div, hquot]
  have hratioPos : 0 < (‖y - x‖ / ‖z - x‖) ^ 2 := sq_pos_of_pos (div_pos hypos hzpos)
  have hlog := Real.log_le_sub_one_of_pos hratioPos
  rw [Real.log_pow, Real.log_div hypos.ne' hzpos.ne'] at hlog
  have hnorm : ‖1 + u‖ ^ 2 = 1 + 2 * u.re + ‖u‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp only [Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im]
    have hu : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by
      rw [Complex.sq_norm, Complex.normSq_apply]
      ring
    rw [hu]
    ring
  rw [hnormquot, hnorm] at hlog
  have hlog' : 2 * (Real.log ‖y - x‖ - Real.log ‖z - x‖) ≤
      2 * u.re + ‖u‖ ^ 2 := by
    norm_num at hlog
    linarith [hlog]
  simpa [u] using (show Real.log ‖y - x‖ - Real.log ‖z - x‖ ≤
      u.re + ‖u‖ ^ 2 / 2 by nlinarith [hlog'])

/-- The logarithmic potential excess is bounded by the variance whenever the
probability measure has the stated barycenter. Integrability and the zero-mass
collision condition are explicit so this lemma preserves the original measure
class rather than silently imposing an absolutely continuous replacement. -/
theorem log_potential_excess_le_variance {μ : Measure ℂ} [IsProbabilityMeasure μ]
    {z x : ℂ} (hzx : z ≠ x) (hμx : μ {x} = 0)
    (hmeanInt : Integrable (fun y : ℂ => y) μ)
    (hmean : (∫ y : ℂ, y ∂μ) = z)
    (hlogInt : Integrable (fun y : ℂ => Real.log ‖y - x‖) μ)
    (hlinInt : Integrable (fun y : ℂ => (y - z) / (z - x)) μ)
    (hvarInt : Integrable (fun y : ℂ => ‖y - z‖ ^ 2) μ) :
    (∫ y : ℂ, Real.log ‖y - x‖ ∂μ) - Real.log ‖z - x‖ ≤
      (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) / (2 * ‖z - x‖ ^ 2) := by
  let u : ℂ → ℂ := fun y => (y - z) / (z - x)
  let lin : ℂ → ℝ := fun y => (u y).re
  let quad : ℂ → ℝ := fun y => ‖u y‖ ^ 2
  have hquadInt : Integrable quad μ := by
    simpa [quad, u, norm_div, div_pow] using
      hvarInt.div_const (‖z - x‖ ^ 2)
  have hlinInt' : Integrable lin μ := hlinInt.re
  have hpoint : ∀ᵐ y ∂μ,
      Real.log ‖y - x‖ - Real.log ‖z - x‖ ≤ lin y + quad y / 2 := by
    have hnotx : ∀ᵐ y ∂μ, y ≠ x := by
      rw [ae_iff]
      simpa using hμx
    filter_upwards [hnotx] with y hy
    simpa [lin, quad, u] using log_norm_sub_le_re_displacement_add_sq hy hzx
  have hmeanShift : (∫ y : ℂ, (y - z) ∂μ) = 0 := by
    rw [integral_sub hmeanInt (integrable_const z), integral_const, hmean]
    simp
  have hlinZero : (∫ y : ℂ, lin y ∂μ) = 0 := by
    have hcomplex : (∫ y : ℂ, u y ∂μ) = 0 := by
      dsimp [u]
      rw [show (fun y : ℂ => (y - z) / (z - x)) =
        fun y => (y - z) * (z - x)⁻¹ by funext y; rw [div_eq_mul_inv]]
      rw [integral_mul_const, hmeanShift]
      simp
    have hlinZero' :
        (∫ y : ℂ, ((y - z) / (z - x)).re ∂μ) = 0 := by
      have hcomplex' : (∫ y : ℂ, (y - z) / (z - x) ∂μ) = 0 := by
        simpa [u] using hcomplex
      calc
        _ = (∫ y : ℂ, (y - z) / (z - x) ∂μ).re := integral_re hlinInt
        _ = 0 := by rw [hcomplex']; simp
    simpa [lin, u] using hlinZero'
  have hleftInt : Integrable
      (fun y : ℂ => Real.log ‖y - x‖ - Real.log ‖z - x‖) μ :=
    hlogInt.sub (integrable_const (Real.log ‖z - x‖))
  have hleft :
      (∫ y : ℂ, Real.log ‖y - x‖ ∂μ) - Real.log ‖z - x‖ =
        ∫ y : ℂ, (Real.log ‖y - x‖ - Real.log ‖z - x‖) ∂μ := by
    rw [integral_sub hlogInt (integrable_const (Real.log ‖z - x‖)), integral_const]
    simp
  have hrightInt : Integrable (fun y : ℂ => lin y + quad y / 2) μ :=
    hlinInt'.add (hquadInt.div_const 2)
  have hmono := integral_mono_ae hleftInt hrightInt hpoint
  rw [← hleft] at hmono
  have hquadEq : (∫ y : ℂ, quad y ∂μ) =
      (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) / ‖z - x‖ ^ 2 := by
    have hpoint' : ∀ y : ℂ, quad y = ‖y - z‖ ^ 2 / ‖z - x‖ ^ 2 := by
      intro y
      simp only [quad, u, norm_div, div_pow]
    simp only [hpoint']
    rw [integral_div]
  calc
    _ ≤ ∫ y : ℂ, (lin y + quad y / 2) ∂μ := hmono
    _ = (∫ y : ℂ, lin y ∂μ) + (∫ y : ℂ, quad y ∂μ) / 2 := by
      rw [integral_add hlinInt' (hquadInt.div_const 2), integral_div]
    _ = (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) / (2 * ‖z - x‖ ^ 2) := by
      rw [hlinZero, hquadEq]
      ring

/-- Conditional measure-level collar bound with the exact v10 coefficient.
Application to the Cauchy sweep still requires proving its barycenter,
variance, collision, and integrability hypotheses. -/
theorem tube_collar_log_potential_excess_bound
    {δ : ℝ} {z x : ℂ} {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hδ : δ ≤ tubeRadiusMax) (hz : z ∈ ellipseInterior) (htube : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0)
    (hμx : μ {x} = 0)
    (hmeanInt : Integrable (fun y : ℂ => y) μ)
    (hmean : (∫ y : ℂ, y ∂μ) = z)
    (hlogInt : Integrable (fun y : ℂ => Real.log ‖y - x‖) μ)
    (hlinInt : Integrable (fun y : ℂ => (y - z) / (z - x)) μ)
    (hvarInt : Integrable (fun y : ℂ => ‖y - z‖ ^ 2) μ)
    (hvariance : (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) ≤
      tubeCollarVarianceCoefficient * ellipseLevel z) :
    (∫ y : ℂ, Real.log ‖y - x‖ ∂μ) - Real.log ‖z - x‖ ≤
      tubeCollarGreenCoefficient * ellipseLevel z := by
  have hclear := tube_collar_source_distance_clearance hδ htube hx him
  have hzx : z ≠ x := by
    intro heq
    rw [heq, dist_self] at hclear
    have hc : 0 < tubeCollarClearance := by
      norm_num [tubeCollarClearance]
    linarith
  have hvar := log_potential_excess_le_variance hzx hμx hmeanInt hmean
    hlogInt hlinInt hvarInt
  have hlevel : 0 < ellipseLevel z := by
    change 0 < ellipseLevel z at hz
    exact hz
  have hvarNonneg : 0 ≤ (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) := by
    apply integral_nonneg_of_ae
    filter_upwards with y
    positivity
  have hcoef : 0 < tubeCollarVarianceCoefficient := by
    dsimp [tubeCollarVarianceCoefficient]
    exact sq_pos_of_pos (by norm_num [semiMajor])
  have hnormClear : tubeCollarClearance ≤ ‖z - x‖ := by
    simpa only [dist_eq_norm] using hclear
  have hclearPos : 0 < tubeCollarClearance := by
    norm_num [tubeCollarClearance]
  have hnormPos : 0 < ‖z - x‖ := hclearPos.trans_le hnormClear
  have hsq : tubeCollarClearance ^ 2 ≤ ‖z - x‖ ^ 2 := by
    have hdiff : 0 ≤ ‖z - x‖ - tubeCollarClearance := sub_nonneg.mpr hnormClear
    have hprod := mul_nonneg hdiff
      (show 0 ≤ ‖z - x‖ + tubeCollarClearance by positivity)
    nlinarith [hprod]
  have hden : 0 < 2 * tubeCollarClearance ^ 2 := by positivity
  have hdenle : 2 * tubeCollarClearance ^ 2 ≤ 2 * ‖z - x‖ ^ 2 := by nlinarith [hsq]
  have hratio :
      (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) / (2 * ‖z - x‖ ^ 2) ≤
        tubeCollarGreenCoefficient * ellipseLevel z := by
    calc
      _ ≤ (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) / (2 * tubeCollarClearance ^ 2) :=
        div_le_div_of_nonneg_left hvarNonneg hden hdenle
      _ ≤ (tubeCollarVarianceCoefficient * ellipseLevel z) /
          (2 * tubeCollarClearance ^ 2) :=
        div_le_div_of_nonneg_right hvariance (le_of_lt hden)
      _ = (tubeCollarVarianceCoefficient / (2 * tubeCollarClearance ^ 2)) *
          ellipseLevel z := by ring
      _ = tubeCollarGreenCoefficient * ellipseLevel z := by
        rw [tubeCollar_coefficients_exact]
  exact le_trans hvar hratio

/-- The exact v10 numerical collar estimate is stronger than the requested
`48 q` bound. -/
theorem tube_collar_log_potential_excess_lt_48
    {δ : ℝ} {z x : ℂ} {μ : Measure ℂ} [IsProbabilityMeasure μ]
    (hδ : δ ≤ tubeRadiusMax) (hz : z ∈ ellipseInterior) (htube : z ∈ tube δ)
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0)
    (hμx : μ {x} = 0)
    (hmeanInt : Integrable (fun y : ℂ => y) μ)
    (hmean : (∫ y : ℂ, y ∂μ) = z)
    (hlogInt : Integrable (fun y : ℂ => Real.log ‖y - x‖) μ)
    (hlinInt : Integrable (fun y : ℂ => (y - z) / (z - x)) μ)
    (hvarInt : Integrable (fun y : ℂ => ‖y - z‖ ^ 2) μ)
    (hvariance : (∫ y : ℂ, ‖y - z‖ ^ 2 ∂μ) ≤
      tubeCollarVarianceCoefficient * ellipseLevel z) :
    (∫ y : ℂ, Real.log ‖y - x‖ ∂μ) - Real.log ‖z - x‖ <
      48 * ellipseLevel z := by
  have h := tube_collar_log_potential_excess_bound hδ hz htube hx him hμx
    hmeanInt hmean hlogInt hlinInt hvarInt hvariance
  have hlevel : 0 < ellipseLevel z := by
    change 0 < ellipseLevel z at hz
    exact hz
  have hc := tubeCollar_greenCoefficient_lt_48
  nlinarith

end
end Li2Lean.P0
