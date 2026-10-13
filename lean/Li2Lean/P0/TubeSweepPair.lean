/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExteriorPair
import Li2Lean.P0.TubeInteriorAtomless
import Li2Lean.P0.TubeInteriorEndpoint
import Li2Lean.P0.TubeCollarVariance
import Li2Lean.P0.TubeInteriorMean
import Li2Lean.P0.TubeVarianceSupport

/-! # The full harmonic sweep and the truncated two-sweep inequality

The sweep family of v10 `sec:tube` is assembled from the actual constructed
measures: the exterior Poisson law strictly outside `D`, and the Cauchy
interior law on the closed ellipse (which is the Dirac mass on `Γ`).

The logarithmic kernel is truncated first,
`truncK ε y x = -log (max ε |y - x|)`, so that every inequality below holds for
every pair of points, including coincident points, with no collision or
separation premise.  The untruncated Green inequalities are only used through
`min`, which is the elementary content of the superharmonic truncation.
-/

open MeasureTheory ProbabilityTheory Filter

namespace Li2Lean.P0.TubeEnergy

noncomputable section

open TubeInterior

/-! ## Geometry: the zero level set is exactly `Γ` -/

theorem mem_Gamma_of_ellipseLevel_eq_zero {z : ℂ} (hz : ellipseLevel z = 0) : z ∈ Gamma := by
  set a := (z.re - center) / semiMajor
  set b := z.im / semiMinor
  have hab : a ^ 2 + b ^ 2 = 1 := by
    simp only [ellipseLevel] at hz; simp only [a, b]; linarith
  set w : ℂ := ⟨a, b⟩
  have hw : ‖w‖ = 1 := by
    rw [← Real.sqrt_one, ← hab, Complex.norm_eq_sqrt_sq_add_sq]
  have hw0 : w ≠ 0 := by
    intro h; rw [h, norm_zero] at hw; norm_num at hw
  refine ⟨w.arg, ?_⟩
  have hc : Real.cos w.arg = a := by rw [Complex.cos_arg hw0, hw, div_one]
  have hs : Real.sin w.arg = b := by rw [Complex.sin_arg, hw, div_one]
  have hA : semiMajor ≠ 0 := by norm_num [semiMajor]
  have hB : semiMinor ≠ 0 := by norm_num [semiMinor]
  apply Complex.ext
  · simp [gammaPoint, hc, a]
    field_simp
    ring
  · simp [gammaPoint, hs, b]
    field_simp

/-! ## Exterior Poisson measures have no atoms -/

theorem ellipsePoissonMeasure_singleton (p x : ℂ) : ellipsePoissonMeasure p {x} = 0 := by
  rw [ellipsePoissonMeasure, Measure.map_apply TubeInterior.continuous_gammaPoint.measurable
    (measurableSet_singleton x)]
  apply withDensity_absolutelyContinuous
  have hc : (gammaPoint ⁻¹' {x}).Countable := countable_gammaPoint_fiber x
  exact hc.measure_zero _

theorem exteriorSweep_singleton (z x : ℂ) : exteriorSweep z {x} = 0 :=
  ellipsePoissonMeasure_singleton _ x

/-! ## The full sweep family -/

/-- Harmonic sweep of v10: exterior Poisson law outside the closed ellipse,
interior Cauchy law on the closed ellipse (the Dirac mass on `Γ`). -/
def tubeSweep (z : ℂ) : Measure ℂ :=
  if ellipseLevel z < 0 then exteriorSweep z else interiorSweep z

/-- The exterior Green correction `e(z)` with the constructed inverse. -/
def tubeCorrection (z : ℂ) : ℝ := exteriorCorrection ellipseExteriorInverse z

theorem continuous_ellipseLevel : Continuous ellipseLevel := by
  unfold ellipseLevel; fun_prop

theorem measurable_tubeSweep : Measurable tubeSweep := by
  unfold tubeSweep
  exact Measurable.ite (measurableSet_lt continuous_ellipseLevel.measurable measurable_const)
    measurable_exteriorSweep measurable_interiorSweep

instance tubeSweep_isProbability (z : ℂ) : IsProbabilityMeasure (tubeSweep z) := by
  unfold tubeSweep
  split_ifs with h
  · exact ⟨exteriorSweep_univ h⟩
  · infer_instance

theorem tubeSweep_boundary_support (z : ℂ) : tubeSweep z Gammaᶜ = 0 := by
  unfold tubeSweep
  split_ifs
  · exact exteriorSweep_boundary_support z
  · exact interiorSweep_boundary_support z

theorem tubeSweep_ae_mem_Gamma (z : ℂ) : ∀ᵐ y ∂tubeSweep z, y ∈ Gamma := by
  rw [ae_iff]; exact tubeSweep_boundary_support z

theorem tubeSweep_eq_dirac_of_mem_Gamma {z : ℂ} (hz : z ∈ Gamma) :
    tubeSweep z = Measure.dirac z := by
  have h0 : ellipseLevel z = 0 := ellipseLevel_eq_zero_of_mem_Gamma hz
  unfold tubeSweep
  rw [if_neg (by rw [h0]; exact lt_irrefl 0)]
  exact interiorSweep_eq_dirac_of_mem_Gamma hz

/-- Off its own center the sweep has no atom; at a boundary center it is a Dirac mass. -/
theorem tubeSweep_singleton_of_ne {z x : ℂ} (hzx : z ≠ x) : tubeSweep z {x} = 0 := by
  by_cases hlt : ellipseLevel z < 0
  · rw [tubeSweep, if_pos hlt]; exact exteriorSweep_singleton z x
  · by_cases hgt : 0 < ellipseLevel z
    · rw [tubeSweep, if_neg hlt]
      exact (interiorSweep_nullSingleton z hgt).measure_singleton x
    · have h0 : ellipseLevel z = 0 := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      rw [tubeSweep_eq_dirac_of_mem_Gamma (mem_Gamma_of_ellipseLevel_eq_zero h0),
        Measure.dirac_apply' _ (measurableSet_singleton x)]
      simp [Set.indicator, hzx]

theorem tubeCorrection_nonneg (z : ℂ) : 0 ≤ tubeCorrection z := by
  unfold tubeCorrection exteriorCorrection
  split_ifs with h
  · exact le_rfl
  · exact Real.log_nonneg (ellipseExteriorInverse_norm_ge_one (not_lt.mp h))

theorem tubeCorrection_eq_zero_of_nonneg_level {z : ℂ} (hz : 0 ≤ ellipseLevel z) :
    tubeCorrection z = 0 := by
  rcases hz.lt_or_eq with h | h
  · exact exteriorCorrection_eq_zero_inside _ h
  · have hG := mem_Gamma_of_ellipseLevel_eq_zero h.symm
    unfold tubeCorrection exteriorCorrection
    rw [if_neg (by rw [← h]; exact lt_irrefl 0)]
    obtain ⟨u, rfl⟩ := hG
    -- On `Γ` the selected exterior root is a unit-circle point.
    have hspec := ellipseExteriorInverse_spec (gammaPoint u) (by rw [← h])
    have hJ : joukowski (Complex.exp (Complex.I * (u : ℂ))) = gammaPoint u :=
      joukowski_unit_circle_eq_gammaPoint u
    have h1 : 1 ≤ ‖Complex.exp (Complex.I * (u : ℂ))‖ := by simp [Complex.norm_exp]
    have heq := joukowski_injective_exterior hspec.1 h1 (hspec.2.trans hJ.symm)
    rw [heq]
    simp [Complex.norm_exp]

theorem measurable_tubeCorrection : Measurable tubeCorrection := by
  unfold tubeCorrection exteriorCorrection
  exact Measurable.ite (measurableSet_lt measurable_const continuous_ellipseLevel.measurable)
    measurable_const (Real.measurable_log.comp measurable_ellipseExteriorInverse.norm)

/-! ## The truncated kernel -/

/-- Truncated logarithmic kernel `-log (max ε |y - x|)`. -/
def truncK (ε : ℝ) (y x : ℂ) : ℝ := -truncatedLogNorm ε (y - x)

theorem truncK_comm (ε : ℝ) (y x : ℂ) : truncK ε y x = truncK ε x y := by
  simp only [truncK, truncatedLogNorm, norm_sub_rev]

theorem continuous_truncK {ε : ℝ} (hε : 0 < ε) :
    Continuous (fun p : ℂ × ℂ => truncK ε p.1 p.2) := by
  unfold truncK
  exact ((continuous_truncatedLogNorm hε).comp (continuous_fst.sub continuous_snd)).neg

theorem continuous_truncK_left {ε : ℝ} (hε : 0 < ε) (x : ℂ) :
    Continuous (fun y => truncK ε y x) :=
  (continuous_truncK hε).comp (continuous_id.prodMk (continuous_const (y := x)))

theorem truncK_le_neg_log {ε : ℝ} (hε : 0 < ε) (y x : ℂ) : truncK ε y x ≤ -Real.log ε := by
  unfold truncK truncatedLogNorm
  exact neg_le_neg (Real.log_le_log hε (le_max_left _ _))

theorem truncK_le_realLogKernel {ε : ℝ} (hε : 0 < ε) {y x : ℂ} (hyx : y ≠ x) :
    truncK ε y x ≤ realLogKernel y x := by
  unfold truncK truncatedLogNorm realLogKernel
  exact neg_le_neg (Real.log_le_log (norm_pos_iff.mpr (sub_ne_zero.mpr hyx)) (le_max_right _ _))

theorem truncK_eq_min {ε : ℝ} (hε : 0 < ε) {y x : ℂ} (hyx : y ≠ x) :
    truncK ε y x = min (-Real.log ε) (realLogKernel y x) := by
  have hpos : 0 < ‖y - x‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hyx)
  unfold truncK truncatedLogNorm realLogKernel
  rcases le_total ε ‖y - x‖ with h | h
  · rw [max_eq_right h, min_eq_right (neg_le_neg (Real.log_le_log hε h))]
  · rw [max_eq_left h, min_eq_left (neg_le_neg (Real.log_le_log hpos h))]

theorem neg_log_le_truncK {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {y x : ℂ}
    (h : ‖y - x‖ ≤ R) : -Real.log R ≤ truncK ε y x := by
  unfold truncK truncatedLogNorm
  exact neg_le_neg (Real.log_le_log (lt_of_lt_of_le hε (le_max_left _ _)) (max_le hεR h))

theorem abs_truncK_le {ε R : ℝ} (hε : 0 < ε) (hεR : ε ≤ R) {y x : ℂ}
    (h : ‖y - x‖ ≤ R) : |truncK ε y x| ≤ |Real.log ε| + |Real.log R| := by
  have h1 := truncK_le_neg_log hε y x
  have h2 := neg_log_le_truncK hε hεR h
  rw [abs_le]
  have a1 := le_abs_self (Real.log R)
  have a2 := abs_nonneg (Real.log ε)
  have a3 := neg_le_abs (Real.log ε)
  have a4 := abs_nonneg (Real.log R)
  constructor <;> linarith

theorem truncK_antitone {ε ε' : ℝ} (hε : 0 < ε) (hεε' : ε ≤ ε') (y x : ℂ) :
    truncK ε' y x ≤ truncK ε y x := by
  unfold truncK truncatedLogNorm
  exact neg_le_neg (Real.log_le_log (lt_of_lt_of_le hε (le_max_left _ _))
    (max_le_max hεε' le_rfl))

theorem truncK_eq_of_le {ε : ℝ} {y x : ℂ} (h : ε ≤ ‖y - x‖) :
    truncK ε y x = realLogKernel y x := by
  unfold truncK truncatedLogNorm realLogKernel
  rw [max_eq_right h]

theorem integrable_truncK_tubeSweep {ε : ℝ} (hε : 0 < ε) (z x : ℂ) :
    Integrable (fun y => truncK ε y x) (tubeSweep z) :=
  TubeVariance.continuous_integrable _ (tubeSweep_ae_mem_Gamma z) (continuous_truncK_left hε x)

/-! ## Truncated point inequality for every center and every source -/

theorem tubeSweep_truncK_le {ε : ℝ} (hε : 0 < ε) (z x : ℂ) :
    (∫ y, truncK ε y x ∂tubeSweep z) ≤ truncK ε z x + tubeCorrection z := by
  have he := tubeCorrection_nonneg z
  have hint := integrable_truncK_tubeSweep hε z x
  by_cases hlt : ellipseLevel z < 0
  · -- exterior center
    have hω : tubeSweep z = exteriorSweep z := by rw [tubeSweep, if_pos hlt]
    have hconst : (∫ y, truncK ε y x ∂tubeSweep z) ≤ -Real.log ε := by
      calc (∫ y, truncK ε y x ∂tubeSweep z) ≤ ∫ _y, -Real.log ε ∂tubeSweep z :=
            integral_mono hint (integrable_const _) (fun y => truncK_le_neg_log hε y x)
        _ = -Real.log ε := by simp
    by_cases hzx : z = x
    · subst hzx
      have : truncK ε z z = -Real.log ε := by
        simp [truncK, truncatedLogNorm, max_eq_left hε.le]
      rw [this]; linarith
    · have hae : ∀ᵐ y ∂tubeSweep z, y ≠ x := by
        rw [ae_iff, hω]
        simpa using exteriorSweep_singleton z x
      have hint0 : Integrable (fun y => realLogKernel y x) (tubeSweep z) := by
        rw [hω]; exact exteriorSweep_integrable_logKernel hlt x
      have hle1 : (∫ y, truncK ε y x ∂tubeSweep z) ≤ ∫ y, realLogKernel y x ∂tubeSweep z :=
        integral_mono_ae hint hint0 (hae.mono fun y hy => truncK_le_realLogKernel hε hy)
      have hgreen : (∫ y, realLogKernel y x ∂tubeSweep z) ≤
          realLogKernel z x + tubeCorrection z := by
        rw [hω]
        by_cases hx : ellipseLevel x = 0
        · exact (exteriorSweep_boundary_source hlt (mem_Gamma_of_ellipseLevel_eq_zero hx)).le
        · exact exteriorSweep_point_green hlt hx hzx
      rw [truncK_eq_min hε hzx, ← min_add_add_right]
      exact le_min (by linarith) (hle1.trans hgreen)
  · by_cases hgt : 0 < ellipseLevel z
    · -- interior center: truncated Jensen
      have hω : tubeSweep z = interiorSweep z := by rw [tubeSweep, if_neg hlt]
      have hj := interiorSweep_truncated_jensen (x := x) hgt hε
      rw [tubeCorrection_eq_zero_of_nonneg_level hgt.le, add_zero, hω]
      simp only [truncK, integral_neg]
      exact neg_le_neg hj
    · -- boundary center: Dirac mass
      have h0 : ellipseLevel z = 0 := le_antisymm (not_lt.mp hgt) (not_lt.mp hlt)
      rw [tubeSweep_eq_dirac_of_mem_Gamma (mem_Gamma_of_ellipseLevel_eq_zero h0),
        integral_dirac]
      linarith

/-! ## Truncated two-sweep inequality (v10 `eq:tube-green`, second half) -/

theorem norm_sub_le_eight_of_mem_Gamma {y y' : ℂ} (hy : y ∈ Gamma) (hy' : y' ∈ Gamma) :
    ‖y - y'‖ ≤ 8 :=
  (norm_sub_le y y').trans (by linarith [TubeVariance.norm_le_four_of_mem_Gamma hy,
    TubeVariance.norm_le_four_of_mem_Gamma hy'])

theorem ae_prod_mem_Gamma (μ ν : Measure ℂ) [SFinite μ] [SFinite ν]
    (hμ : ∀ᵐ y ∂μ, y ∈ Gamma) (hν : ∀ᵐ y ∂ν, y ∈ Gamma) :
    ∀ᵐ p ∂μ.prod ν, p.1 ∈ Gamma ∧ p.2 ∈ Gamma := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ν)).ae hμ
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ν)).ae hν
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

/-- A truncated kernel is integrable against any product of finite measures carried by `Γ`. -/
theorem integrable_truncK_prod_of_Gamma {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 8)
    (μ ν : Measure ℂ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hμ : ∀ᵐ y ∂μ, y ∈ Gamma) (hν : ∀ᵐ y ∂ν, y ∈ Gamma) :
    Integrable (fun p : ℂ × ℂ => truncK ε p.1 p.2) (μ.prod ν) := by
  apply (integrable_const (|Real.log ε| + |Real.log 8|)).mono'
    (continuous_truncK hε).aestronglyMeasurable
  filter_upwards [ae_prod_mem_Gamma μ ν hμ hν] with p hp
  rw [Real.norm_eq_abs]
  exact abs_truncK_le hε hε8 (norm_sub_le_eight_of_mem_Gamma hp.1 hp.2)

theorem tubeSweep_pair_truncK_le {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 8) (z w : ℂ) :
    (∫ p, truncK ε p.1 p.2 ∂(tubeSweep z).prod (tubeSweep w)) ≤
      truncK ε z w + tubeCorrection z + tubeCorrection w := by
  have hint := integrable_truncK_prod_of_Gamma hε hε8 (tubeSweep z) (tubeSweep w)
    (tubeSweep_ae_mem_Gamma z) (tubeSweep_ae_mem_Gamma w)
  rw [integral_prod _ hint]
  have hinner : ∀ y, (∫ y', truncK ε y y' ∂tubeSweep w) ≤ truncK ε y w + tubeCorrection w := by
    intro y
    have h := tubeSweep_truncK_le hε w y
    simp only [truncK_comm ε _ y] at h ⊢
    rw [truncK_comm ε y w]
    simpa [truncK_comm] using h
  calc (∫ y, ∫ y', truncK ε (y, y').1 (y, y').2 ∂tubeSweep w ∂tubeSweep z)
      ≤ ∫ y, (truncK ε y w + tubeCorrection w) ∂tubeSweep z :=
        integral_mono hint.integral_prod_left
          ((integrable_truncK_tubeSweep hε z w).add (integrable_const _)) hinner
    _ = (∫ y, truncK ε y w ∂tubeSweep z) + tubeCorrection w := by
        rw [integral_add (integrable_truncK_tubeSweep hε z w) (integrable_const _)]
        simp
    _ ≤ truncK ε z w + tubeCorrection z + tubeCorrection w := by
        linarith [tubeSweep_truncK_le hε z w]

end
end Li2Lean.P0.TubeEnergy
