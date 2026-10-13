/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube

namespace Li2Lean.P0

noncomputable section

/-- The affine map from the actual ellipse to the unit disk. -/
def ellipseNormalize (z : ℂ) : ℂ :=
  ⟨(z.re - center) / semiMajor, z.im / semiMinor⟩

theorem ellipseLevel_eq_one_sub_norm_sq (z : ℂ) :
    ellipseLevel z = 1 - ‖ellipseNormalize z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [ellipseNormalize, ellipseLevel]
  ring

theorem ellipseNormalize_norm_le_one {z : ℂ} (hz : 0 ≤ ellipseLevel z) :
    ‖ellipseNormalize z‖ ≤ 1 := by
  rw [ellipseLevel_eq_one_sub_norm_sq] at hz
  nlinarith [norm_nonneg (ellipseNormalize z)]

/-- The inverse of the smaller semiaxis is the actual operator norm bound. -/
theorem ellipseNormalize_dist_le (z w : ℂ) :
    ‖ellipseNormalize z - ellipseNormalize w‖ ≤ dist z w / semiMinor := by
  have hn : 0 ≤ dist z w / semiMinor := by
    exact div_nonneg dist_nonneg (by norm_num [semiMinor])
  have he : ‖ellipseNormalize z - ellipseNormalize w‖ ^ 2 =
      ((z.re - w.re) / semiMajor) ^ 2 + ((z.im - w.im) / semiMinor) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]
    simp [ellipseNormalize]
    ring
  have hd : dist z w ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by
    rw [dist_eq_norm, Complex.sq_norm, Complex.normSq_apply]
    simp [pow_two]
  have hs : ‖ellipseNormalize z - ellipseNormalize w‖ ^ 2 ≤
      (dist z w / semiMinor) ^ 2 := by
    rw [he]
    simp only [div_pow]
    rw [hd]
    norm_num [semiMajor, semiMinor]
    nlinarith [sq_nonneg (z.re - w.re)]
  nlinarith [norm_nonneg (ellipseNormalize z - ellipseNormalize w)]

/-- The defining function is `2/B`-Lipschitz on the closed ellipse. -/
theorem ellipseLevel_sub_le_dist {z w : ℂ}
    (hz : 0 ≤ ellipseLevel z) (hw : 0 ≤ ellipseLevel w) :
    ellipseLevel z - ellipseLevel w ≤ 2 * dist z w / semiMinor := by
  have hz1 := ellipseNormalize_norm_le_one hz
  have hw1 := ellipseNormalize_norm_le_one hw
  have hz0 := norm_nonneg (ellipseNormalize z)
  have hw0 := norm_nonneg (ellipseNormalize w)
  have hdiff := norm_sub_norm_le (ellipseNormalize w) (ellipseNormalize z)
  rw [norm_sub_rev] at hdiff
  have hnd := ellipseNormalize_dist_le z w
  have ht0 := norm_nonneg (ellipseNormalize z - ellipseNormalize w)
  have hsq : ‖ellipseNormalize w‖ ^ 2 - ‖ellipseNormalize z‖ ^ 2 ≤
      2 * ‖ellipseNormalize z - ellipseNormalize w‖ := by
    by_cases horder : ‖ellipseNormalize z‖ ≤ ‖ellipseNormalize w‖
    · have hp := mul_nonneg (sub_nonneg.mpr (show
          ‖ellipseNormalize w‖ + ‖ellipseNormalize z‖ ≤ 2 by linarith))
          (sub_nonneg.mpr horder)
      nlinarith
    · have horder' : ‖ellipseNormalize w‖ ≤ ‖ellipseNormalize z‖ := le_of_not_ge horder
      have hp := mul_nonneg (sub_nonneg.mpr horder') (add_nonneg hz0 hw0)
      nlinarith
  rw [ellipseLevel_eq_one_sub_norm_sq, ellipseLevel_eq_one_sub_norm_sq]
  calc
    _ ≤ 2 * ‖ellipseNormalize z - ellipseNormalize w‖ := by linarith
    _ ≤ 2 * (dist z w / semiMinor) := by linarith
    _ = _ := by ring

theorem gamma_nonempty_collar : Gamma.Nonempty :=
  Set.range_nonempty gammaPoint

/-- This uses the actual metric infimum over the original ellipse boundary. -/
theorem ellipseLevel_le_infDist_boundary {z : ℂ} (hz : 0 ≤ ellipseLevel z) :
    ellipseLevel z ≤ 2 * Metric.infDist z Gamma / semiMinor := by
  have hb : 0 < semiMinor := by norm_num [semiMinor]
  have hlow : ellipseLevel z * semiMinor / 2 ≤ Metric.infDist z Gamma := by
    apply (Metric.le_infDist gamma_nonempty_collar).2
    rintro w ⟨u, rfl⟩
    have hh := ellipseLevel_sub_le_dist hz
      (show 0 ≤ ellipseLevel (gammaPoint u) by rw [ellipseLevel_gammaPoint])
    rw [ellipseLevel_gammaPoint, sub_zero] at hh
    have hh' := (le_div_iff₀ hb).mp hh
    nlinarith
  apply (le_div_iff₀ hb).2
  nlinarith

/-- The numerical collar bound in the paper, without an assumed geometry premise. -/
theorem inner_tube_level_bound {δ : ℝ} {z : ℂ}
    (hz : z ∈ ellipseInterior) (htube : z ∈ tube δ) :
    ellipseLevel z ≤ 2 * δ / semiMinor := by
  have h := ellipseLevel_le_infDist_boundary (show 0 ≤ ellipseLevel z from hz.le)
  have hδ : Metric.infDist z Gamma ≤ δ := htube
  have hb : 0 < semiMinor := by norm_num [semiMinor]
  exact h.trans ((div_le_div_iff_of_pos_right hb).2 (by linarith))

theorem inner_tube_level_lt_one_eighth {δ : ℝ} {z : ℂ}
    (hδ : δ ≤ tubeRadiusMax) (hz : z ∈ ellipseInterior) (htube : z ∈ tube δ) :
    ellipseLevel z < 1 / 8 := by
  have h := inner_tube_level_bound hz htube
  norm_num [tubeRadiusMax] at hδ
  norm_num [semiMinor] at h
  linarith

/-- All of the original positive real source interval is quantitatively interior. -/
theorem positive_source_ellipseLevel {x : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0) :
    1 / 5 < ellipseLevel x := by
  rcases hx with ⟨hx0, hx2⟩
  have hp := mul_nonneg hx0 (sub_nonneg.mpr hx2)
  norm_num [ellipseLevel, center, semiMajor, semiMinor, him]
  nlinarith

/-- A fixed point witnesses nonemptiness of the actual `q = 1/8` level curve. -/
theorem ellipse_eighth_level_nonempty : {z : ℂ | ellipseLevel z = 1 / 8}.Nonempty := by
  refine ⟨⟨center + semiMajor * Real.sqrt (7 / 8), 0⟩, ?_⟩
  change 1 - (((center + semiMajor * Real.sqrt (7 / 8)) - center) / semiMajor) ^ 2 -
    (0 / semiMinor) ^ 2 = 1 / 8
  have he : (center + semiMajor * Real.sqrt (7 / 8) - center) / semiMajor =
      Real.sqrt (7 / 8) := by
    field_simp [semiMajor]
    ring
  rw [he, Real.sq_sqrt (show (0 : ℝ) ≤ 7 / 8 by norm_num)]
  norm_num

theorem positive_source_level_distance {x : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0) :
    3 * semiMinor / 80 ≤ Metric.infDist x {z : ℂ | ellipseLevel z = 1 / 8} := by
  have hsource := positive_source_ellipseLevel hx him
  have hb : 0 < semiMinor := by norm_num [semiMinor]
  apply (Metric.le_infDist ellipse_eighth_level_nonempty).2
  intro z hz
  have hh := ellipseLevel_sub_le_dist (show 0 ≤ ellipseLevel x by linarith)
    (show 0 ≤ ellipseLevel z by rw [hz]; norm_num)
  rw [hz] at hh
  have hh' := (le_div_iff₀ hb).mp hh
  nlinarith

theorem positive_source_level_separation {x : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0) :
    1 / 32 < Metric.infDist x {z : ℂ | ellipseLevel z = 1 / 8} := by
  have h := positive_source_level_distance hx him
  norm_num [semiMinor] at h
  linarith

theorem closed_ellipse_re_bound {z : ℂ} (hz : 0 ≤ ellipseLevel z) :
    |z.re - center| ≤ semiMajor := by
  have h := (Complex.abs_re_le_norm (ellipseNormalize z)).trans
    (ellipseNormalize_norm_le_one hz)
  have hA : 0 < semiMajor := by norm_num [semiMajor]
  change |(z.re - center) / semiMajor| ≤ 1 at h
  rw [abs_div, abs_of_pos hA, div_le_iff₀ hA, one_mul] at h
  exact h

theorem closed_ellipse_im_bound {z : ℂ} (hz : 0 ≤ ellipseLevel z) :
    |z.im| ≤ semiMinor := by
  have h := (Complex.abs_im_le_norm (ellipseNormalize z)).trans
    (ellipseNormalize_norm_le_one hz)
  have hB : 0 < semiMinor := by norm_num [semiMinor]
  change |z.im / semiMinor| ≤ 1 at h
  rw [abs_div, abs_of_pos hB, div_le_iff₀ hB, one_mul] at h
  exact h

/-- Every closed-ellipse point lies in the disk of radius five about each positive source. -/
theorem closed_ellipse_dist_positive_source_lt_five {z x : ℂ}
    (hz : 0 ≤ ellipseLevel z) (hx : x.re ∈ Set.Icc (0 : ℝ) 2)
    (him : x.im = 0) : dist z x < 5 := by
  have hr := closed_ellipse_re_bound hz
  have hi := closed_ellipse_im_bound hz
  have hc : |center - x.re| ≤ 2 := by
    apply abs_le.mpr
    rcases hx with ⟨hx0, hx2⟩
    norm_num [center]
    constructor <;> linarith
  have hd : |z.re - x.re| ≤ semiMajor + 2 := by
    calc
      |z.re - x.re| = |(z.re - center) + (center - x.re)| := by ring_nf
      _ ≤ |z.re - center| + |center - x.re| := abs_add_le _ _
      _ ≤ semiMajor + 2 := add_le_add hr hc
  have hn := Complex.norm_le_abs_re_add_abs_im (z - x)
  simp only [Complex.sub_re, Complex.sub_im, him, sub_zero] at hn
  rw [dist_eq_norm]
  norm_num [semiMajor, semiMinor] at hd hi
  linarith

theorem ellipseInterior_subset_positive_source_ball {x : ℂ}
    (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (him : x.im = 0) :
    ellipseInterior ⊆ Metric.ball x 5 := by
  intro z hz
  exact closed_ellipse_dist_positive_source_lt_five hz.le hx him

/-- The elementary numerical logarithm budget is proved from the exponential series. -/
theorem log_one_sixty_lt_six : Real.log (160 : ℝ) < 6 := by
  apply (Real.log_lt_iff_lt_exp (by norm_num)).2
  have he := Real.sum_le_exp_of_nonneg (show (0 : ℝ) ≤ 6 by norm_num) 6
  norm_num [Finset.sum_range_succ] at he
  linarith

end
end Li2Lean.P0
