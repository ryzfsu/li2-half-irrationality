/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube

open MeasureTheory Complex

namespace Li2Lean.P0.TubeVariance

noncomputable section

/-- The literal ellipse is contained in a fixed compact ball. -/
theorem norm_gammaPoint_le_four (u : ℝ) : ‖gammaPoint u‖ ≤ 4 := by
  have hA : 0 ≤ semiMajor := by norm_num [semiMajor]
  have hB : 0 ≤ semiMinor := by norm_num [semiMinor]
  have hc : 0 ≤ center := by norm_num [center]
  calc
    ‖gammaPoint u‖ ≤ |center + semiMajor * Real.cos u| +
        |semiMinor * Real.sin u| := by
      simpa only [gammaPoint, norm_mul, Complex.norm_I, Complex.norm_real, Real.norm_eq_abs, one_mul, abs_mul] using
        norm_add_le (Complex.ofReal (center + semiMajor * Real.cos u))
          (Complex.I * Complex.ofReal (semiMinor * Real.sin u))
    _ ≤ center + semiMajor + semiMinor := by
      have h₁ := abs_add_le center (semiMajor * Real.cos u)
      have h₂ := mul_le_mul_of_nonneg_left (Real.abs_cos_le_one u) hA
      have h₃ := mul_le_mul_of_nonneg_left (Real.abs_sin_le_one u) hB
      rw [abs_mul, abs_of_nonneg hA] at h₁
      rw [abs_mul, abs_of_nonneg hB]
      rw [abs_of_nonneg hc] at h₁
      nlinarith
    _ ≤ 4 := by norm_num [center, semiMajor, semiMinor]

theorem norm_le_four_of_mem_Gamma {y : ℂ} (hy : y ∈ Gamma) : ‖y‖ ≤ 4 := by
  obtain ⟨u, rfl⟩ := hy
  exact norm_gammaPoint_le_four u

/-- Every continuous function is integrable for a finite measure carried by Γ. -/
theorem continuous_integrable {E : Type*} [NormedAddCommGroup E]
    (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {f : ℂ → E} (hf : Continuous f) :
    Integrable f ω := by
  obtain ⟨C, hC⟩ := (isCompact_closedBall (0 : ℂ) 4).exists_bound_of_continuousOn
    hf.continuousOn
  apply (integrable_const C).mono' hf.aestronglyMeasurable
  filter_upwards [hω] with y hy
  apply hC y
  simpa [Metric.mem_closedBall, dist_zero_right] using norm_le_four_of_mem_Gamma hy

/-- Separation from the source supplies logarithmic integrability; no
integrability premise is passed to the quantitative theorem. -/
theorem log_integrable_of_separation (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) (x : ℂ) {d : ℝ} (hd : 0 < d)
    (hsep : ∀ y ∈ Gamma, d ≤ ‖y - x‖) :
    Integrable (fun y => Real.log ‖y - x‖) ω := by
  have hm : Measurable (fun y : ℂ => Real.log ‖y - x‖) :=
    Real.measurable_log.comp (by fun_prop)
  apply (integrable_const (|Real.log d| + |Real.log (4 + ‖x‖)|)).mono'
    hm.aestronglyMeasurable
  filter_upwards [hω] with y hy
  have hlow := hsep y hy
  have hhigh : ‖y - x‖ ≤ 4 + ‖x‖ :=
    (norm_sub_le y x).trans (by linarith [norm_le_four_of_mem_Gamma hy])
  have hl : Real.log d ≤ Real.log ‖y - x‖ := Real.log_le_log hd hlow
  have hu : Real.log ‖y - x‖ ≤ Real.log (4 + ‖x‖) :=
    Real.log_le_log (lt_of_lt_of_le hd hlow) hhigh
  rw [Real.norm_eq_abs]
  exact abs_le.mpr ⟨by linarith [neg_abs_le (Real.log d), abs_nonneg (Real.log (4 + ‖x‖))],
    by linarith [le_abs_self (Real.log (4 + ‖x‖)), abs_nonneg (Real.log d)]⟩

private theorem norm_sq_eq_coords (w : ℂ) :
    ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  ring

private theorem mean_re (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z : ℂ} (hm : ∫ y, y ∂ω = z) :
    (∫ y, y.re ∂ω) = z.re := by
  rw [← hm]
  exact integral_re (continuous_integrable ω hω continuous_id)

private theorem mean_im (ω : Measure ℂ) [IsFiniteMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z : ℂ} (hm : ∫ y, y ∂ω = z) :
    (∫ y, y.im ∂ω) = z.im := by
  rw [← hm]
  exact integral_im (continuous_integrable ω hω continuous_id)

/-- The barycentric second-moment identity on the literal ellipse. -/
theorem second_moment_identity (ω : Measure ℂ) [IsProbabilityMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z : ℂ} (hm : ∫ y, y ∂ω = z) (x : ℂ) :
    (∫ y, ‖y - x‖ ^ 2 ∂ω) =
      (∫ y, ‖y - z‖ ^ 2 ∂ω) + ‖z - x‖ ^ 2 := by
  have hre := mean_re ω hω hm
  have him := mean_im ω hω hm
  have hid (y : ℂ) : ‖y - x‖ ^ 2 = ‖y - z‖ ^ 2 + ‖z - x‖ ^ 2 +
      (2 * (z.re - x.re) * (y.re - z.re) + 2 * (z.im - x.im) * (y.im - z.im)) := by
    simp only [norm_sq_eq_coords, Complex.sub_re, Complex.sub_im]
    ring
  calc
    (∫ y, ‖y - x‖ ^ 2 ∂ω) = ∫ y, ‖y - z‖ ^ 2 + ‖z - x‖ ^ 2 +
      (2 * (z.re - x.re) * (y.re - z.re) + 2 * (z.im - x.im) * (y.im - z.im)) ∂ω :=
        integral_congr_ae (Filter.Eventually.of_forall hid)
    _ = _ := by
      rw [integral_add, integral_add, integral_add, integral_const_mul, integral_const_mul,
        integral_sub, integral_sub]
      · simp [hre, him]
      all_goals exact continuous_integrable ω hω (by fun_prop)

/-- The exact normalized ellipse variance equals its defining function. -/
theorem normalized_variance_identity (ω : Measure ℂ) [IsProbabilityMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z : ℂ} (hm : ∫ y, y ∂ω = z) :
    (∫ y, ((y.re - z.re) / semiMajor) ^ 2 +
      ((y.im - z.im) / semiMinor) ^ 2 ∂ω) = ellipseLevel z := by
  have hre := mean_re ω hω hm
  have him := mean_im ω hω hm
  have hid : (fun y : ℂ => ((y.re - z.re) / semiMajor) ^ 2 +
      ((y.im - z.im) / semiMinor) ^ 2) =ᵐ[ω]
      (fun y => ellipseLevel z +
        ((2 * (z.re - center) / semiMajor ^ 2) * (z.re - y.re) +
         (2 * z.im / semiMinor ^ 2) * (z.im - y.im))) := by
    filter_upwards [hω] with y hy
    obtain ⟨u, rfl⟩ := hy
    have hq := ellipseLevel_gammaPoint u
    unfold ellipseLevel at hq ⊢
    norm_num [semiMajor, semiMinor] at hq ⊢
    nlinarith
  rw [integral_congr_ae hid, integral_add, integral_add,
    integral_const_mul, integral_const_mul, integral_sub, integral_sub]
  · simp [hre, him]
  all_goals exact continuous_integrable ω hω (by fun_prop)

/-- The major semiaxis bounds the true Euclidean variance. -/
theorem variance_le_ellipseLevel (ω : Measure ℂ) [IsProbabilityMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z : ℂ} (hm : ∫ y, y ∂ω = z) :
    (∫ y, ‖y - z‖ ^ 2 ∂ω) ≤ semiMajor ^ 2 * ellipseLevel z := by
  rw [← normalized_variance_identity ω hω hm, ← integral_const_mul]
  apply integral_mono_ae
    (continuous_integrable ω hω (by fun_prop))
    (continuous_integrable ω hω (by fun_prop))
  filter_upwards [] with y
  simp only [norm_sq_eq_coords, Complex.sub_re, Complex.sub_im]
  norm_num [semiMajor, semiMinor]
  nlinarith [sq_nonneg (y.im - z.im)]

/-- A barycenter of a probability carried by Γ lies in the closed ellipse. -/
theorem ellipseLevel_nonneg_of_mean (ω : Measure ℂ) [IsProbabilityMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z : ℂ} (hm : ∫ y, y ∂ω = z) :
    0 ≤ ellipseLevel z := by
  have h := variance_le_ellipseLevel ω hω hm
  have hn : 0 ≤ ∫ y, ‖y - z‖ ^ 2 ∂ω := integral_nonneg (fun _ => sq_nonneg _)
  have hA : 0 < semiMajor ^ 2 := by norm_num [semiMajor]
  nlinarith

/-- The scalar estimate used in the logarithmic potential comparison. -/
theorem log_sub_log_le_sq {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    Real.log a - Real.log b ≤ (a ^ 2 - b ^ 2) / (2 * b ^ 2) := by
  have h := Real.log_le_sub_one_of_pos (div_pos (sq_pos_of_pos ha) (sq_pos_of_pos hb))
  rw [Real.log_div (ne_of_gt (sq_pos_of_pos ha)) (ne_of_gt (sq_pos_of_pos hb)),
    Real.log_pow, Real.log_pow] at h
  norm_num at h
  apply (le_div_iff₀ (by positivity : 0 < 2 * b ^ 2)).mpr
  have h' := (le_div_iff₀ (sq_pos_of_pos hb)).mp
    (show 2 * Real.log a - 2 * Real.log b + 1 ≤ a ^ 2 / b ^ 2 by linarith)
  nlinarith

/-- Logarithmic potential gain is bounded by half the normalized variance.
Only probability, Γ support, barycenter and geometric separation are assumed. -/
theorem log_gain_le_variance (ω : Measure ℂ) [IsProbabilityMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z x : ℂ} (hm : ∫ y, y ∂ω = z)
    (hzx : z ≠ x) {d : ℝ} (hd : 0 < d) (hsep : ∀ y ∈ Gamma, d ≤ ‖y - x‖) :
    (∫ y, Real.log ‖y - x‖ ∂ω) - Real.log ‖z - x‖ ≤
      (∫ y, ‖y - z‖ ^ 2 ∂ω) / (2 * ‖z - x‖ ^ 2) := by
  have hlog := log_integrable_of_separation ω hω x hd hsep
  have hsq : Integrable (fun y : ℂ => ‖y - x‖ ^ 2) ω :=
    continuous_integrable ω hω (by fun_prop)
  have hbound : (∫ y, Real.log ‖y - x‖ - Real.log ‖z - x‖ ∂ω) ≤
      ∫ y, (‖y - x‖ ^ 2 - ‖z - x‖ ^ 2) / (2 * ‖z - x‖ ^ 2) ∂ω := by
    apply integral_mono_ae (hlog.sub (integrable_const _))
      ((hsq.sub (integrable_const _)).div_const _)
    filter_upwards [hω] with y hy
    exact log_sub_log_le_sq (lt_of_lt_of_le hd (hsep y hy))
      (norm_pos_iff.mpr (sub_ne_zero.mpr hzx))
  rw [integral_sub hlog (integrable_const _), integral_div,
    integral_sub hsq (integrable_const _), second_moment_identity ω hω hm x] at hbound
  simpa using hbound

/-- Quantitative logarithmic gain for any separated source. -/
theorem log_gain_le_ellipseLevel (ω : Measure ℂ) [IsProbabilityMeasure ω]
    (hω : ∀ᵐ y ∂ω, y ∈ Gamma) {z x : ℂ} (hm : ∫ y, y ∂ω = z)
    (hzx : z ≠ x) {d : ℝ} (hd : 0 < d) (hsep : ∀ y ∈ Gamma, d ≤ ‖y - x‖) :
    (∫ y, Real.log ‖y - x‖ ∂ω) - Real.log ‖z - x‖ ≤
      (semiMajor ^ 2 / (2 * ‖z - x‖ ^ 2)) * ellipseLevel z := by
  calc
    _ ≤ (∫ y, ‖y - z‖ ^ 2 ∂ω) / (2 * ‖z - x‖ ^ 2) :=
      log_gain_le_variance ω hω hm hzx hd hsep
    _ ≤ (semiMajor ^ 2 * ellipseLevel z) / (2 * ‖z - x‖ ^ 2) :=
      div_le_div_of_nonneg_right (variance_le_ellipseLevel ω hω hm) (by positivity)
    _ = _ := by ring

end
end Li2Lean.P0.TubeVariance
