/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.Kit.LogSegment
import Li2Lean.P0.TubeCollarVariance
import Li2Lean.P0.TubeVarianceSupport

/-! # An explicit lower bound for the contour energy

Every admissible competitor of v10 `eq:contour-alpha` with finite energy has
regularized energy at least `-200`.  Hence `Set.range p0ExtendedEnergy` is
bounded below, which is the `BddBelow` premise of the infimum passage.

The bound is termwise:

* companion field `A_0 - φ ≥ -180` on `[1/4,5/4] ∪ Γ` (closed segment formula for `A_0`);
* frequency field `B_0 - ψ - 3 log(1+t) ≥ -6` for `t ≥ 1/2`;
* self-interaction of `η` at least `-log 8` (all points in the disk of radius `4`);
* frequency kernel `≥ 0`; mixed kernel `≥ -log 4`.
-/

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

namespace EnergyLowerBound

open Li2Lean.LogSegment

/-! ## Scalar estimates -/

theorem abs_mul_log_abs_le (v : ℝ) : abs (v * Real.log (abs v)) ≤ v ^ 2 + 1 := by
  rcases le_or_gt |v| 1 with h | h
  · rcases eq_or_lt_of_le (abs_nonneg v) with h0 | h0
    · rw [← h0]; simp; positivity
    · have h1 := Real.abs_log_mul_self_lt (abs v) h0 h
      have e : abs (v * Real.log (abs v)) = abs (Real.log (abs v) * abs v) := by
        rw [abs_mul, abs_mul, abs_abs, mul_comm]
      rw [e]
      nlinarith [sq_nonneg v]
  · have hlog0 : 0 ≤ Real.log |v| := Real.log_nonneg h.le
    have hlog1 : Real.log |v| ≤ |v| - 1 := Real.log_le_sub_one_of_pos (by linarith)
    rw [abs_mul, abs_of_nonneg hlog0]
    have : |v| * Real.log |v| ≤ |v| * |v| := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg v)
    nlinarith [sq_abs v]

theorem abs_primitive_le (v : ℝ) : |primitive v| ≤ v ^ 2 + |v| + 1 := by
  unfold primitive
  have h := abs_mul_log_abs_le v
  calc abs (v * (Real.log (abs v) - 1)) = abs (v * Real.log (abs v) - v) := by ring_nf
    _ ≤ abs (v * Real.log (abs v)) + abs v := abs_sub _ _
    _ ≤ v ^ 2 + |v| + 1 := by linarith

theorem primitive_ge {v : ℝ} (hv : |v| ≤ 6) : -43 ≤ primitive v := by
  have h := abs_primitive_le v
  have hv2 : v ^ 2 ≤ 36 := by nlinarith [sq_abs v, abs_nonneg v]
  have := neg_abs_le (primitive v)
  linarith

theorem primitive_le {v : ℝ} (hv : |v| ≤ 6) : primitive v ≤ 43 := by
  have h := abs_primitive_le v
  have hv2 : v ^ 2 ≤ 36 := by nlinarith [sq_abs v, abs_nonneg v]
  have := le_abs_self (primitive v)
  linarith

theorem log_two_le_one : Real.log 2 ≤ 1 := by
  have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2); linarith

/-! ## The companion field -/

/-- One logarithmic segment potential is at least `-86` for `|z| ≤ 4`, segment in `[0,2]`. -/
theorem segment_log_ge {z : ℂ} (hz : ‖z‖ ≤ 4) {a b : ℝ} (hab : a ≤ b)
    (ha : 0 ≤ a) (hb : b ≤ 2) :
    -86 ≤ ∫ x in a..b, Real.log ‖z - (x : ℂ)‖ := by
  have hre : |z.re| ≤ 4 := (Complex.abs_re_le_norm z).trans hz
  by_cases hint : IntervalIntegrable (fun x : ℝ => Real.log ‖z - (x : ℂ)‖) volume a b
  · have hcmp : (∫ x in a..b, Real.log |z.re - x|) ≤ ∫ x in a..b, Real.log ‖z - (x : ℂ)‖ := by
      apply intervalIntegral.integral_mono_ae hab (intervalIntegrable_log_abs_sub z.re a b) hint
      have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ z.re := by
        rw [ae_iff]; simp
      filter_upwards [hne] with x hx
      have hpos : 0 < |z.re - x| := abs_pos.mpr (sub_ne_zero.mpr (Ne.symm hx))
      apply Real.log_le_log hpos
      have := Complex.abs_re_le_norm (z - (x : ℂ))
      simpa using this
    rw [integral_log_abs_sub] at hcmp
    have h1 : |z.re - a| ≤ 6 := by
      rw [abs_le] at hre ⊢; constructor <;> linarith
    have h2 : |z.re - b| ≤ 6 := by
      rw [abs_le] at hre ⊢; constructor <;> linarith
    linarith [primitive_ge h1, primitive_le h2]
  · rw [intervalIntegral.integral_undef hint]; norm_num

theorem A0_ge {z : ℂ} (hz : ‖z‖ ≤ 4) : -172 ≤ A0 z := by
  unfold A0
  linarith [segment_log_ge hz (by norm_num : (1 / 4 : ℝ) ≤ 5 / 4) (by norm_num) (by norm_num),
    segment_log_ge hz (by norm_num : (0 : ℝ) ≤ 2) (by norm_num) (by norm_num)]

theorem phi_le {z : ℂ} (hz : ‖z‖ ≤ 4) : phi z ≤ 8 := by
  unfold phi
  have hre : z.re ≤ 4 := (Complex.re_le_norm z).trans hz
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl2' := log_two_le_one
  have hseg : (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) ≤ 5 / 2 := by
    by_cases hint : IntervalIntegrable (fun s : ℝ => Real.log ‖z + (s : ℂ)‖) volume 0 (1 / 2)
    · calc (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) ≤
            ∫ _s in (0 : ℝ)..(1 / 2 : ℝ), (5 : ℝ) := by
            apply intervalIntegral.integral_mono_on (by norm_num) hint intervalIntegrable_const
            intro s hs
            have hn : ‖z + (s : ℂ)‖ ≤ 5 := by
              calc ‖z + (s : ℂ)‖ ≤ ‖z‖ + ‖(s : ℂ)‖ := norm_add_le _ _
                _ ≤ 5 := by
                  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs.1]
                  linarith [hs.2]
            exact (Real.log_le_self (norm_nonneg _)).trans hn
        _ = 5 / 2 := by rw [intervalIntegral.integral_const]; norm_num
    · rw [intervalIntegral.integral_undef hint]; norm_num
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hhalf]
  simp only [ell]
  nlinarith

theorem companionField_ge {z : ℂ} (hz : ‖z‖ ≤ 4) : -180 ≤ p0CompanionField z := by
  unfold p0CompanionField
  linarith [A0_ge hz, phi_le hz]

/-! ## The frequency field -/

theorem B0_ge {t : ℝ} (ht : 0 < t) : 3 * Real.log t ≤ B0 t := by
  have hcont : ∀ a b : ℝ, 0 ≤ a → 0 ≤ b →
      IntervalIntegrable (fun x : ℝ => Real.log (t + x)) volume a b := by
    intro a b ha hb
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.log (continuousOn_const.add continuousOn_id)
    intro x hx
    have : 0 ≤ x := by
      rcases Set.mem_uIcc.mp hx with h | h
      · linarith [h.1]
      · linarith [h.1]
    have hp : 0 < t + x := by linarith
    exact hp.ne'
  have hseg : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (b - a) * Real.log t ≤ ∫ x in a..b, Real.log (t + x) := by
    intro a b ha hab
    calc (b - a) * Real.log t = ∫ _x in a..b, Real.log t := by simp
      _ ≤ ∫ x in a..b, Real.log (t + x) := by
        apply intervalIntegral.integral_mono_on hab intervalIntegrable_const
          (hcont a b ha (by linarith))
        intro x hx
        exact Real.log_le_log ht (by linarith [hx.1])
  unfold B0
  have h1 := hseg (1 / 4) (5 / 4) (by norm_num) (by norm_num)
  have h2 := hseg 0 2 le_rfl (by norm_num)
  linarith

theorem psi_le {t : ℝ} (ht : 1 / 2 ≤ t) :
    psi t ≤ Real.log t / 2 + 1 / 2 + Real.log 2 / 2 - t * Real.log 2 := by
  have htpos : 0 < t := by linarith
  have key : (t - 1 / 2) * Real.log t - 1 / 2 ≤ (t - 1 / 2) * Real.log (t - 1 / 2) := by
    rcases eq_or_lt_of_le ht with h | h
    · rw [← h]; norm_num
    · have hpos : 0 < t - 1 / 2 := by linarith
      have hx : 0 < (t - 1 / 2) / t := div_pos hpos htpos
      have hl := Real.one_sub_inv_le_log_of_pos hx
      rw [Real.log_div hpos.ne' htpos.ne', inv_div] at hl
      have hc : (t - 1 / 2) * (t / (t - 1 / 2)) = t := by
        rw [mul_div_assoc', mul_div_cancel_left₀ _ hpos.ne']
      have : (t - 1 / 2) * (1 - t / (t - 1 / 2)) = -(1 / 2) := by
        rw [mul_sub, mul_one, hc]; ring
      nlinarith [mul_le_mul_of_nonneg_left hl hpos.le]
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by rw [one_div, Real.log_inv]
  unfold psi
  simp only [ell, hhalf]
  nlinarith

theorem frequencyField_ge {t : ℝ} (ht : 1 / 2 ≤ t) : -6 ≤ p0RegularizedFrequencyField t := by
  have htpos : 0 < t := by linarith
  have hB := B0_ge htpos
  have hψ := psi_le ht
  have h3 : Real.log (1 + t) ≤ Real.log 3 + Real.log t := by
    rw [← Real.log_mul (by norm_num) htpos.ne']
    exact Real.log_le_log (by linarith) (by linarith)
  have hl3 : Real.log 3 ≤ 2 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3); linarith
  have h1t : Real.log (1 + t) ≤ t := by
    have := Real.log_le_sub_one_of_pos (by linarith : (0 : ℝ) < 1 + t); linarith
  have hl2 : 1 / 2 < Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hl2' := log_two_le_one
  unfold p0RegularizedFrequencyField
  nlinarith

/-! ## Kernels -/

theorem frequencyKernel_nonneg {t s : ℝ} (ht : 0 ≤ t) (hs : 0 ≤ s) :
    0 ≤ p0RegularizedFrequencyKernel t s := by
  unfold p0RegularizedFrequencyKernel
  split_ifs with h
  · exact le_rfl
  · have hpos : 0 < |t - s| := abs_pos.mpr (sub_ne_zero.mpr h)
    apply Real.log_nonneg
    rw [le_div_iff₀ hpos, one_mul]
    rcases le_total t s with h' | h'
    · rw [abs_of_nonpos (by linarith)]; nlinarith
    · rw [abs_of_nonneg (by linarith)]; nlinarith

theorem mixedKernel_ge {z : ℂ} (hz : ‖z‖ ≤ 4) {t : ℝ} (ht : 0 ≤ t) :
    -Real.log 4 ≤ p0RegularizedMixedKernel z t := by
  unfold p0RegularizedMixedKernel
  rcases eq_or_lt_of_le (norm_nonneg (z + (t : ℂ))) with h0 | hpos
  · rw [← h0, div_zero, Real.log_zero]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 4)]
  · have hn : ‖z + (t : ℂ)‖ ≤ 4 * (1 + t) := by
      calc ‖z + (t : ℂ)‖ ≤ ‖z‖ + ‖(t : ℂ)‖ := norm_add_le _ _
        _ ≤ 4 * (1 + t) := by
          rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht]; linarith
    rw [← Real.log_inv]
    apply Real.log_le_log (by norm_num)
    rw [le_div_iff₀ hpos]
    linarith

theorem logKernel_ge {z w : ℂ} (hz : ‖z‖ ≤ 4) (hw : ‖w‖ ≤ 4) :
    -Real.log 8 ≤ li2LogKernel z w := by
  unfold li2LogKernel
  rcases eq_or_lt_of_le (norm_nonneg (z - w)) with h0 | hpos
  · rw [← h0, Real.log_zero]
    linarith [Real.log_nonneg (by norm_num : (1 : ℝ) ≤ 8)]
  · apply neg_le_neg
    apply Real.log_le_log hpos
    calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
      _ ≤ 8 := by linarith

/-! ## Supports of admissible competitors -/

theorem integral_ge_of_ae {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [IsProbabilityMeasure μ] {f : α → ℝ} (hf : Integrable f μ) {c : ℝ}
    (h : ∀ᵐ x ∂μ, c ≤ f x) : c ≤ ∫ x, f x ∂μ := by
  calc c = ∫ _x, c ∂μ := by simp
    _ ≤ ∫ x, f x ∂μ := integral_mono_ae (integrable_const c) hf h

theorem kappa_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ x ∂M.kappa, x ∈ Set.Icc (1 / 4 : ℝ) (5 / 4) :=
  (Measure.absolutelyContinuous_of_le M.kappa_le_density).ae_le
    (ae_restrict_mem measurableSet_Icc)

theorem mu_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ t ∂M.mu, t ∈ Set.Ici (1 / 2 : ℝ) :=
  (Measure.absolutelyContinuous_of_le M.mu_le_density).ae_le
    (ae_restrict_mem measurableSet_Ici)

theorem nu_ae_mem_Gamma (M : P0AdmissibleMeasures) : ∀ᵐ z ∂M.nu, z ∈ Gamma := by
  rw [ae_iff]
  apply measure_mono_null (Set.compl_subset_compl.mpr M.nu_supported)
  exact Measure.measure_compl_support

theorem eta_ae_norm_le (M : P0AdmissibleMeasures) : ∀ᵐ z ∂M.eta, ‖z‖ ≤ 4 := by
  change ∀ᵐ z ∂(Measure.map Complex.ofReal M.kappa + M.nu), ‖z‖ ≤ 4
  rw [ae_add_measure_iff]
  constructor
  · rw [ae_map_iff Complex.measurable_ofReal.aemeasurable
      (isClosed_le continuous_norm continuous_const).measurableSet]
    filter_upwards [kappa_ae_mem M] with x hx
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [hx.1])]
    linarith [hx.2]
  · filter_upwards [nu_ae_mem_Gamma M] with z hz
    exact TubeVariance.norm_le_four_of_mem_Gamma hz

instance eta_isProbability (M : P0AdmissibleMeasures) : IsProbabilityMeasure M.eta :=
  ⟨M.companion_mass⟩

instance mu_isProbability (M : P0AdmissibleMeasures) : IsProbabilityMeasure M.mu :=
  ⟨M.frequency_mass⟩

/-! ## The energy lower bound -/

theorem p0RegularizedEnergyValue_ge (M : P0AdmissibleMeasures)
    (hM : P0FiniteEnergyCondition M) : (-200 : ℝ) ≤ p0RegularizedEnergyValue M := by
  rcases hM with ⟨_, hfield, hfreq, hlog, _, hkernel, hmixed⟩
  have hη := eta_ae_norm_le M
  have hμ := mu_ae_mem M
  have h1 : (-180 : ℝ) ≤ ∫ z, p0CompanionField z ∂M.eta :=
    integral_ge_of_ae _ hfield (hη.mono fun z hz => companionField_ge hz)
  have h2 : (-6 : ℝ) ≤ ∫ t, p0RegularizedFrequencyField t ∂M.mu :=
    integral_ge_of_ae _ hfreq (hμ.mono fun t ht => frequencyField_ge ht)
  have h3 : -Real.log 8 ≤ li2LogInteraction M.eta M.eta := by
    apply integral_ge_of_ae _ hlog
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := M.eta) (ν := M.eta)).ae hη
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := M.eta) (ν := M.eta)).ae hη
    filter_upwards [a1, a2] with p hp1 hp2
    exact logKernel_ge hp1 hp2
  have h4 : (0 : ℝ) ≤ ∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂(M.mu.prod M.mu) := by
    apply integral_ge_of_ae _ hkernel
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := M.mu) (ν := M.mu)).ae hμ
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := M.mu) (ν := M.mu)).ae hμ
    filter_upwards [a1, a2] with p hp1 hp2
    exact frequencyKernel_nonneg (by linarith [Set.mem_Ici.mp hp1])
      (by linarith [Set.mem_Ici.mp hp2])
  have h5 : -Real.log 4 ≤ ∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(M.eta.prod M.mu) := by
    apply integral_ge_of_ae _ hmixed
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := M.eta) (ν := M.mu)).ae hη
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := M.eta) (ν := M.mu)).ae hμ
    filter_upwards [a1, a2] with p hp1 hp2
    exact mixedKernel_ge hp1 (by linarith [Set.mem_Ici.mp hp2])
  have hl8 : Real.log 8 ≤ 7 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 8); linarith
  have hl4 : Real.log 4 ≤ 3 := by
    have := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 4); linarith
  have hl2 := log_two_le_one
  unfold p0RegularizedEnergyValue
  simp only [ell]
  linarith

theorem p0ExtendedEnergy_ge (M : P0AdmissibleMeasures) :
    (((-200 : ℝ)) : WithTop ℝ) ≤ p0ExtendedEnergy M := by
  classical
  unfold p0ExtendedEnergy
  split_ifs with h
  · exact_mod_cast p0RegularizedEnergyValue_ge M h
  · exact le_top

/-- `BddBelow` for the contour energies, with the explicit bound `-200`. -/
theorem p0ExtendedEnergy_bddBelow : BddBelow (Set.range p0ExtendedEnergy) := by
  refine ⟨((-200 : ℝ) : WithTop ℝ), ?_⟩
  rintro _ ⟨M, rfl⟩
  exact p0ExtendedEnergy_ge M

/-- The admissible class is nonempty: pinned density on `[1/4,5/4]`, zero contour part. -/
theorem p0AdmissibleMeasures_nonempty : Nonempty P0AdmissibleMeasures := by
  refine ⟨{
    kappa := volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
    nu := 0
    mu := volume.restrict (Set.Icc (1 / 2 : ℝ) (3 / 2 : ℝ))
    kappa_le_density := le_rfl
    nu_supported := by simp
    companion_mass := ?_
    mu_le_density := ?_
    frequency_mass := ?_ }⟩
  · rw [p0CompanionMeasure, Measure.add_apply,
      Measure.map_apply (by fun_prop) MeasurableSet.univ]
    simp [Real.volume_Icc]
    norm_num
  · exact Measure.restrict_mono Set.Icc_subset_Ici_self le_rfl
  · rw [Measure.restrict_apply_univ, Real.volume_Icc]
    norm_num

/-- Consequently `alpha_Γ ≥ -200`; in particular `alpha_Γ` is a finite lower-bounded infimum. -/
theorem alphaGamma_ge : (((-200 : ℝ)) : WithTop ℝ) ≤ alphaGamma := by
  unfold alphaGamma
  have := p0AdmissibleMeasures_nonempty
  apply le_csInf (Set.range_nonempty _)
  rintro _ ⟨M, rfl⟩
  exact p0ExtendedEnergy_ge M

end EnergyLowerBound
end
end Li2Lean.P0
