/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeSweepEnergy
import Li2Lean.P0.TubeEnergyGain
import Li2Lean.P0.Contour
import Li2Lean.P0.TubeVarianceSupport

/-! # Sweep transfer for the fixed-source interactions

Untruncated point Green bounds for the actual sweep at separated sources, and
their integrated forms against an arbitrary finite source measure.  These are
the pinned (`κ`) and frequency (`μ`) parts of the interaction cost `3b` in v10
`sec:tube`:

* `∫∫ K₀ d(ν# ⊗ κ) ≤ ∫∫ K₀ d(ν ⊗ κ) + κ(ℂ) b` for `κ` carried by `[0,2]`;
* `∫∫ M d(ν# ⊗ μ) ≤ ∫∫ M d(ν ⊗ μ) + μ(ℝ) b` for the regularized mixed kernel
  `M(z,t) = log((1+t)/|z+t|)` and `μ` carried by `[1/2,∞)`.
-/

open MeasureTheory ProbabilityTheory Filter

namespace Li2Lean.P0.TubeEnergy

noncomputable section

open TubeInterior

theorem Gamma_subset_tube {δ : ℝ} (hδ : 0 ≤ δ) : Gamma ⊆ tube δ := by
  intro y hy
  change Metric.infDist y Gamma ≤ δ
  rw [Metric.infDist_zero_of_mem hy]; exact hδ

/-- Untruncated point Green bound at any separated source, from the truncated one. -/
theorem tubeSweep_point_green_of_sep {z x : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hzx : ε ≤ ‖z - x‖) (hΓ : ∀ y ∈ Gamma, ε ≤ ‖y - x‖) :
    (∫ y, realLogKernel y x ∂tubeSweep z) ≤ realLogKernel z x + tubeCorrection z := by
  have h := tubeSweep_truncK_le hε z x
  rw [truncK_eq_of_le hzx] at h
  have heq : (fun y => truncK ε y x) =ᵐ[tubeSweep z] (fun y => realLogKernel y x) := by
    filter_upwards [tubeSweep_ae_mem_Gamma z] with y hy
    exact truncK_eq_of_le (hΓ y hy)
  rwa [integral_congr_ae heq] at h

/-- Positive sources `x ∈ [0,2]`, every tube center. -/
theorem tubeSweep_point_green_positive {δ : ℝ} (hδ : δ ≤ tubeRadiusMax) {z x : ℂ}
    (hz : z ∈ tube δ) (hx : x.re ∈ Set.Icc (0 : ℝ) 2) (hxim : x.im = 0) :
    (∫ y, realLogKernel y x ∂tubeSweep z) ≤ realLogKernel z x + tubeCorrection z :=
  tubeSweep_point_green_of_sep (ε := 5383 / 40000) (by norm_num)
    (tube_positive_source_norm_sub_ge hδ hz hx hxim)
    (fun y hy => le_trans (by norm_num) (positive_source_norm_sub_ge hx hxim hy))

/-- Distance from a reflected frequency source to `Γ`. -/
theorem frequency_source_norm_sub_ge {x y : ℂ} (hx : x.re ≤ -(1 : ℝ) / 2) (hy : y ∈ Gamma) :
    (1749 / 5000 : ℝ) ≤ ‖y - x‖ := by
  have h := ellipse_infDist_lower_by_real_part x
  have h2 := Metric.infDist_le_dist_of_mem (x := x) hy
  rw [dist_eq_norm, norm_sub_rev] at h2
  norm_num [center, semiMajor] at h
  linarith

theorem tube_frequency_source_norm_sub_ge {δ : ℝ} (hδ : δ ≤ tubeRadiusMax) {z x : ℂ}
    (hz : z ∈ tube δ) (hx : x.re ≤ -(1 : ℝ) / 2) : (1 / 3 : ℝ) ≤ ‖z - x‖ := by
  have hsrc := ellipse_infDist_lower_by_real_part x
  have htri := Metric.infDist_le_infDist_add_dist (x := x) (y := z) (s := Gamma)
  change Metric.infDist z Gamma ≤ δ at hz
  rw [dist_eq_norm, norm_sub_rev] at htri
  norm_num [tubeRadiusMax, center, semiMajor] at hδ hsrc
  linarith

/-- Reflected frequency sources `x.re ≤ -1/2`, every tube center. -/
theorem tubeSweep_point_green_frequency {δ : ℝ} (hδ : δ ≤ tubeRadiusMax) {z x : ℂ}
    (hz : z ∈ tube δ) (hx : x.re ≤ -(1 : ℝ) / 2) :
    (∫ y, realLogKernel y x ∂tubeSweep z) ≤ realLogKernel z x + tubeCorrection z :=
  tubeSweep_point_green_of_sep (ε := 1 / 3) (by norm_num)
    (tube_frequency_source_norm_sub_ge hδ hz hx)
    (fun y hy => le_trans (by norm_num) (frequency_source_norm_sub_ge hx hy))

/-! ## The integrated transfer against a finite source measure -/

theorem integrable_of_bound_ae {α : Type*} [MeasurableSpace α] {μ : Measure α}
    [IsFiniteMeasure μ] {f : α → ℝ} (hf : AEStronglyMeasurable f μ) {C : ℝ}
    (h : ∀ᵐ a ∂μ, |f a| ≤ C) : Integrable f μ :=
  (integrable_const C).mono' hf (h.mono fun a ha => by rwa [Real.norm_eq_abs])

/-! A reusable bounded-integrability adapter for swept products.  The
support hypotheses are kept explicit: this is the part of the generic
`tubeSwept_source_transfer` proof that is also needed when a caller only
needs the finite-energy premise. -/
theorem tubeSwept_source_integrable {α : Type*} [MeasurableSpace α]
    {δ : ℝ} (hδ : 0 ≤ δ) (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (ρ : Measure α) [IsFiniteMeasure ρ] (S : Set α)
    (hS : ∀ᵐ a ∂ρ, a ∈ S) (G : ℂ → α → ℝ)
    (hG : Measurable (Function.uncurry G)) (C : ℝ)
    (hbound : ∀ y ∈ tube δ, ∀ a ∈ S, |G y a| ≤ C) :
    Integrable (fun p : ℂ × α => G p.1 p.2) ((tubeSwept ν).prod ρ) := by
  have hGm : StronglyMeasurable (fun p : ℂ × α => G p.1 p.2) :=
    hG.stronglyMeasurable
  have hΓt := Gamma_subset_tube hδ
  have hswept_tube : ∀ᵐ y ∂tubeSwept ν, y ∈ tube δ :=
    (tubeSwept_ae_mem_Gamma ν).mono fun y hy => hΓt hy
  apply integrable_of_bound_ae hGm.aestronglyMeasurable
  have a1 := (Measure.quasiMeasurePreserving_fst
    (μ := tubeSwept ν) (ν := ρ)).ae hswept_tube
  have a2 := (Measure.quasiMeasurePreserving_snd
    (μ := tubeSwept ν) (ν := ρ)).ae hS
  filter_upwards [a1, a2] with p hp1 hp2
  exact hbound p.1 hp1 p.2 hp2

/-- Generic sweep transfer for a bounded measurable interaction `G` whose point
Green bound holds at every tube center. -/
theorem tubeSwept_source_transfer {α : Type*} [MeasurableSpace α]
    {δ : ℝ} (hδ : 0 ≤ δ) (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (ρ : Measure α) [IsFiniteMeasure ρ] (S : Set α) (hS : ∀ᵐ a ∂ρ, a ∈ S)
    (G : ℂ → α → ℝ) (hG : Measurable (Function.uncurry G)) (C : ℝ)
    (hbound : ∀ y ∈ tube δ, ∀ a ∈ S, |G y a| ≤ C)
    (hpoint : ∀ z ∈ tube δ, ∀ a ∈ S,
      (∫ y, G y a ∂tubeSweep z) ≤ G z a + tubeCorrection z) :
    (∫ p, G p.1 p.2 ∂(tubeSwept ν).prod ρ) ≤
      (∫ p, G p.1 p.2 ∂ν.prod ρ) + ρ.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
  have hGm : StronglyMeasurable (fun p : ℂ × α => G p.1 p.2) := hG.stronglyMeasurable
  have hΓt := Gamma_subset_tube hδ
  -- bounded integrability on the relevant products
  have hprod_int : ∀ (μ : Measure ℂ) [IsFiniteMeasure μ], (∀ᵐ y ∂μ, y ∈ tube δ) →
      Integrable (fun p : ℂ × α => G p.1 p.2) (μ.prod ρ) := by
    intro μ _ hμ
    apply integrable_of_bound_ae hGm.aestronglyMeasurable
    have a1 := (Measure.quasiMeasurePreserving_fst (μ := μ) (ν := ρ)).ae hμ
    have a2 := (Measure.quasiMeasurePreserving_snd (μ := μ) (ν := ρ)).ae hS
    filter_upwards [a1, a2] with p hp1 hp2
    exact hbound p.1 hp1 p.2 hp2
  have hswept_tube : ∀ᵐ y ∂tubeSwept ν, y ∈ tube δ :=
    (tubeSwept_ae_mem_Gamma ν).mono fun y hy => hΓt hy
  have hsweep_tube : ∀ z, ∀ᵐ y ∂tubeSweep z, y ∈ tube δ := fun z =>
    (tubeSweep_ae_mem_Gamma z).mono fun y hy => hΓt hy
  -- step 1: product Fubini for the swept measure
  rw [integral_prod _ (hprod_int _ hswept_tube)]
  -- step 2: bind Fubini
  set g : ℂ → ℝ := fun y => ∫ a, G y a ∂ρ with hg
  have hg_meas : StronglyMeasurable g := hGm.integral_prod_right'
  have hg_bound : ∀ y ∈ tube δ, |g y| ≤ C * ρ.real Set.univ := by
    intro y hy
    have := norm_integral_le_of_norm_le_const (μ := ρ) (f := fun a => G y a) (C := C)
      (hS.mono fun a ha => by rw [Real.norm_eq_abs]; exact hbound y hy a ha)
    simpa [Real.norm_eq_abs] using this
  have hg_int : Integrable g (tubeSwept ν) :=
    integrable_of_bound_ae hg_meas.aestronglyMeasurable
      (hswept_tube.mono fun y hy => hg_bound y hy)
  rw [show (∫ y, ∫ a, G y a ∂ρ ∂tubeSwept ν) = ∫ y, g y ∂tubeSwept ν from rfl,
    tubeSwept, integral_sweptMeasure ν tubeSweep g measurable_tubeSweep.aemeasurable hg_int]
  -- step 3: pointwise comparison
  have hinner : ∀ z ∈ tube δ, (∫ y, g y ∂tubeSweep z) ≤
      (∫ a, G z a ∂ρ) + ρ.real Set.univ * tubeCorrection z := by
    intro z hz
    have hzint : Integrable (fun p : ℂ × α => G p.1 p.2) ((tubeSweep z).prod ρ) :=
      hprod_int _ (hsweep_tube z)
    have hswap : (∫ y, g y ∂tubeSweep z) = ∫ a, ∫ y, G y a ∂tubeSweep z ∂ρ := by
      simp only [g]
      exact integral_integral_swap hzint
    rw [hswap]
    have hGz : Integrable (fun a => G z a) ρ :=
      integrable_of_bound_ae (hGm.comp_measurable (measurable_const.prodMk measurable_id)).aestronglyMeasurable
        (hS.mono fun a ha => hbound z hz a ha)
    calc (∫ a, ∫ y, G y a ∂tubeSweep z ∂ρ) ≤ ∫ a, (G z a + tubeCorrection z) ∂ρ := by
          apply integral_mono_ae hzint.integral_prod_right (hGz.add (integrable_const _))
          filter_upwards [hS] with a ha
          exact hpoint z hz a ha
      _ = (∫ a, G z a ∂ρ) + ρ.real Set.univ * tubeCorrection z := by
          rw [integral_add hGz (integrable_const _), integral_const, smul_eq_mul, mul_comm]
  -- step 4: integrate over ν
  have hout_meas : StronglyMeasurable (fun z => ∫ y, g y ∂tubeSweep z) := by
    have := StronglyMeasurable.integral_kernel_prod_right' (κ := tubeKernel)
      (f := fun q : ℂ × ℂ => g q.2) (hg_meas.comp_measurable measurable_snd)
    simpa using this
  have hout_int : Integrable (fun z => ∫ y, g y ∂tubeSweep z) ν := by
    apply integrable_of_bound_ae hout_meas.aestronglyMeasurable (C := C * ρ.real Set.univ)
    filter_upwards with z
    have := norm_integral_le_of_norm_le_const (μ := tubeSweep z) (f := g)
      (C := C * ρ.real Set.univ)
      ((hsweep_tube z).mono fun y hy => by rw [Real.norm_eq_abs]; exact hg_bound y hy)
    simpa [Real.norm_eq_abs] using this
  have he := integrable_tubeCorrection hδ ν hsupp
  have hνprod := hprod_int ν hsupp
  calc (∫ z, ∫ y, g y ∂tubeSweep z ∂ν) ≤
        ∫ z, ((∫ a, G z a ∂ρ) + ρ.real Set.univ * tubeCorrection z) ∂ν := by
        apply integral_mono_ae hout_int (hνprod.integral_prod_left.add (he.const_mul _))
        filter_upwards [hsupp] with z hz
        exact hinner z hz
    _ = (∫ p, G p.1 p.2 ∂ν.prod ρ) + ρ.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
        rw [integral_add hνprod.integral_prod_left (he.const_mul _), integral_const_mul,
          integral_prod _ hνprod]

/-! ## Instances: pinned and frequency sources -/

/-- Pinned interaction: `κ` carried by real points of `[0,2]`. -/
theorem tubeSwept_pinned_transfer {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (κc : Measure ℂ) [IsFiniteMeasure κc]
    (hκ : ∀ᵐ x ∂κc, x.re ∈ Set.Icc (0 : ℝ) 2 ∧ x.im = 0) :
    (∫ p, realLogKernel p.1 p.2 ∂(tubeSwept ν).prod κc) ≤
      (∫ p, realLogKernel p.1 p.2 ∂ν.prod κc) +
        κc.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
  apply tubeSwept_source_transfer hδ ν hsupp κc {x | x.re ∈ Set.Icc (0 : ℝ) 2 ∧ x.im = 0} hκ
    realLogKernel (by unfold realLogKernel; fun_prop) (|Real.log (5383 / 40000)| + |Real.log 7|)
  · intro y hy x hx
    have hlow := tube_positive_source_norm_sub_ge hδmax hy hx.1 hx.2
    have hyn := norm_le_of_mem_tube hy
    have hxn : ‖x‖ ≤ 2 := by
      have : x = (x.re : ℂ) := Complex.ext (by simp) (by simp [hx.2])
      rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1.1]; exact hx.1.2
    norm_num [tubeRadiusMax] at hδmax
    have hup : ‖y - x‖ ≤ 7 := (norm_sub_le _ _).trans (by linarith)
    have hpos : (0 : ℝ) < 5383 / 40000 := by norm_num
    have h1 : Real.log (5383 / 40000) ≤ Real.log ‖y - x‖ := Real.log_le_log hpos hlow
    have h2 : Real.log ‖y - x‖ ≤ Real.log 7 := Real.log_le_log (lt_of_lt_of_le hpos hlow) hup
    have a1 := le_abs_self (Real.log 7)
    have a2 := neg_abs_le (Real.log (5383 / 40000))
    have a3 := abs_nonneg (Real.log 7)
    have a4 := abs_nonneg (Real.log (5383 / 40000))
    unfold realLogKernel
    rw [abs_neg, abs_le]
    constructor <;> linarith
  · intro z hz x hx
    exact tubeSweep_point_green_positive hδmax hz hx.1 hx.2

/-- The regularized mixed kernel splits as `log(1+t) + K₀(y,-t)` away from collisions. -/
theorem mixedKernel_eq {y : ℂ} {t : ℝ} (ht : 0 ≤ t) (hy : y + (t : ℂ) ≠ 0) :
    p0RegularizedMixedKernel y t = Real.log (1 + t) + realLogKernel y (-(t : ℂ)) := by
  unfold p0RegularizedMixedKernel realLogKernel
  rw [sub_neg_eq_add, Real.log_div (by linarith) (norm_ne_zero_iff.mpr hy)]
  ring

/-- Frequency interaction: the regularized mixed kernel against `μ` carried by `[1/2,∞)`. -/
/- The mixed kernel is uniformly bounded on the swept tube and the
frequency half-line.  Keeping this estimate separate lets finite-energy
consumers obtain product integrability without replaying the transfer
inequality. -/
theorem p0RegularizedMixedKernel_bound_on_tube {δ : ℝ}
    (hδmax : δ ≤ tubeRadiusMax) :
    ∀ y ∈ tube δ, ∀ t ∈ Set.Ici (1 / 2 : ℝ),
      |p0RegularizedMixedKernel y t| ≤ Real.log 18 := by
  intro y hy t ht
  have ht' : (1 / 2 : ℝ) ≤ t := ht
  have hs : (1 / 3 : ℝ) ≤ ‖y + (t : ℂ)‖ := by
    have h := tube_frequency_source_norm_sub_ge hδmax hy (x := -(t : ℂ))
      (by simp; linarith [Set.mem_Ici.mp ht])
    simpa [sub_neg_eq_add] using h
  have hyn := norm_le_of_mem_tube hy
  norm_num [tubeRadiusMax] at hδmax
  have hpos : 0 < ‖y + (t : ℂ)‖ := lt_of_lt_of_le (by norm_num) hs
  have hup : ‖y + (t : ℂ)‖ ≤ 5 * (1 + t) := by
    calc ‖y + (t : ℂ)‖ ≤ ‖y‖ + ‖(t : ℂ)‖ := norm_add_le _ _
      _ ≤ 5 * (1 + t) := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
        linarith
  have hlow : 1 + t ≤ 18 * ‖y + (t : ℂ)‖ := by
    have h2 : t - ‖y‖ ≤ ‖y + (t : ℂ)‖ := by
      have := norm_sub_norm_le (y + (t : ℂ)) y
      have hy' : ‖y + (t : ℂ) - y‖ = t := by
        rw [add_sub_cancel_left, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (by linarith)]
      have := norm_sub_norm_le (y + (t : ℂ) - y) (y + (t : ℂ))
      rw [hy'] at this
      have h3 : ‖y + (t : ℂ) - y - (y + (t : ℂ))‖ = ‖y‖ := by
        rw [show y + (t : ℂ) - y - (y + (t : ℂ)) = -y by ring, norm_neg]
      linarith
    rcases le_or_gt t 5 with h5 | h5
    · linarith
    · linarith
  unfold p0RegularizedMixedKernel
  have hq : 0 < (1 + t) / ‖y + (t : ℂ)‖ := div_pos (by linarith) hpos
  rw [abs_le]
  constructor
  · have hlow' : (1 / 5 : ℝ) ≤ (1 + t) / ‖y + (t : ℂ)‖ := by
      rw [le_div_iff₀ hpos]
      linarith
    have hl := Real.log_le_log (by norm_num) hlow'
    have h5 : Real.log (1 / 5 : ℝ) = -Real.log 5 := by
      rw [one_div, Real.log_inv]
    have h518 : Real.log 5 ≤ Real.log 18 :=
      Real.log_le_log (by norm_num) (by norm_num)
    linarith
  · have hu : (1 + t) / ‖y + (t : ℂ)‖ ≤ 18 := by
      rw [div_le_iff₀ hpos]
      linarith
    exact Real.log_le_log hq hu

/-- Product integrability of the swept mixed interaction, for use in the
finite-energy side of the tube transfer. -/
theorem tubeSwept_mixed_integrable {δ : ℝ} (hδ : 0 ≤ δ)
    (hδmax : δ ≤ tubeRadiusMax) (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ) (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hμ : ∀ᵐ t ∂μ, t ∈ Set.Ici (1 / 2 : ℝ)) :
    Integrable (fun p : ℂ × ℝ => p0RegularizedMixedKernel p.1 p.2)
      ((tubeSwept ν).prod μ) := by
  apply tubeSwept_source_integrable hδ ν hsupp μ (Set.Ici (1 / 2 : ℝ)) hμ
    p0RegularizedMixedKernel (by unfold p0RegularizedMixedKernel; fun_prop)
    (Real.log 18)
  exact p0RegularizedMixedKernel_bound_on_tube hδmax

theorem tubeSwept_mixed_transfer {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (μ : Measure ℝ) [IsFiniteMeasure μ] (hμ : ∀ᵐ t ∂μ, t ∈ Set.Ici (1 / 2 : ℝ)) :
    (∫ p, p0RegularizedMixedKernel p.1 p.2 ∂(tubeSwept ν).prod μ) ≤
      (∫ p, p0RegularizedMixedKernel p.1 p.2 ∂ν.prod μ) +
        μ.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
  have hsep : ∀ y ∈ tube δ, ∀ t ∈ Set.Ici (1 / 2 : ℝ), (1 / 3 : ℝ) ≤ ‖y + (t : ℂ)‖ := by
    intro y hy t ht
    have h := tube_frequency_source_norm_sub_ge hδmax hy (x := -(t : ℂ))
      (by simp; linarith [Set.mem_Ici.mp ht])
    simpa [sub_neg_eq_add] using h
  apply tubeSwept_source_transfer hδ ν hsupp μ (Set.Ici (1 / 2 : ℝ)) hμ
    p0RegularizedMixedKernel (by unfold p0RegularizedMixedKernel; fun_prop) (Real.log 18)
  · exact p0RegularizedMixedKernel_bound_on_tube hδmax
  · intro z hz t ht
    have ht' : (1 / 2 : ℝ) ≤ t := ht
    have hzt : z + (t : ℂ) ≠ 0 := by
      intro h; have := hsep z hz t ht; rw [h, norm_zero] at this; norm_num at this
    have hfreq := tubeSweep_point_green_frequency hδmax hz (x := -(t : ℂ))
      (by simp; linarith)
    have heq : (fun y => p0RegularizedMixedKernel y t) =ᵐ[tubeSweep z]
        (fun y => Real.log (1 + t) + realLogKernel y (-(t : ℂ))) := by
      filter_upwards [tubeSweep_ae_mem_Gamma z] with y hy
      have hyt : y + (t : ℂ) ≠ 0 := by
        intro h
        have := hsep y (Gamma_subset_tube hδ hy) t ht
        rw [h, norm_zero] at this; norm_num at this
      exact mixedKernel_eq (by linarith) hyt
    have hint : Integrable (fun y => realLogKernel y (-(t : ℂ))) (tubeSweep z) := by
      apply integrable_of_bound_ae (C := |Real.log (1749 / 5000)| + |Real.log (9 + t)|)
        ((Real.measurable_log.comp (by fun_prop : Measurable fun y : ℂ => ‖y - -(t : ℂ)‖)).neg).aestronglyMeasurable
      filter_upwards [tubeSweep_ae_mem_Gamma z] with y hy
      have hl := frequency_source_norm_sub_ge (x := -(t : ℂ)) (by simp; linarith) hy
      have hu : ‖y - -(t : ℂ)‖ ≤ 9 + t := by
        have := TubeVariance.norm_le_four_of_mem_Gamma hy
        calc ‖y - -(t : ℂ)‖ ≤ ‖y‖ + ‖(t : ℂ)‖ := by rw [sub_neg_eq_add]; exact norm_add_le _ _
          _ ≤ 9 + t := by
            rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]; linarith
      have hp : (0 : ℝ) < 1749 / 5000 := by norm_num
      have h1 := Real.log_le_log hp hl
      have h2 := Real.log_le_log (lt_of_lt_of_le hp hl) hu
      show |-Real.log ‖y - -(t : ℂ)‖| ≤ _
      rw [abs_neg, abs_le]
      constructor <;> linarith [le_abs_self (Real.log (9 + t)), neg_abs_le (Real.log (1749 / 5000)),
        abs_nonneg (Real.log (9 + t)), neg_le_abs (Real.log (1749 / 5000)),
        abs_nonneg (Real.log (1749 / 5000))]
    have hone : (tubeSweep z).real Set.univ = 1 := by simp [Measure.real]
    rw [integral_congr_ae heq, integral_add (integrable_const _) hint, integral_const,
      hone, one_smul, mixedKernel_eq (by linarith) hzt]
    linarith

/-! ## The paper's constant chain -/

/-- Interaction bookkeeping of v10: `2sb + 2(1-s)b + b = 3b`. -/
theorem interaction_cost_eq (s b : ℝ) : 2 * s * b + 2 * (1 - s) * b + b = 3 * b := by ring

/-- Constant chain: a field cost `≤ 288 s δ / B` and an interaction cost `≤ 3b`
with `b ≤ s δ / B` (as delivered by `tubeSwept_properties`) total at most `300 δ`. -/
theorem tube_transfer_cost_chain {δ s b F I : ℝ} (hδ : 0 < δ) (hs1 : s ≤ 1)
    (hb : b ≤ s * (δ / semiMinor)) (hF : F ≤ 288 * s * δ / semiMinor) (hI : I ≤ 3 * b) :
    F + I ≤ 300 * δ := by
  have h291 : F + I ≤ 291 * s * δ / semiMinor := by
    have : 3 * b ≤ 3 * s * δ / semiMinor := by
      have := mul_le_mul_of_nonneg_left hb (by norm_num : (0 : ℝ) ≤ 3)
      calc 3 * b ≤ 3 * (s * (δ / semiMinor)) := this
        _ = 3 * s * δ / semiMinor := by ring
    have e : 291 * s * δ / semiMinor = 288 * s * δ / semiMinor + 3 * s * δ / semiMinor := by ring
    linarith
  exact h291.trans (tube_error_cost_lt_300 hδ hs1).le

/-! ## Companion interaction split -/

/-- Bind is additive in its source measure for the measurable tube kernel. -/
theorem tubeSwept_add (μ ν : Measure ℂ) :
    tubeSwept (μ + ν) = tubeSwept μ + tubeSwept ν := by
  ext s hs
  rw [tubeSwept, sweptMeasure, Measure.bind_apply hs measurable_tubeSweep.aemeasurable,
    Measure.add_apply]
  rw [tubeSwept, sweptMeasure, Measure.bind_apply hs measurable_tubeSweep.aemeasurable,
    tubeSwept, sweptMeasure, Measure.bind_apply hs measurable_tubeSweep.aemeasurable]
  exact lintegral_add_measure _ _ _

/-- Additivity of logarithmic interaction under two measure sums.

The four integrability premises keep the real-valued expansion honest; no
finite-energy conclusion is hidden in this algebraic split. -/
theorem li2LogInteraction_add_add
    (μ₁ μ₂ ν₁ ν₂ : Measure ℂ)
    [SFinite μ₁] [SFinite μ₂] [SFinite ν₁] [SFinite ν₂]
    (h11 : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ₁.prod ν₁))
    (h12 : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ₁.prod ν₂))
    (h21 : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ₂.prod ν₁))
    (h22 : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (μ₂.prod ν₂)) :
    li2LogInteraction (μ₁ + μ₂) (ν₁ + ν₂) =
      li2LogInteraction μ₁ ν₁ + li2LogInteraction μ₁ ν₂ +
        li2LogInteraction μ₂ ν₁ + li2LogInteraction μ₂ ν₂ := by
  unfold li2LogInteraction
  rw [Measure.add_prod, Measure.prod_add, Measure.prod_add]
  rw [integral_add_measure (h11.add_measure h12) (h21.add_measure h22)]
  rw [integral_add_measure h11 h12, integral_add_measure h21 h22]
  ring

/-- The `η# × η#` interaction split from v10 `sec-tube`: the pinned
component stays fixed while the tube component is swept. -/
theorem tubeSwept_companion_interaction_split
    (κ ν : Measure ℂ)
    [IsFiniteMeasure κ] [IsFiniteMeasure ν]
    (hκκ : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2) (κ.prod κ))
    (hκν : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      (κ.prod (tubeSwept ν)))
    (hνκ : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((tubeSwept ν).prod κ))
    (hνν : Integrable (fun p : ℂ × ℂ => li2LogKernel p.1 p.2)
      ((tubeSwept ν).prod (tubeSwept ν))) :
    li2LogInteraction (κ + tubeSwept ν) (κ + tubeSwept ν) =
      li2LogInteraction κ κ + li2LogInteraction κ (tubeSwept ν) +
        li2LogInteraction (tubeSwept ν) κ +
        li2LogInteraction (tubeSwept ν) (tubeSwept ν) := by
  exact li2LogInteraction_add_add κ (tubeSwept ν) κ (tubeSwept ν)
    hκκ hκν hνκ hνν

end
end Li2Lean.P0.TubeEnergy
