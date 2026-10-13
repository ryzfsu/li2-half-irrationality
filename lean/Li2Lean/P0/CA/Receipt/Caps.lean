/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.Tube

/-!
# First-variation caps for admissible measures

For every literal admissible pair `M` (v10 `eq:contour-admissible`) and every
field `W` integrable against `M.eta`:

* if `h ≤ W` on `Γ`, and `h - W ≤ p` on `[1/4,5/4]` with `0 ≤ p`
  integrable there, then `h - ∫_{[1/4,5/4]} p ≤ ∫ W dη`;
* if `h - W ≤ q` on `[1/2,∞)` with `0 ≤ q` integrable there, then
  `h - ∫_{[1/2,∞)} q ≤ ∫ W dμ`.

These use only the density caps, the support condition and the exact masses
of `P0AdmissibleMeasures`; they are the cap estimates `∫W_η dη ≥ h_η - P`,
`∫W_μ dμ ≥ h_μ - T` of v10 `lem:dual-lower`.
-/

open MeasureTheory Set

namespace Li2Lean.P0.CA.Receipt

noncomputable section

theorem kappa_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ x ∂M.kappa, x ∈ Icc (1 / 4 : ℝ) (5 / 4) := by
  have h0 : M.kappa (Icc (1 / 4 : ℝ) (5 / 4))ᶜ = 0 := by
    refine le_antisymm ?_ bot_le
    calc M.kappa (Icc (1 / 4 : ℝ) (5 / 4))ᶜ
        ≤ volume.restrict (Icc (1 / 4 : ℝ) (5 / 4)) (Icc (1 / 4 : ℝ) (5 / 4))ᶜ :=
          M.kappa_le_density _
      _ = 0 := by
          rw [Measure.restrict_apply measurableSet_Icc.compl, Set.compl_inter_self,
            measure_empty]
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx

theorem mu_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ t ∂M.mu, t ∈ Ici (1 / 2 : ℝ) := by
  have h0 : M.mu (Ici (1 / 2 : ℝ))ᶜ = 0 := by
    refine le_antisymm ?_ bot_le
    calc M.mu (Ici (1 / 2 : ℝ))ᶜ
        ≤ volume.restrict (Ici (1 / 2 : ℝ)) (Ici (1 / 2 : ℝ))ᶜ :=
          M.mu_le_density _
      _ = 0 := by
          rw [Measure.restrict_apply measurableSet_Ici.compl, Set.compl_inter_self,
            measure_empty]
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx

theorem nu_ae_mem (M : P0AdmissibleMeasures) :
    ∀ᵐ z ∂M.nu, z ∈ Gamma := by
  have h0 : M.nu (Gamma)ᶜ = 0 :=
    measure_mono_null (compl_subset_compl.mpr M.nu_supported)
      (Measure.measure_compl_support)
  exact measure_eq_zero_iff_ae_notMem.mp h0 |>.mono fun x hx => by simpa using hx

/-- The exact mass split `κ(ℝ) + ν(ℂ) = 1`. -/
theorem kappa_nu_mass (M : P0AdmissibleMeasures) :
    M.kappa univ + M.nu univ = 1 := by
  have h := M.companion_mass
  rw [p0CompanionMeasure, Measure.add_apply,
    Measure.map_apply Complex.measurable_ofReal MeasurableSet.univ,
    preimage_univ] at h
  exact h

instance kappa_isFinite (M : P0AdmissibleMeasures) : IsFiniteMeasure M.kappa := by
  constructor
  have h := kappa_nu_mass M
  have : M.kappa univ ≤ 1 := by rw [← h]; exact le_self_add
  exact lt_of_le_of_lt this ENNReal.one_lt_top

instance nu_isFinite (M : P0AdmissibleMeasures) : IsFiniteMeasure M.nu := by
  constructor
  have h := kappa_nu_mass M
  have : M.nu univ ≤ 1 := by rw [← h]; exact le_add_self
  exact lt_of_le_of_lt this ENNReal.one_lt_top

instance mu_isProb (M : P0AdmissibleMeasures) : IsProbabilityMeasure M.mu :=
  ⟨M.frequency_mass⟩

theorem kappa_nu_real_mass (M : P0AdmissibleMeasures) :
    M.kappa.real univ + M.nu.real univ = 1 := by
  have h := congrArg ENNReal.toReal (kappa_nu_mass M)
  rw [ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)] at h
  simpa [Measure.real] using h

/-- Lower bound of a nonnegative-penalty integral against a density-capped
measure: `h·m(ℝ) - ∫_S p ≤ ∫ W dm`. -/
theorem integral_ge_of_cap {m : Measure ℝ} [IsFiniteMeasure m] {S : Set ℝ}
    (hS : MeasurableSet S) (hm : m ≤ volume.restrict S)
    (hmS : ∀ᵐ x ∂m, x ∈ S)
    {W p : ℝ → ℝ} {h : ℝ} (hW : Integrable W m)
    (hp0 : ∀ x ∈ S, 0 ≤ p x) (hpW : ∀ x ∈ S, h - W x ≤ p x)
    (hpInt : IntegrableOn p S) :
    h * m.real univ - ∫ x in S, p x ≤ ∫ x, W x ∂m := by
  have hpm : Integrable p m := (show Integrable p (volume.restrict S) from hpInt).mono_measure hm
  have hmono : ∫ x, (h - p x) ∂m ≤ ∫ x, W x ∂m := by
    apply integral_mono_ae ((integrable_const h).sub hpm) hW
    filter_upwards [hmS] with x hx
    show h - p x ≤ W x
    linarith [hpW x hx]
  have hsplit : ∫ x, (h - p x) ∂m = h * m.real univ - ∫ x, p x ∂m := by
    rw [integral_sub (integrable_const h) hpm, integral_const, smul_eq_mul, mul_comm]
  have hpS : ∫ x, p x ∂m ≤ ∫ x in S, p x := by
    apply integral_mono_measure hm _ hpInt
    filter_upwards [ae_restrict_mem hS] with x hx
    exact hp0 x hx
  linarith

/-- The pinned/contour cap `h - P ≤ ∫ W dη`. -/
theorem eta_cap (M : P0AdmissibleMeasures) {W : ℂ → ℝ} {h : ℝ} {p : ℝ → ℝ}
    (hW : Integrable W M.eta)
    (hΓ : ∀ z ∈ Gamma, h ≤ W z)
    (hp0 : ∀ x ∈ Icc (1 / 4 : ℝ) (5 / 4), 0 ≤ p x)
    (hpW : ∀ x ∈ Icc (1 / 4 : ℝ) (5 / 4), h - W (x : ℂ) ≤ p x)
    (hpInt : IntegrableOn p (Icc (1 / 4 : ℝ) (5 / 4))) :
    h - ∫ x in Icc (1 / 4 : ℝ) (5 / 4), p x ≤ ∫ z, W z ∂M.eta := by
  have hemb := Complex.isometry_ofReal.isClosedEmbedding.measurableEmbedding
  have hWmap : Integrable W (Measure.map Complex.ofReal M.kappa) :=
    hW.mono_measure (Measure.le_add_right le_rfl)
  have hWnu : Integrable W M.nu := hW.mono_measure (Measure.le_add_left le_rfl)
  have hWk : Integrable (fun x : ℝ => W (x : ℂ)) M.kappa :=
    (hemb.integrable_map_iff).mp hWmap
  have hsplit : ∫ z, W z ∂M.eta =
      (∫ x, W (x : ℂ) ∂M.kappa) + ∫ z, W z ∂M.nu := by
    rw [P0AdmissibleMeasures.eta, p0CompanionMeasure,
      integral_add_measure hWmap hWnu, hemb.integral_map]
  have hk := integral_ge_of_cap measurableSet_Icc M.kappa_le_density
    (kappa_ae_mem M) hWk hp0 hpW hpInt
  have hn : h * M.nu.real univ ≤ ∫ z, W z ∂M.nu := by
    have := integral_mono_ae (integrable_const h) hWnu
      ((nu_ae_mem M).mono fun z hz => hΓ z hz)
    rwa [integral_const, smul_eq_mul, mul_comm] at this
  have hmass : h * M.kappa.real univ + h * M.nu.real univ = h := by
    rw [← mul_add, kappa_nu_real_mass M, mul_one]
  rw [hsplit]
  linarith

/-- The frequency cap `h - T ≤ ∫ W dμ`. -/
theorem mu_cap (M : P0AdmissibleMeasures) {W : ℝ → ℝ} {h : ℝ} {q : ℝ → ℝ}
    (hW : Integrable W M.mu)
    (hq0 : ∀ t ∈ Ici (1 / 2 : ℝ), 0 ≤ q t)
    (hqW : ∀ t ∈ Ici (1 / 2 : ℝ), h - W t ≤ q t)
    (hqInt : IntegrableOn q (Ici (1 / 2 : ℝ))) :
    h - ∫ t in Ici (1 / 2 : ℝ), q t ≤ ∫ t, W t ∂M.mu := by
  have hk := integral_ge_of_cap measurableSet_Ici M.mu_le_density
    (mu_ae_mem M) hW hq0 hqW hqInt
  have hmass : M.mu.real univ = 1 := by simp [Measure.real, M.frequency_mass]
  rw [hmass, mul_one] at hk
  exact hk

end

end Li2Lean.P0.CA.Receipt
