/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.CircleField

/-!
# The circle pieces of the cell inequality

Paper v13 `p0-analytic.tex` ll. 275-283 and 369-383:

* `nuNuPiece`: contour self-energy with the circle smoothing loss `2 d log m`;
* `kNuPiece`: pinned-contour interaction (exact circle average, then the
  cell displacement `1/(2 m^2 d_+)` per pair);
* `nuMuPiece`: contour-frequency interaction (exact circle average, then the
  right-endpoint displacement `1/(2 m^2 d_-)` per pair);
* `contFieldPiece`: the companion field `A_0 - φ` on the circles; `A_0` is
  harmonic there and `φ` is subharmonic.
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

theorem wν_eq (C : FiniteConfiguration) :
    wν C = circleEmpiricalMeasure C.contour (configTubeRadius C) C.m := rfl

theorem configTubeRadius_le_dPlus (C : FiniteConfiguration) :
    configTubeRadius C ≤ dPlus := by
  have := configTubeRadius_le C
  norm_num [dPlus] at *
  linarith

theorem configTubeRadius_le_dMinus (C : FiniteConfiguration) :
    configTubeRadius C ≤ dMinus := by
  have := configTubeRadius_le C
  norm_num [dMinus] at *
  linarith

theorem contour_mem_base (C : FiniteConfiguration) (a : Fin C.contourCount) :
    C.contour a ∈ baseEllipseSet :=
  Gamma_subset_baseEllipseSet (contour_mem_Gamma C a)

/-! ## Contour self-energy -/

theorem nuNuPiece : NuNuPiece := by
  intro C hdist
  have hm : (0 : ℝ) < C.m := by
    have := C.m_ge_eight; exact_mod_cast (show 0 < C.m by omega)
  have hr := configTubeRadius_pos C
  have h := circleEmpiricalMeasure_energy_transfer C.contour hr hdist C.m
  have hsum : (∑ i : Fin C.contourCount, ∑ j : Fin C.contourCount,
      if i = j then 0 else realLogKernel (C.contour i) (C.contour j)) = -contCont C := by
    unfold contCont
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    split_ifs <;> simp [realLogKernel]
  have hlog : Real.log (1 / configTubeRadius C) = 2 * Real.log (C.m : ℝ) := by
    unfold configTubeRadius
    rw [one_div_one_div, Real.log_pow]
    norm_num
  have hI : eIνν C = ∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleEmpiricalMeasure C.contour (configTubeRadius C) C.m).prod
        (circleEmpiricalMeasure C.contour (configTubeRadius C) C.m)) := rfl
  rw [hsum, hlog] at h
  rw [hI]
  set X := ∫ p : ℂ × ℂ, realLogKernel p.1 p.2
      ∂((circleEmpiricalMeasure C.contour (configTubeRadius C) C.m).prod
        (circleEmpiricalMeasure C.contour (configTubeRadius C) C.m))
  have hm2 : (0 : ℝ) < (C.m : ℝ) ^ 2 := by positivity
  have h' : X ≤ (-contCont C + 2 * (C.contourCount : ℝ) * Real.log (C.m : ℝ)) /
      (C.m : ℝ) ^ 2 := by
    rw [add_div]
    have : (C.contourCount : ℝ) / (C.m : ℝ) ^ 2 * (2 * Real.log (C.m : ℝ)) =
        2 * (C.contourCount : ℝ) * Real.log (C.m : ℝ) / (C.m : ℝ) ^ 2 := by ring
    linarith
  rw [le_div_iff₀ hm2] at h'
  linarith

/-! ## Cell geometry -/

theorem pinned_cell_bounds (C : FiniteConfiguration) {s : ℕ} (hs : s ∈ C.pinned) :
    (1 / 4 : ℝ) ≤ (s : ℝ) / (C.m : ℝ) ∧ (((s + 1 : ℕ) : ℝ) / (C.m : ℝ)) ≤ 5 / 4 := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hiS := C.pinned_subset hs
  simp only [pinnedUniverse, Finset.mem_Ico] at hiS
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  have hlo' : (k : ℝ) ≤ s := by
    have : k ≤ s := by omega
    exact_mod_cast this
  have hhi' : ((s + 1 : ℕ) : ℝ) ≤ 5 * k := by
    have : s + 1 ≤ 5 * k := by omega
    exact_mod_cast this
  constructor
  · rw [le_div_iff₀ hmR, hmk]; linarith
  · rw [div_le_iff₀ hmR, hmk]; linarith

theorem frequency_cell_bounds (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency) :
    (1 / 2 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) ∧
      (r : ℝ) / (C.m : ℝ) - ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) = 1 / (C.m : ℝ) := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  have h1 := C.frequency_lower r hr
  have hr1 : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  constructor
  · have : (2 * k : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
      have : 2 * k ≤ r - 1 := by omega
      exact_mod_cast this
    rw [le_div_iff₀ hmR, hmk]; linarith
  · rw [hr1]; field_simp; ring

/-! ## Pinned-contour interaction -/

/-- One pinned cell against one circle. -/
theorem pinned_contour_pair (C : FiniteConfiguration) {s : ℕ} (hs : s ∈ C.pinned)
    (a : Fin C.contourCount) :
    -((C.m : ℝ) * ∫ x in pinnedCell C.m s,
        Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)) ≤
      -Real.log ‖(((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖ +
        1 / (2 * (C.m : ℝ) * dPlus) := by
  have hmR : (0 : ℝ) < C.m := by
    have := C.m_ge_eight; exact_mod_cast (show 0 < C.m by omega)
  have hdP : (0 : ℝ) < dPlus := by norm_num [dPlus]
  have hrd := configTubeRadius_le_dPlus C
  obtain ⟨hlo, hhi⟩ := pinned_cell_bounds C hs
  set a0 : ℝ := (s : ℝ) / (C.m : ℝ)
  set b0 : ℝ := ((s + 1 : ℕ) : ℝ) / (C.m : ℝ)
  have hba : b0 - a0 = 1 / (C.m : ℝ) := by
    simp only [a0, b0]; push_cast; field_simp; ring
  have hab : a0 ≤ b0 := by linarith [show 0 < 1 / (C.m : ℝ) by positivity]
  have hcl : ∀ x ∈ Set.Icc a0 b0, dPlus ≤ ‖(x : ℂ) - C.contour a‖ := by
    intro x hx
    rw [norm_sub_rev]
    exact mixedCellClearance_full.1 _ (contour_mem_base C a) x
      ⟨by linarith [hx.1], by linarith [hx.2]⟩
  set f : ℝ → ℝ := fun x => Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)
  have hfeq : ∀ x ∈ Set.Icc a0 b0, f x = Real.log ‖(x : ℂ) - C.contour a‖ := by
    intro x hx
    simp only [f]
    rw [max_eq_right ((hrd).trans (hcl x hx))]
  have hcont : Continuous f := by
    apply Continuous.log (by fun_prop)
    intro x
    exact (lt_of_lt_of_le (configTubeRadius_pos C) (le_max_left _ _)).ne'
  have hL : ∀ x ∈ Set.Icc a0 b0, |f x - f a0| ≤ (1 / dPlus) * (x - a0) := by
    intro x hx
    have ha0 : a0 ∈ Set.Icc a0 b0 := ⟨le_rfl, hab⟩
    rw [hfeq x hx, hfeq a0 ha0]
    calc |Real.log ‖(x : ℂ) - C.contour a‖ - Real.log ‖(a0 : ℂ) - C.contour a‖|
        ≤ |‖(x : ℂ) - C.contour a‖ - ‖(a0 : ℂ) - C.contour a‖| / dPlus :=
          abs_log_sub_log_le hdP (hcl x hx) (hcl a0 ha0)
      _ ≤ ‖((x : ℂ) - C.contour a) - ((a0 : ℂ) - C.contour a)‖ / dPlus :=
          div_le_div_of_nonneg_right (abs_norm_sub_norm_le _ _) hdP.le
      _ = (1 / dPlus) * (x - a0) := by
          rw [show ((x : ℂ) - C.contour a) - ((a0 : ℂ) - C.contour a) =
            ((x - a0 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (by linarith [hx.1])]
          ring
  have hcell := cell_left_endpoint hab hcont.continuousOn hL
  rw [hba] at hcell
  have hfa : f a0 = Real.log ‖(a0 : ℂ) - C.contour a‖ := hfeq a0 ⟨le_rfl, hab⟩
  rw [hfa] at hcell
  have hcellset : pinnedCell C.m s = Set.Ico a0 b0 := rfl
  rw [hcellset]
  set I := ∫ x in Set.Ico a0 b0, f x
  have h1 := (abs_le.mp hcell).1
  have hmul : (C.m : ℝ) * (1 / dPlus * (1 / (C.m : ℝ)) ^ 2 / 2) =
      1 / (2 * (C.m : ℝ) * dPlus) := by field_simp
  have hmul2 : (C.m : ℝ) * (1 / (C.m : ℝ) * Real.log ‖(a0 : ℂ) - C.contour a‖) =
      Real.log ‖(a0 : ℂ) - C.contour a‖ := by field_simp
  have := mul_le_mul_of_nonneg_left h1 hmR.le
  rw [mul_sub, mul_neg, hmul, hmul2] at this
  change -((C.m : ℝ) * I) ≤ _
  linarith

/-- Integrability of the pinned-contour kernel on `κ × ν`. -/
theorem integrable_pinned_contour (C : FiniteConfiguration) :
    Integrable (fun q : ℝ × ℂ => li2LogKernel (q.1 : ℂ) q.2) ((wκ C).prod (wν C)) := by
  have hδ := configTubeRadius_le C
  have hmeas : Measurable (fun q : ℝ × ℂ => li2LogKernel (q.1 : ℂ) q.2) :=
    measurable_li2LogKernel.comp
      ((Complex.measurable_ofReal.comp measurable_fst).prodMk measurable_snd)
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.log 5 - Real.log (1 / 8)) ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := wκ C) (ν := wν C)).ae
      (pinnedMeasure_ae_mem C),
    (Measure.quasiMeasurePreserving_snd (μ := wκ C) (ν := wν C)).ae
      (configContourMeasure_ae_tube C)] with q h1 h2
  rw [Real.norm_eq_abs]
  have hlo : (1 / 8 : ℝ) ≤ ‖q.2 - (q.1 : ℂ)‖ :=
    tube_pinned_clearance hδ h2 ⟨by linarith [h1.1], by linarith [h1.2]⟩
  have hwn := tube_norm_le hδ h2
  have hhi : ‖q.2 - (q.1 : ℂ)‖ ≤ 5 := by
    have := norm_sub_le q.2 (q.1 : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [h1.1])] at this
    linarith [h1.2]
  have hb := abs_log_le_of_bounds (by norm_num) (by norm_num) (by norm_num) hlo hhi
  unfold li2LogKernel
  rw [abs_neg, norm_sub_rev]
  exact hb

theorem eIkν_eq (C : FiniteConfiguration) :
    eIkν C = -∑ s ∈ C.pinned, ∫ x in pinnedCell C.m s,
      (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
        Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖) := by
  have hr := configTubeRadius_pos C
  have hmap : (Measure.map Complex.ofReal (wκ C)).prod (wν C) =
      Measure.map (Prod.map Complex.ofReal id) ((wκ C).prod (wν C)) := by
    have := Measure.map_prod_map (wκ C) (wν C) Complex.measurable_ofReal measurable_id
    rw [Measure.map_id] at this
    exact this
  unfold eIkν
  rw [hmap, integral_map (Complex.measurable_ofReal.prodMap measurable_id).aemeasurable
    measurable_li2LogKernel.aestronglyMeasurable]
  simp only [Prod.map_fst, Prod.map_snd, id]
  rw [integral_prod _ (integrable_pinned_contour C)]
  have hinner : ∀ x : ℝ, (∫ w, li2LogKernel (x : ℂ) w ∂(wν C)) =
      -((C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
        Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)) := by
    intro x
    unfold li2LogKernel
    rw [integral_neg, wν_eq, integral_log_norm_sub_circleEmpirical C.contour hr C.m]
  simp_rw [hinner]
  rw [integral_neg]
  congr 1
  have hg : Continuous (fun x : ℝ => (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
      Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro a _
    apply Continuous.log (by fun_prop)
    intro x
    exact (lt_of_lt_of_le hr (le_max_left _ _)).ne'
  change ∫ x, _ ∂(∑ s ∈ C.pinned, volume.restrict (pinnedCell C.m s)) = _
  rw [integral_finsetSum_measure]
  intro s _
  exact (hg.integrableOn_Icc (a := (s : ℝ) / C.m) (b := ((s + 1 : ℕ) : ℝ) / C.m)).mono_set
    Set.Ico_subset_Icc_self

theorem kNuPiece : KNuPiece := by
  intro C
  have hmR : (0 : ℝ) < C.m := by
    have := C.m_ge_eight; exact_mod_cast (show 0 < C.m by omega)
  have hdP : (0 : ℝ) < dPlus := by norm_num [dPlus]
  have hr := configTubeRadius_pos C
  rw [eIkν_eq]
  set I : ℕ → Fin C.contourCount → ℝ := fun s a => ∫ x in pinnedCell C.m s,
    Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)
  have hsplit : ∀ s, (∫ x in pinnedCell C.m s, (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
      Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)) =
      (C.m : ℝ)⁻¹ * ∑ a, I s a := by
    intro s
    rw [integral_const_mul, integral_finsetSum]
    intro a _
    have hc : Continuous (fun x : ℝ =>
        Real.log (max (configTubeRadius C) ‖(x : ℂ) - C.contour a‖)) := by
      apply Continuous.log (by fun_prop)
      intro x
      exact (lt_of_lt_of_le hr (le_max_left _ _)).ne'
    exact (hc.integrableOn_Icc (a := (s : ℝ) / C.m)
      (b := ((s + 1 : ℕ) : ℝ) / C.m)).mono_set Set.Ico_subset_Icc_self
  simp_rw [hsplit]
  set c : ℝ := 1 / (2 * (C.m : ℝ) * dPlus)
  have hrw : (C.m : ℝ) ^ 2 * -∑ s ∈ C.pinned, (C.m : ℝ)⁻¹ * ∑ a, I s a =
      ∑ s ∈ C.pinned, ∑ a, -((C.m : ℝ) * I s a) := by
    rw [mul_neg, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro s _
    rw [← mul_assoc, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  rw [hrw]
  have hle : ∑ s ∈ C.pinned, ∑ a, -((C.m : ℝ) * I s a) ≤
      ∑ s ∈ C.pinned, ∑ a : Fin C.contourCount,
        (-Real.log ‖(((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖ + c) := by
    apply Finset.sum_le_sum
    intro s hs
    apply Finset.sum_le_sum
    intro a _
    exact pinned_contour_pair C hs a
  have hval : (∑ s ∈ C.pinned, ∑ a : Fin C.contourCount,
        (-Real.log ‖(((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖ + c)) =
      -pinCont C + (C.pinned.card : ℝ) * (C.contourCount : ℝ) * c := by
    unfold pinCont
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    ring
  have hbal : (C.contourCount : ℝ) + C.pinned.card = C.m := by
    exact_mod_cast C.mass_balance
  have hk0 : (0 : ℝ) ≤ C.pinned.card := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ C.contourCount := Nat.cast_nonneg _
  have hkd : (C.pinned.card : ℝ) * (C.contourCount : ℝ) ≤ (C.m : ℝ) * C.m := by
    apply mul_le_mul <;> linarith
  have hc0 : 0 ≤ c := by positivity
  have hfin : (C.pinned.card : ℝ) * (C.contourCount : ℝ) * c ≤ (C.m : ℝ) / (2 * dPlus) := by
    calc (C.pinned.card : ℝ) * (C.contourCount : ℝ) * c ≤ (C.m : ℝ) * C.m * c :=
          mul_le_mul_of_nonneg_right hkd hc0
      _ = (C.m : ℝ) / (2 * dPlus) := by simp only [c]; field_simp
  linarith

/-! ## Contour-frequency interaction -/

theorem contour_frequency_pair (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency)
    (a : Fin C.contourCount) :
    -((C.m : ℝ) * ∫ t in frequencyCell C.m r,
        Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖)) ≤
      -Real.log ‖C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ +
        1 / (2 * (C.m : ℝ) * dMinus) := by
  have hmR : (0 : ℝ) < C.m := by
    have := C.m_ge_eight; exact_mod_cast (show 0 < C.m by omega)
  have hdM : (0 : ℝ) < dMinus := by norm_num [dMinus]
  have hrd := configTubeRadius_le_dMinus C
  obtain ⟨hlo, hba⟩ := frequency_cell_bounds C hr
  set a0 : ℝ := ((r - 1 : ℕ) : ℝ) / (C.m : ℝ)
  set b0 : ℝ := (r : ℝ) / (C.m : ℝ)
  have hab : a0 ≤ b0 := by linarith [show 0 < 1 / (C.m : ℝ) by positivity]
  have hnorm : ∀ t : ℝ, ‖-(t : ℂ) - C.contour a‖ = ‖C.contour a + (t : ℂ)‖ := by
    intro t
    rw [show -(t : ℂ) - C.contour a = -(C.contour a + (t : ℂ)) by ring, norm_neg]
  have hcl : ∀ t ∈ Set.Icc a0 b0, dMinus ≤ ‖C.contour a + (t : ℂ)‖ := by
    intro t ht
    exact mixedCellClearance_full.2 _ (contour_mem_base C a) t (by linarith [ht.1])
  set f : ℝ → ℝ := fun t => Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖)
  have hfeq : ∀ t ∈ Set.Icc a0 b0, f t = Real.log ‖C.contour a + (t : ℂ)‖ := by
    intro t ht
    simp only [f]
    rw [hnorm, max_eq_right (hrd.trans (hcl t ht))]
  have hcont : Continuous f := by
    apply Continuous.log (by fun_prop)
    intro x
    exact (lt_of_lt_of_le (configTubeRadius_pos C) (le_max_left _ _)).ne'
  have hb0 : b0 ∈ Set.Icc a0 b0 := ⟨hab, le_rfl⟩
  have hL : ∀ t ∈ Set.Icc a0 b0, |f t - f b0| ≤ (1 / dMinus) * (b0 - t) := by
    intro t ht
    rw [hfeq t ht, hfeq b0 hb0]
    calc |Real.log ‖C.contour a + (t : ℂ)‖ - Real.log ‖C.contour a + (b0 : ℂ)‖|
        ≤ |‖C.contour a + (t : ℂ)‖ - ‖C.contour a + (b0 : ℂ)‖| / dMinus :=
          abs_log_sub_log_le hdM (hcl t ht) (hcl b0 hb0)
      _ ≤ ‖(C.contour a + (t : ℂ)) - (C.contour a + (b0 : ℂ))‖ / dMinus :=
          div_le_div_of_nonneg_right (abs_norm_sub_norm_le _ _) hdM.le
      _ = (1 / dMinus) * (b0 - t) := by
          rw [show (C.contour a + (t : ℂ)) - (C.contour a + (b0 : ℂ)) =
            ((t - b0 : ℝ) : ℂ) by push_cast; ring, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonpos (by linarith [ht.2])]
          ring
  have hcell := cell_right_endpoint hab hcont.continuousOn hL
  rw [hba] at hcell
  rw [hfeq b0 hb0] at hcell
  have hcellset : frequencyCell C.m r = Set.Ico a0 b0 := rfl
  rw [hcellset]
  set I := ∫ x in Set.Ico a0 b0, f x
  have h1 := (abs_le.mp hcell).1
  have hmul : (C.m : ℝ) * (1 / dMinus * (1 / (C.m : ℝ)) ^ 2 / 2) =
      1 / (2 * (C.m : ℝ) * dMinus) := by field_simp
  have hmul2 : (C.m : ℝ) * (1 / (C.m : ℝ) * Real.log ‖C.contour a + (b0 : ℂ)‖) =
      Real.log ‖C.contour a + (b0 : ℂ)‖ := by field_simp
  have := mul_le_mul_of_nonneg_left h1 hmR.le
  rw [mul_sub, mul_neg, hmul, hmul2] at this
  change -((C.m : ℝ) * I) ≤ _
  linarith

theorem integrable_frequency_contour (C : FiniteConfiguration)
    (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    Integrable (fun q : ℝ × ℂ => Real.log ‖q.2 + (q.1 : ℂ)‖) ((wμ C).prod (wν C)) := by
  have hδ := configTubeRadius_le C
  have hmeas : Measurable (fun q : ℝ × ℂ => Real.log ‖q.2 + (q.1 : ℂ)‖) := by fun_prop
  refine Integrable.of_bound hmeas.aestronglyMeasurable (Real.log 24 - Real.log (1 / 4)) ?_
  filter_upwards [(Measure.quasiMeasurePreserving_fst (μ := wμ C) (ν := wν C)).ae
      (frequencyMeasure_ae_mem C hhead),
    (Measure.quasiMeasurePreserving_snd (μ := wμ C) (ν := wν C)).ae
      (configContourMeasure_ae_tube C)] with q h1 h2
  rw [Real.norm_eq_abs]
  have hlo : (1 / 4 : ℝ) ≤ ‖q.2 + (q.1 : ℂ)‖ := tube_frequency_clearance hδ h2 h1.1
  have hwn := tube_norm_le hδ h2
  have hhi : ‖q.2 + (q.1 : ℂ)‖ ≤ 24 := by
    have := norm_add_le q.2 (q.1 : ℂ)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith [h1.1])] at this
    linarith [h1.2]
  exact abs_log_le_of_bounds (by norm_num) (by norm_num) (by norm_num) hlo hhi

theorem eMνμ_eq (C : FiniteConfiguration) (hhead : ∀ r ∈ C.frequency, r ≤ 20 * C.m) :
    eMνμ C = ∑ r ∈ C.frequency, ∫ t in frequencyCell C.m r,
      (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
        Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖) := by
  have hr := configTubeRadius_pos C
  unfold eMνμ
  rw [← integral_prod_swap]
  simp only [Prod.fst_swap, Prod.snd_swap]
  rw [integral_prod _ (integrable_frequency_contour C hhead)]
  have hinner : ∀ t : ℝ, (∫ w, Real.log ‖w + (t : ℂ)‖ ∂(wν C)) =
      (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
        Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖) := by
    intro t
    rw [← integral_log_norm_sub_circleEmpirical C.contour hr C.m (-(t : ℂ)), ← wν_eq]
    apply integral_congr_ae
    filter_upwards with w
    rw [show -(t : ℂ) - w = -(w + (t : ℂ)) by ring, norm_neg]
  simp_rw [hinner]
  have hg : Continuous (fun t : ℝ => (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
      Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖)) := by
    apply continuous_const.mul
    apply continuous_finsetSum
    intro a _
    apply Continuous.log (by fun_prop)
    intro x
    exact (lt_of_lt_of_le hr (le_max_left _ _)).ne'
  change ∫ x, _ ∂(∑ r ∈ C.frequency, volume.restrict (frequencyCell C.m r)) = _
  rw [integral_finsetSum_measure]
  intro r _
  exact (hg.integrableOn_Icc (a := ((r - 1 : ℕ) : ℝ) / C.m)
    (b := (r : ℝ) / C.m)).mono_set Set.Ico_subset_Icc_self

theorem nuMuPiece : NuMuPiece := by
  intro C hhead
  have hmR : (0 : ℝ) < C.m := by
    have := C.m_ge_eight; exact_mod_cast (show 0 < C.m by omega)
  have hdM : (0 : ℝ) < dMinus := by norm_num [dMinus]
  have hr := configTubeRadius_pos C
  rw [eMνμ_eq C hhead]
  set I : ℕ → Fin C.contourCount → ℝ := fun r a => ∫ t in frequencyCell C.m r,
    Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖)
  have hsplit : ∀ r, (∫ t in frequencyCell C.m r, (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
      Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖)) =
      (C.m : ℝ)⁻¹ * ∑ a, I r a := by
    intro r
    rw [integral_const_mul, integral_finsetSum]
    intro a _
    have hc : Continuous (fun t : ℝ =>
        Real.log (max (configTubeRadius C) ‖-(t : ℂ) - C.contour a‖)) := by
      apply Continuous.log (by fun_prop)
      intro x
      exact (lt_of_lt_of_le hr (le_max_left _ _)).ne'
    exact (hc.integrableOn_Icc (a := ((r - 1 : ℕ) : ℝ) / C.m)
      (b := (r : ℝ) / C.m)).mono_set Set.Ico_subset_Icc_self
  simp_rw [hsplit]
  set c : ℝ := 1 / (2 * (C.m : ℝ) * dMinus)
  have hrw : -((C.m : ℝ) ^ 2 * ∑ r ∈ C.frequency, (C.m : ℝ)⁻¹ * ∑ a, I r a) =
      ∑ a : Fin C.contourCount, ∑ r ∈ C.frequency, -((C.m : ℝ) * I r a) := by
    rw [Finset.sum_comm, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro r _
    rw [← mul_assoc, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro a _
    field_simp
  rw [hrw]
  have hle : ∑ a : Fin C.contourCount, ∑ r ∈ C.frequency, -((C.m : ℝ) * I r a) ≤
      ∑ a : Fin C.contourCount, ∑ r ∈ C.frequency,
        (-Real.log ‖C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ + c) := by
    apply Finset.sum_le_sum
    intro a _
    apply Finset.sum_le_sum
    intro r hr'
    exact contour_frequency_pair C hr' a
  have hval : (∑ a : Fin C.contourCount, ∑ r ∈ C.frequency,
        (-Real.log ‖C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ + c)) =
      -contFreq C + (C.contourCount : ℝ) * (C.m : ℝ) * c := by
    unfold contFreq
    simp only [Finset.sum_add_distrib, Finset.sum_neg_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, C.frequency_card]
    ring
  have hbal : (C.contourCount : ℝ) + C.pinned.card = C.m := by
    exact_mod_cast C.mass_balance
  have hk0 : (0 : ℝ) ≤ C.pinned.card := Nat.cast_nonneg _
  have hc0 : 0 ≤ c := by positivity
  have hfin : (C.contourCount : ℝ) * (C.m : ℝ) * c ≤ (C.m : ℝ) / (2 * dMinus) := by
    calc (C.contourCount : ℝ) * (C.m : ℝ) * c ≤ (C.m : ℝ) * C.m * c := by
          apply mul_le_mul_of_nonneg_right _ hc0
          apply mul_le_mul_of_nonneg_right _ hmR.le
          linarith
      _ = (C.m : ℝ) / (2 * dMinus) := by simp only [c]; field_simp
  linarith

/-! ## Contour field -/

theorem contFieldPiece : ContFieldPiece := by
  intro C
  have hmR : (0 : ℝ) < C.m := by
    have := C.m_ge_eight; exact_mod_cast (show 0 < C.m by omega)
  have hr := configTubeRadius_pos C
  have hr64 := configTubeRadius_le C
  have h : ∀ a : Fin C.contourCount,
      Integrable (fun w => p0CompanionField w) (circleProbability (C.contour a)
        (configTubeRadius C)) ∧
      ∫ w, p0CompanionField w ∂(circleProbability (C.contour a) (configTubeRadius C)) ≤
        p0CompanionField (C.contour a) :=
    fun a => integral_companion_circleProbability_le (contour_mem_Gamma C a) hr hr64
  have hP : ePν C = (C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
      ∫ w, p0CompanionField w ∂(circleProbability (C.contour a) (configTubeRadius C)) := by
    unfold ePν
    rw [wν_eq]
    unfold circleEmpiricalMeasure
    rw [integral_smul_measure, ENNReal.toReal_ofReal (inv_nonneg.mpr (Nat.cast_nonneg _)),
      Measure.sum_fintype, integral_finsetSum_measure (fun a _ => (h a).1), smul_eq_mul]
  rw [hP]
  calc (C.m : ℝ) ^ 2 * ((C.m : ℝ)⁻¹ * ∑ a : Fin C.contourCount,
        ∫ w, p0CompanionField w ∂(circleProbability (C.contour a) (configTubeRadius C))) =
      (C.m : ℝ) * ∑ a : Fin C.contourCount,
        ∫ w, p0CompanionField w ∂(circleProbability (C.contour a) (configTubeRadius C)) := by
        field_simp
    _ ≤ (C.m : ℝ) * ∑ a : Fin C.contourCount, p0CompanionField (C.contour a) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum (fun a _ => (h a).2)) hmR.le

#print axioms contFieldPiece
#print axioms kNuPiece
#print axioms nuNuPiece
#print axioms nuMuPiece

end

end Li2Lean.P0.CellBound
