/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Defs
import Li2Lean.P0.ConfigQuadrature
import Li2Lean.P0.ConfigPinnedVariation

/-!
# Cell inequality: the real-cell pieces

Paper v13 `p0-analytic.tex` ll. 285-356 and 376-383.  Five pieces of the
witness energy are compared with their discrete counterparts using only real
cells:

* `kkPiece`, `muMuPiece`: the self-cell inequality `eq:config-self` on the
  pinned sites and on the shifted frequency sites `R - 1`;
* `freqFieldPiece`: `B_0` is increasing, so each right-endpoint value
  dominates its cell average, and `eq:config-psi`;
* `pinFieldPiece`: on each pinned cell the field `A_0 - φ` exceeds its
  left-endpoint value by at most the cell variation, and the variations sum
  to at most `log 168`;
* `kMuPiece`: on each pinned-frequency cell pair `x + t ≥ 3/4` and
  `|x + t - (x_s + t_r)| ≤ 1/m`, so the loss is at most `4/(3m)` per pair.
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

/-! ## Elementary cell facts -/

theorem cfg_m_pos (C : FiniteConfiguration) : 0 < C.m := by
  have := C.m_ge_eight; omega

theorem real_pinned_cell_bounds (C : FiniteConfiguration) {s : ℕ} (hs : s ∈ C.pinned) :
    (1 / 4 : ℝ) ≤ (s : ℝ) / (C.m : ℝ) ∧ ((s + 1 : ℕ) : ℝ) / (C.m : ℝ) ≤ 5 / 4 := by
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hiS := C.pinned_subset hs
  simp only [pinnedUniverse, Finset.mem_Ico] at hiS
  have hk4 : C.m / 4 = k := by omega
  have hk5 : 5 * C.m / 4 = 5 * k := by omega
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  have hlo' : (k : ℝ) ≤ s := by exact_mod_cast (hk4 ▸ hiS.1)
  have hhi' : ((s + 1 : ℕ) : ℝ) ≤ 5 * k := by exact_mod_cast (hk5 ▸ hiS.2)
  constructor
  · rw [le_div_iff₀ hmR, hmk]; linarith
  · rw [div_le_iff₀ hmR, hmk]; linarith

theorem freq_cell_lower (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency) :
    (1 / 2 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) := by
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  have h1 := C.frequency_lower r hr
  have hr' : (2 * k : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
    have : 2 * k ≤ r - 1 := by omega
    exact_mod_cast this
  rw [le_div_iff₀ hmR, hmk]; linarith

theorem freq_cell_width (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency) :
    (r : ℝ) / (C.m : ℝ) = ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) + 1 / (C.m : ℝ) := by
  have h1 := C.frequency_lower r hr
  rw [Nat.cast_sub (by omega)]
  push_cast
  ring

theorem volume_frequencyCell (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency) :
    volume (frequencyCell C.m r) = ENNReal.ofReal ((C.m : ℝ)⁻¹) := by
  have h1 := C.frequency_lower r hr
  have h := volume_cell (cfg_m_pos C) (r - 1)
  unfold frequencyCell
  rwa [show r - 1 + 1 = r by omega] at h

theorem volume_pinnedCell (C : FiniteConfiguration) (s : ℕ) :
    volume (pinnedCell C.m s) = ENNReal.ofReal ((C.m : ℝ)⁻¹) :=
  volume_cell (cfg_m_pos C) s

theorem real_pinnedCell (C : FiniteConfiguration) (s : ℕ) :
    volume.real (pinnedCell C.m s) = (C.m : ℝ)⁻¹ := by
  rw [Measure.real, volume_pinnedCell, ENNReal.toReal_ofReal (by positivity)]

theorem real_frequencyCell (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency) :
    volume.real (frequencyCell C.m r) = (C.m : ℝ)⁻¹ := by
  rw [Measure.real, volume_frequencyCell C hr, ENNReal.toReal_ofReal (by positivity)]

/-! ## Pinned self-energy -/

theorem kkPiece : KKPiece := by
  intro C
  have h := selfCellBound C.m (cfg_m_pos C) C.pinned
  have heq : latticeCellMeasure C.m C.pinned = pinnedMeasure C.m C.pinned := rfl
  rw [heq] at h
  unfold eIkk pinPin
  linarith

/-! ## Frequency self-energy -/

theorem freq_pred_injOn (C : FiniteConfiguration) :
    Set.InjOn (fun r : ℕ => r - 1) (C.frequency : Set ℕ) := by
  intro r hr q hq h
  have := C.frequency_lower r hr
  have := C.frequency_lower q hq
  simp only at h
  omega

theorem latticeCellMeasure_freq (C : FiniteConfiguration) :
    latticeCellMeasure C.m (C.frequency.image (fun r => r - 1)) =
      frequencyMeasure C.m C.frequency := by
  unfold latticeCellMeasure frequencyMeasure
  rw [Finset.sum_image (fun r hr q hq h => freq_pred_injOn C hr hq h)]
  apply Finset.sum_congr rfl
  intro r hr
  have := C.frequency_lower r hr
  unfold pinnedCell frequencyCell
  rw [show r - 1 + 1 = r by omega]

theorem offDiag_freq (C : FiniteConfiguration) :
    latticeOffDiagonalLogSum C.m (C.frequency.image (fun r => r - 1)) = freqFreq C := by
  unfold freqFreq latticeOffDiagonalLogSum
  rw [Finset.sum_image (fun r hr q hq h => freq_pred_injOn C hr hq h)]
  apply Finset.sum_congr rfl
  intro r hr
  rw [Finset.sum_image (fun r hr q hq h => freq_pred_injOn C hr hq h)]
  apply Finset.sum_congr rfl
  intro q hq
  have h1 := C.frequency_lower r hr
  have h2 := C.frequency_lower q hq
  by_cases h : r = q
  · subst h; simp
  · have h' : r - 1 ≠ q - 1 := by omega
    rw [if_neg h', if_neg h]
    rw [Nat.cast_sub (by omega : 1 ≤ r), Nat.cast_sub (by omega : 1 ≤ q)]
    congr 2
    ring

theorem muMuPiece : MuMuPiece := by
  intro C
  have h := selfCellBound C.m (cfg_m_pos C) (C.frequency.image (fun r => r - 1))
  rw [latticeCellMeasure_freq, offDiag_freq,
    Finset.card_image_of_injOn (freq_pred_injOn C), C.frequency_card] at h
  unfold eLLμ
  linarith

/-! ## Frequency field -/

theorem B0_mono {t t' : ℝ} (ht : (1 / 2 : ℝ) ≤ t) (htt : t ≤ t') :
    P0.B0 t ≤ P0.B0 t' := by
  have key : ∀ a b : ℝ, 0 ≤ a → a ≤ b →
      (∫ x in a..b, Real.log (t + x)) ≤ ∫ x in a..b, Real.log (t' + x) := by
    intro a b ha hab
    have hcont : ∀ u : ℝ, (1 / 2 : ℝ) ≤ u →
        IntervalIntegrable (fun x => Real.log (u + x)) volume a b := by
      intro u hu
      apply ContinuousOn.intervalIntegrable
      apply ContinuousOn.log (by fun_prop)
      intro x hx
      rw [Set.uIcc_of_le hab] at hx
      have := hx.1
      intro h0
      linarith
    apply intervalIntegral.integral_mono_on hab (hcont t ht) (hcont t' (ht.trans htt))
    intro x hx
    exact Real.log_le_log (by linarith [hx.1]) (by linarith)
  unfold P0.B0
  exact add_le_add (key _ _ (by norm_num) (by norm_num)) (key _ _ le_rfl (by norm_num))

theorem integral_B0_cell_le (C : FiniteConfiguration) {r : ℕ} (hr : r ∈ C.frequency) :
    (∫ t in frequencyCell C.m r, P0.B0 t) ≤
      (C.m : ℝ)⁻¹ * P0.B0 ((r : ℝ) / (C.m : ℝ)) := by
  have hlo := freq_cell_lower C hr
  have hw := freq_cell_width C hr
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  have hcontB : Continuous P0.B0 := ReferencePackaging.continuous_B0_literal
  have hInt : IntegrableOn P0.B0 (frequencyCell C.m r) volume := by
    unfold frequencyCell
    exact (hcontB.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hle : (∫ t in frequencyCell C.m r, P0.B0 t) ≤
      ∫ _t in frequencyCell C.m r, P0.B0 ((r : ℝ) / (C.m : ℝ)) := by
    apply setIntegral_mono_on hInt
    · unfold frequencyCell
      exact integrableOn_const (by
        rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
    · exact measurableSet_Ico
    · intro t ht
      unfold frequencyCell at ht
      apply B0_mono (by linarith [ht.1])
      exact ht.2.le
  rw [setIntegral_const, real_frequencyCell C hr, smul_eq_mul] at hle
  exact hle

theorem integral_B0_freq_le (C : FiniteConfiguration) :
    (C.m : ℝ) ^ 2 * eBμ C ≤
      (C.m : ℝ) * ∑ r ∈ C.frequency, P0.B0 ((r : ℝ) / (C.m : ℝ)) := by
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  have hcontB : Continuous P0.B0 := ReferencePackaging.continuous_B0_literal
  have hsplit : eBμ C = ∑ r ∈ C.frequency, ∫ t in frequencyCell C.m r, P0.B0 t := by
    unfold eBμ wμ frequencyMeasure
    rw [integral_finsetSum_measure]
    intro r _
    unfold frequencyCell
    exact (hcontB.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hsum : eBμ C ≤ ∑ r ∈ C.frequency, (C.m : ℝ)⁻¹ * P0.B0 ((r : ℝ) / (C.m : ℝ)) := by
    rw [hsplit]
    exact Finset.sum_le_sum (fun r hr => integral_B0_cell_le C hr)
  rw [← Finset.mul_sum] at hsum
  have h2 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (C.m : ℝ))
  calc (C.m : ℝ) ^ 2 * eBμ C ≤ (C.m : ℝ) ^ 2 * ((C.m : ℝ)⁻¹ *
        ∑ r ∈ C.frequency, P0.B0 ((r : ℝ) / (C.m : ℝ))) := h2
    _ = _ := by field_simp

theorem freqFieldPiece : FreqFieldPiece := by
  intro C _
  have hB := integral_B0_freq_le C
  have hpsi : PsiQuadratureBound C := psiQuadratureBound C
  unfold PsiQuadratureBound FiniteConfiguration.mu at hpsi
  have hΨ : eΨμ C = ∫ t, Config.psi t ∂(frequencyMeasure C.m C.frequency) := rfl
  have hs : (∑ r ∈ C.frequency,
        (P0.B0 ((r : ℝ) / (C.m : ℝ)) - P0.psi ((r : ℝ) / (C.m : ℝ)))) =
      (∑ r ∈ C.frequency, P0.B0 ((r : ℝ) / (C.m : ℝ))) -
        ∑ r ∈ C.frequency, Config.psi ((r : ℝ) / (C.m : ℝ)) := by
    rw [Finset.sum_sub_distrib]; rfl
  rw [hs, hΨ]
  linarith [hB, hpsi]

/-! ## Pinned field -/

theorem companion_real_eq (x : ℝ) :
    p0CompanionField (x : ℂ) = -pinnedGapClosed x := by
  rw [← pinnedFieldGap_eq]
  show P0.A0 (x : ℂ) - P0.phi (x : ℂ) = -(Config.phi (x : ℂ) - Config.A0 (x : ℂ))
  have h1 : P0.A0 = Config.A0 := rfl
  have h2 : P0.phi = Config.phi := rfl
  rw [h1, h2]
  ring

/-- On a subinterval of `E`, the closed gap lies above its left value minus
the variation. -/
theorem gap_left_le {a b x : ℝ} (ha : 1 / 4 ≤ a) (hb : b ≤ 5 / 4) (hax : a ≤ x)
    (hxb : x ≤ b) :
    pinnedGapClosed a - pinnedGapClosed x ≤ ∫ y in a..b, |pinnedGapDeriv y| := by
  have hftc : (∫ y in a..x, pinnedGapDeriv y) = pinnedGapClosed x - pinnedGapClosed a := by
    apply intervalIntegral.integral_eq_sub_of_hasDerivAt_of_le hax
      pinnedGapClosed_continuous.continuousOn
    · intro y hy
      exact pinnedGapClosed_hasDerivAt (by linarith [hy.1]) (by linarith [hy.1])
        (by linarith [hy.1]) (by linarith [hy.2]) (by linarith [hy.2])
    · exact pinnedGapDeriv_integrable a x
  have habs := intervalIntegral.abs_integral_le_integral_abs (f := pinnedGapDeriv)
    (μ := volume) hax
  have hmono : (∫ y in a..x, |pinnedGapDeriv y|) ≤ ∫ y in a..b, |pinnedGapDeriv y| :=
    intervalIntegral.integral_mono_interval le_rfl hax hxb
      (Filter.Eventually.of_forall (fun y => abs_nonneg _))
      (pinnedGapDeriv_integrable a b).abs
  rw [hftc] at habs
  have := neg_abs_le (pinnedGapClosed x - pinnedGapClosed a)
  linarith

theorem integrableOn_absDerivGap :
    IntegrableOn (fun x => |deriv pinnedFieldGap x|) p0SupportE volume := by
  unfold p0SupportE
  rw [integrableOn_Icc_iff_integrableOn_Ioo]
  have h := ((intervalIntegrable_iff_integrableOn_Ioo_of_le (by norm_num)).1
    ((pinnedGapDeriv_integrable (1 / 4) (5 / 4)).abs))
  refine h.congr_fun ?_ measurableSet_Ioo
  intro x hx
  show |pinnedGapDeriv x| = |deriv pinnedFieldGap x|
  rw [deriv_pinnedFieldGap hx]

theorem cell_variation_eq (C : FiniteConfiguration) {s : ℕ} (hs : s ∈ C.pinned) :
    (∫ y in (s : ℝ) / (C.m : ℝ)..((s + 1 : ℕ) : ℝ) / (C.m : ℝ), |pinnedGapDeriv y|) =
      ∫ y in pinnedCell C.m s, |deriv pinnedFieldGap y| := by
  obtain ⟨hlo, hhi⟩ := real_pinned_cell_bounds C hs
  have hab := SelfCells.pinnedCell_endpoints_le C.m s
  rw [intervalIntegral.integral_of_le hab, integral_Ioc_eq_integral_Ioo, pinnedCell,
    integral_Ico_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro y hy
  show |pinnedGapDeriv y| = |deriv pinnedFieldGap y|
  rw [deriv_pinnedFieldGap ⟨by linarith [hy.1], by linarith [hy.2]⟩]

theorem pinned_variation_sum_le (C : FiniteConfiguration) :
    (∑ s ∈ C.pinned, ∫ y in pinnedCell C.m s, |deriv pinnedFieldGap y|) ≤
      Real.log 168 := by
  have hI := integrableOn_absDerivGap
  have hsum : (∑ s ∈ C.pinned, ∫ y in pinnedCell C.m s, |deriv pinnedFieldGap y|) =
      ∫ y, |deriv pinnedFieldGap y| ∂(pinnedMeasure C.m C.pinned) := by
    unfold pinnedMeasure
    rw [integral_finsetSum_measure]
    intro s hs
    apply hI.mono_set
    obtain ⟨hlo, hhi⟩ := real_pinned_cell_bounds C hs
    intro y hy
    unfold pinnedCell at hy
    exact ⟨by linarith [hy.1], by linarith [hy.2]⟩
  rw [hsum]
  have hle := integral_mono_measure (pinnedMeasure_le C)
    (Filter.Eventually.of_forall (fun y => abs_nonneg (deriv pinnedFieldGap y))) hI
  have hv := pinnedFieldVariationBound
  unfold PinnedFieldVariationBound p0SupportE at hv
  exact hle.trans hv

theorem pinFieldPiece : PinFieldPiece := by
  intro C
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  have hcont : Continuous (fun x : ℝ => -pinnedGapClosed x) :=
    pinnedGapClosed_continuous.neg
  set V : ℕ → ℝ := fun s => ∫ y in pinnedCell C.m s, |deriv pinnedFieldGap y| with hV
  have hcell : ∀ s ∈ C.pinned,
      (∫ x in pinnedCell C.m s, p0CompanionField (x : ℂ)) ≤
        (C.m : ℝ)⁻¹ * (p0CompanionField (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ) + V s) := by
    intro s hs
    obtain ⟨hlo, hhi⟩ := real_pinned_cell_bounds C hs
    have hab := SelfCells.pinnedCell_endpoints_le C.m s
    simp_rw [companion_real_eq]
    have hle : (∫ x in pinnedCell C.m s, -pinnedGapClosed x) ≤
        ∫ _x in pinnedCell C.m s,
          (-pinnedGapClosed ((s : ℝ) / (C.m : ℝ)) + V s) := by
      apply setIntegral_mono_on
      · unfold pinnedCell
        exact (hcont.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
      · unfold pinnedCell
        exact integrableOn_const (by rw [Real.volume_Ico]; exact ENNReal.ofReal_ne_top)
      · exact measurableSet_Ico
      · intro x hx
        unfold pinnedCell at hx
        have := gap_left_le hlo hhi hx.1 hx.2.le
        rw [cell_variation_eq C hs] at this
        simp only [hV]
        linarith
    rw [setIntegral_const, real_pinnedCell, smul_eq_mul] at hle
    exact hle
  have hsplit : ePk C = ∑ s ∈ C.pinned, ∫ x in pinnedCell C.m s, p0CompanionField (x : ℂ) := by
    unfold ePk wκ pinnedMeasure
    rw [integral_finsetSum_measure]
    intro s _
    have : (fun x : ℝ => p0CompanionField (x : ℂ)) = fun x => -pinnedGapClosed x := by
      funext x; exact companion_real_eq x
    rw [this]
    unfold pinnedCell
    exact (hcont.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self
  have hsum := Finset.sum_le_sum hcell
  rw [← hsplit, ← Finset.mul_sum, Finset.sum_add_distrib] at hsum
  have hvar : (∑ s ∈ C.pinned, V s) ≤ Real.log 168 := pinned_variation_sum_le C
  have h2 := mul_le_mul_of_nonneg_left hsum (sq_nonneg (C.m : ℝ))
  have he : (C.m : ℝ) ^ 2 * ((C.m : ℝ)⁻¹ *
      ((∑ s ∈ C.pinned, p0CompanionField (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) +
        ∑ s ∈ C.pinned, V s)) =
      (C.m : ℝ) * (∑ s ∈ C.pinned, p0CompanionField (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) +
        (C.m : ℝ) * ∑ s ∈ C.pinned, V s := by
    field_simp
  rw [he] at h2
  have h3 := mul_le_mul_of_nonneg_left hvar hmR.le
  linarith

/-! ## Pinned-frequency interaction -/

theorem sFinite_finset_sum {ι : Type*} (S : Finset ι) (A : ι → Set ℝ) :
    SFinite (∑ i ∈ S, volume.restrict (A i)) := by
  rw [← Measure.sum_coe_finset]
  infer_instance

theorem prod_finset_sum_restrict {ι κ : Type*} (S : Finset ι) (R : Finset κ)
    (A : ι → Set ℝ) (B : κ → Set ℝ) :
    (∑ i ∈ S, volume.restrict (A i)).prod (∑ j ∈ R, volume.restrict (B j)) =
      ∑ i ∈ S, ∑ j ∈ R, (volume.restrict (A i)).prod (volume.restrict (B j)) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert i S hi ih =>
    have := sFinite_finset_sum S A
    have := sFinite_finset_sum R B
    rw [Finset.sum_insert hi, Finset.sum_insert hi, Measure.add_prod, ih]
    congr 1
    clear ih
    induction R using Finset.induction_on with
    | empty => simp
    | insert j R hj ih =>
      have := sFinite_finset_sum R B
      rw [Finset.sum_insert hj, Finset.sum_insert hj, Measure.prod_add, ih this]

theorem log_pair_lower {x t c : ℝ} {m : ℝ} (hm : 0 < m) (hy : 3 / 4 ≤ x + t)
    (hc : c - (x + t) ≤ 1 / m) (hc0 : 0 < c) :
    Real.log c - 4 / (3 * m) ≤ Real.log (x + t) := by
  have hy0 : 0 < x + t := by linarith
  have h := Real.log_le_sub_one_of_pos (div_pos hc0 hy0)
  rw [Real.log_div hc0.ne' hy0.ne'] at h
  have hq : c / (x + t) - 1 ≤ 4 / (3 * m) := by
    rw [div_sub_one hy0.ne', div_le_div_iff₀ hy0 (by positivity)]
    have : (c - (x + t)) * m ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hc hm.le
      rwa [div_mul_cancel₀ _ hm.ne'] at this
    nlinarith
  linarith

theorem pair_integral_lower (C : FiniteConfiguration) {s r : ℕ} (hs : s ∈ C.pinned)
    (hr : r ∈ C.frequency) :
    Integrable (fun p : ℝ × ℝ => Real.log (p.1 + p.2))
        ((volume.restrict (pinnedCell C.m s)).prod (volume.restrict (frequencyCell C.m r))) ∧
      (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ *
          (Real.log ((s : ℝ) / (C.m : ℝ) + (r : ℝ) / (C.m : ℝ)) - 4 / (3 * (C.m : ℝ))) ≤
        ∫ p : ℝ × ℝ, Real.log (p.1 + p.2)
          ∂((volume.restrict (pinnedCell C.m s)).prod (volume.restrict (frequencyCell C.m r))) := by
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  obtain ⟨hlo, hhi⟩ := real_pinned_cell_bounds C hs
  have hflo := freq_cell_lower C hr
  have hw := freq_cell_width C hr
  have hs1 : ((s + 1 : ℕ) : ℝ) / (C.m : ℝ) = (s : ℝ) / (C.m : ℝ) + 1 / (C.m : ℝ) := by
    push_cast; ring
  set ρ := (volume.restrict (pinnedCell C.m s)).prod (volume.restrict (frequencyCell C.m r))
    with hρ
  have hρ' : ρ = (volume.prod volume).restrict (pinnedCell C.m s ×ˢ frequencyCell C.m r) := by
    rw [hρ, Measure.prod_restrict]
  have hmeasS : MeasurableSet (pinnedCell C.m s ×ˢ frequencyCell C.m r) :=
    measurableSet_Ico.prod measurableSet_Ico
  have hae : ∀ᵐ p ∂ρ, p ∈ pinnedCell C.m s ×ˢ frequencyCell C.m r := by
    rw [hρ']; exact ae_restrict_mem hmeasS
  have : IsFiniteMeasure (volume.restrict (pinnedCell C.m s)) := by
    unfold pinnedCell; infer_instance
  have : IsFiniteMeasure (volume.restrict (frequencyCell C.m r)) := by
    unfold frequencyCell; infer_instance
  have hfin : IsFiniteMeasure ρ := by rw [hρ]; infer_instance
  set c : ℝ := (s : ℝ) / (C.m : ℝ) + (r : ℝ) / (C.m : ℝ) with hcdef
  set Y : ℝ := 5 / 4 + (r : ℝ) / (C.m : ℝ) with hY
  have hr0 : 0 ≤ (r : ℝ) / (C.m : ℝ) := by positivity
  have hpt : ∀ p ∈ pinnedCell C.m s ×ˢ frequencyCell C.m r,
      3 / 4 ≤ p.1 + p.2 ∧ p.1 + p.2 ≤ Y ∧ c - (p.1 + p.2) ≤ 1 / (C.m : ℝ) := by
    intro p hp
    obtain ⟨h1, h2⟩ := hp
    unfold pinnedCell at h1
    unfold frequencyCell at h2
    rw [hs1] at h1
    refine ⟨by linarith [h1.1, h2.1], by linarith [h1.2, h2.2], ?_⟩
    rw [hcdef]
    linarith [h1.1, h2.1]
  have hint : Integrable (fun p : ℝ × ℝ => Real.log (p.1 + p.2)) ρ := by
    refine Integrable.of_bound
      (Real.measurable_log.comp (measurable_fst.add measurable_snd)).aestronglyMeasurable
      (Real.log Y - Real.log (3 / 4)) ?_
    filter_upwards [hae] with p hp
    obtain ⟨h1, h2, _⟩ := hpt p hp
    rw [Real.norm_eq_abs]
    exact abs_log_le_of_bounds (by norm_num) (by norm_num) (by linarith) h1 h2
  refine ⟨hint, ?_⟩
  have hc0 : 0 < c := by rw [hcdef]; have := hw; linarith
  have hmono := integral_mono_ae (integrable_const
      (Real.log c - 4 / (3 * (C.m : ℝ)))) hint (by
    filter_upwards [hae] with p hp
    obtain ⟨h1, _, h3⟩ := hpt p hp
    exact log_pair_lower hmR h1 h3 hc0)
  rw [integral_const, smul_eq_mul] at hmono
  have hmass : ρ.real Set.univ = (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ := by
    rw [Measure.real, hρ, ← Set.univ_prod_univ, Measure.prod_prod,
      Measure.restrict_apply_univ, Measure.restrict_apply_univ, volume_pinnedCell,
      volume_frequencyCell C hr, ← ENNReal.ofReal_mul (by positivity),
      ENNReal.toReal_ofReal (by positivity)]
  rw [hmass] at hmono
  exact hmono

theorem kMuPiece : KMuPiece := by
  intro C
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast cfg_m_pos C
  have hsplit : eMkμ C = ∑ s ∈ C.pinned, ∑ r ∈ C.frequency,
      ∫ p : ℝ × ℝ, Real.log (p.1 + p.2)
        ∂((volume.restrict (pinnedCell C.m s)).prod (volume.restrict (frequencyCell C.m r))) := by
    unfold eMkμ wκ wμ pinnedMeasure frequencyMeasure
    rw [prod_finset_sum_restrict, integral_finsetSum_measure]
    · apply Finset.sum_congr rfl
      intro s hs
      rw [integral_finsetSum_measure]
      intro r hr
      exact (pair_integral_lower C hs hr).1
    · intro s hs
      exact integrable_finsetSum_measure.mpr (fun r hr => (pair_integral_lower C hs hr).1)
  have hlow : (∑ s ∈ C.pinned, ∑ r ∈ C.frequency, (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ *
      (Real.log ((s : ℝ) / (C.m : ℝ) + (r : ℝ) / (C.m : ℝ)) - 4 / (3 * (C.m : ℝ)))) ≤
      eMkμ C := by
    rw [hsplit]
    exact Finset.sum_le_sum (fun s hs => Finset.sum_le_sum
      (fun r hr => (pair_integral_lower C hs hr).2))
  have hrw : (∑ s ∈ C.pinned, ∑ r ∈ C.frequency, (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ *
      (Real.log ((s : ℝ) / (C.m : ℝ) + (r : ℝ) / (C.m : ℝ)) - 4 / (3 * (C.m : ℝ)))) =
      (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ * pinFreq C -
        (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ * ((C.pinned.card : ℝ) * (C.m : ℝ) * (4 / (3 * (C.m : ℝ)))) := by
    unfold pinFreq
    simp_rw [mul_sub, Finset.sum_sub_distrib, Finset.sum_const, C.frequency_card,
      nsmul_eq_mul, ← Finset.mul_sum]
    ring
  rw [hrw] at hlow
  have h2 := mul_le_mul_of_nonneg_left hlow (sq_nonneg (C.m : ℝ))
  have he : (C.m : ℝ) ^ 2 * ((C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ * pinFreq C -
      (C.m : ℝ)⁻¹ * (C.m : ℝ)⁻¹ * ((C.pinned.card : ℝ) * (C.m : ℝ) * (4 / (3 * (C.m : ℝ))))) =
      pinFreq C - 4 * (C.pinned.card : ℝ) / 3 := by
    field_simp
  rw [he] at h2
  have hk : (C.pinned.card : ℝ) ≤ C.m := by
    have := C.mass_balance
    exact_mod_cast (by omega : C.pinned.card ≤ C.m)
  linarith


end

end Li2Lean.P0.CellBound
