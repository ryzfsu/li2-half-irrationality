/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.FrequencyGenerating
import Li2Lean.P0.FrequencyCutoff
import Li2Lean.P0.FrequencyRegularity

/-!
# Monotone passage for the literal frequency envelope

The full envelope is first defined with nonnegative extended-real integrals.
No integrability or convergence of the infinite-frequency expression is assumed.
The finite-cutoff estimate implies its finiteness.
-/

open MeasureTheory Filter Topology

namespace Li2Lean.P0.FrequencyLimit

noncomputable section

open scoped BigOperators ENNReal
open FrequencyCutoff FrequencyRegularity

instance actualTruncatedFintype (g m H : ℕ) :
    Fintype (TruncatedFrequencyTuple g m H) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- The exact generating function stated with the pre-existing contour weight constant. -/
theorem hasSum_actualWeights (g : ℕ) {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t < 2) :
    HasSum (fun r : {r : ℕ // g < r} => P0.frequencyWeightReal g r.val * t ^ r.val)
      ((t / (2 - t)) ^ (g + 1)) :=
  FrequencyGenerating.hasSum_weighted_subtype g ht0 ht2

/-- Exact finite subset/tuple conversion for the pre-existing contour tuple type. -/
theorem sum_subsets_eq_sum_actualTuples {A : Type*} [AddCommMonoid A]
    (g m H : ℕ) (f : Finset ℕ → A) :
    (∑ R ∈ (Finset.Ioc g H).powersetCard m, f R) =
      ∑ r : TruncatedFrequencyTuple g m H, f (tupleSet (forgetCutoff r)) :=
  sum_powersetCard_eq_sum_truncated g m H f

/-- The nonnegative parameter integrand, preserving all three determinants and arc factors. -/
def envelopeTerm (m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) : ℝ :=
  contourQValue S h4 hSI r.val r.property.1
    (fun i => p0EllipsePoint m (u i)) *
      ∏ i : Fin (m - S.card), contourArcDensity m (u i)

def finiteEnvelopeIntegrand (m H : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) : ℝ≥0∞ :=
  ∑ r ∈ cutoffTuples (m / 2) m H, ENNReal.ofReal (envelopeTerm m h4 S hSI r u)

/-- The nonnegative finite-cutoff contribution on the same tuple domain. -/
def finiteContribution (m H : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m) : ℝ≥0∞ :=
  ENNReal.ofReal ((Nat.factorial (m - S.card) : ℝ)⁻¹) *
    ∫⁻ u : Fin (m - S.card) → ℝ, finiteEnvelopeIntegrand m H h4 S hSI u
      ∂(ContourKit.productMeasure contourParameterMeasure)

/-- The nonnegative finite-cutoff envelope. -/
def finiteEnvelope (m H : ℕ) (h4 : 4 ∣ m) : ℝ≥0∞ := by
  classical
  exact ∑ S ∈ (Iset m).powerset,
    if hSI : S ⊆ Iset m then finiteContribution m H h4 S hSI else 0

/-- The literal full nonnegative contribution of one pinned set in `eq:contour-E`. -/
def fullContribution (m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m) : ℝ≥0∞ :=
  ENNReal.ofReal ((Nat.factorial (m - S.card) : ℝ)⁻¹) *
    ∫⁻ u : Fin (m - S.card) → ℝ,
      ∑' r : IncreasingFrequencyTuple (m / 2) m,
        ENNReal.ofReal (envelopeTerm m h4 S hSI r u)
      ∂(ContourKit.productMeasure contourParameterMeasure)

/-- The literal full envelope of v10, before its finiteness has been proved. -/
def fullEnvelope (m : ℕ) (h4 : 4 ∣ m) : ℝ≥0∞ := by
  classical
  exact ∑ S ∈ (Iset m).powerset,
    if hSI : S ⊆ Iset m then fullContribution m h4 S hSI else 0

/-- Every factor of the paper's absolute parameter integrand is nonnegative. -/
theorem envelopeTerm_nonneg (m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (r : IncreasingFrequencyTuple (m / 2) m)
    (u : Fin (m - S.card) → ℝ) : 0 ≤ envelopeTerm m h4 S hSI r u := by
  have hell : 0 ≤ ell := Real.log_nonneg (by norm_num)
  unfold envelopeTerm contourQValue UReal frequencyWeightReal contourArcDensity
  positivity

private theorem orderedElem_mem (R : Finset ℕ) (i : Fin R.card) :
    orderedElem R i ∈ R := (Finset.orderIsoOfFin R rfl i).property

/-- Each literal three-minor contour integrand is continuous on the entire parameter space. -/
theorem continuous_envelopeTerm (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) : Continuous (envelopeTerm m h4 S hSI r) := by
  classical
  let d := m - S.card
  let Ic := Iset m \ S
  let Jc := Jset m \ S
  have hScard : S.card ≤ m := by
    rw [← Iset_card m]
    exact Finset.card_le_card hSI
  have hIc : Ic.card = d := by
    rw [Finset.card_sdiff_of_subset hSI, Iset_card]
  have hSJ : S ⊆ Jset m := hSI.trans (Iset_subset_Jset m h4)
  have hJc : Jc.card = d + m := by
    rw [Finset.card_sdiff_of_subset hSJ]
    simp [d, Jset, Finset.card_range]
    omega
  have hpoint (i : Fin d) : Continuous (fun u : Fin d → ℝ => p0EllipsePoint m (u i)) :=
    (continuous_ellipsePoint m).comp (continuous_apply i)
  have hleftpole (i : Fin d) : orderedElem Ic (Fin.cast hIc.symm i) < 2 * m := by
    have hi := (Finset.mem_sdiff.mp (orderedElem_mem Ic (Fin.cast hIc.symm i))).1
    exact Finset.mem_range.mp (Iset_subset_Jset m h4 hi)
  have hrightpole (i : Fin (d + m)) : orderedElem Jc (Fin.cast hJc.symm i) < 2 * m := by
    exact Finset.mem_range.mp
      (Finset.mem_sdiff.mp (orderedElem_mem Jc (Fin.cast hJc.symm i))).1
  have hpole (a : ℕ) (ha : a < 2 * m) (u : ℝ) :
      (a : ℂ) - p0EllipsePoint m u ≠ 0 := by
    apply sub_ne_zero.mpr
    apply Ne.symm
    exact ellipsePoint_ne_real m hm u a (by positivity) (by exact_mod_cast Nat.le_of_lt ha)
  have hleft : Continuous (fun u : Fin d → ℝ => cauchyDet
      (fun i : Fin d => ((orderedElem Ic (Fin.cast hIc.symm i) : ℕ) : ℂ))
      (fun i => -p0EllipsePoint m (u i))) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    apply Continuous.inv₀ (continuous_const.add (hpoint j).neg)
    intro u
    simpa [sub_eq_add_neg] using hpole _ (hleftpole i) (u j)
  have hright : Continuous (fun u : Fin d → ℝ => Matrix.det
      (fun i : Fin (d + m) => fun j : Fin (d + m) =>
        ((if hi : i.val < d then -p0EllipsePoint m (u ⟨i.val, hi⟩) else
            (r.val ⟨i.val - d, by omega⟩ : ℂ)) +
          ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ))⁻¹)) := by
    apply Continuous.matrix_det
    apply continuous_pi
    intro i
    apply continuous_pi
    intro j
    by_cases hi : i.val < d
    · simp only [dite_eq_left hi]
      apply Continuous.inv₀ ((hpoint ⟨i.val, hi⟩).neg.add continuous_const)
      intro u
      simpa [sub_eq_add_neg, add_comm] using hpole _ (hrightpole j) (u ⟨i.val, hi⟩)
    · simp only [dite_eq_right hi]
      exact continuous_const
  have hminors : Continuous (fun u : Fin d → ℝ =>
      contourQMinors S h4 hSI r.val r.property.1 (fun i => p0EllipsePoint m (u i))) := by
    exact hleft.prodMk (continuous_const.prodMk hright)
  have hFG : Continuous (fun u : Fin d → ℝ =>
      ∏ i : Fin d, ‖p0Entire (m / 2) (p0EllipsePoint m (u i))‖) :=
    continuous_finsetProd _ (fun i _ => ((continuous_entire (m / 2)).comp (hpoint i)).norm)
  have hdensity : Continuous (fun u : Fin d → ℝ =>
      ∏ i : Fin d, contourArcDensity m (u i)) := by
    apply continuous_finsetProd
    intro i _
    exact ((continuous_ellipseTangent m).comp (continuous_apply i)).norm.div_const _
  exact (((continuous_const.mul continuous_const).mul hFG).mul
    ((hminors.fst.mul hminors.snd.fst).mul hminors.snd.snd).norm).mul hdensity

/-- Finite-cutoff integrability follows from compactness of the fixed parameter box. -/
theorem integrable_finite_envelope (m H : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Integrable (fun u : Fin (m - S.card) → ℝ =>
      ∑ r ∈ cutoffTuples (m / 2) m H, envelopeTerm m h4 S hSI r u)
      (ContourKit.productMeasure contourParameterMeasure) := by
  apply integrable_parameter
  exact continuous_finsetSum _ (fun r _ => continuous_envelopeTerm m hm h4 S hSI r)

/-- The existing finite envelope contribution is unchanged by the common-domain cutoff encoding. -/
theorem contourEContribution_eq_cutoff (m H : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    contourEContribution m H h4 S hSI =
      (Nat.factorial (m - S.card) : ℝ)⁻¹ *
        ∫ u : Fin (m - S.card) → ℝ,
          ∑ r ∈ cutoffTuples (m / 2) m H, envelopeTerm m h4 S hSI r u
          ∂(ContourKit.productMeasure contourParameterMeasure) := by
  classical
  unfold contourEContribution
  dsimp only
  congr 1
  apply integral_congr_ae
  exact Filter.Eventually.of_forall (fun u => (sum_cutoffTuples (m / 2) m H
    (fun r => envelopeTerm m h4 S hSI r u)).symm)

theorem contourEContribution_nonneg (m H : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) : 0 ≤ contourEContribution m H h4 S hSI := by
  rw [contourEContribution_eq_cutoff]
  apply mul_nonneg (by positivity)
  apply integral_nonneg
  intro u
  exact Finset.sum_nonneg (fun r _ => envelopeTerm_nonneg m h4 S hSI r u)

theorem E_nonneg (m H : ℕ) (h4 : 4 ∣ m) : 0 ≤ E m H h4 := by
  classical
  apply Finset.sum_nonneg
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  exact contourEContribution_nonneg m H h4 S hSI

/-- Identification of the finite nonnegative integral with the existing real integral definition. -/
theorem finiteContribution_eq_ofReal (m H : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    finiteContribution m H h4 S hSI = ENNReal.ofReal (contourEContribution m H h4 S hSI) := by
  classical
  rw [contourEContribution_eq_cutoff, ENNReal.ofReal_mul (by positivity)]
  unfold finiteContribution
  congr 1
  rw [ofReal_integral_eq_lintegral_ofReal (integrable_finite_envelope m H hm h4 S hSI)
    (Filter.Eventually.of_forall (fun u =>
      Finset.sum_nonneg (fun r _ => envelopeTerm_nonneg m h4 S hSI r u)))]
  apply lintegral_congr
  intro u
  exact (ENNReal.ofReal_sum_of_nonneg (fun r _ => envelopeTerm_nonneg m h4 S hSI r u)).symm

/-- The finite extended-real envelope is exactly `ofReal` of the pre-existing `E_m(H)`. -/
theorem finiteEnvelope_eq_ofReal (m H : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    finiteEnvelope m H h4 = ENNReal.ofReal (E m H h4) := by
  classical
  unfold finiteEnvelope E
  rw [ENNReal.ofReal_sum_of_nonneg]
  · apply Finset.sum_congr rfl
    intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simp only [dite_eq_left hSI]
    exact finiteContribution_eq_ofReal m H hm h4 S hSI
  · intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simp only [dite_eq_left hSI]
    exact contourEContribution_nonneg m H h4 S hSI

/-- The exact contribution is the monotone limit of finite cutoffs, without any convergence premise. -/
theorem fullContribution_eq_iSup (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    fullContribution m h4 S hSI = ⨆ H, finiteContribution m H h4 S hSI := by
  unfold fullContribution finiteContribution finiteEnvelopeIntegrand
  erw [lintegral_tsum_eq_iSup_cutoff _ (m / 2) m
    (fun r u => ENNReal.ofReal (envelopeTerm m h4 S hSI r u))
    (fun r => (continuous_envelopeTerm m hm h4 S hSI r).measurable.ennreal_ofReal)]
  exact ENNReal.mul_iSup _ _

theorem finiteContribution_mono (m : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Monotone (fun H => finiteContribution m H h4 S hSI) := by
  intro H K hHK
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply lintegral_mono
  intro u
  exact Finset.sum_le_sum_of_subset (cutoffTuples_mono (m / 2) m hHK)

theorem finiteEnvelope_mono (m : ℕ) (h4 : 4 ∣ m) :
    Monotone (fun H => finiteEnvelope m H h4) := by
  classical
  intro H K hHK
  apply Finset.sum_le_sum
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  exact finiteContribution_mono m h4 S hSI hHK

/-- Finite pinned-set summation commutes with the exact monotone cutoff limit. -/
theorem fullEnvelope_eq_iSup_finiteEnvelope (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    fullEnvelope m h4 = ⨆ H, finiteEnvelope m H h4 := by
  classical
  unfold fullEnvelope finiteEnvelope
  rw [← sum_iSup_of_monotone (Iset m).powerset
    (fun S H => if hSI : S ⊆ Iset m then finiteContribution m H h4 S hSI else 0)]
  · apply Finset.sum_congr rfl
    intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simp only [dite_eq_left hSI]
    exact fullContribution_eq_iSup m hm h4 S hSI
  · intro S hS
    have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
    simpa only [dite_eq_left hSI] using finiteContribution_mono m h4 S hSI

/-- The literal infinite integral is exactly the supremum of the existing finite `E_m(H)`. -/
theorem fullEnvelope_eq_iSup_E (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    fullEnvelope m h4 = ⨆ H, ENNReal.ofReal (E m H h4) := by
  rw [fullEnvelope_eq_iSup_finiteEnvelope m hm h4]
  simp_rw [finiteEnvelope_eq_ofReal m _ hm h4]

/-- The ENNReal envelope defined directly as the supremum of the existing finite cutoffs. -/
def EInfinityENN (m : ℕ) (h4 : 4 ∣ m) : ℝ≥0∞ :=
  ⨆ H : ℕ, ENNReal.ofReal (E m H h4)

/-- The cutoff supremum is the literal full contour integral, including zero-valued terms. -/
theorem EInfinityENN_eq_fullEnvelope (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    EInfinityENN m h4 = fullEnvelope m h4 :=
  (fullEnvelope_eq_iSup_E m hm h4).symm

/-- The ENNReal envelope is also the supremum of the finite integral cutoffs. -/
theorem EInfinityENN_eq_iSup_finiteEnvelope (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    EInfinityENN m h4 = ⨆ H, finiteEnvelope m H h4 := by
  calc
    EInfinityENN m h4 = fullEnvelope m h4 := EInfinityENN_eq_fullEnvelope m hm h4
    _ = ⨆ H, finiteEnvelope m H h4 := fullEnvelope_eq_iSup_finiteEnvelope m hm h4

/-- The actual finite `Q_m` sum at a fixed configuration of contour points. -/
def finiteQSum (m H : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ) : ℝ :=
  ∑ r ∈ cutoffTuples (m / 2) m H, contourQValue S h4 hSI r.val r.property.1 Z

/-- Pointwise finite `Q_m` bounds pass to the exact existing contour integral envelope.
All required finite integrability has already been proved from the ellipse geometry. -/
theorem E_le_of_finiteQSum_le (m H K : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (C : ℝ)
    (hpoint : ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ),
      finiteQSum m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
        C * finiteQSum m K h4 S hSI (fun i => p0EllipsePoint m (u i))) :
    E m H h4 ≤ C * E m K h4 := by
  classical
  unfold E
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dite_eq_left hSI]
  rw [contourEContribution_eq_cutoff, contourEContribution_eq_cutoff]
  let fH := fun u : Fin (m - S.card) → ℝ =>
    ∑ r ∈ cutoffTuples (m / 2) m H, envelopeTerm m h4 S hSI r u
  let fK := fun u : Fin (m - S.card) → ℝ =>
    ∑ r ∈ cutoffTuples (m / 2) m K, envelopeTerm m h4 S hSI r u
  have hpoint' : ∀ u, fH u ≤ C * fK u := by
    intro u
    dsimp [fH, fK]
    simp only [envelopeTerm, ← Finset.sum_mul]
    have hden : 0 ≤ ∏ i : Fin (m - S.card), contourArcDensity m (u i) := by
      unfold contourArcDensity
      positivity
    exact (mul_le_mul_of_nonneg_right (hpoint S hSI u) hden).trans_eq (by unfold finiteQSum; ring)
  have hI : (∫ u, fH u ∂(ContourKit.productMeasure contourParameterMeasure)) ≤
      C * ∫ u, fK u ∂(ContourKit.productMeasure contourParameterMeasure) := by
    rw [← integral_const_mul]
    exact integral_mono (integrable_finite_envelope m H hm h4 S hSI)
      ((integrable_finite_envelope m K hm h4 S hSI).const_mul C) hpoint'
  calc
    _ ≤ (Nat.factorial (m - S.card) : ℝ)⁻¹ *
        (C * ∫ u, fK u ∂(ContourKit.productMeasure contourParameterMeasure)) :=
      mul_le_mul_of_nonneg_left hI (by positivity)
    _ = _ := by ring

/-- The real full envelope, used only after a finite-cutoff bound proves the extended value finite. -/
def EInfinity (m : ℕ) (h4 : 4 ∣ m) : ℝ := (fullEnvelope m h4).toReal

/-- Cofinality of cutoffs above `20m` transfers any uniform finite bound to the literal full integral. -/
theorem fullEnvelope_le_of_finiteCutoff (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (C : ℝ)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤ C * E m (20 * m) h4) :
    fullEnvelope m h4 ≤ ENNReal.ofReal (C * E m (20 * m) h4) := by
  rw [fullEnvelope_eq_iSup_finiteEnvelope m hm h4]
  apply iSup_le
  intro H
  calc
    finiteEnvelope m H h4 ≤ finiteEnvelope m (max H (20 * m)) h4 :=
      finiteEnvelope_mono m h4 (le_max_left _ _)
    _ = ENNReal.ofReal (E m (max H (20 * m)) h4) :=
      finiteEnvelope_eq_ofReal m _ hm h4
    _ ≤ ENNReal.ofReal (C * E m (20 * m) h4) :=
      ENNReal.ofReal_le_ofReal (hfinite _ (le_max_right _ _))

/-- A uniform finite-cutoff bound controls the explicit ENNReal cutoff supremum. -/
theorem EInfinityENN_le_of_finiteCutoff (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (C : ℝ)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤ C * E m (20 * m) h4) :
    EInfinityENN m h4 ≤ ENNReal.ofReal (C * E m (20 * m) h4) := by
  rw [EInfinityENN_eq_fullEnvelope m hm h4]
  exact fullEnvelope_le_of_finiteCutoff m hm h4 C hfinite

/-- Any finite-cutoff bound makes the literal ENNReal envelope finite. -/
theorem EInfinityENN_ne_top_of_finiteCutoff (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) :
    EInfinityENN m h4 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (EInfinityENN_le_of_finiteCutoff m hm h4 _ hfinite)

/-- The v10 finite-cutoff estimate itself proves that the infinite envelope is finite. -/
theorem fullEnvelope_ne_top_of_finiteCutoff (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) :
    fullEnvelope m h4 ≠ ⊤ :=
  ne_top_of_le_ne_top ENNReal.ofReal_ne_top
    (fullEnvelope_le_of_finiteCutoff m hm h4 _ hfinite)

/-- The finite-cutoff bound certifies that converting the full envelope to a real number loses
no information; in particular, the `toReal` value cannot be a default value for infinity. -/
theorem ofReal_EInfinity_eq_of_finiteCutoff (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) :
    ENNReal.ofReal (EInfinity m h4) = fullEnvelope m h4 :=
  ENNReal.ofReal_toReal (fullEnvelope_ne_top_of_finiteCutoff m hm h4 hfinite)

/-- The real value `EInfinity` recovers the ENNReal cutoff supremum after finiteness. -/
theorem ofReal_EInfinity_eq_EInfinityENN (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) :
    ENNReal.ofReal (EInfinity m h4) = EInfinityENN m h4 := by
  rw [EInfinityENN_eq_fullEnvelope m hm h4]
  exact ofReal_EInfinity_eq_of_finiteCutoff m hm h4 hfinite

/-- The exact R5 monotone-passage theorem for the literal `Q`, contour measure, and cutoff `20m`.
The only producer input is the finite-cutoff inequality; no infinite summability or integrability
assumption appears. -/
theorem EInfinity_le_cutoff_of_finiteCutoff (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) :
    EInfinity m h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4 := by
  have h := ENNReal.toReal_mono ENNReal.ofReal_ne_top
    (fullEnvelope_le_of_finiteCutoff m hm h4 _ hfinite)
  have hn : 0 ≤ (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4 := by
    exact mul_nonneg (by positivity) (E_nonneg m (20 * m) h4)
  simpa only [EInfinity, ENNReal.toReal_ofReal hn] using h

/-- The literal full cutoff result follows from finite `Q_m` bounds, with finiteness proved as output.
The remaining algebraic producer is the Cauchy-minor-to-frequency-factor bridge followed by the
finite replacement estimate. -/
theorem full_cutoff_of_Q_bounds (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hQ : ∀ (H : ℕ), 20 * m ≤ H →
      ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ),
        finiteQSum m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
          (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
            finiteQSum m (20 * m) h4 S hSI (fun i => p0EllipsePoint m (u i))) :
    fullEnvelope m h4 ≠ ⊤ ∧
      EInfinity m h4 ≤ (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4 := by
  have hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4 := by
    intro H hH
    exact E_le_of_finiteQSum_le m H (20 * m) hm h4 _ (hQ H hH)
  exact ⟨fullEnvelope_ne_top_of_finiteCutoff m hm h4 hfinite,
    EInfinity_le_cutoff_of_finiteCutoff m hm h4 hfinite⟩

/-- ENNReal-valued cutoff conclusion from a pointwise bound on the literal finite `Q` sums.
The producer obligation is kept explicit; this theorem does not assert a `Q`/`frequencyFactor`
identity. The raw nonnegative integrand permits zero determinants and parameter collisions, and
the monotone-convergence argument needs no atomlessness assumption on the contour measure. -/
theorem full_cutoffENN_of_Q_bounds (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hQ : ∀ (H : ℕ), 20 * m ≤ H →
      ∀ (S : Finset ℕ) (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ),
        finiteQSum m H h4 S hSI (fun i => p0EllipsePoint m (u i)) ≤
          (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
            finiteQSum m (20 * m) h4 S hSI (fun i => p0EllipsePoint m (u i))) :
    EInfinityENN m h4 ≠ ⊤ ∧
      EInfinityENN m h4 ≤
        ENNReal.ofReal ((1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) := by
  have hfinite : ∀ H : ℕ, 20 * m ≤ H → E m H h4 ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4 := by
    intro H hH
    exact E_le_of_finiteQSum_le m H (20 * m) hm h4 _ (hQ H hH)
  exact ⟨EInfinityENN_ne_top_of_finiteCutoff m hm h4 hfinite,
    EInfinityENN_le_of_finiteCutoff m hm h4 _ hfinite⟩

end

end Li2Lean.P0.FrequencyLimit
