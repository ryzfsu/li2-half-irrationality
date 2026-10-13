/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Defs

/-!
# Exact expansion of `log Q` for a finite configuration

Paper v13 `p0-analytic.tex` ll. 95-156.  The literal integrand
`literalConfigQWeight C` is a product of one-body factors and the absolute
values of three Cauchy minors.  Each minor is expanded by the Cauchy
determinant (`cauchy_det_eq_vandermonde_mul_inv_denominator`) into
Vandermonde factors over denominators; `2 log |Δ(v)| = ∑_{i≠j} log |v_i - v_j|`.
The `Fin`-indexed sums are reindexed to the sets `I_m \ S`, `J_m \ S`, `R`,
the deleted sites are restored, and every logarithm is rescaled by `m`, which
leaves the net power `-(2m + 2d) log m`.  `Q > 0` also yields distinct
contour points and nonvanishing contour product (`qPosFacts`).
-/


open MeasureTheory

namespace Li2Lean.P0.CellBound.LogQ

open Li2Lean.P0
open Li2Lean.P0.Config

noncomputable section

/-! ## Generic off-diagonal sums -/

/-- Ordered off-diagonal logarithmic sum of a finite tuple. -/
def odFin {n : ℕ} (v : Fin n → ℂ) : ℝ :=
  ∑ i, ∑ j, if i = j then 0 else Real.log ‖v i - v j‖

/-- Ordered off-diagonal logarithmic sum over a finite set of labels. -/
def odSet {α : Type*} [DecidableEq α] (T : Finset α) (g : α → ℂ) : ℝ :=
  ∑ p ∈ T, ∑ q ∈ T, if p = q then 0 else Real.log ‖g p - g q‖

theorem sum_offdiag_symm {n : ℕ} (f : Fin n → Fin n → ℝ) (hf : ∀ i j, f i j = f j i) :
    (∑ i, ∑ j, if i = j then 0 else f i j) = 2 * ∑ i, ∑ j ∈ Finset.Ioi i, f i j := by
  have h1 : ∀ i, (∑ j, if i = j then 0 else f i j) =
      (∑ j, if i < j then f i j else 0) + ∑ j, if j < i then f i j else 0 := by
    intro i
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    rcases lt_trichotomy i j with h | h | h
    · simp [h, h.ne, not_lt.mpr h.le]
    · subst h; simp
    · simp [h, h.ne', not_lt.mpr h.le]
  simp_rw [h1, Finset.sum_add_distrib]
  rw [Finset.sum_comm (f := fun i j => if j < i then f i j else 0)]
  have h2 : ∀ i, (∑ j, if i < j then f i j else 0) = ∑ j ∈ Finset.Ioi i, f i j := by
    intro i
    rw [← Finset.sum_filter]
    congr 1
    ext j
    simp
  have h3 : ∀ j, (∑ i, if j < i then f i j else 0) = ∑ i ∈ Finset.Ioi j, f j i := by
    intro j
    rw [← Finset.sum_filter]
    have : (Finset.univ.filter fun i => j < i) = Finset.Ioi j := by
      ext i; simp
    rw [this]
    exact Finset.sum_congr rfl (fun i _ => hf i j)
  simp_rw [h2, h3]
  ring

theorem log_norm_det_vandermonde {n : ℕ} (v : Fin n → ℂ) (hv : Function.Injective v) :
    Real.log ‖(Matrix.vandermonde v).det‖ = (1 / 2) * odFin v := by
  rw [Matrix.det_vandermonde, norm_prod,
    Real.log_prod (fun i _ => by
      rw [norm_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun j hj => norm_ne_zero_iff.mpr
        (sub_ne_zero.mpr (fun h => (ne_of_gt (Finset.mem_Ioi.mp hj)) (hv h)))))]
  have hin : ∀ i, Real.log ‖∏ j ∈ Finset.Ioi i, (v j - v i)‖ =
      ∑ j ∈ Finset.Ioi i, Real.log ‖v i - v j‖ := by
    intro i
    rw [norm_prod, Real.log_prod (fun j hj => norm_ne_zero_iff.mpr
        (sub_ne_zero.mpr (fun h => (ne_of_gt (Finset.mem_Ioi.mp hj)) (hv h))))]
    exact Finset.sum_congr rfl (fun j _ => by rw [norm_sub_rev])
  simp_rw [hin]
  unfold odFin
  rw [sum_offdiag_symm (fun i j => Real.log ‖v i - v j‖)
    (fun i j => by rw [norm_sub_rev])]
  ring

/-- `log |det (x_i + y_j)^{-1}|` by the Cauchy determinant. -/
theorem log_norm_cauchy {n : ℕ} (x y : Fin n → ℂ)
    (hdet : (Matrix.of fun i j => (x i + y j)⁻¹).det ≠ 0)
    (hxy : ∀ i j, x i + y j ≠ 0) :
    Real.log ‖(Matrix.of fun i j => (x i + y j)⁻¹).det‖ =
      (1 / 2) * odFin x + (1 / 2) * odFin y - ∑ i, ∑ j, Real.log ‖x i + y j‖ := by
  have hx : Function.Injective x := by
    intro i i' h
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_row_eq hne
    funext j
    simp [h]
  have hy : Function.Injective y := by
    intro j j' h
    by_contra hne
    apply hdet
    apply Matrix.det_zero_of_column_eq hne
    intro i
    simp [h]
  rw [Li2Lean.P0.CauchyDeterminant.cauchy_det_eq_vandermonde_mul_inv_denominator x y hy hxy]
  have hVx : (Matrix.vandermonde x).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hx
  have hVy : (Matrix.vandermonde y).det ≠ 0 := Matrix.det_vandermonde_ne_zero_iff.mpr hy
  have hD : (∏ i : Fin n, ∏ j : Fin n, (x i + y j)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr (fun i _ => Finset.prod_ne_zero_iff.mpr (fun j _ => hxy i j))
  rw [norm_mul, norm_mul, norm_inv,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hVx) (norm_ne_zero_iff.mpr hVy))
      (inv_ne_zero (norm_ne_zero_iff.mpr hD)),
    Real.log_mul (norm_ne_zero_iff.mpr hVx) (norm_ne_zero_iff.mpr hVy), Real.log_inv,
    log_norm_det_vandermonde x hx, log_norm_det_vandermonde y hy, norm_prod,
    Real.log_prod (fun i _ => by
      rw [norm_prod]
      exact Finset.prod_ne_zero_iff.mpr (fun j _ => norm_ne_zero_iff.mpr (hxy i j)))]
  have hin : ∀ i, Real.log ‖∏ j : Fin n, (x i + y j)‖ = ∑ j, Real.log ‖x i + y j‖ := by
    intro i
    rw [norm_prod, Real.log_prod (fun j _ => norm_ne_zero_iff.mpr (hxy i j))]
  simp_rw [hin]
  ring

/-! ## Reindexing -/

theorem sum_reindex {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α)
    (hf : Function.Injective f) (T : Finset α) (hmem : ∀ i, f i ∈ T)
    (hcard : T.card = n) (h : α → ℝ) :
    ∑ i, h (f i) = ∑ p ∈ T, h p := by
  have himg : Finset.univ.image f = T := by
    apply Finset.eq_of_subset_of_card_le
    · intro p hp
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp hp
      exact hmem i
    · rw [Finset.card_image_of_injective _ hf, hcard, Finset.card_univ, Fintype.card_fin]
  rw [← himg, Finset.sum_image (fun i _ j _ hij => hf hij)]

theorem odFin_reindex {α : Type*} [DecidableEq α] {n : ℕ} (f : Fin n → α)
    (hf : Function.Injective f) (T : Finset α) (hmem : ∀ i, f i ∈ T)
    (hcard : T.card = n) (g : α → ℂ) :
    odFin (fun i => g (f i)) = odSet T g := by
  unfold odFin odSet
  have hite : ∀ i j, (if i = j then (0 : ℝ) else Real.log ‖g (f i) - g (f j)‖) =
      (if f i = f j then 0 else Real.log ‖g (f i) - g (f j)‖) := by
    intro i j
    simp only [hf.eq_iff]
  simp_rw [hite]
  rw [sum_reindex f hf T hmem hcard
    (fun p => ∑ j, if p = f j then (0 : ℝ) else Real.log ‖g p - g (f j)‖)]
  apply Finset.sum_congr rfl
  intro p _
  exact sum_reindex f hf T hmem hcard
    (fun q => if p = q then (0 : ℝ) else Real.log ‖g p - g q‖)

theorem sum_sum_reindex {α β : Type*} [DecidableEq α] [DecidableEq β] {n k : ℕ}
    (f : Fin n → α) (hf : Function.Injective f) (T : Finset α) (hmem : ∀ i, f i ∈ T)
    (hcard : T.card = n)
    (e : Fin k → β) (he : Function.Injective e) (U : Finset β) (hmemU : ∀ i, e i ∈ U)
    (hcardU : U.card = k) (h : α → β → ℝ) :
    ∑ i, ∑ j, h (f i) (e j) = ∑ p ∈ T, ∑ q ∈ U, h p q := by
  rw [sum_reindex f hf T hmem hcard (fun p => ∑ j, h p (e j))]
  exact Finset.sum_congr rfl (fun p _ => sum_reindex e he U hmemU hcardU (h p))

/-! ## Restoration of deleted sites -/

theorem odSet_sdiff {α : Type*} [DecidableEq α] (A S : Finset α) (hSA : S ⊆ A)
    (g : α → ℂ) :
    odSet (A \ S) g = odSet A g -
      2 * (∑ p ∈ S, ∑ q ∈ A, if q = p then 0 else Real.log ‖g p - g q‖) + odSet S g := by
  set G : α → α → ℝ := fun p q => if p = q then 0 else Real.log ‖g p - g q‖ with hG
  have hsymm : ∀ p q, G p q = G q p := by
    intro p q
    simp only [hG]
    by_cases h : p = q
    · simp [h]
    · rw [if_neg h, if_neg (Ne.symm h), norm_sub_rev]
  have hsplit : ∀ (B : Finset α) (F : α → ℝ), ∑ q ∈ A, F q = ∑ q ∈ A \ S, F q + ∑ q ∈ S, F q :=
    fun _ F => (Finset.sum_sdiff hSA).symm
  have hA : odSet A g = ∑ p ∈ A, ∑ q ∈ A, G p q := rfl
  have hAS : odSet (A \ S) g = ∑ p ∈ A \ S, ∑ q ∈ A \ S, G p q := rfl
  have hS : odSet S g = ∑ p ∈ S, ∑ q ∈ S, G p q := rfl
  have hmid : (∑ p ∈ S, ∑ q ∈ A, if q = p then 0 else Real.log ‖g p - g q‖) =
      ∑ p ∈ S, ∑ q ∈ A, G p q := by
    apply Finset.sum_congr rfl; intro p _; apply Finset.sum_congr rfl; intro q _
    simp only [hG, eq_comm]
  rw [hA, hAS, hS, hmid]
  have e1 : ∑ p ∈ A, ∑ q ∈ A, G p q =
      ∑ p ∈ A \ S, ∑ q ∈ A, G p q + ∑ p ∈ S, ∑ q ∈ A, G p q :=
    (Finset.sum_sdiff hSA).symm
  have e2 : ∀ p, ∑ q ∈ A, G p q = ∑ q ∈ A \ S, G p q + ∑ q ∈ S, G p q :=
    fun p => (Finset.sum_sdiff hSA).symm
  have e3 : ∑ p ∈ A \ S, ∑ q ∈ S, G p q = ∑ p ∈ S, ∑ q ∈ A \ S, G p q := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl (fun q _ => hsymm q p))
  rw [e1]
  simp_rw [e2]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, e3]
  ring

theorem sum_sdiff_sub {α : Type*} [DecidableEq α] (A S : Finset α) (hSA : S ⊆ A)
    (F : α → ℝ) : ∑ p ∈ A \ S, F p = ∑ p ∈ A, F p - ∑ p ∈ S, F p := by
  rw [← Finset.sum_sdiff hSA]
  ring

theorem Ic_card {m : ℕ} (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    (Iset m \ S).card = m - S.card := by
  rw [Finset.card_sdiff_of_subset hSI, Iset_card]

theorem Jc_card {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) :
    (Jset m \ S).card = m - S.card + m := by
  have hSJ : S ⊆ Jset m := hSI.trans (Iset_subset_Jset m h4)
  have hScard : S.card ≤ m := by
    rw [← Iset_card m]; exact Finset.card_le_card hSI
  rw [Finset.card_sdiff_of_subset hSJ]
  simp [Jset, Finset.card_range]
  omega

def xL {m : ℕ} (S : Finset ℕ) (hSI : S ⊆ Iset m) (i : Fin (m - S.card)) : ℂ :=
  ((orderedElem (Iset m \ S) (Fin.cast (Ic_card S hSI).symm i) : ℕ) : ℂ)

def yR {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (j : Fin (m - S.card + m)) : ℂ :=
  ((orderedElem (Jset m \ S) (Fin.cast (Jc_card S h4 hSI).symm j) : ℕ) : ℂ)

def xR {m : ℕ} (S : Finset ℕ) (R : Fin m → ℕ) (Z : Fin (m - S.card) → ℂ)
    (i : Fin (m - S.card + m)) : ℂ :=
  if hi : i.val < m - S.card then -Z ⟨i.val, hi⟩ else
    (R ⟨i.val - (m - S.card), by omega⟩ : ℂ)

theorem contourQValue_explicit {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) :
    contourQValue S h4 hSI R hR Z =
      (∏ a ∈ S, ell * UReal (m / 2) a) *
        (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
        (∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖) *
        ‖(Matrix.of fun i j => (xL S hSI i + (fun j => -Z j) j)⁻¹).det *
          (Matrix.of fun i j => ((fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) i +
            (fun i => (R i : ℂ)) j)⁻¹).det *
          (Matrix.of fun i j => (xR S R Z i + yR S h4 hSI j)⁻¹).det‖ := by
  rfl


theorem log_contourQValue {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) (hQ : 0 < contourQValue S h4 hSI R hR Z)
    (hRpos : ∀ j, 0 < R j)
    (hxyL : ∀ i j, xL S hSI i + -Z j ≠ 0)
    (hxyR : ∀ i j, xR S R Z i + yR S h4 hSI j ≠ 0) :
    Real.log (contourQValue S h4 hSI R hR Z) =
      (∑ a ∈ S, Real.log (ell * UReal (m / 2) a)) +
        (∑ i : Fin m, Real.log (frequencyWeightReal (m / 2) (R i))) +
        (∑ i : Fin (m - S.card), Real.log ‖p0Entire (m / 2) (Z i)‖) +
        ((1 / 2) * odFin (xL S hSI) + (1 / 2) * odFin (fun j => -Z j) -
          ∑ i, ∑ j, Real.log ‖xL S hSI i + -Z j‖) +
        ((1 / 2) * odFin (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) +
          (1 / 2) * odFin (fun i => (R i : ℂ)) -
          ∑ i : Fin m, ∑ j : Fin m, Real.log ‖((rowIndex m i : ℕ) : ℂ) + (R j : ℂ)‖) +
        ((1 / 2) * odFin (xR S R Z) + (1 / 2) * odFin (yR S h4 hSI) -
          ∑ i, ∑ j, Real.log ‖xR S R Z i + yR S h4 hSI j‖) := by
  have hQ0 := hQ.ne'
  rw [contourQValue_explicit] at hQ0 ⊢
  have hxyM : ∀ i j : Fin m, (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) i +
      (fun i => (R i : ℂ)) j ≠ 0 := by
    intro i j h
    have h' : ((rowIndex m i + R j : ℕ) : ℂ) = 0 := by push_cast; exact h
    have h'' : rowIndex m i + R j = 0 := by exact_mod_cast h'
    have := hRpos j
    omega
  set A := ∏ a ∈ S, ell * UReal (m / 2) a with hA
  set W := ∏ i : Fin m, frequencyWeightReal (m / 2) (R i) with hW
  set P := ∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖ with hP
  set L := (Matrix.of fun i j => (xL S hSI i + (fun j => -Z j) j)⁻¹).det with hL
  set M := (Matrix.of fun i j => ((fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) i +
            (fun i => (R i : ℂ)) j)⁻¹).det with hM
  set N := (Matrix.of fun i j => (xR S R Z i + yR S h4 hSI j)⁻¹).det with hN
  have hAW : A * W * P ≠ 0 := left_ne_zero_of_mul hQ0
  have hAW' : A * W ≠ 0 := left_ne_zero_of_mul hAW
  have hA0 : A ≠ 0 := left_ne_zero_of_mul hAW'
  have hW0 : W ≠ 0 := right_ne_zero_of_mul hAW'
  have hP0 : P ≠ 0 := right_ne_zero_of_mul hAW
  have hn : ‖L * M * N‖ ≠ 0 := right_ne_zero_of_mul hQ0
  have hLMN : L * M * N ≠ 0 := norm_ne_zero_iff.mp hn
  have hLM : L * M ≠ 0 := left_ne_zero_of_mul hLMN
  have hL0 : L ≠ 0 := left_ne_zero_of_mul hLM
  have hM0 : M ≠ 0 := right_ne_zero_of_mul hLM
  have hN0 : N ≠ 0 := right_ne_zero_of_mul hLMN
  rw [Real.log_mul hAW hn, Real.log_mul hAW' hP0, Real.log_mul hA0 hW0, norm_mul, norm_mul,
    Real.log_mul (mul_ne_zero (norm_ne_zero_iff.mpr hL0) (norm_ne_zero_iff.mpr hM0))
      (norm_ne_zero_iff.mpr hN0),
    Real.log_mul (norm_ne_zero_iff.mpr hL0) (norm_ne_zero_iff.mpr hM0)]
  rw [hA, Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mp hA0 a ha),
    hW, Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mp hW0 a ha),
    hP, Real.log_prod (fun a ha => Finset.prod_ne_zero_iff.mp hP0 a ha)]
  rw [hL, log_norm_cauchy _ _ hL0 hxyL, hM, log_norm_cauchy _ _ hM0 hxyM,
    hN, log_norm_cauchy _ _ hN0 hxyR]
  ring

/-! ## Consequences of `Q > 0` -/

theorem qpos_generic {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) (hQ : 0 < contourQValue S h4 hSI R hR Z) :
    Function.Injective Z ∧ ∀ i, p0Entire (m / 2) (Z i) ≠ 0 := by
  have hQ0 := hQ.ne'
  rw [contourQValue_explicit] at hQ0
  have hAW := left_ne_zero_of_mul hQ0
  have hP0 := right_ne_zero_of_mul hAW
  have hn := right_ne_zero_of_mul hQ0
  have hLMN := norm_ne_zero_iff.mp hn
  have hL0 := left_ne_zero_of_mul (left_ne_zero_of_mul hLMN)
  constructor
  · intro j j' h
    by_contra hne
    apply hL0
    apply Matrix.det_zero_of_column_eq hne
    intro i
    simp [h]
  · intro i
    exact norm_ne_zero_iff.mp (Finset.prod_ne_zero_iff.mp hP0 i (Finset.mem_univ i))

/-! ## The configuration instance -/

theorem pinned_subset_Iset' (C : FiniteConfiguration) : C.pinned ⊆ Iset C.m := by
  rw [Iset_eq_paper_interval C.m C.four_dvd_m]
  simpa [pinnedUniverse] using C.pinned_subset

theorem contourCount_eq' (C : FiniteConfiguration) :
    C.m - C.pinned.card = C.contourCount := by
  have h := C.mass_balance
  omega

def Zs (C : FiniteConfiguration) (i : Fin (C.m - C.pinned.card)) : ℂ :=
  Complex.ofReal (C.m : ℝ) * C.contour (Fin.cast (contourCount_eq' C) i)

def Rs (C : FiniteConfiguration) (i : Fin C.m) : ℕ :=
  orderedElem C.frequency (Fin.cast C.frequency_card.symm i)

theorem Rs_strictMono (C : FiniteConfiguration) : StrictMono (Rs C) := by
  intro i j hij
  exact (Finset.orderIsoOfFin C.frequency C.frequency_card).strictMono hij

theorem literal_eq (C : FiniteConfiguration) :
    literalConfigQWeight C =
      contourQValue C.pinned C.four_dvd_m (pinned_subset_Iset' C) (Rs C)
        (Rs_strictMono C) (Zs C) := rfl

theorem orderedElem_cast_injective {α : Type} [LinearOrder α] (s : Finset α) {n : ℕ}
    (h : s.card = n) :
    Function.Injective (fun i : Fin n => orderedElem s (Fin.cast h.symm i)) := by
  intro i j hij
  exact Fin.cast_injective _ ((Finset.orderIsoOfFin s rfl).injective (Subtype.ext hij))

theorem orderedElem_mem' {α : Type} [LinearOrder α] (s : Finset α) (i : Fin s.card) :
    orderedElem s i ∈ s :=
  (Finset.orderIsoOfFin s rfl i).2

theorem Rs_pos (C : FiniteConfiguration) (j : Fin C.m) : 0 < Rs C j := by
  have := C.frequency_lower _ (orderedElem_mem' C.frequency (Fin.cast C.frequency_card.symm j))
  unfold Rs
  omega

theorem qPosFacts' : QPosFacts := by
  intro C hQ
  rw [literal_eq] at hQ
  obtain ⟨hinj, hF⟩ := qpos_generic _ _ _ _ _ _ hQ
  constructor
  · intro a b hab heq
    apply hab
    have h1 : Zs C (Fin.cast (contourCount_eq' C).symm a) =
        Zs C (Fin.cast (contourCount_eq' C).symm b) := by
      simp [Zs, heq]
    have := hinj h1
    exact Fin.cast_injective _ this
  · intro a
    have := hF (Fin.cast (contourCount_eq' C).symm a)
    simpa [Zs] using this

/-! ## Splitting the mixed row vector -/

theorem odFin_append {d n : ℕ} (v : Fin (d + n) → ℂ) (a : Fin d → ℂ) (b : Fin n → ℂ)
    (ha : ∀ i, v (Fin.castAdd n i) = a i) (hb : ∀ j, v (Fin.natAdd d j) = b j) :
    odFin v = odFin a + odFin b + 2 * ∑ i, ∑ j, Real.log ‖a i - b j‖ := by
  unfold odFin
  rw [Fin.sum_univ_add]
  have hc : ∀ i : Fin d, (∑ j : Fin (d + n), if Fin.castAdd n i = j then (0 : ℝ) else
      Real.log ‖v (Fin.castAdd n i) - v j‖) =
      (∑ j, if i = j then 0 else Real.log ‖a i - a j‖) + ∑ j, Real.log ‖a i - b j‖ := by
    intro i
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro j _
      have : (Fin.castAdd n i = Fin.castAdd n j) ↔ i = j := by
        simp [Fin.ext_iff]
      simp only [this, ha]
    · apply Finset.sum_congr rfl
      intro j _
      have : ¬ (Fin.castAdd n i = Fin.natAdd d j) := by
        simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        omega
      rw [if_neg this, ha, hb]
  have hn : ∀ j : Fin n, (∑ k : Fin (d + n), if Fin.natAdd d j = k then (0 : ℝ) else
      Real.log ‖v (Fin.natAdd d j) - v k‖) =
      (∑ i, Real.log ‖b j - a i‖) + ∑ k, if j = k then 0 else Real.log ‖b j - b k‖ := by
    intro j
    rw [Fin.sum_univ_add]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      have : ¬ (Fin.natAdd d j = Fin.castAdd n i) := by
        simp only [Fin.ext_iff, Fin.val_castAdd, Fin.val_natAdd]
        omega
      rw [if_neg this, ha, hb]
    · apply Finset.sum_congr rfl
      intro k _
      have : (Fin.natAdd d j = Fin.natAdd d k) ↔ j = k := by
        simp [Fin.ext_iff]
      simp only [this, hb]
  simp_rw [hc, hn, Finset.sum_add_distrib]
  have hswap : (∑ j : Fin n, ∑ i : Fin d, Real.log ‖b j - a i‖) =
      ∑ i, ∑ j, Real.log ‖a i - b j‖ := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl
      (fun j _ => by rw [norm_sub_rev]))
  rw [hswap]
  ring

theorem xR_castAdd {m : ℕ} (S : Finset ℕ) (R : Fin m → ℕ) (Z : Fin (m - S.card) → ℂ)
    (i : Fin (m - S.card)) : xR S R Z (Fin.castAdd m i) = -Z i := by
  unfold xR
  rw [dif_pos (by simp)]
  rfl

theorem xR_natAdd {m : ℕ} (S : Finset ℕ) (R : Fin m → ℕ) (Z : Fin (m - S.card) → ℂ)
    (j : Fin m) : xR S R Z (Fin.natAdd (m - S.card) j) = (R j : ℂ) := by
  unfold xR
  rw [dif_neg (by simp)]
  congr 2
  ext
  simp

/-! ## Reindexing the concrete blocks -/

section Concrete

variable (C : FiniteConfiguration)

def natC (p : ℕ) : ℂ := (p : ℂ)

def Zc (a : Fin C.contourCount) : ℂ := Complex.ofReal (C.m : ℝ) * C.contour a

theorem Rs_injective : Function.Injective (Rs C) :=
  orderedElem_cast_injective C.frequency C.frequency_card

theorem Rs_mem (i : Fin C.m) : Rs C i ∈ C.frequency := orderedElem_mem' _ _

theorem cast_injective' : Function.Injective
    (fun i : Fin (C.m - C.pinned.card) => Fin.cast (contourCount_eq' C) i) :=
  Fin.cast_injective _

theorem univ_card' : (Finset.univ : Finset (Fin C.contourCount)).card =
    C.m - C.pinned.card := by
  rw [Finset.card_univ, Fintype.card_fin, contourCount_eq']

theorem E_freqWeight :
    (∑ i : Fin C.m, Real.log (frequencyWeightReal (C.m / 2) (Rs C i))) =
      ∑ r ∈ C.frequency, Real.log (frequencyWeightReal (C.m / 2) r) :=
  sum_reindex (Rs C) (Rs_injective C) C.frequency (Rs_mem C) C.frequency_card
    (fun r => Real.log (frequencyWeightReal (C.m / 2) r))

theorem E_entire :
    (∑ i : Fin (C.m - C.pinned.card), Real.log ‖p0Entire (C.m / 2) (Zs C i)‖) =
      ∑ a : Fin C.contourCount,
        Real.log ‖p0Entire (C.m / 2) (Complex.ofReal (C.m : ℝ) * C.contour a)‖ :=
  sum_reindex (fun i => Fin.cast (contourCount_eq' C) i) (cast_injective' C) Finset.univ
    (fun _ => Finset.mem_univ _) (univ_card' C)
    (fun a => Real.log ‖p0Entire (C.m / 2) (Complex.ofReal (C.m : ℝ) * C.contour a)‖)

theorem E_odL :
    odFin (xL C.pinned (pinned_subset_Iset' C)) =
      odSet (Iset C.m \ C.pinned) natC :=
  odFin_reindex _ (orderedElem_cast_injective _ (Ic_card C.pinned (pinned_subset_Iset' C)))
    _ (fun i => orderedElem_mem' _ _) (Ic_card C.pinned (pinned_subset_Iset' C)) natC

theorem E_odZ :
    odFin (fun j => -Zs C j) = odSet Finset.univ (fun a => -Zc C a) :=
  odFin_reindex (fun i => Fin.cast (contourCount_eq' C) i) (cast_injective' C) Finset.univ
    (fun _ => Finset.mem_univ _) (univ_card' C) (fun a => -Zc C a)

theorem E_crossL :
    (∑ i, ∑ j, Real.log ‖xL C.pinned (pinned_subset_Iset' C) i + -Zs C j‖) =
      ∑ p ∈ Iset C.m \ C.pinned, ∑ a, Real.log ‖natC p + -Zc C a‖ :=
  sum_sum_reindex _ (orderedElem_cast_injective _ (Ic_card C.pinned (pinned_subset_Iset' C)))
    _ (fun i => orderedElem_mem' _ _) (Ic_card C.pinned (pinned_subset_Iset' C))
    (fun i => Fin.cast (contourCount_eq' C) i) (cast_injective' C) Finset.univ
    (fun _ => Finset.mem_univ _) (univ_card' C)
    (fun p a => Real.log ‖natC p + -Zc C a‖)

theorem rowIndex_injective (m : ℕ) : Function.Injective (rowIndex m) := by
  intro i j h
  apply Fin.ext
  simp only [rowIndex] at h
  omega

theorem rowIndex_mem (m : ℕ) (i : Fin m) : rowIndex m i ∈ Iset m :=
  Finset.mem_image_of_mem _ (Finset.mem_univ i)

theorem E_odM :
    odFin (fun i : Fin C.m => ((rowIndex C.m i : ℕ) : ℂ)) = odSet (Iset C.m) natC :=
  odFin_reindex (rowIndex C.m) (rowIndex_injective C.m) (Iset C.m) (rowIndex_mem C.m)
    (Iset_card C.m) natC

theorem E_odR :
    odFin (fun i => ((Rs C i : ℕ) : ℂ)) = odSet C.frequency natC :=
  odFin_reindex (Rs C) (Rs_injective C) C.frequency (Rs_mem C) C.frequency_card natC

theorem E_crossM :
    (∑ i : Fin C.m, ∑ j : Fin C.m,
        Real.log ‖((rowIndex C.m i : ℕ) : ℂ) + (Rs C j : ℂ)‖) =
      ∑ p ∈ Iset C.m, ∑ r ∈ C.frequency, Real.log ‖natC p + natC r‖ :=
  sum_sum_reindex (rowIndex C.m) (rowIndex_injective C.m) (Iset C.m) (rowIndex_mem C.m)
    (Iset_card C.m) (Rs C) (Rs_injective C) C.frequency (Rs_mem C) C.frequency_card
    (fun p r => Real.log ‖natC p + natC r‖)

theorem E_odXR :
    odFin (xR C.pinned (Rs C) (Zs C)) =
      odSet Finset.univ (fun a => -Zc C a) + odSet C.frequency natC +
        2 * ∑ a, ∑ r ∈ C.frequency, Real.log ‖-Zc C a - natC r‖ := by
  rw [odFin_append (xR C.pinned (Rs C) (Zs C)) (fun j => -Zs C j)
    (fun i => ((Rs C i : ℕ) : ℂ)) (xR_castAdd _ _ _) (xR_natAdd _ _ _), E_odZ, E_odR]
  congr 2
  exact sum_sum_reindex (fun i => Fin.cast (contourCount_eq' C) i) (cast_injective' C)
    Finset.univ (fun _ => Finset.mem_univ _) (univ_card' C)
    (Rs C) (Rs_injective C) C.frequency (Rs_mem C) C.frequency_card
    (fun a r => Real.log ‖-Zc C a - natC r‖)

theorem E_odYR :
    odFin (yR C.pinned C.four_dvd_m (pinned_subset_Iset' C)) =
      odSet (Jset C.m \ C.pinned) natC :=
  odFin_reindex _ (orderedElem_cast_injective _
      (Jc_card C.pinned C.four_dvd_m (pinned_subset_Iset' C)))
    _ (fun i => orderedElem_mem' _ _) (Jc_card C.pinned C.four_dvd_m (pinned_subset_Iset' C))
    natC

theorem E_crossR :
    (∑ i, ∑ j, Real.log ‖xR C.pinned (Rs C) (Zs C) i +
        yR C.pinned C.four_dvd_m (pinned_subset_Iset' C) j‖) =
      (∑ a, ∑ q ∈ Jset C.m \ C.pinned, Real.log ‖-Zc C a + natC q‖) +
        ∑ r ∈ C.frequency, ∑ q ∈ Jset C.m \ C.pinned, Real.log ‖natC r + natC q‖ := by
  rw [Fin.sum_univ_add]
  simp_rw [xR_castAdd, xR_natAdd]
  have hJ := Jc_card C.pinned C.four_dvd_m (pinned_subset_Iset' C)
  congr 1
  · exact sum_sum_reindex (fun i => Fin.cast (contourCount_eq' C) i) (cast_injective' C)
      Finset.univ (fun _ => Finset.mem_univ _) (univ_card' C)
      _ (orderedElem_cast_injective _ hJ) _ (fun i => orderedElem_mem' _ _) hJ
      (fun a q => Real.log ‖-Zc C a + natC q‖)
  · exact sum_sum_reindex (Rs C) (Rs_injective C) C.frequency (Rs_mem C) C.frequency_card
      _ (orderedElem_cast_injective _ hJ) _ (fun i => orderedElem_mem' _ _) hJ
      (fun r q => Real.log ‖natC r + natC q‖)

end Concrete

/-! ## Counting and scaling -/

theorem count_offdiag {α : Type*} [DecidableEq α] (T : Finset α) (c : ℝ) :
    (∑ p ∈ T, ∑ q ∈ T, if p = q then (0 : ℝ) else c) =
      ((T.card : ℝ) * T.card - T.card) * c := by
  have h : ∀ p ∈ T, (∑ q ∈ T, if p = q then (0 : ℝ) else c) = (T.card : ℝ) * c - c := by
    intro p hp
    have e : ∀ q, (if p = q then (0 : ℝ) else c) = c - if p = q then c else 0 := by
      intro q; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq, if_pos hp, Finset.sum_const, nsmul_eq_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  ring

theorem count_field {α : Type*} [DecidableEq α] (S A : Finset α) (hSA : S ⊆ A) (c : ℝ) :
    (∑ p ∈ S, ∑ q ∈ A, if q = p then (0 : ℝ) else c) =
      ((S.card : ℝ) * A.card - S.card) * c := by
  have h : ∀ p ∈ S, (∑ q ∈ A, if q = p then (0 : ℝ) else c) = (A.card : ℝ) * c - c := by
    intro p hp
    have e : ∀ q, (if q = p then (0 : ℝ) else c) = c - if q = p then c else 0 := by
      intro q; split_ifs <;> ring
    simp_rw [e]
    rw [Finset.sum_sub_distrib, Finset.sum_ite_eq', if_pos (hSA hp), Finset.sum_const,
      nsmul_eq_mul]
  rw [Finset.sum_congr rfl h, Finset.sum_const, nsmul_eq_mul]
  ring

theorem log_norm_ofReal_mul {M : ℝ} (hM : 0 < M) {w : ℂ} (hw : w ≠ 0) :
    Real.log ‖Complex.ofReal M * w‖ = Real.log M + Real.log ‖w‖ := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hM,
    Real.log_mul hM.ne' (norm_ne_zero_iff.mpr hw)]

theorem natC_sub_eq {M : ℝ} (hM : 0 < M) (p q : ℕ) :
    natC p - natC q = Complex.ofReal M *
      ((((p : ℝ) / M : ℝ) : ℂ) - (((q : ℝ) / M : ℝ) : ℂ)) := by
  unfold natC
  have : (M : ℂ) ≠ 0 := by exact_mod_cast hM.ne'
  push_cast
  field_simp

theorem norm_real_sub (x y : ℝ) : ‖((x : ℝ) : ℂ) - ((y : ℝ) : ℂ)‖ = |x - y| := by
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]

/-- Scaled off-diagonal sum on lattice sites. -/
theorem odSet_natC (m : ℕ) (hm : 0 < m) (T : Finset ℕ) :
    odSet T natC = latticeOffDiagonalLogSum m T +
      ((T.card : ℝ) * T.card - T.card) * Real.log (m : ℝ) := by
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  unfold odSet latticeOffDiagonalLogSum
  rw [← count_offdiag, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : p = q
  · simp [hpq]
  · rw [if_neg hpq, if_neg hpq, if_neg hpq, natC_sub_eq hM]
    have hne : (((p : ℝ) / (m : ℝ) : ℝ) : ℂ) - (((q : ℝ) / (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hpq
      have h' := Complex.ofReal_injective h
      field_simp at h'
      exact_mod_cast h'
    rw [log_norm_ofReal_mul hM hne, norm_real_sub]
    ring

/-- Scaled pinned field sums. -/
theorem field_natC (m : ℕ) (hm : 0 < m) (S A : Finset ℕ) (hSA : S ⊆ A) :
    (∑ p ∈ S, ∑ q ∈ A, if q = p then (0 : ℝ) else Real.log ‖natC p - natC q‖) =
      (∑ p ∈ S, ∑ q ∈ A, if q = p then (0 : ℝ) else
          Real.log |(p : ℝ) / (m : ℝ) - (q : ℝ) / (m : ℝ)|) +
        ((S.card : ℝ) * A.card - S.card) * Real.log (m : ℝ) := by
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  rw [← count_field S A hSA, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro q _
  by_cases hpq : q = p
  · simp [hpq]
  · rw [if_neg hpq, if_neg hpq, if_neg hpq, natC_sub_eq hM]
    have hne : (((p : ℝ) / (m : ℝ) : ℝ) : ℂ) - (((q : ℝ) / (m : ℝ) : ℝ) : ℂ) ≠ 0 := by
      rw [sub_ne_zero]
      intro h
      apply hpq
      have h' := Complex.ofReal_injective h
      field_simp at h'
      exact_mod_cast h'.symm
    rw [log_norm_ofReal_mul hM hne, norm_real_sub]
    ring

/-- Scaled sums of lattice pairs `log (p + r)`. -/
theorem cross_natC (m : ℕ) (hm : 0 < m) (T U : Finset ℕ)
    (hpos : ∀ p ∈ T, ∀ r ∈ U, 0 < p + r) :
    (∑ p ∈ T, ∑ r ∈ U, Real.log ‖natC p + natC r‖) =
      (∑ p ∈ T, ∑ r ∈ U, Real.log ((p : ℝ) / (m : ℝ) + (r : ℝ) / (m : ℝ))) +
        (T.card : ℝ) * U.card * Real.log (m : ℝ) := by
  have hM : (0 : ℝ) < m := by exact_mod_cast hm
  have e : ∀ p ∈ T, ∀ r ∈ U, Real.log ‖natC p + natC r‖ =
      Real.log ((p : ℝ) / (m : ℝ) + (r : ℝ) / (m : ℝ)) + Real.log (m : ℝ) := by
    intro p hp r hr
    have h0 : (0 : ℝ) < (p : ℝ) + r := by exact_mod_cast hpos p hp r hr
    have h1 : natC p + natC r = (((p : ℝ) + r : ℝ) : ℂ) := by unfold natC; push_cast; ring
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_pos h0]
    have h3 : 0 < (p : ℝ) / m + (r : ℝ) / m := by rw [← add_div]; positivity
    have h2 : (p : ℝ) + r = ((p : ℝ) / m + (r : ℝ) / m) * m := by field_simp
    rw [h2, Real.log_mul h3.ne' hM.ne']
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun r hr => e p hp r hr))]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul]
  ring

theorem swap_add_log (T U : Finset ℕ) (m : ℕ) :
    (∑ p ∈ T, ∑ r ∈ U, Real.log ((p : ℝ) / (m : ℝ) + (r : ℝ) / (m : ℝ))) =
      ∑ r ∈ U, ∑ p ∈ T, Real.log ((r : ℝ) / (m : ℝ) + (p : ℝ) / (m : ℝ)) := by
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl (fun r _ => Finset.sum_congr rfl (fun p _ => by rw [add_comm]))

section Concrete2

variable (C : FiniteConfiguration)

theorem m_pos' : 0 < C.m := by have := C.m_ge_eight; omega

theorem dPlus_pos' : (0 : ℝ) < dPlus := by norm_num [dPlus]
theorem dMinus_pos' : (0 : ℝ) < dMinus := by norm_num [dMinus]

/-- Clearance from the fixed grid. -/
theorem grid_ne (a : Fin C.contourCount) (q : ℕ) (hq : q ∈ Jset C.m) :
    C.contour a - (((q : ℝ) / (C.m : ℝ) : ℝ) : ℂ) ≠ 0 := by
  have hM : (0 : ℝ) < C.m := by exact_mod_cast m_pos' C
  have hq' : q < 2 * C.m := Finset.mem_range.mp hq
  have hx : (q : ℝ) / C.m ∈ Set.Icc (0 : ℝ) 2 := by
    constructor
    · positivity
    · rw [div_le_iff₀ hM]
      have : (q : ℝ) ≤ 2 * C.m := by exact_mod_cast hq'.le
      linarith
  have h := mixedCellClearance_full.1 (C.contour a) (C.contour_mem a) _ hx
  intro h0
  rw [h0, norm_zero] at h
  linarith [dPlus_pos']

theorem freq_ne (a : Fin C.contourCount) (r : ℕ) (hr : r ∈ C.frequency) :
    C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ) ≠ 0 := by
  have hM : (0 : ℝ) < C.m := by exact_mod_cast m_pos' C
  have hlow := C.frequency_lower r hr
  have h2 : C.m ≤ 2 * r := by omega
  have ht : (1 / 2 : ℝ) ≤ (r : ℝ) / C.m := by
    rw [le_div_iff₀ hM]
    have : (C.m : ℝ) ≤ 2 * r := by exact_mod_cast h2
    linarith
  have h := mixedCellClearance_full.2 (C.contour a) (C.contour_mem a) _ ht
  intro h0
  rw [h0, norm_zero] at h
  linarith [dMinus_pos']

theorem F_crossL (T : Finset ℕ) (hT : T ⊆ Jset C.m) :
    (∑ p ∈ T, ∑ a, Real.log ‖natC p + -Zc C a‖) =
      (∑ p ∈ T, ∑ a, Real.log ‖(((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖) +
        (T.card : ℝ) * C.contourCount * Real.log (C.m : ℝ) := by
  have hM : (0 : ℝ) < C.m := by exact_mod_cast m_pos' C
  have e : ∀ p ∈ T, ∀ a : Fin C.contourCount, Real.log ‖natC p + -Zc C a‖ =
      Real.log ‖(((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖ + Real.log (C.m : ℝ) := by
    intro p hp a
    have hw : (((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a ≠ 0 := by
      intro h0; apply grid_ne C a p (hT hp); rw [← neg_sub, h0, neg_zero]
    have h1 : natC p + -Zc C a = Complex.ofReal (C.m : ℝ) *
        ((((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a) := by
      unfold natC Zc
      have : (C.m : ℂ) ≠ 0 := by exact_mod_cast (m_pos' C).ne'
      push_cast
      field_simp
      ring
    rw [h1, log_norm_ofReal_mul hM hw]
    ring
  rw [Finset.sum_congr rfl (fun p hp => Finset.sum_congr rfl (fun a _ => e p hp a))]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  ring

theorem F_crossR1 :
    (∑ a, ∑ r ∈ C.frequency, Real.log ‖-Zc C a - natC r‖) =
      contFreq C + (C.contourCount : ℝ) * C.m * Real.log (C.m : ℝ) := by
  have hM : (0 : ℝ) < C.m := by exact_mod_cast m_pos' C
  have e : ∀ a : Fin C.contourCount, ∀ r ∈ C.frequency, Real.log ‖-Zc C a - natC r‖ =
      Real.log ‖C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ + Real.log (C.m : ℝ) := by
    intro a r hr
    have h1 : -Zc C a - natC r = -(Complex.ofReal (C.m : ℝ) *
        (C.contour a + (((r : ℝ) / (C.m : ℝ) : ℝ) : ℂ))) := by
      unfold natC Zc
      have : (C.m : ℂ) ≠ 0 := by exact_mod_cast (m_pos' C).ne'
      push_cast
      field_simp
      ring
    rw [h1, norm_neg, log_norm_ofReal_mul hM (freq_ne C a r hr)]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun r hr => e a r hr))]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin, C.frequency_card]
  unfold contFreq
  ring

theorem F_crossR2 (T : Finset ℕ) (hT : T ⊆ Jset C.m) :
    (∑ a, ∑ q ∈ T, Real.log ‖-Zc C a + natC q‖) =
      (∑ a, ∑ q ∈ T, Real.log ‖C.contour a - (((q : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖) +
        (C.contourCount : ℝ) * T.card * Real.log (C.m : ℝ) := by
  have hM : (0 : ℝ) < C.m := by exact_mod_cast m_pos' C
  have e : ∀ a : Fin C.contourCount, ∀ q ∈ T, Real.log ‖-Zc C a + natC q‖ =
      Real.log ‖C.contour a - (((q : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ + Real.log (C.m : ℝ) := by
    intro a q hq
    have h1 : -Zc C a + natC q = -(Complex.ofReal (C.m : ℝ) *
        (C.contour a - (((q : ℝ) / (C.m : ℝ) : ℝ) : ℂ))) := by
      unfold natC Zc
      have : (C.m : ℂ) ≠ 0 := by exact_mod_cast (m_pos' C).ne'
      push_cast
      field_simp
      ring
    rw [h1, norm_neg, log_norm_ofReal_mul hM (grid_ne C a q (hT hq))]
    ring
  rw [Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl (fun q hq => e a q hq))]
  simp_rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, Finset.card_univ,
    Fintype.card_fin]
  ring

theorem F_odZ (hinj : ∀ a b : Fin C.contourCount, a ≠ b → C.contour a ≠ C.contour b) :
    odSet Finset.univ (fun a => -Zc C a) =
      contCont C + ((C.contourCount : ℝ) * C.contourCount - C.contourCount) *
        Real.log (C.m : ℝ) := by
  have hM : (0 : ℝ) < C.m := by exact_mod_cast m_pos' C
  have hc := count_offdiag (Finset.univ : Finset (Fin C.contourCount)) (Real.log (C.m : ℝ))
  rw [Finset.card_univ, Fintype.card_fin] at hc
  rw [← hc]
  unfold odSet contCont
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro a _
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro b _
  by_cases hab : a = b
  · simp [hab]
  · rw [if_neg hab, if_neg hab, if_neg hab]
    have h1 : -Zc C a - -Zc C b = -(Complex.ofReal (C.m : ℝ) *
        (C.contour a - C.contour b)) := by
      unfold Zc; ring
    rw [h1, norm_neg, log_norm_ofReal_mul hM (sub_ne_zero.mpr (hinj a b hab))]
    ring

end Concrete2

/-! ## The identity -/

section Final

variable (C : FiniteConfiguration)

theorem natC_add_negZc (p : ℕ) (a : Fin C.contourCount) :
    natC p + -Zc C a = Complex.ofReal (C.m : ℝ) *
      ((((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a) := by
  unfold natC Zc
  have : (C.m : ℂ) ≠ 0 := by exact_mod_cast (m_pos' C).ne'
  push_cast
  field_simp
  ring

theorem natC_add_negZc_ne (p : ℕ) (hp : p ∈ Jset C.m) (a : Fin C.contourCount) :
    natC p + -Zc C a ≠ 0 := by
  rw [natC_add_negZc]
  apply mul_ne_zero
  · exact_mod_cast (m_pos' C).ne'
  · intro h0; apply grid_ne C a p hp; rw [← neg_sub, h0, neg_zero]

theorem hxyL_conf (i : Fin (C.m - C.pinned.card)) (j : Fin (C.m - C.pinned.card)) :
    xL C.pinned (pinned_subset_Iset' C) i + -Zs C j ≠ 0 := by
  have hmem := orderedElem_mem' (Iset C.m \ C.pinned)
    (Fin.cast (Ic_card C.pinned (pinned_subset_Iset' C)).symm i)
  have hJ : orderedElem (Iset C.m \ C.pinned)
      (Fin.cast (Ic_card C.pinned (pinned_subset_Iset' C)).symm i) ∈ Jset C.m :=
    Iset_subset_Jset C.m C.four_dvd_m (Finset.mem_sdiff.mp hmem).1
  exact natC_add_negZc_ne C _ hJ (Fin.cast (contourCount_eq' C) j)

theorem hxyR_conf (i : Fin (C.m - C.pinned.card + C.m))
    (j : Fin (C.m - C.pinned.card + C.m)) :
    xR C.pinned (Rs C) (Zs C) i + yR C.pinned C.four_dvd_m (pinned_subset_Iset' C) j ≠ 0 := by
  have hmem := orderedElem_mem' (Jset C.m \ C.pinned)
    (Fin.cast (Jc_card C.pinned C.four_dvd_m (pinned_subset_Iset' C)).symm j)
  set q := orderedElem (Jset C.m \ C.pinned)
    (Fin.cast (Jc_card C.pinned C.four_dvd_m (pinned_subset_Iset' C)).symm j) with hq
  have hqJ : q ∈ Jset C.m := (Finset.mem_sdiff.mp hmem).1
  have hy : yR C.pinned C.four_dvd_m (pinned_subset_Iset' C) j = natC q := rfl
  rw [hy]
  refine Fin.addCases (fun k => ?_) (fun k => ?_) i
  · rw [xR_castAdd]
    intro h0
    apply natC_add_negZc_ne C q hqJ (Fin.cast (contourCount_eq' C) k)
    rw [← h0]
    unfold Zs Zc
    ring
  · rw [xR_natAdd]
    intro h0
    have h1 : ((Rs C k + q : ℕ) : ℂ) = 0 := by unfold natC at h0; push_cast; exact h0
    have h2 : Rs C k + q = 0 := by exact_mod_cast h1
    have := Rs_pos C k
    omega

theorem sum_sum_sdiff {β : Type*} (U : Finset β) (A S : Finset ℕ) (hSA : S ⊆ A)
    (f : β → ℕ → ℝ) :
    (∑ a ∈ U, ∑ q ∈ A \ S, f a q) = (∑ a ∈ U, ∑ q ∈ A, f a q) - ∑ a ∈ U, ∑ q ∈ S, f a q := by
  rw [← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl (fun a _ => sum_sdiff_sub A S hSA (f a))

theorem logQIdentity_conf (hQ : 0 < literalConfigQWeight C) :
    Real.log (literalConfigQWeight C) =
      oneBody C + fixedV C + pinPin C + 2 * pinCont C + contCont C + freqFreq C +
        pinFreq C + contFreq C - pinField C - contField C - freqField C -
        (2 * (C.m : ℝ) + 2 * (C.contourCount : ℝ)) * Real.log (C.m : ℝ) := by
  have hdist := (qPosFacts' C hQ).1
  have hm := m_pos' C
  have hSI := pinned_subset_Iset' C
  have hSJ : C.pinned ⊆ Jset C.m := hSI.trans (Iset_subset_Jset C.m C.four_dvd_m)
  have hIJ : Iset C.m ⊆ Jset C.m := Iset_subset_Jset C.m C.four_dvd_m
  have hfpos : ∀ r ∈ C.frequency, 0 < r := by
    intro r hr; have := C.frequency_lower r hr; omega
  rw [literal_eq] at hQ ⊢
  have hlog := log_contourQValue C.pinned C.four_dvd_m hSI (Rs C) (Rs_strictMono C) (Zs C)
    hQ (Rs_pos C) (hxyL_conf C) (hxyR_conf C)
  rw [E_freqWeight, E_entire, E_odL, E_odZ, E_crossL, E_odM, E_odR, E_crossM, E_odXR,
    E_odYR, E_crossR] at hlog
  rw [odSet_sdiff _ _ hSI, odSet_sdiff _ _ hSJ, sum_sdiff_sub _ _ hSI,
    sum_sum_sdiff _ _ _ hSJ, sum_sum_sdiff _ _ _ hSJ] at hlog
  rw [odSet_natC C.m hm, odSet_natC C.m hm, odSet_natC C.m hm, odSet_natC C.m hm,
    field_natC C.m hm _ _ hSI, field_natC C.m hm _ _ hSJ,
    F_crossL C _ hIJ, F_crossL C _ hSJ, F_crossR1, F_crossR2 C _ (subset_refl _),
    F_crossR2 C _ hSJ,
    cross_natC C.m hm _ _ (fun p _ r hr => by have := hfpos r hr; omega),
    cross_natC C.m hm _ _ (fun p hp r _ => by have := hfpos p hp; omega),
    cross_natC C.m hm _ _ (fun p hp r _ => by have := hfpos p hp; omega),
    F_odZ C hdist] at hlog
  have hIP : Iset C.m = pinnedUniverse C.m := by
    rw [Iset_eq_paper_interval C.m C.four_dvd_m]; rfl
  have hJF : Jset C.m = frequencyUniverse C.m := rfl
  have hJc : (Jset C.m).card = 2 * C.m := Finset.card_range _
  rw [Iset_card, hJc, C.frequency_card] at hlog
  rw [hIP, hJF] at hlog
  have hpcA : pinCont C = ∑ p ∈ C.pinned, ∑ a : Fin C.contourCount,
      Real.log ‖(((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖ := rfl
  have hpcB : (∑ a : Fin C.contourCount, ∑ q ∈ C.pinned,
      Real.log ‖C.contour a - (((q : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖) = pinCont C := by
    rw [hpcA, Finset.sum_comm]
    exact Finset.sum_congr rfl (fun p _ => Finset.sum_congr rfl
      (fun a _ => by rw [norm_sub_rev]))
  have hcI : (∑ p ∈ pinnedUniverse C.m, ∑ a : Fin C.contourCount,
      Real.log ‖(((p : ℝ) / (C.m : ℝ) : ℝ) : ℂ) - C.contour a‖) =
      ∑ a : Fin C.contourCount, ∑ i ∈ pinnedUniverse C.m,
        Real.log ‖C.contour a - (((i : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ := by
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl (fun a _ => Finset.sum_congr rfl
      (fun p _ => by rw [norm_sub_rev]))
  have hpf : pinFreq C = ∑ r ∈ C.frequency, ∑ p ∈ C.pinned,
      Real.log ((r : ℝ) / (C.m : ℝ) + (p : ℝ) / (C.m : ℝ)) := swap_add_log _ _ _
  rw [← hpcA, hpcB, hcI, swap_add_log (pinnedUniverse C.m) C.frequency C.m, ← hpf] at hlog
  have hpinField : pinField C =
      (∑ s ∈ C.pinned, ∑ i ∈ pinnedUniverse C.m,
        if i = s then (0 : ℝ) else Real.log |(s : ℝ) / (C.m : ℝ) - (i : ℝ) / (C.m : ℝ)|) +
      ∑ s ∈ C.pinned, ∑ j ∈ frequencyUniverse C.m,
        if j = s then (0 : ℝ) else Real.log |(s : ℝ) / (C.m : ℝ) - (j : ℝ) / (C.m : ℝ)| := by
    unfold pinField; rw [Finset.sum_add_distrib]
  have hcontField : contField C =
      (∑ a : Fin C.contourCount, ∑ i ∈ pinnedUniverse C.m,
        Real.log ‖C.contour a - (((i : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖) +
      ∑ a : Fin C.contourCount, ∑ j ∈ frequencyUniverse C.m,
        Real.log ‖C.contour a - (((j : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖ := by
    unfold contField; rw [Finset.sum_add_distrib]
  have hfreqField : freqField C =
      (∑ r ∈ C.frequency, ∑ i ∈ pinnedUniverse C.m,
        Real.log ((r : ℝ) / (C.m : ℝ) + (i : ℝ) / (C.m : ℝ))) +
      ∑ r ∈ C.frequency, ∑ j ∈ frequencyUniverse C.m,
        Real.log ((r : ℝ) / (C.m : ℝ) + (j : ℝ) / (C.m : ℝ)) := by
    unfold freqField fixedLatticeLogSum; rw [Finset.sum_add_distrib]
  have hbal : (C.pinned.card : ℝ) + C.contourCount = C.m := by
    have := C.mass_balance
    rw [add_comm]; exact_mod_cast this
  have hc2 : ((2 * C.m : ℕ) : ℝ) = 2 * (C.m : ℝ) := by push_cast; ring
  rw [hc2] at hlog
  rw [hpinField, hcontField, hfreqField]
  unfold pinPin freqFreq fixedV oneBody
  linear_combination hlog + ((C.pinned.card : ℝ) + C.contourCount - C.m + 1) *
    Real.log (C.m : ℝ) * hbal

end Final

end

end Li2Lean.P0.CellBound.LogQ

namespace Li2Lean.P0.CellBound

/-- `Q > 0` forces distinct contour points and a nonvanishing contour product. -/
theorem qPosFacts : QPosFacts := LogQ.qPosFacts'

/-- The exact expansion of `log Q` (v13 ll. 95-156). -/
theorem logQIdentity : LogQIdentity := fun C hQ => LogQ.logQIdentity_conf C hQ

end Li2Lean.P0.CellBound

#print axioms Li2Lean.P0.CellBound.logQIdentity
#print axioms Li2Lean.P0.CellBound.qPosFacts
