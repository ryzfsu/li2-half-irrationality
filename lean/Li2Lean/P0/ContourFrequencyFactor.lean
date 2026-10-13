/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.FrequencyLeaf
import Li2Lean.P0.FrequencyEllipse
import Li2Lean.P0.CauchyDeterminant

namespace Li2Lean.P0

open Finset

noncomputable section

lemma prod_orderedElem {s : Finset ℕ} {n : ℕ} (h : s.card = n)
    (f : ℕ → ℝ) :
    (∏ i : Fin n, f (orderedElem s (Fin.cast h.symm i))) =
      ∏ a ∈ s, f a := by
  classical
  let g : Fin n → ℕ := fun i => orderedElem s (Fin.cast h.symm i)
  have hg (i : Fin n) : g i = (s.orderIsoOfFin h i).val := by
    cases h
    rfl
  have hinj : Function.Injective g := by
    intro i j hij
    apply (s.orderIsoOfFin h).injective
    apply Subtype.ext
    simpa [g, hg] using hij
  have himage : (Finset.univ : Finset (Fin n)).image g = s := by
    ext a
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨i, rfl⟩
      rw [hg]
      exact (s.orderIsoOfFin h i).property
    · intro ha
      let a' : s := ⟨a, ha⟩
      refine ⟨(s.orderIsoOfFin h).symm a', ?_⟩
      rw [hg]
      exact congrArg Subtype.val ((s.orderIsoOfFin h).apply_symm_apply a')
  calc
    (∏ i : Fin n, f (g i)) =
        ∏ a ∈ (Finset.univ : Finset (Fin n)).image g, f a := by
          symm
          exact Finset.prod_image hinj.injOn
    _ = ∏ a ∈ s, f a := by rw [himage]

lemma frequencyVandermonde_image {m : ℕ} (R : Fin m → ℕ)
    (hR : StrictMono R) :
    FrequencyLeaf.frequencyVandermonde (Finset.univ.image R) =
      ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
        ((R j - R i : ℕ) : ℝ) := by
  classical
  have hinj : Function.Injective R := hR.injective
  have hlt (i j : Fin m) : R i < R j ↔ i < j := hR.lt_iff_lt
  have hIoi (i : Fin m) :
      (Finset.univ : Finset (Fin m)).filter (fun j => i < j) = Finset.Ioi i := by
    ext j
    simp
  calc
    FrequencyLeaf.frequencyVandermonde (Finset.univ.image R) =
        ∏ i : Fin m, ∏ j : Fin m,
          if R i < R j then ((R j - R i : ℕ) : ℝ) else 1 := by
            unfold FrequencyLeaf.frequencyVandermonde
            rw [Finset.prod_image hinj.injOn]
            apply Finset.prod_congr rfl
            intro i hi
            rw [Finset.prod_image hinj.injOn]
            apply Finset.prod_congr rfl
            intro j hj
            by_cases h : R i < R j
            · simp [h, Nat.cast_sub (Nat.le_of_lt h)]
            · simp [h]
    _ = ∏ i : Fin m, ∏ j : Fin m,
          if i < j then ((R j - R i : ℕ) : ℝ) else 1 := by
            simp_rw [hlt]
    _ = ∏ i : Fin m, ∏ j ∈ Finset.Ioi i,
          ((R j - R i : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro i hi
            rw [← hIoi i, Finset.prod_filter]

lemma prod_fin_image {m : ℕ} (f : Fin m → ℕ)
    (hf : Function.Injective f) (g : ℕ → ℝ) :
    (∏ i : Fin m, g (f i)) =
      ∏ r ∈ (Finset.univ : Finset (Fin m)).image f, g r := by
  classical
  symm
  exact Finset.prod_image hf.injOn

lemma frequencyWeights_eq_image {m : ℕ} (R : Fin m → ℕ)
    (hR : StrictMono R) :
    (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) =
      ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
        FrequencyLeaf.weight (m / 2) r := by
  rw [prod_fin_image R hR.injective]
  apply Finset.prod_congr rfl
  intro r hr
  simp only [frequencyWeightReal, FrequencyLeaf.weight]
  have hpow (r : ℕ) : ((1 : ℝ) / 2) ^ r = 1 / (2 : ℝ) ^ r := by
    rw [div_pow]
    norm_num
  rw [hpow]
  ring

lemma norm_vandermonde_eq_frequencyVandermonde {m : ℕ}
    (R : Fin m → ℕ) (hR : StrictMono R) :
    ‖(Matrix.vandermonde (fun i => (R i : ℂ))).det‖ =
      FrequencyLeaf.frequencyVandermonde
        ((Finset.univ : Finset (Fin m)).image R) := by
  rw [Matrix.det_vandermonde, frequencyVandermonde_image R hR]
  simp only [norm_prod]
  apply Finset.prod_congr rfl
  intro i hi
  apply Finset.prod_congr rfl
  intro j hj
  have hij : i < j := Finset.mem_Ioi.mp hj
  rw [← Nat.cast_sub (Nat.le_of_lt (hR hij))]
  simp

lemma contourQJComplement_card {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) :
    (Jset m \ S).card = (m - S.card) + m := by
  have hSJ : S ⊆ Jset m := hSI.trans (Iset_subset_Jset m h4)
  have hScard : S.card ≤ m := by
    rw [← Iset_card m]
    exact Finset.card_le_card hSI
  rw [Finset.card_sdiff_of_subset hSJ]
  simp [Jset, Finset.card_range]
  omega

def contourQRightRows {m : ℕ} (S : Finset ℕ)
    (R : Fin m → ℕ) (Z : Fin (m - S.card) → ℂ)
    : Fin ((m - S.card) + m) → ℂ :=
  Fin.append (fun i => -Z i) (fun i => (R i : ℂ))

lemma contourQRightRows_piecewise {m : ℕ} (S : Finset ℕ)
    (R : Fin m → ℕ) (Z : Fin (m - S.card) → ℂ)
    (i : Fin ((m - S.card) + m)) :
    contourQRightRows S R Z i =
      if hi : i.val < m - S.card then -Z ⟨i.val, hi⟩
      else (R ⟨i.val - (m - S.card), by omega⟩ : ℂ) := by
  by_cases hi : i.val < m - S.card
  · have h : i = Fin.castAdd m ⟨i.val, hi⟩ := by
      apply Fin.ext
      rfl
    have hfirst : contourQRightRows S R Z i =
        contourQRightRows S R Z (Fin.castAdd m ⟨i.val, hi⟩) := congrArg _ h
    calc
      contourQRightRows S R Z i =
          contourQRightRows S R Z (Fin.castAdd m ⟨i.val, hi⟩) := hfirst
      _ = -Z ⟨i.val, hi⟩ := by simp only [contourQRightRows, Fin.append_left]
      _ = if h : i.val < m - S.card then -Z ⟨i.val, h⟩
          else (R ⟨i.val - (m - S.card), by omega⟩ : ℂ) := by simp [hi]
  · have h : i = Fin.natAdd (m - S.card)
        ⟨i.val - (m - S.card), by omega⟩ := by
      apply Fin.ext
      simp
      omega
    have hfirst : contourQRightRows S R Z i = contourQRightRows S R Z
        (Fin.natAdd (m - S.card) ⟨i.val - (m - S.card), by omega⟩) := congrArg _ h
    calc
      contourQRightRows S R Z i = contourQRightRows S R Z
          (Fin.natAdd (m - S.card) ⟨i.val - (m - S.card), by omega⟩) := hfirst
      _ = (R ⟨i.val - (m - S.card), by omega⟩ : ℂ) := by
          simp only [contourQRightRows, Fin.append_right]
      _ = if h : i.val < m - S.card then -Z ⟨i.val, h⟩
          else (R ⟨i.val - (m - S.card), by omega⟩ : ℂ) := by simp [hi]

noncomputable def contourQRightColumns {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (j : Fin ((m - S.card) + m)) : ℂ := by
  classical
  let Jc := Jset m \ S
  have hJc : Jc.card = (m - S.card) + m := by
    exact contourQJComplement_card S h4 hSI
  exact ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ)

lemma orderedElem_cast_injective {s : Finset ℕ} {n : ℕ}
    (h : s.card = n) :
    Function.Injective (fun i : Fin n => orderedElem s (Fin.cast h.symm i)) := by
  have hg (i : Fin n) :
      orderedElem s (Fin.cast h.symm i) = (s.orderIsoOfFin h i).val := by
    cases h
    rfl
  intro i j hij
  apply (s.orderIsoOfFin h).injective
  apply Subtype.ext
  calc
    (s.orderIsoOfFin h i).val = orderedElem s (Fin.cast h.symm i) := (hg i).symm
    _ = orderedElem s (Fin.cast h.symm j) := hij
    _ = (s.orderIsoOfFin h j).val := hg j

lemma contourQRightColumns_injective {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) :
    Function.Injective (contourQRightColumns S h4 hSI) := by
  let Jc := Jset m \ S
  have hJc : Jc.card = (m - S.card) + m := contourQJComplement_card S h4 hSI
  intro i j hij
  have hval :
      orderedElem Jc (Fin.cast hJc.symm i) =
        orderedElem Jc (Fin.cast hJc.symm j) := by
    have hij' :
        ((orderedElem Jc (Fin.cast hJc.symm i) : ℕ) : ℂ) =
          ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ) := by
      simpa only [contourQRightColumns] using hij
    exact_mod_cast hij'
  exact orderedElem_cast_injective hJc hval

lemma Iset_eq_frequency_I_m {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m) :
    Iset m = FrequencyLeaf.I_m m := by
  rw [Iset_eq_paper_interval m h4]
  rcases h4 with ⟨q, hq⟩
  have hqpos : 0 < q := by omega
  have hmq : m / 4 = q := by rw [hq]; omega
  have hdiv : 5 * m / 4 = 5 * (m / 4) := by
    rw [hq]
    have hmul : 5 * (4 * q) = 4 * (5 * q) := by omega
    rw [hmul]
    omega
  ext a
  simp only [Finset.mem_Ico, FrequencyLeaf.I_m, Finset.mem_Icc]
  rw [hmq, hdiv, hmq]
  omega

lemma norm_fin_prod {n : ℕ} (f : Fin n → ℂ) :
    ‖∏ i : Fin n, f i‖ = ∏ i : Fin n, ‖f i‖ :=
  norm_prod (Finset.univ : Finset (Fin n)) f

lemma norm_cauchy_determinant {n : ℕ} (x y : Fin n → ℂ)
    (hy : Function.Injective y) (hxy : ∀ i j, x i + y j ≠ 0) :
    ‖(Matrix.of (fun (i j : Fin n) => (x i + y j)⁻¹)).det‖ =
      ‖(Matrix.vandermonde x).det‖ * ‖(Matrix.vandermonde y).det‖ /
        (∏ i : Fin n, ∏ j : Fin n, ‖x i + y j‖) := by
  rw [CauchyDeterminant.cauchy_det_eq_vandermonde_mul_inv_denominator
    x y hy hxy]
  rw [norm_mul, norm_mul, norm_inv]
  simp_rw [norm_fin_prod]
  ring

lemma norm_vandermonde_append {d m : ℕ} (x : Fin d → ℂ) (r : Fin m → ℂ) :
    ‖(Matrix.vandermonde (Fin.append x r)).det‖ =
      ‖(Matrix.vandermonde x).det‖ * ‖(Matrix.vandermonde r).det‖ *
        (∏ i : Fin d, ∏ j : Fin m, ‖r j - x i‖) := by
  rw [Matrix.det_vandermonde, Matrix.det_vandermonde, Matrix.det_vandermonde,
    CauchyDeterminant.vandermonde_append_product]
  rw [norm_mul, norm_mul]
  simp_rw [norm_fin_prod]

def contourQMiddleRows (m : ℕ) : Fin m → ℂ :=
  fun i => (rowIndex m i : ℕ)

noncomputable def contourQFrequencyIndependentFactor {m : ℕ}
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ) : ℝ := by
  classical
  let Jc := Jset m \ S
  let d := m - S.card
  let n := d + m
  have hJc : Jc.card = n := contourQJComplement_card S h4 hSI
  exact contourQFixedFactor S hSI Z *
      ‖(Matrix.vandermonde (contourQMiddleRows m)).det‖ *
      ‖(Matrix.vandermonde (fun i : Fin d => -Z i)).det‖ *
      ‖(Matrix.vandermonde (contourQRightColumns S h4 hSI)).det‖ /
      (∏ z : Fin d, ∏ j : Fin n,
        ‖-(Z z) + contourQRightColumns S h4 hSI j‖)

lemma norm_natCast_add (a b : ℕ) :
    ‖(a : ℂ) + (b : ℂ)‖ = ((a + b : ℕ) : ℝ) := by
  have hc : (a : ℂ) + (b : ℂ) = ((a + b : ℕ) : ℂ) := by norm_cast
  rw [hc]
  exact Complex.norm_natCast _

lemma rowIndex_injective (m : ℕ) : Function.Injective (rowIndex m) := by
  intro i j hij
  apply Fin.ext
  dsimp [rowIndex] at hij
  omega

lemma contourQMiddle_denominator {m : ℕ} (R : Fin m → ℕ)
    (hR : StrictMono R) :
    (∏ i : Fin m, ∏ j : Fin m,
      ‖contourQMiddleRows m i + (R j : ℂ)‖) =
      ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
        ∏ a ∈ Iset m, ((r + a : ℕ) : ℝ) := by
  classical
  have hrow : (Finset.univ : Finset (Fin m)).image (rowIndex m) = Iset m := rfl
  have hval (i j : Fin m) :
      ‖contourQMiddleRows m i + (R j : ℂ)‖ =
        ((rowIndex m i + R j : ℕ) : ℝ) := by
    exact norm_natCast_add _ _
  rw [Finset.prod_comm]
  simp_rw [hval]
  let g : ℕ → ℝ := fun r =>
    ∏ i : Fin m, ((rowIndex m i + r : ℕ) : ℝ)
  change (∏ j : Fin m, g (R j)) = _
  rw [prod_fin_image R hR.injective g]
  apply Finset.prod_congr rfl
  intro r hr
  change (∏ i : Fin m, ((rowIndex m i + r : ℕ) : ℝ)) = _
  have hcomm :
      (∏ i : Fin m, ((rowIndex m i + r : ℕ) : ℝ)) =
        ∏ i : Fin m, ((r + rowIndex m i : ℕ) : ℝ) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [Nat.add_comm]
  rw [hcomm, prod_fin_image (rowIndex m) (rowIndex_injective m)
    (fun a => ((r + a : ℕ) : ℝ))]
  rw [hrow]

lemma prod_if_mem_eq_sdiff {s t : Finset ℕ} (f : ℕ → ℝ) :
    (∏ j ∈ s, if j ∈ t then 1 else f j) =
      ∏ j ∈ s \ t, f j := by
  classical
  have hfilter : s.filter (fun j => j ∉ t) = s \ t := by
    ext j
    simp
  calc
    (∏ j ∈ s, if j ∈ t then 1 else f j) =
        ∏ j ∈ s, if j ∉ t then f j else 1 := by
          apply Finset.prod_congr rfl
          intro j hj
          by_cases h : j ∈ t <;> simp [h]
    _ = ∏ j ∈ s.filter (fun j => j ∉ t), f j := by
          rw [← Finset.prod_filter]
    _ = ∏ j ∈ s \ t, f j := by rw [hfilter]

lemma contourQRight_denominator {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ)
    (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) :
    (∏ i : Fin ((m - S.card) + m),
      ∏ j : Fin ((m - S.card) + m),
        ‖contourQRightRows S R Z i + contourQRightColumns S h4 hSI j‖) =
      (∏ z : Fin (m - S.card), ∏ j : Fin ((m - S.card) + m),
        ‖-(Z z) + contourQRightColumns S h4 hSI j‖) *
      ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
        ∏ a ∈ Jset m \ S, ((r + a : ℕ) : ℝ) := by
  classical
  let d := m - S.card
  let n := d + m
  let Jc := Jset m \ S
  have hJc : Jc.card = n := contourQJComplement_card S h4 hSI
  have hsplit :
      (∏ i : Fin n, ∏ j : Fin n,
        ‖contourQRightRows S R Z i + contourQRightColumns S h4 hSI j‖) =
        (∏ z : Fin d, ∏ j : Fin n,
          ‖-Z z + contourQRightColumns S h4 hSI j‖) *
        (∏ i : Fin m, ∏ j : Fin n,
          ‖(R i : ℂ) + contourQRightColumns S h4 hSI j‖) := by
    rw [Fin.prod_univ_add]
    simp only [contourQRightRows, Fin.append_left]
    congr 1
    apply Finset.prod_congr rfl
    intro i hi
    apply Finset.prod_congr rfl
    intro j hj
    congr 1
    rw [Fin.append_right]
  have hfreq :
      (∏ i : Fin m, ∏ j : Fin n,
        ‖(R i : ℂ) + contourQRightColumns S h4 hSI j‖) =
        ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
          ∏ a ∈ Jc, ((r + a : ℕ) : ℝ) := by
    calc
      (∏ i : Fin m, ∏ j : Fin n,
          ‖(R i : ℂ) + contourQRightColumns S h4 hSI j‖) =
          ∏ i : Fin m, ∏ a ∈ Jc, ((R i + a : ℕ) : ℝ) := by
            apply Finset.prod_congr rfl
            intro i hi
            simp_rw [contourQRightColumns, norm_natCast_add]
            exact prod_orderedElem hJc (fun a => ((R i + a : ℕ) : ℝ))
      _ = ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
            ∏ a ∈ Jc, ((r + a : ℕ) : ℝ) := by
          let g : ℕ → ℝ := fun r => ∏ a ∈ Jc, ((r + a : ℕ) : ℝ)
          change (∏ i : Fin m, g (R i)) = _
          exact prod_fin_image R hR.injective g
  calc
    (∏ i : Fin n, ∏ j : Fin n,
        ‖contourQRightRows S R Z i + contourQRightColumns S h4 hSI j‖) =
        (∏ z : Fin d, ∏ j : Fin n,
          ‖-Z z + contourQRightColumns S h4 hSI j‖) *
        (∏ i : Fin m, ∏ j : Fin n,
          ‖(R i : ℂ) + contourQRightColumns S h4 hSI j‖) := hsplit
    _ = (∏ z : Fin d, ∏ j : Fin n,
          ‖-Z z + contourQRightColumns S h4 hSI j‖) *
        (∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
          ∏ a ∈ Jc, ((r + a : ℕ) : ℝ)) := by rw [hfreq]

lemma contourQCross_eq {m d : ℕ} (R : Fin m → ℕ)
    (hR : StrictMono R) (Z : Fin d → ℂ) :
    (∏ z : Fin d, ∏ j : Fin m, ‖(R j : ℂ) + Z z‖) =
      ∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
        ∏ z : Fin d, ‖(r : ℂ) + Z z‖ := by
  rw [Finset.prod_comm]
  let g : ℕ → ℝ := fun r => ∏ z : Fin d, ‖(r : ℂ) + Z z‖
  change (∏ j : Fin m, g (R j)) = _
  exact prod_fin_image R hR.injective g

lemma contourQRightFixedDenominator_pos {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ)
    (hZ : ∀ z j, Z z ≠ contourQRightColumns S h4 hSI j) :
    0 < ∏ z : Fin (m - S.card), ∏ j : Fin ((m - S.card) + m),
      ‖-Z z + contourQRightColumns S h4 hSI j‖ := by
  apply Finset.prod_pos
  intro z hz
  apply Finset.prod_pos
  intro j hj
  have hne : -Z z + contourQRightColumns S h4 hSI j ≠ 0 := by
    intro hzero
    apply hZ z j
    exact neg_injective (add_eq_zero_iff_eq_neg.mp hzero)
  exact norm_pos_iff.mpr hne

lemma contourQFrequencyDenominators_pos {m : ℕ} (S : Finset ℕ)
    (R : Fin m → ℕ)
    (hRpos : ∀ i, 0 < R i) :
    0 < (∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
          ∏ a ∈ Iset m, ((r + a : ℕ) : ℝ)) ∧
      0 < (∏ r ∈ (Finset.univ : Finset (Fin m)).image R,
          ∏ a ∈ Jset m \ S, ((r + a : ℕ) : ℝ)) := by
  constructor
  · apply Finset.prod_pos
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.prod_pos
    intro a ha
    have hRi : 0 < R i := hRpos i
    positivity
  · apply Finset.prod_pos
    intro r hr
    obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hr
    apply Finset.prod_pos
    intro a ha
    have hRi : 0 < R i := hRpos i
    positivity

noncomputable def contourQMinorFrequencyIndependentFactor {m : ℕ}
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ) : ℝ := by
  classical
  let d := m - S.card
  let n := d + m
  exact (‖(Matrix.vandermonde (contourQMiddleRows m)).det‖ *
      ‖(Matrix.vandermonde (fun i : Fin d => -Z i)).det‖ *
      ‖(Matrix.vandermonde (contourQRightColumns S h4 hSI)).det‖) /
    (∏ z : Fin d, ∏ j : Fin n,
      ‖-Z z + contourQRightColumns S h4 hSI j‖)

theorem contourQMinorFrequencyIndependentFactor_nonneg {m : ℕ}
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (Z : Fin (m - S.card) → ℂ)
    (hZ : ∀ z j, Z z ≠ contourQRightColumns S h4 hSI j) :
    0 ≤ contourQMinorFrequencyIndependentFactor S h4 hSI Z := by
  have hden := contourQRightFixedDenominator_pos S h4 hSI Z hZ
  unfold contourQMinorFrequencyIndependentFactor
  exact div_nonneg
    (mul_nonneg (mul_nonneg (norm_nonneg _) (norm_nonneg _)) (norm_nonneg _))
    hden.le

theorem contourQMinorFrequencyProduct_eq_fixedFactor_mul_frequencyFactor
    {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R) (hRpos : ∀ i, 0 < R i)
    (Z : Fin (m - S.card) → ℂ)
    (hZ : ∀ z j, Z z ≠ contourQRightColumns S h4 hSI j) :
    contourQMinorFrequencyProduct S h4 hSI R hR Z =
      contourQMinorFrequencyIndependentFactor S h4 hSI Z *
        FrequencyLeaf.frequencyFactor m (m / 2) S
          ((Finset.univ : Finset (Fin m)).image R) (m - S.card) Z := by
  classical
  let d := m - S.card
  let RF := (Finset.univ : Finset (Fin m)).image R
  let W : ℝ := ∏ r ∈ RF, FrequencyLeaf.weight (m / 2) r
  let V : ℝ := FrequencyLeaf.frequencyVandermonde RF
  let X : ℝ := ∏ r ∈ RF, ∏ z : Fin d, ‖(r : ℂ) + Z z‖
  let DI : ℝ := ∏ r ∈ RF, ∏ a ∈ Iset m, ((r + a : ℕ) : ℝ)
  let DJ : ℝ := ∏ r ∈ RF, ∏ a ∈ Jset m \ S, ((r + a : ℕ) : ℝ)
  let ZD : ℝ := ∏ z : Fin d, ∏ j : Fin (d + m),
    ‖-Z z + contourQRightColumns S h4 hSI j‖
  let VA : ℝ := ‖(Matrix.vandermonde (contourQMiddleRows m)).det‖
  let VZ : ℝ := ‖(Matrix.vandermonde (fun i : Fin d => -Z i)).det‖
  let VC : ℝ := ‖(Matrix.vandermonde (contourQRightColumns S h4 hSI)).det‖
  have hmge4 : 4 ≤ m := by
    rcases h4 with ⟨q, hq⟩
    omega
  have hI : Iset m = FrequencyLeaf.I_m m := Iset_eq_frequency_I_m hm h4
  have hJc : (Jset m \ S).card = d + m := by
    simpa [d] using contourQJComplement_card S h4 hSI
  have hmidXY : ∀ i j, contourQMiddleRows m i + (R j : ℂ) ≠ 0 := by
    intro i j
    change ((rowIndex m i : ℂ) + (R j : ℂ) ≠ 0)
    norm_cast
    dsimp [rowIndex]
    omega
  have hRcomplex : Function.Injective (fun i : Fin m => (R i : ℂ)) := by
    intro i j hij
    have hreal : (R i : ℝ) = (R j : ℝ) := congrArg Complex.re hij
    have hnat : R i = R j := by exact_mod_cast hreal
    exact hR.injective hnat
  have hmiddle :
      ‖(contourQMinors S h4 hSI R hR Z).2.1‖ = VA * V / DI := by
    change ‖(Matrix.of (fun (i j : Fin m) =>
      (contourQMiddleRows m i + (R j : ℂ))⁻¹)).det‖ = _
    rw [norm_cauchy_determinant (contourQMiddleRows m)
      (fun i => (R i : ℂ)) hRcomplex hmidXY]
    rw [norm_vandermonde_eq_frequencyVandermonde R hR,
      contourQMiddle_denominator R hR]
  have hrightXY : ∀ i j,
      contourQRightRows S R Z i + contourQRightColumns S h4 hSI j ≠ 0 := by
    intro i j
    rw [contourQRightRows_piecewise]
    split_ifs with hi
    · intro hz
      have heq : Z ⟨i.val, hi⟩ = contourQRightColumns S h4 hSI j := by
        have hneg : -Z ⟨i.val, hi⟩ = -contourQRightColumns S h4 hSI j :=
          (add_eq_zero_iff_eq_neg.mp hz)
        exact neg_injective hneg
      exact hZ ⟨i.val, hi⟩ j heq
    · intro hz
      simp only [contourQRightColumns] at hz
      have hnat : R ⟨i.val - d, by omega⟩ +
          orderedElem (Jset m \ S) (Fin.cast hJc.symm j) = 0 := by
        exact_mod_cast hz
      have hpos : 0 < R ⟨i.val - d, by omega⟩ := hRpos _
      omega
  have hrightDef :
      (contourQMinors S h4 hSI R hR Z).2.2 =
        (Matrix.of (fun (i j : Fin ((m - S.card) + m)) =>
          (contourQRightRows S R Z i +
            contourQRightColumns S h4 hSI j)⁻¹)).det := by
    simp [contourQMinors, contourQRightRows_piecewise, contourQRightColumns]
    rfl
  have hright :
      ‖(contourQMinors S h4 hSI R hR Z).2.2‖ =
        (VZ * V * X * VC) / (ZD * DJ) := by
    rw [hrightDef,
      norm_cauchy_determinant (contourQRightRows S R Z)
        (contourQRightColumns S h4 hSI) (contourQRightColumns_injective S h4 hSI)
        hrightXY]
    rw [contourQRight_denominator S h4 hSI R hR Z]
    have hcross :
        (∏ z : Fin d, ∏ j : Fin m,
          ‖(R j : ℂ) - (-(Z z))‖) = X := by
      simp_rw [sub_neg_eq_add]
      exact contourQCross_eq R hR Z
    rw [show contourQRightRows S R Z =
      Fin.append (fun z : Fin d => -Z z) (fun i : Fin m => (R i : ℂ)) from rfl]
    rw [norm_vandermonde_append, norm_vandermonde_eq_frequencyVandermonde R hR,
      hcross]
  have hweights : (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) = W := by
    rw [frequencyWeights_eq_image R hR]
  have hJprod :
      (∏ r ∈ RF, ∏ j ∈ FrequencyLeaf.J_m m,
        if j ∈ S then 1 else ((r + j : ℕ) : ℝ)) = DJ := by
    simp only [FrequencyLeaf.J_m]
    apply Finset.prod_congr rfl
    intro r hr
    rw [prod_if_mem_eq_sdiff]
    rfl
  have hfactor :
      FrequencyLeaf.frequencyFactor m (m / 2) S RF d Z =
        (W * V ^ 2 * X) / (DI * DJ) := by
    rw [FrequencyLeaf.frequencyFactor, ← hI, hJprod]
  have hq :
      contourQMinorFrequencyProduct S h4 hSI R hR Z =
        (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
          ‖(contourQMinors S h4 hSI R hR Z).2.1‖ *
          ‖(contourQMinors S h4 hSI R hR Z).2.2‖ := by
    rfl
  have hden := contourQRightFixedDenominator_pos S h4 hSI Z hZ
  have hfreqden := contourQFrequencyDenominators_pos S R hRpos
  have hDI : DI ≠ 0 := by
    dsimp [DI, RF]
    exact ne_of_gt hfreqden.1
  have hDJ : DJ ≠ 0 := by
    dsimp [DJ, RF]
    exact ne_of_gt hfreqden.2
  have hZD : ZD ≠ 0 := by
    dsimp [ZD, d]
    exact ne_of_gt hden
  rw [hq, hweights, hmiddle, hright, hfactor]
  change W * (VA * V / DI) * ((VZ * V * X * VC) / (ZD * DJ)) =
    (VA * VZ * VC / ZD) * ((W * V ^ 2 * X) / (DI * DJ))
  field_simp [hDI, hDJ, hZD]

theorem contourQValue_eq_frequencyIndependentFactor_mul_frequencyFactor
    {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R) (hRpos : ∀ i, 0 < R i)
    (Z : Fin (m - S.card) → ℂ)
    (hZ : ∀ z j, Z z ≠ contourQRightColumns S h4 hSI j) :
    contourQValue S h4 hSI R hR Z =
      contourQFrequencyIndependentFactor S h4 hSI Z *
        FrequencyLeaf.frequencyFactor m (m / 2) S
          ((Finset.univ : Finset (Fin m)).image R) (m - S.card) Z := by
  classical
  let d := m - S.card
  let RF := (Finset.univ : Finset (Fin m)).image R
  let W : ℝ := ∏ r ∈ RF, FrequencyLeaf.weight (m / 2) r
  let V : ℝ := FrequencyLeaf.frequencyVandermonde RF
  let X : ℝ := ∏ r ∈ RF, ∏ z : Fin d, ‖(r : ℂ) + Z z‖
  let DI : ℝ := ∏ r ∈ RF, ∏ a ∈ Iset m, ((r + a : ℕ) : ℝ)
  let DJ : ℝ := ∏ r ∈ RF, ∏ a ∈ Jset m \ S, ((r + a : ℕ) : ℝ)
  let ZD : ℝ := ∏ z : Fin d, ∏ j : Fin (d + m),
    ‖-Z z + contourQRightColumns S h4 hSI j‖
  let VA : ℝ := ‖(Matrix.vandermonde (contourQMiddleRows m)).det‖
  let VZ : ℝ := ‖(Matrix.vandermonde (fun i : Fin d => -Z i)).det‖
  let VC : ℝ := ‖(Matrix.vandermonde (contourQRightColumns S h4 hSI)).det‖
  have hmge4 : 4 ≤ m := by
    rcases h4 with ⟨q, hq⟩
    omega
  have hI : Iset m = FrequencyLeaf.I_m m :=
    Iset_eq_frequency_I_m hm h4
  have hJc : (Jset m \ S).card = d + m := by
    simpa [d] using contourQJComplement_card S h4 hSI
  have hmidXY : ∀ i j, contourQMiddleRows m i + (R j : ℂ) ≠ 0 := by
    intro i j
    change ((rowIndex m i : ℂ) + (R j : ℂ) ≠ 0)
    norm_cast
    dsimp [rowIndex]
    omega
  have hRcomplex : Function.Injective (fun i : Fin m => (R i : ℂ)) := by
    intro i j hij
    have hreal : (R i : ℝ) = (R j : ℝ) := congrArg Complex.re hij
    have hnat : R i = R j := by exact_mod_cast hreal
    exact hR.injective hnat
  have hmiddle :
      ‖(contourQMinors S h4 hSI R hR Z).2.1‖ = VA * V / DI := by
    change ‖(Matrix.of (fun (i j : Fin m) =>
      (contourQMiddleRows m i + (R j : ℂ))⁻¹)).det‖ = _
    rw [norm_cauchy_determinant (contourQMiddleRows m)
      (fun i => (R i : ℂ)) hRcomplex hmidXY]
    rw [norm_vandermonde_eq_frequencyVandermonde R hR,
      contourQMiddle_denominator R hR]
  have hrightXY : ∀ i j,
      contourQRightRows S R Z i + contourQRightColumns S h4 hSI j ≠ 0 := by
    intro i j
    rw [contourQRightRows_piecewise]
    split_ifs with hi
    · intro hz
      have heq : Z ⟨i.val, hi⟩ = contourQRightColumns S h4 hSI j := by
        have hneg : -Z ⟨i.val, hi⟩ = -contourQRightColumns S h4 hSI j :=
          (add_eq_zero_iff_eq_neg.mp hz)
        exact neg_injective hneg
      exact hZ ⟨i.val, hi⟩ j heq
    · intro hz
      simp only [contourQRightColumns] at hz
      have hnat : R ⟨i.val - d, by omega⟩ +
          orderedElem (Jset m \ S) (Fin.cast hJc.symm j) = 0 := by
        exact_mod_cast hz
      have hpos : 0 < R ⟨i.val - d, by omega⟩ := hRpos _
      omega
  have hrightDef :
      (contourQMinors S h4 hSI R hR Z).2.2 =
        (Matrix.of (fun (i j : Fin ((m - S.card) + m)) =>
          (contourQRightRows S R Z i +
            contourQRightColumns S h4 hSI j)⁻¹)).det := by
    simp [contourQMinors, contourQRightRows_piecewise, contourQRightColumns]
    rfl
  have hright :
      ‖(contourQMinors S h4 hSI R hR Z).2.2‖ =
        (VZ * V * X * VC) / (ZD * DJ) := by
    rw [hrightDef,
      norm_cauchy_determinant (contourQRightRows S R Z)
        (contourQRightColumns S h4 hSI) (contourQRightColumns_injective S h4 hSI)
        hrightXY]
    rw [contourQRight_denominator S h4 hSI R hR Z]
    have hcross :
        (∏ z : Fin d, ∏ j : Fin m,
          ‖(R j : ℂ) - (-(Z z))‖) = X := by
      simp_rw [sub_neg_eq_add]
      exact contourQCross_eq R hR Z
    rw [show contourQRightRows S R Z =
      Fin.append (fun z : Fin d => -Z z) (fun i : Fin m => (R i : ℂ)) from rfl]
    rw [norm_vandermonde_append, norm_vandermonde_eq_frequencyVandermonde R hR,
      hcross]
  have hweights :
      (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) = W := by
    rw [frequencyWeights_eq_image R hR]
  have hJprod :
      (∏ r ∈ RF, ∏ j ∈ FrequencyLeaf.J_m m,
        if j ∈ S then 1 else ((r + j : ℕ) : ℝ)) = DJ := by
    simp only [FrequencyLeaf.J_m]
    apply Finset.prod_congr rfl
    intro r hr
    rw [prod_if_mem_eq_sdiff]
    rfl
  have hfactor :
      FrequencyLeaf.frequencyFactor m (m / 2) S RF d Z =
        (W * V ^ 2 * X) / (DI * DJ) := by
    rw [FrequencyLeaf.frequencyFactor, ← hI, hJprod]
  have hq :
      contourQValue S h4 hSI R hR Z =
        contourQFixedFactor S hSI Z *
          ((∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
            ‖(contourQMinors S h4 hSI R hR Z).2.1‖ *
            ‖(contourQMinors S h4 hSI R hR Z).2.2‖) := by
    rw [contourQValue_eq_fixedFactor_mul_minorFrequencyProduct]
    rfl
  rw [hq, hweights, hmiddle, hright, hfactor]
  change contourQFixedFactor S hSI Z * (W * (VA * V / DI) *
      ((VZ * V * X * VC) / (ZD * DJ))) =
    (contourQFixedFactor S hSI Z * VA * VZ * VC / ZD) *
      ((W * V ^ 2 * X) / (DI * DJ))
  ring

theorem p0EllipsePoint_avoids_contourQRightColumns {m : ℕ}
    (hm : 0 < m) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) :
    ∀ z j, p0EllipsePoint m (u z) ≠ contourQRightColumns S h4 hSI j := by
  classical
  intro z j
  let Jc := Jset m \ S
  let d := m - S.card
  have hJc : Jc.card = d + m := by
    simpa [Jc, d] using contourQJComplement_card S h4 hSI
  have hjmem : orderedElem Jc (Fin.cast hJc.symm j) ∈ Jc := by
    change (Finset.orderIsoOfFin Jc rfl (Fin.cast hJc.symm j)).val ∈ Jc
    exact (Finset.orderIsoOfFin Jc rfl (Fin.cast hJc.symm j)).property
  have hj : orderedElem Jc (Fin.cast hJc.symm j) < 2 * m := by
    have := (Finset.mem_sdiff.mp hjmem).1
    simpa [Jset] using this
  change p0EllipsePoint m (u z) ≠
    ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ)
  exact FrequencyLeaf.p0EllipsePoint_ne_nat hm (u z) hj

theorem contourQValue_eq_frequencyFactor_ellipse
    {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R)
    (hRg : ∀ i, m / 2 < R i)
    (u : Fin (m - S.card) → ℝ) :
    contourQValue S h4 hSI R hR (fun z => p0EllipsePoint m (u z)) =
      contourQFrequencyIndependentFactor S h4 hSI
        (fun z => p0EllipsePoint m (u z)) *
      FrequencyLeaf.frequencyFactor m (m / 2) S
        ((Finset.univ : Finset (Fin m)).image R) (m - S.card)
        (fun z => p0EllipsePoint m (u z)) := by
  apply contourQValue_eq_frequencyIndependentFactor_mul_frequencyFactor hm h4
  · intro i
    exact lt_of_le_of_lt (Nat.zero_le _) (hRg i)
  · exact p0EllipsePoint_avoids_contourQRightColumns hm h4 S hSI u

end

end Li2Lean.P0
