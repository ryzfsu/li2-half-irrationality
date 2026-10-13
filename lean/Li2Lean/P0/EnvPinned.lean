/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvContour
import Li2Lean.P0.EnvSplit
import Li2Lean.P0.ContourFrequencyFactor

/-!
# Pinned rows: subset expansion and block reduction

For a pinned set `S ⊆ I_m` the source rows with labels in `S` keep their diagonal part
`log 2 · U_a e_a`, the others keep their contour part.  Reindexing rows and columns
(`pinRowEquiv`, `pinColEquiv`) puts the matrix in block lower-triangular form, so its
determinant is `∏_{a∈S} log 2 · U_a` times the determinant of the `(d+m) × (d+m)` matrix
`pinnedD` with rows: the `d` contour rows (labels `I_m \ S` increasing) and the `m`
frequency rows, and columns `J_m \ S` increasing (paper v13 `p0-analytic.tex` ll. 80-83).
-/

open Finset

namespace Li2Lean.P0.Env

noncomputable section

/-- The source rows whose label lies in `S`. -/
def tOf (m : ℕ) (S : Finset ℕ) : Finset (Fin m) := univ.filter (fun i => rowIndex m i ∈ S)

theorem rowIndex_val (m : ℕ) (i : Fin m) : rowIndex m i = m / 4 + i.val := rfl

theorem mem_Iset_iff (m a : ℕ) : a ∈ Iset m ↔ m / 4 ≤ a ∧ a < m / 4 + m := by
  simp only [Iset, Finset.mem_image, Finset.mem_univ, true_and, rowIndex]
  constructor
  · rintro ⟨i, rfl⟩; omega
  · intro h; exact ⟨⟨a - m / 4, by omega⟩, by simp; omega⟩

theorem tOf_image (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    (tOf m S).image (rowIndex m) = S := by
  ext a
  simp only [tOf, Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨i, hi, rfl⟩; exact hi
  · intro ha
    have := (mem_Iset_iff m a).mp (hSI ha)
    exact ⟨⟨a - m / 4, by omega⟩, by simpa [rowIndex_val, show m / 4 + (a - m / 4) = a by omega]
      using ha, by simp [rowIndex_val]; omega⟩

theorem tOf_card (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) : (tOf m S).card = S.card := by
  conv_rhs => rw [← tOf_image m S hSI]
  rw [Finset.card_image_of_injective _ (rowIndex_injective m)]

/-- The row position of a label `a ∈ I_m`. -/
def posI (m : ℕ) (hm : 0 < m) (a : ℕ) : Fin m := ⟨(a - m / 4) % m, Nat.mod_lt _ hm⟩

theorem rowIndex_posI (m : ℕ) (hm : 0 < m) (a : ℕ) (ha : a ∈ Iset m) :
    rowIndex m (posI m hm a) = a := by
  have := (mem_Iset_iff m a).mp ha
  simp only [rowIndex_val, posI]
  rw [Nat.mod_eq_of_lt (by omega)]
  omega

/-- The reindexed column with label `j < 2m`. -/
def colOf (m : ℕ) (hm : 0 < m) (j : ℕ) : Fin m ⊕ Fin m :=
  (eρ m).symm ⟨j % (2 * m), Nat.mod_lt _ (by omega)⟩

theorem colLab_colOf (m : ℕ) (hm : 0 < m) (j : ℕ) (hj : j < 2 * m) :
    colLab m (colOf m hm j) = j := by
  simp [colLab, colOf, Nat.mod_eq_of_lt hj]

theorem orderedElem_mem' (s : Finset ℕ) (i : Fin s.card) : orderedElem s i ∈ s :=
  (Finset.orderIsoOfFin s rfl i).property

theorem Ic_card (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    (Iset m \ S).card = m - S.card := by
  rw [Finset.card_sdiff_of_subset hSI, Iset_card]

/-- Increasing contour row labels `I_m \ S`. -/
def aLab (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) (l : Fin (m - S.card)) : ℕ :=
  orderedElem (Iset m \ S) (Fin.cast (Ic_card m S hSI).symm l)

/-- Increasing column labels `J_m \ S`, split as `Fin d ⊕ Fin m`. -/
def jLab (m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (x : Fin (m - S.card) ⊕ Fin m) : ℕ :=
  orderedElem (Jset m \ S)
    (Fin.cast (contourQJComplement_card S h4 hSI).symm (finSumFinEquiv x))

theorem aLab_mem (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) (l : Fin (m - S.card)) :
    aLab m S hSI l ∈ Iset m \ S := orderedElem_mem' _ _

theorem jLab_mem (m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (x : Fin (m - S.card) ⊕ Fin m) : jLab m S h4 hSI x ∈ Jset m \ S := orderedElem_mem' _ _

theorem jLab_lt (m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (x : Fin (m - S.card) ⊕ Fin m) : jLab m S h4 hSI x < 2 * m := by
  have := (Finset.mem_sdiff.mp (jLab_mem m S h4 hSI x)).1
  simpa [Jset] using this

theorem aLab_injective (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Function.Injective (aLab m S hSI) :=
  orderedElem_cast_injective (Ic_card m S hSI)

theorem jLab_injective (m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) :
    Function.Injective (jLab m S h4 hSI) := by
  intro x y h
  exact finSumFinEquiv.injective
    (orderedElem_cast_injective (contourQJComplement_card S h4 hSI) h)

theorem rowIndex_lt (m : ℕ) (h4 : 4 ∣ m) (i : Fin m) : rowIndex m i < 2 * m := by
  rw [rowIndex_val]; omega

/-- The row map of the block reduction. -/
def pinRowFun (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    (Fin (m - S.card) ⊕ Fin m) ⊕ {i : Fin m // i ∈ tOf m S} → Fin m ⊕ Fin m
  | Sum.inl (Sum.inl l) => Sum.inr (posI m hm (aLab m S hSI l))
  | Sum.inl (Sum.inr k) => Sum.inl k
  | Sum.inr b => Sum.inr b.val

/-- The column map of the block reduction. -/
def pinColFun (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) :
    (Fin (m - S.card) ⊕ Fin m) ⊕ {i : Fin m // i ∈ tOf m S} → Fin m ⊕ Fin m
  | Sum.inl x => colOf m hm (jLab m S h4 hSI x)
  | Sum.inr b => colOf m hm (rowIndex m b.val)

theorem card_pin_domain (m : ℕ) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Fintype.card ((Fin (m - S.card) ⊕ Fin m) ⊕ {i : Fin m // i ∈ tOf m S}) =
      Fintype.card (Fin m ⊕ Fin m) := by
  have hS : S.card ≤ m := by rw [← Iset_card m]; exact Finset.card_le_card hSI
  simp only [Fintype.card_sum, Fintype.card_fin, Fintype.card_coe, tOf_card m S hSI]
  omega

theorem pinRowFun_injective (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    Function.Injective (pinRowFun m hm S hSI) := by
  have hpos : ∀ l, rowIndex m (posI m hm (aLab m S hSI l)) = aLab m S hSI l := fun l =>
    rowIndex_posI m hm _ (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).1
  rintro ((l | k) | b) ((l' | k') | b') h <;> simp only [pinRowFun, Sum.inl.injEq,
    Sum.inr.injEq, reduceCtorEq] at h
  · have := congrArg (rowIndex m) h
    rw [hpos, hpos] at this
    rw [aLab_injective m S hSI this]
  · exfalso
    have hb := b'.property
    simp only [tOf, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [← h, hpos] at hb
    exact (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).2 hb
  · rw [h]
  · exfalso
    have hb := b.property
    simp only [tOf, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [h, hpos] at hb
    exact (Finset.mem_sdiff.mp (aLab_mem m S hSI l')).2 hb
  · rw [Subtype.ext h]

theorem pinColFun_injective (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) : Function.Injective (pinColFun m hm S h4 hSI) := by
  have hlab : ∀ y, colLab m (pinColFun m hm S h4 hSI y) =
      Sum.elim (jLab m S h4 hSI) (fun b => rowIndex m b.val) y := by
    rintro (x | b)
    · exact colLab_colOf m hm _ (jLab_lt m S h4 hSI x)
    · exact colLab_colOf m hm _ (rowIndex_lt m h4 b.val)
  intro y y' h
  have h' := congrArg (colLab m) h
  rw [hlab, hlab] at h'
  rcases y with x | b <;> rcases y' with x' | b' <;> simp only [Sum.elim_inl, Sum.elim_inr] at h'
  · rw [jLab_injective m S h4 hSI h']
  · exfalso
    have hb := b'.property
    simp only [tOf, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [← h'] at hb
    exact (Finset.mem_sdiff.mp (jLab_mem m S h4 hSI x)).2 hb
  · exfalso
    have hb := b.property
    simp only [tOf, Finset.mem_filter, Finset.mem_univ, true_and] at hb
    rw [h'] at hb
    exact (Finset.mem_sdiff.mp (jLab_mem m S h4 hSI x')).2 hb
  · rw [Subtype.ext (rowIndex_injective m h')]

def pinRowEquiv (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    (Fin (m - S.card) ⊕ Fin m) ⊕ {i : Fin m // i ∈ tOf m S} ≃ Fin m ⊕ Fin m :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨pinRowFun_injective m hm S hSI, card_pin_domain m S hSI⟩)

def pinColEquiv (m : ℕ) (hm : 0 < m) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) :
    (Fin (m - S.card) ⊕ Fin m) ⊕ {i : Fin m // i ∈ tOf m S} ≃ Fin m ⊕ Fin m :=
  Equiv.ofBijective _ ((Fintype.bijective_iff_injective_and_card _).mpr
    ⟨pinColFun_injective m hm S h4 hSI, card_pin_domain m S hSI⟩)


/-- Diagonal part of the source rows, in reindexed coordinates. -/
def Pp (m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) : ℂ := pinPart (m / 2) (rowIndex m i) (colLab m c)

/-- Contour part of the source rows, in reindexed coordinates. -/
def Qp (m : ℕ) (i : Fin m) (c : Fin m ⊕ Fin m) : ℂ := contPart m (rowIndex m i) (colLab m c)

theorem Ymat_inr_split (m : ℕ) (h4 : 4 ∣ m) (R : Fin m → ℕ) (i : Fin m)
    (c : Fin m ⊕ Fin m) : Ymat m R (Sum.inr i) c = Pp m i c + Qp m i c := by
  simp only [Ymat, Matrix.of_apply, Sum.elim_inr, topRow, Pp, Qp]
  rw [p0CQ_two_cast_complex]
  exact p0C_split m h4 _ _ (rowIndex_lt m h4 i) (colLab_lt m c)

/-- The reduced `(d+m) × (d+m)` matrix: contour rows over frequency rows,
columns `J_m \ S`. -/
def pinnedD (m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ) :
    Matrix (Fin (m - S.card) ⊕ Fin m) (Fin (m - S.card) ⊕ Fin m) ℂ :=
  Matrix.of fun a a' => Sum.elim (fun l => contPart m (aLab m S hSI l) (jLab m S h4 hSI a'))
    (fun k => cauchyKernel (R k) (jLab m S h4 hSI a')) a

theorem norm_ell_p0U (g a : ℕ) :
    ‖((Real.log 2 : ℝ) : ℂ) * p0U g a‖ = ell * UReal g a := by
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg (by norm_num))]
  simp [p0U, UReal, ell]

theorem norm_det_split_eq (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) :
    ‖(splitMat (Ymat m R) (Pp m) (Qp m) (tOf m S)).det‖ =
      ‖(pinnedD m S h4 hSI R).det‖ * ∏ a ∈ S, (ell * UReal (m / 2) a) := by
  have hrow : ∀ x, pinRowEquiv m hm S hSI x = pinRowFun m hm S hSI x := fun _ => rfl
  have hcol : ∀ x, pinColEquiv m hm S h4 hSI x = pinColFun m hm S h4 hSI x := fun _ => rfl
  have hmemS : ∀ i : Fin m, i ∈ tOf m S ↔ rowIndex m i ∈ S := fun i => by simp [tOf]
  have hjS : ∀ x, jLab m S h4 hSI x ∉ S := fun x => (Finset.mem_sdiff.mp (jLab_mem m S h4 hSI x)).2
  have hcolLab : ∀ x, colLab m (colOf m hm (jLab m S h4 hSI x)) = jLab m S h4 hSI x :=
    fun x => colLab_colOf m hm _ (jLab_lt m S h4 hSI x)
  have hblock := norm_det_of_block (splitMat (Ymat m R) (Pp m) (Qp m) (tOf m S))
    (pinRowEquiv m hm S hSI) (pinColEquiv m hm S h4 hSI)
    (fun b => ((Real.log 2 : ℝ) : ℂ) * p0U (m / 2) (rowIndex m b.val))
    (by
      intro b a
      rw [hrow, hcol]
      simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inr, if_pos b.property,
        Pp, pinPart, hcolLab]
      rw [if_neg]
      intro h
      exact hjS a (h ▸ (hmemS b.val).mp b.property))
    (by
      intro b b'
      rw [hrow, hcol]
      simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inr, if_pos b.property,
        Pp, pinPart, colLab_colOf m hm _ (rowIndex_lt m h4 b'.val)]
      by_cases hb : b = b'
      · subst hb; simp
      · rw [if_neg, if_neg hb]
        intro h
        exact hb (Subtype.ext (rowIndex_injective m h)))
  rw [hblock]
  congr 1
  · congr 2
    ext a a'
    simp only [Matrix.of_apply]
    rw [hrow, hcol]
    rcases a with l | k
    · have hnot : posI m hm (aLab m S hSI l) ∉ tOf m S := by
        rw [hmemS, rowIndex_posI m hm _ (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).1]
        exact (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).2
      simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inr, if_neg hnot, Qp,
        hcolLab, pinnedD, Sum.elim_inl,
        rowIndex_posI m hm _ (Finset.mem_sdiff.mp (aLab_mem m S hSI l)).1]
    · simp only [pinRowFun, pinColFun, splitMat, Matrix.of_apply, Sum.elim_inl, Ymat, freqVec,
        hcolLab, pinnedD, Sum.elim_inr]
  · rw [Finset.prod_coe_sort (tOf m S) (fun i => ‖((Real.log 2 : ℝ) : ℂ) *
      p0U (m / 2) (rowIndex m i)‖)]
    conv_rhs => rw [← tOf_image m S hSI]
    rw [Finset.prod_image (fun i _ j _ h => rowIndex_injective m h)]
    apply Finset.prod_congr rfl
    intro i _
    exact norm_ell_p0U _ _

end

end Li2Lean.P0.Env
