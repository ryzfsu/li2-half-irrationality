/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.FrequencyCutoff

/-!
# Determinant expansions for the P0 coefficient envelope

Abstract determinant identities used for paper v13 `p0-analytic.tex` ll. 40-140
(Cauchy-Binet in the frequencies, the row-by-row diagonal splitting, and the
Andreief antisymmetrization of the contour variables).

All matrices have rows indexed by `Fin q ⊕ ι`: the `inl` rows are the rows that are
integrals (or finite sums) of a common vector function, the `inr` rows are fixed.

* `discrete_andreief`: if `M (inl k) c = Σ_{t∈T} a k t * v t c` then
  `Σ_{f : Fin q → T} det (a k (f l)) * det (rows v (f l), fixed rows) = q! det M`
  (Cauchy-Binet in symmetrized form).
* `continuous_andreief`: the same with `∫ … dμ` and the product measure.
* `sum_piFinset_le_factorial_mul_cutoff`: a symmetric nonnegative function vanishing on
  non-injective tuples has total sum at most `q!` times its sum over increasing tuples.
* `norm_det_submatrix_equiv`: reindexing rows and columns by two equivalences
  preserves `‖det‖`.
-/

open Finset MeasureTheory

namespace Li2Lean.P0.Env

noncomputable section

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The sign of a permutation as a complex number. -/
abbrev sgnC {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ)

theorem sgnC_mul_self {α : Type*} [Fintype α] [DecidableEq α] (σ : Equiv.Perm α) :
    sgnC σ * sgnC σ = 1 := by
  unfold sgnC
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]
  simp

/-- Row-wise Leibniz expansion for a `Sum`-indexed matrix. -/
theorem det_sum_rows {q : ℕ} (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ) :
    M.det = ∑ τ : Equiv.Perm (Fin q ⊕ ι), sgnC τ *
      ((∏ l, M (Sum.inl l) (τ (Sum.inl l))) * ∏ i, M (Sum.inr i) (τ (Sum.inr i))) := by
  rw [← Matrix.det_transpose, Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro τ _
  rw [Fintype.prod_sum_type]
  simp [Matrix.transpose_apply, sgnC]

/-- Replace the `inl` rows of `M` by the vectors `w l`. -/
def rowRepl {q : ℕ} (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ)
    (w : Fin q → (Fin q ⊕ ι) → ℂ) : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ :=
  Matrix.of fun r c => Sum.elim (fun l => w l c) (fun i => M (Sum.inr i) c) r

/-- The permutation sum behind both Andreief identities. -/
theorem perm_core {q : ℕ} (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ) :
    (∑ σ : Equiv.Perm (Fin q), ∑ τ : Equiv.Perm (Fin q ⊕ ι),
      sgnC σ * sgnC τ * ((∏ l, M (Sum.inl (σ l)) (τ (Sum.inl l))) *
        ∏ i, M (Sum.inr i) (τ (Sum.inr i)))) = (q.factorial : ℂ) * M.det := by
  have hσ : ∀ σ : Equiv.Perm (Fin q),
      (∑ τ : Equiv.Perm (Fin q ⊕ ι), sgnC σ * sgnC τ *
        ((∏ l, M (Sum.inl (σ l)) (τ (Sum.inl l))) *
          ∏ i, M (Sum.inr i) (τ (Sum.inr i)))) = M.det := by
    intro σ
    let M' := M.submatrix (Equiv.sumCongr σ (Equiv.refl ι)) id
    have h1 : M'.det = sgnC σ * M.det := by
      rw [Matrix.det_permute, Equiv.Perm.sign_sumCongr, Equiv.Perm.sign_refl, mul_one]
    have h2 := det_sum_rows M'
    simp only [M', Matrix.submatrix_apply, Equiv.sumCongr_apply, Sum.map_inl, Sum.map_inr,
      Equiv.refl_apply, id] at h2
    calc (∑ τ : Equiv.Perm (Fin q ⊕ ι), sgnC σ * sgnC τ *
          ((∏ l, M (Sum.inl (σ l)) (τ (Sum.inl l))) *
            ∏ i, M (Sum.inr i) (τ (Sum.inr i))))
        = sgnC σ * (M.submatrix (Equiv.sumCongr σ (Equiv.refl ι)) id).det := by
          rw [h2, Finset.mul_sum]
          apply Finset.sum_congr rfl; intro τ _; ring
      _ = M.det := by
          rw [h1, ← mul_assoc, sgnC_mul_self, one_mul]
  rw [Finset.sum_congr rfl (fun σ _ => hσ σ), Finset.sum_const, Finset.card_univ,
    Fintype.card_perm, Fintype.card_fin, nsmul_eq_mul]

/-- Leibniz expansion of the matrix `(a k (x l))`. -/
theorem det_of_apply {q : ℕ} (A : Fin q → Fin q → ℂ) :
    (Matrix.of A).det = ∑ σ : Equiv.Perm (Fin q), sgnC σ * ∏ l, A (σ l) l := by
  rw [Matrix.det_apply']
  rfl

/-- Pointwise double-permutation expansion of the Andreief integrand. -/
theorem andreief_integrand_expand {q : ℕ} {α : Type*} (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ)
    (a : Fin q → α → ℂ) (v : α → (Fin q ⊕ ι) → ℂ) (x : Fin q → α) :
    (Matrix.of fun k l => a k (x l)).det * (rowRepl M (fun l => v (x l))).det =
      ∑ σ : Equiv.Perm (Fin q), ∑ τ : Equiv.Perm (Fin q ⊕ ι),
        sgnC σ * sgnC τ * (∏ i, M (Sum.inr i) (τ (Sum.inr i))) *
          ∏ l, (a (σ l) (x l) * v (x l) (τ (Sum.inl l))) := by
  rw [det_of_apply, det_sum_rows, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro τ _
  simp only [rowRepl, Matrix.of_apply, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib]
  ring

/-- Symmetrized Cauchy-Binet for finitely many frequency rows. -/
theorem discrete_andreief {q : ℕ} {α : Type*} (T : Finset α)
    (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ) (a : Fin q → α → ℂ) (v : α → (Fin q ⊕ ι) → ℂ)
    (hM : ∀ k c, M (Sum.inl k) c = ∑ t ∈ T, a k t * v t c) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin q => T),
        (Matrix.of fun k l => a k (f l)).det * (rowRepl M (fun l => v (f l))).det =
      (q.factorial : ℂ) * M.det := by
  classical
  simp_rw [andreief_integrand_expand M a v]
  rw [Finset.sum_comm]
  rw [← perm_core M]
  apply Finset.sum_congr rfl
  intro σ _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro τ _
  rw [← Finset.mul_sum, ← Finset.prod_univ_sum (t := fun _ : Fin q => T)
    (f := fun l t => a (σ l) t * v t (τ (Sum.inl l)))]
  simp only [← hM]
  ring

/-- Symmetrized Andreief identity for integral rows, with fixed rows kept. -/
theorem continuous_andreief {q : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (M : Matrix (Fin q ⊕ ι) (Fin q ⊕ ι) ℂ) (a : Fin q → ℝ → ℂ) (v : ℝ → (Fin q ⊕ ι) → ℂ)
    (hint : ∀ k c, Integrable (fun x => a k x * v x c) μ)
    (hM : ∀ k c, M (Sum.inl k) c = ∫ x, a k x * v x c ∂μ) :
    (∫ x : Fin q → ℝ, (Matrix.of fun k l => a k (x l)).det *
        (rowRepl M (fun l => v (x l))).det ∂(Measure.pi fun _ => μ)) =
      (q.factorial : ℂ) * M.det := by
  have hterm : ∀ (σ : Equiv.Perm (Fin q)) (τ : Equiv.Perm (Fin q ⊕ ι)),
      Integrable (fun x : Fin q → ℝ => sgnC σ * sgnC τ * (∏ i, M (Sum.inr i) (τ (Sum.inr i))) *
        ∏ l, (a (σ l) (x l) * v (x l) (τ (Sum.inl l)))) (Measure.pi fun _ => μ) := by
    intro σ τ
    apply Integrable.const_mul
    exact Integrable.fintype_prod (μ := fun _ : Fin q => μ)
      (f := fun l x => a (σ l) x * v x (τ (Sum.inl l))) (fun l => hint _ _)
  simp_rw [andreief_integrand_expand M a v]
  rw [integral_finsetSum _ (fun σ _ => integrable_finsetSum _ (fun τ _ => hterm σ τ))]
  rw [← perm_core M]
  apply Finset.sum_congr rfl
  intro σ _
  rw [integral_finsetSum _ (fun τ _ => hterm σ τ)]
  apply Finset.sum_congr rfl
  intro τ _
  rw [integral_const_mul, MeasureTheory.integral_fintype_prod_eq_prod (μ := fun _ : Fin q => μ)
    (f := fun l x => a (σ l) x * v x (τ (Sum.inl l)))]
  simp only [← hM]
  ring

/-- Reindexing rows and columns by two equivalences preserves the norm of the determinant. -/
theorem norm_det_submatrix_equiv {m n : Type*} [Fintype m] [DecidableEq m] [Fintype n]
    [DecidableEq n] (A : Matrix n n ℂ) (e₁ e₂ : m ≃ n) :
    ‖(A.submatrix e₁ e₂).det‖ = ‖A.det‖ := by
  have h : A.submatrix e₁ e₂ = (A.submatrix e₁ e₁).submatrix id (e₂.trans e₁.symm) := by
    ext i j; simp
  rw [h, Matrix.det_permute', Matrix.det_submatrix_equiv_self, norm_mul]
  have : ‖((Equiv.Perm.sign (e₂.trans e₁.symm) : ℤ) : ℂ)‖ = 1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (e₂.trans e₁.symm)) with h | h <;> simp [h]
  rw [this, one_mul]


/-- Every injective tuple with values in `(g, H]` is an increasing cutoff tuple composed with
a permutation (`Tuple.sort`). -/
theorem injective_mem_image_cutoff {g H q : ℕ} (f : Fin q → ℕ)
    (hf : f ∈ Fintype.piFinset (fun _ : Fin q => Ioc g H)) (hinj : Function.Injective f) :
    f ∈ ((FrequencyCutoff.cutoffTuples g q H) ×ˢ (univ : Finset (Equiv.Perm (Fin q)))).image
      (fun p => p.1.val ∘ p.2) := by
  classical
  let σ := Tuple.sort f
  have hmono : Monotone (f ∘ σ) := Tuple.monotone_sort f
  have hinj' : Function.Injective (f ∘ σ) := hinj.comp σ.injective
  have hmem : ∀ i, f i ∈ Ioc g H := fun i => Fintype.mem_piFinset.mp hf i
  let r : FrequencyCutoff.IncreasingTuple g q :=
    ⟨f ∘ σ, hmono.strictMono_of_injective hinj', fun i => (Finset.mem_Ioc.mp (hmem (σ i))).1⟩
  have hr : r ∈ FrequencyCutoff.cutoffTuples g q H := by
    rw [FrequencyCutoff.mem_cutoffTuples]
    intro i
    exact (Finset.mem_Ioc.mp (hmem (σ i))).2
  refine Finset.mem_image.mpr ⟨(r, σ⁻¹), Finset.mem_product.mpr ⟨hr, Finset.mem_univ _⟩, ?_⟩
  funext i
  simp [r]

/-- A symmetric nonnegative weight vanishing on non-injective tuples sums to at most `q!` times
its sum over increasing cutoff tuples. -/
theorem sum_piFinset_le_factorial_mul_cutoff (g H q : ℕ) (G : (Fin q → ℕ) → ℝ)
    (hG0 : ∀ f, 0 ≤ G f) (hsym : ∀ f (π : Equiv.Perm (Fin q)), G (f ∘ π) = G f)
    (hinj : ∀ f, ¬ Function.Injective f → G f = 0) :
    ∑ f ∈ Fintype.piFinset (fun _ : Fin q => Ioc g H), G f ≤
      (q.factorial : ℝ) * ∑ r ∈ FrequencyCutoff.cutoffTuples g q H, G r.val := by
  classical
  set A := Fintype.piFinset (fun _ : Fin q => Ioc g H)
  set P := (FrequencyCutoff.cutoffTuples g q H) ×ˢ (univ : Finset (Equiv.Perm (Fin q)))
  have h1 : ∑ f ∈ A, G f = ∑ f ∈ A.filter Function.Injective, G f := by
    rw [Finset.sum_filter_of_ne]
    intro f _ hf
    by_contra h
    exact hf (hinj f h)
  have h2 : ∑ f ∈ A.filter Function.Injective, G f ≤
      ∑ f ∈ P.image (fun p => p.1.val ∘ p.2), G f := by
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro f hf
      rw [Finset.mem_filter] at hf
      exact injective_mem_image_cutoff f hf.1 hf.2
    · intro f _ _; exact hG0 f
  have h3 : ∑ f ∈ P.image (fun p => p.1.val ∘ p.2), G f ≤ ∑ p ∈ P, G (p.1.val ∘ p.2) :=
    Finset.sum_image_le_of_nonneg (fun p _ => hG0 _)
  have h4 : ∑ p ∈ P, G (p.1.val ∘ p.2) =
      (q.factorial : ℝ) * ∑ r ∈ FrequencyCutoff.cutoffTuples g q H, G r.val := by
    rw [Finset.sum_product, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r _
    simp only [hsym, Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
      nsmul_eq_mul]
  rw [h1]
  exact h2.trans (h3.trans h4.le)

end

end Li2Lean.P0.Env
