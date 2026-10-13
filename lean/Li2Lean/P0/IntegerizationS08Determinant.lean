/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationS08Series
import Li2Lean.P0.IntegerizationFormalMoments
import Li2Lean.P0.IntegerizationActualFeatureTruncation

/-!
# S08 formal feature divisibility of the literal P0 determinant

For `m = 4h`, the literal bivariate determinant `formalCanonicalPolynomial m`
(outer variable `a`, coefficients in `ℚ[T]`) is divisible by `a^(13h^2-4h)`.

Route (paper v13, Lemma `lem:p0-a-divisor`): pass to `ℚ[T][[a]]`, write every
entry, modulo `a^N`, as a finite sum of weighted rank-one features with the
exact supports `I = [h,5h)` and `J = [0,8h)`, and apply the weighted rank-one
determinant kernel over the commutative ring `ℚ[T][[a]]`.  The shear by
`L₁ · (top row)`, the unit `(a-1)^g` on the lower rows and the pencil
translation are absorbed into the (series-valued) left feature vectors, so no
row operation or substitution is needed.
-/

namespace Li2Lean.P0.Integerization.S08

open Finset

noncomputable section

/-- Pencil-coefficient formal power series in the base variable `a`. -/
abbrev PS := PowerSeries (Polynomial ℚ)

/-- Constant-coefficient embedding `ℚ[[a]] → ℚ[T][[a]]`. -/
abbrev phiC : QS →+* PS := PowerSeries.map (Polynomial.C : ℚ →+* Polynomial ℚ)

/-- Coercion of bivariate polynomials to series in the outer variable. -/
abbrev iota : BivPoly →+* PS := Polynomial.coeToPowerSeries.ringHom

/-- Rational constants in `ℚ[T][[a]]`. -/
abbrev kq : ℚ →+* PS := phiC.comp PowerSeries.C

/-- The pencil variable as a constant series. -/
def Tser : PS := PowerSeries.C (Polynomial.X : Polynomial ℚ)

theorem iota_map (p : Polynomial ℚ) :
    iota (p.map (Polynomial.C : ℚ →+* Polynomial ℚ)) = phiC (co p) := by
  ext k
  rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe,
    Polynomial.coeff_map, PowerSeries.coeff_map, coeff_co]

theorem phiC_trunc (N : ℕ) (α : ℕ → ℚ) :
    phiC (∑ k ∈ range N, PowerSeries.C (α k) * PowerSeries.X ^ k) =
      ∑ k ∈ range N, kq (α k) * PowerSeries.X ^ k := by
  simp only [map_sum, map_mul, map_pow, PowerSeries.map_X, RingHom.comp_apply]

theorem phiC_X_pow_dvd {N : ℕ} {x : QS} (h : PowerSeries.X ^ N ∣ x) :
    PowerSeries.X ^ N ∣ phiC x := by
  have := map_dvd phiC h
  simpa only [map_pow, PowerSeries.map_X] using this

/-! ### The formal entries are images of the scalar mirror -/

theorem formalU_eq (g i : ℕ) :
    formalU g i = (uP g i).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  simp [formalU, uP, ratConst, aVar, Polynomial.map_mul, Polynomial.map_pow]

theorem formalQNum_eq (g s : ℕ) :
    formalQNum g s = (qP g s).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  simp [formalQNum, qP, ratConst, aVar, Polynomial.map_mul, Polynomial.map_pow,
    Polynomial.map_sub]

theorem formalTScaled_eq (g i : ℕ) :
    formalTScaled g i = (tsP g i).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  simp only [formalTScaled, tsP, P1, Q1, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_X,
    Polynomial.map_C, formalU_eq, formalQNum_eq, aVar, ratConst]

theorem formalBScaled_eq (g i : ℕ) :
    formalBScaled g i = (bsP g i).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  simp only [formalBScaled, bsP, P2, Q2, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_pow, Polynomial.map_sub, Polynomial.map_sum, Polynomial.map_X,
    Polynomial.map_C, formalU_eq, formalQNum_eq, aVar, ratConst]

theorem formalC_eq (g i j : ℕ) :
    formalC g i j = (cP g i j).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  unfold formalC cP
  split_ifs <;>
    simp only [Polynomial.map_mul, Polynomial.map_neg, Polynomial.map_sub,
      Polynomial.map_C, formalU_eq, ratConst]

theorem formalA_eq (g i j : ℕ) :
    formalA g i j = (aP g i j).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  unfold formalA aP
  split_ifs <;> simp [formalU_eq]

theorem formalB_eq (g i j : ℕ) :
    formalB g i j = (bP g i j).map (Polynomial.C : ℚ →+* Polynomial ℚ) := by
  unfold formalB bP
  split_ifs <;>
    simp only [Polynomial.map_mul, Polynomial.map_sub, Polynomial.map_C,
      formalBScaled_eq, formalTScaled_eq, ratConst]

/-- Row index of the literal matrix. -/
def rowIdx (m : ℕ) (r : Fin (2 * m)) : ℕ :=
  m / 4 + (if r.val < m then r.val else r.val - m)

theorem iota_formalMatrix (m : ℕ) (r c : Fin (2 * m)) :
    iota (formalMatrix m r c) =
      if r.val < m then phiC (co (cP (m / 2) (rowIdx m r) c.val))
      else phiC (co (bP (m / 2) (rowIdx m r) c.val)) -
        Tser * phiC (co (aP (m / 2) (rowIdx m r) c.val)) := by
  unfold formalMatrix rowIdx
  by_cases hr : r.val < m
  · simp only [hr, if_true, formalC_eq, iota_map]
  · simp only [hr, if_false, map_sub, map_mul, formalB_eq, formalA_eq, iota_map]
    congr 2
    rw [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C]
    rfl

/-! ### Feature data -/

def topL (g : ℕ) (t : Fin 3) (k i : ℕ) : ℚ :=
  if t = 0 then eR i k else if t = 1 then 0 else vR i k - hS g k * eR i k

def lowL (g : ℕ) (t : Fin 3) (k i : ℕ) : ℚ :=
  if t = 0 then vR i k - hS g k * eR i k
  else if t = 1 then -eR i k
  else -(vR i k) ^ 2 - hS g k * vR i k + gam g k * eR i k

def rgt (t : Fin 3) (k j : ℕ) : ℚ :=
  if t = 0 then vR j k else if t = 1 then (vR j k) ^ 2 else eR j k

theorem topF_eq (g i j k : ℕ) :
    topF g i j k = ∑ t : Fin 3, topL g t k i * rgt t k j := by
  rw [Fin.sum_univ_three]
  simp [topL, rgt, topF]

theorem lowF_eq (g i j k : ℕ) :
    lowF g i j k = ∑ t : Fin 3, lowL g t k i * rgt t k j := by
  rw [Fin.sum_univ_three]
  simp [lowL, rgt, lowF]

/-- The pencil translation absorbed into the third lower feature. -/
def Yser (g : ℕ) : PS := phiC L2 + Tser * phiC binv ^ g

/-- Series-valued left feature vectors. -/
def featU (m : ℕ) (k : ℕ) (t : Fin 3) (r : Fin (2 * m)) : PS :=
  if r.val < m then kq (cw (m / 2) k * topL (m / 2) t k (rowIdx m r))
  else phiC bS ^ (m / 2) *
    (kq (cw (m / 2) k * lowL (m / 2) t k (rowIdx m r)) +
      phiC L1 * kq (cw (m / 2) k * topL (m / 2) t k (rowIdx m r)) -
      (if t = 2 then Yser (m / 2) * kq (cw (m / 2) k * eR (rowIdx m r) k) else 0))

/-- Rational right feature vectors. -/
def featV (m : ℕ) (k : ℕ) (t : Fin 3) (c : Fin (2 * m)) : PS :=
  kq (rgt t k c.val)

open Classical in
/-- Feature weight: the `a`-exponent for an admissible feature, `N` otherwise. -/
def featW (h : ℕ) (f : Fin (13 * h ^ 2 - 4 * h) × Fin 3) : ℕ :=
  if p0FeatureAllowed h ((f.1 : ℕ), f.2) then (f.1 : ℕ) else 13 * h ^ 2 - 4 * h

theorem featW_bound (h : ℕ)
    (p : Fin (2 * (4 * h)) → Fin (13 * h ^ 2 - 4 * h) × Fin 3)
    (hp : Function.Injective p) :
    13 * h ^ 2 - 4 * h ≤ ∑ j, featW h (p j) := by
  classical
  by_cases hall : ∀ j, p0FeatureAllowed h (((p j).1 : ℕ), (p j).2)
  · have e : 8 * h = 2 * (4 * h) := by ring
    let q : Fin (8 * h) → ℕ × Fin 3 := fun j =>
      (((p (finCongr e j)).1 : ℕ), (p (finCongr e j)).2)
    have hq : Function.Injective q := by
      intro a b hab
      simp only [q, Prod.mk.injEq] at hab
      have : p (finCongr e a) = p (finCongr e b) := Prod.ext (Fin.ext hab.1) hab.2
      exact (finCongr e).injective (hp this)
    have hb := p0_actual_feature_exponent_lower_bound h q hq (fun j => hall _)
    calc 13 * h ^ 2 - 4 * h ≤ ∑ j, (q j).1 := hb
      _ = ∑ j : Fin (2 * (4 * h)), ((p j).1 : ℕ) :=
          Fintype.sum_equiv (finCongr e) _ _ (fun j => rfl)
      _ = ∑ j, featW h (p j) := by
          apply sum_congr rfl
          intro j _
          simp [featW, hall j]
  · push_neg at hall
    obtain ⟨j0, hj0⟩ := hall
    calc 13 * h ^ 2 - 4 * h = featW h (p j0) := by simp [featW, hj0]
      _ ≤ ∑ j, featW h (p j) :=
          Finset.single_le_sum (f := fun j => featW h (p j))
            (fun _ _ => Nat.zero_le _) (mem_univ j0)

/-- The rank-one model matrix. -/
def featMatrix (h : ℕ) : Matrix (Fin (2 * (4 * h))) (Fin (2 * (4 * h))) PS :=
  Matrix.of fun r c => ∑ f : Fin (13 * h ^ 2 - 4 * h) × Fin 3,
    featU (4 * h) f.1 f.2 r * (PowerSeries.X ^ featW h f * featV (4 * h) f.1 f.2 c)

theorem featMatrix_det_dvd (h : ℕ) :
    PowerSeries.X ^ (13 * h ^ 2 - 4 * h) ∣ (featMatrix h).det := by
  exact pow_dvd_det_weighted_rank_one (R := PS) (n := Fin (2 * (4 * h)))
    (κ := Fin (13 * h ^ 2 - 4 * h) × Fin 3) PowerSeries.X
    (fun f r => featU (4 * h) f.1 f.2 r) (fun f c => featV (4 * h) f.1 f.2 c)
    (featW h) (13 * h ^ 2 - 4 * h) (featW_bound h)

theorem rowIdx_bounds (h : ℕ) (r : Fin (2 * (4 * h))) :
    h ≤ rowIdx (4 * h) r ∧ rowIdx (4 * h) r < 5 * h := by
  have hr := r.isLt
  have e : 4 * h / 4 = h := by omega
  unfold rowIdx
  rw [e]
  split_ifs <;> omega

/-- Forbidden features contribute nothing. -/
theorem feat_forbidden (h : ℕ) (k : ℕ) (t : Fin 3) (r c : Fin (2 * (4 * h)))
    (hf : ¬ p0FeatureAllowed h (k, t)) :
    featU (4 * h) k t r * featV (4 * h) k t c = 0 := by
  have hrb := rowIdx_bounds h r
  have hc := c.isLt
  unfold p0FeatureAllowed at hf
  simp only [not_and_or, not_imp] at hf
  rcases hf with ⟨ht, hk⟩ | ⟨ht, hk⟩
  · subst ht
    have hik : rowIdx (4 * h) r ≠ k := by omega
    have hz : featU (4 * h) k 1 r = 0 := by
      unfold featU topL lowL
      simp [eR, hik]
    rw [hz, zero_mul]
  · subst ht
    have hjk : (c : ℕ) ≠ k := by omega
    have hz : featV (4 * h) k 2 c = 0 := by
      unfold featV rgt
      simp [eR, hjk]
    rw [hz, mul_zero]

theorem featMatrix_apply (h : ℕ) (r c : Fin (2 * (4 * h))) :
    featMatrix h r c = ∑ k ∈ range (13 * h ^ 2 - 4 * h), ∑ t : Fin 3,
      featU (4 * h) k t r * (PowerSeries.X ^ k * featV (4 * h) k t c) := by
  classical
  unfold featMatrix
  rw [Matrix.of_apply, Fintype.sum_prod_type]
  rw [← Fin.sum_univ_eq_sum_range (fun k => ∑ t : Fin 3,
      featU (4 * h) k t r * (PowerSeries.X ^ k * featV (4 * h) k t c))]
  apply sum_congr rfl
  intro k _
  apply sum_congr rfl
  intro t _
  unfold featW
  split_ifs with hf
  · rfl
  · have hz := feat_forbidden h k t r c hf
    calc featU (4 * h) (↑k) t r *
          (PowerSeries.X ^ (13 * h ^ 2 - 4 * h) * featV (4 * h) (↑k) t c)
        = PowerSeries.X ^ (13 * h ^ 2 - 4 * h) *
            (featU (4 * h) (↑k) t r * featV (4 * h) (↑k) t c) := by ring
      _ = 0 := by rw [hz, mul_zero]
      _ = PowerSeries.X ^ (k : ℕ) *
            (featU (4 * h) (↑k) t r * featV (4 * h) (↑k) t c) := by rw [hz, mul_zero]
      _ = featU (4 * h) (↑k) t r * (PowerSeries.X ^ (k : ℕ) * featV (4 * h) (↑k) t c) := by
          ring

/-! ### Entrywise congruence -/

theorem top_row_sum (g i j k : ℕ) :
    ∑ t : Fin 3, kq (cw g k * topL g t k i) * (PowerSeries.X ^ k * kq (rgt t k j)) =
      kq (cw g k * topF g i j k) * PowerSeries.X ^ k := by
  rw [topF_eq, mul_sum, map_sum, sum_mul]
  apply sum_congr rfl
  intro t _
  simp only [map_mul]
  ring

theorem low_row_sum (g i j k : ℕ) (b l1 y : PS) :
    ∑ t : Fin 3, b * (kq (cw g k * lowL g t k i) + l1 * kq (cw g k * topL g t k i) -
        (if t = 2 then y * kq (cw g k * eR i k) else 0)) *
        (PowerSeries.X ^ k * kq (rgt t k j)) =
      b * (kq (cw g k * lowF g i j k) * PowerSeries.X ^ k +
        l1 * (kq (cw g k * topF g i j k) * PowerSeries.X ^ k) -
        y * (kq (cw g k * (eR i k * eR j k)) * PowerSeries.X ^ k)) := by
  rw [lowF_eq, topF_eq, Fin.sum_univ_three, Fin.sum_univ_three, Fin.sum_univ_three]
  simp only [rgt, Fin.isValue, show (0 : Fin 3) ≠ 2 by decide,
    show (1 : Fin 3) ≠ 2 by decide, show (1 : Fin 3) ≠ 0 by decide,
    show (2 : Fin 3) ≠ 0 by decide, show (2 : Fin 3) ≠ 1 by decide,
    if_true, if_false, map_mul, map_add]
  ring

theorem entry_congr (h : ℕ) (hh : 1 ≤ h) (r c : Fin (2 * (4 * h))) :
    PowerSeries.X ^ (13 * h ^ 2 - 4 * h) ∣
      iota (formalMatrix (4 * h) r c) - featMatrix h r c := by
  set N := 13 * h ^ 2 - 4 * h with hN
  set g := 4 * h / 2 with hg
  have hg1 : 1 ≤ g := by omega
  set i := rowIdx (4 * h) r with hi
  set j : ℕ := c.val with hj
  -- the three scalar congruences
  have dC := X_pow_dvd_sub_trunc N (co (cP g i j)) (fun k => cw g k * topF g i j k)
    (fun k _ => coeff_top g i j k)
  have dE := X_pow_dvd_sub_trunc N (Eser g i j) (fun k => cw g k * lowF g i j k)
    (fun k _ => coeff_low g i j k hg1)
  have dA := X_pow_dvd_sub_trunc N (co (aP g i j)) (fun k => cw g k * (eR i k * eR j k))
    (fun k _ => coeff_aP g i j k)
  have mC := phiC_X_pow_dvd dC
  have mE := phiC_X_pow_dvd dE
  have mA := phiC_X_pow_dvd dA
  simp only [map_sub, phiC_trunc] at mC mE mA
  rw [featMatrix_apply, iota_formalMatrix]
  by_cases hr : r.val < 4 * h
  · rw [if_pos hr]
    have hsum : ∑ k ∈ range N, ∑ t : Fin 3,
        featU (4 * h) k t r * (PowerSeries.X ^ k * featV (4 * h) k t c) =
        ∑ k ∈ range N, kq (cw g k * topF g i j k) * PowerSeries.X ^ k := by
      apply sum_congr rfl
      intro k _
      rw [← top_row_sum]
      apply sum_congr rfl
      intro t _
      simp only [featU, featV, if_pos hr]
      rfl
    rw [hsum]
    exact mC
  · rw [if_neg hr]
    have hsum : ∑ k ∈ range N, ∑ t : Fin 3,
        featU (4 * h) k t r * (PowerSeries.X ^ k * featV (4 * h) k t c) =
        phiC bS ^ g * (∑ k ∈ range N, kq (cw g k * lowF g i j k) * PowerSeries.X ^ k +
          phiC L1 * ∑ k ∈ range N, kq (cw g k * topF g i j k) * PowerSeries.X ^ k -
          Yser g * ∑ k ∈ range N, kq (cw g k * (eR i k * eR j k)) * PowerSeries.X ^ k) := by
      rw [mul_sum (s := range N) (a := phiC L1), mul_sum (s := range N) (a := Yser g),
        ← sum_add_distrib, ← sum_sub_distrib, mul_sum]
      apply sum_congr rfl
      intro k _
      rw [← low_row_sum g i j k (phiC bS ^ g) (phiC L1) (Yser g)]
      apply sum_congr rfl
      intro t _
      simp only [featU, featV, if_neg hr]
      rfl
    rw [hsum]
    -- express the actual lower entry through `Eser`
    have hb : phiC bS ^ g * phiC binv ^ g = 1 := by
      rw [← mul_pow, ← map_mul, bS_mul_binv, map_one, one_pow]
    have hbP : phiC (co (bP g i j)) = phiC bS ^ g *
        (phiC (Eser g i j) + phiC L1 * phiC (co (cP g i j)) -
          phiC L2 * phiC (co (aP g i j))) := by
      have : co (bP g i j) = bS ^ g *
          (Eser g i j + L1 * co (cP g i j) - L2 * co (aP g i j)) := by
        unfold Eser
        have hb0 : bS ^ g * binv ^ g = 1 := by rw [← mul_pow, bS_mul_binv, one_pow]
        linear_combination (-(co (bP g i j))) * hb0
      rw [this]
      simp only [map_mul, map_pow, map_add, map_sub]
    rw [hbP]
    set E := phiC (Eser g i j)
    set Cc := phiC (co (cP g i j))
    set Aa := phiC (co (aP g i j))
    set TE := ∑ k ∈ range N, kq (cw g k * lowF g i j k) * PowerSeries.X ^ k
    set TC := ∑ k ∈ range N, kq (cw g k * topF g i j k) * PowerSeries.X ^ k
    set TA := ∑ k ∈ range N, kq (cw g k * (eR i k * eR j k)) * PowerSeries.X ^ k
    have key : phiC bS ^ g * (E + phiC L1 * Cc - phiC L2 * Aa) - Tser * Aa -
        phiC bS ^ g * (TE + phiC L1 * TC - Yser g * TA) =
        phiC bS ^ g * ((E - TE) + phiC L1 * (Cc - TC) - Yser g * (Aa - TA)) := by
      unfold Yser
      linear_combination (Tser * Aa) * hb
    rw [key]
    apply dvd_mul_of_dvd_right
    exact dvd_sub (dvd_add mE (dvd_mul_of_dvd_right mC _)) (dvd_mul_of_dvd_right mA _)

/-! ### The formal feature divisibility -/

theorem formalCanonical_feature_dvd (h : ℕ) (hh : 1 ≤ h) :
    (Polynomial.X : BivPoly) ^ (13 * h ^ 2 - 4 * h) ∣
      formalCanonicalPolynomial (4 * h) := by
  have hdet : PowerSeries.X ^ (13 * h ^ 2 - 4 * h) ∣
      iota (formalCanonicalPolynomial (4 * h)) := by
    unfold formalCanonicalPolynomial
    rw [RingHom.map_det]
    apply dvd_det_of_entrywise_congr _ _ (featMatrix h)
    · intro r c
      exact entry_congr h hh r c
    · exact featMatrix_det_dvd h
  rw [Polynomial.X_pow_dvd_iff]
  intro d hd
  have hz := (PowerSeries.X_pow_dvd_iff.mp hdet) d hd
  rwa [Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coeff_coe] at hz

end

end Li2Lean.P0.Integerization.S08

#print axioms Li2Lean.P0.Integerization.S08.featW_bound
#print axioms Li2Lean.P0.Integerization.S08.entry_congr
#print axioms Li2Lean.P0.Integerization.S08.formalCanonical_feature_dvd
