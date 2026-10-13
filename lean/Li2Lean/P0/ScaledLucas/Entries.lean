/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ScaledLucas.Basic

/-!
# Scaled C and B entries of the `a = 2` P0 pencil modulo 83

Entry formulas `EC` and `EB` over the full row/column ranges, and their
`k = 0` specializations `seedC` and `seedB` for the literal 64-by-64 seed.
-/

namespace Li2Lean.P0
namespace ScaledLucas

noncomputable section

open ControlledResidue
open Finset

local instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

set_option hygiene false in
/-- `omega` after abstracting the block length `83 ^ k` to an atom. -/
local macro "qomega" : tactic => `(tactic| (generalize 83 ^ k = q at *; omega))

/-! ## The scaled C entries `q C_ij` -/

theorem qC_diag_decomp (k g i : ℕ) :
    qRat k * p0CQ (2 : ℚ) g i i =
      -p0UQ (2 : ℚ) g i * ∑ s ∈ range g, qRat k / ((i + s + 1 : ℕ) : ℚ) := by
  unfold p0CQ
  rw [if_pos rfl]
  simp only [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro s hs
  push_cast
  ring

theorem qC_off_decomp (k g i j : ℕ) (hij : i ≠ j) :
    qRat k * p0CQ (2 : ℚ) g i j =
      (p0UQ (2 : ℚ) g i - p0UQ (2 : ℚ) g j) *
        (qRat k / ((j : ℚ) - (i : ℚ))) := by
  unfold p0CQ
  rw [if_neg hij]
  ring

theorem ar_split0 (A c q v t : ℕ) :
    A * q + v + (c * q + t) + 1 = (A + c) * q + (v + t + 1) := by ring

theorem ar_split1 (A c q v t : ℕ) (h : q ≤ v + t + 1) :
    A * q + v + (c * q + t) + 1 = (A + c + 1) * q + (v + t + 1 - q) := by
  have h1 : (A + c + 1) * q = A * q + c * q + q := by ring
  omega

theorem ar_diag_hit (A c q v : ℕ) (hv : v < q) :
    A * q + v + (c * q + (q - 1 - v)) + 1 = (A + c + 1) * q := by
  have h1 : (A + c + 1) * q = A * q + c * q + q := by ring
  omega

theorem cast_qC_diag (k A v : ℕ) (hA : A < 40) (hv : v < 83 ^ k) :
    ((qRat k * p0CQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v)
        (A * 83 ^ k + v) : ℚ) : F83) =
      (2 : F83) ^ v *
        (-YU A * ∑ c ∈ range 16, (((A + c + 1 : ℕ) : F83))⁻¹) := by
  have hq : 0 < 83 ^ k := by positivity
  have hiq : A * 83 ^ k + v < 40 * 83 ^ k := ar_lt A v _ 40 hA hv
  rw [qC_diag_decomp]
  have hm : ∀ s ∈ range (16 * 83 ^ k),
      qRat k / ((A * 83 ^ k + v + s + 1 : ℕ) : ℚ) ∈ Good83 := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    exact qdiv_mem k _ (by omega) (ar_lt83 _ _ 57 (by qomega) (by norm_num))
  rw [cast_mul' (Good83.neg_mem (mem_U _ _)) (Good83.sum_mem hm), Rat.cast_neg,
    cast_U k A v hv, cast_sum' _ _ hm]
  have hsum : (∑ s ∈ range (16 * 83 ^ k),
      ((qRat k / ((A * 83 ^ k + v + s + 1 : ℕ) : ℚ) : ℚ) : F83)) =
      ∑ c ∈ range 16, (((A + c + 1 : ℕ) : F83))⁻¹ := by
    rw [block_sum_full (83 ^ k) (83 ^ k - 1 - v) _ (by qomega) 16]
    · apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      rw [show A * 83 ^ k + v + (c * 83 ^ k + (83 ^ k - 1 - v)) + 1 =
          (A + c + 1) * 83 ^ k from ar_diag_hit A c _ v hv,
        qdiv_cast_unit k (A + c + 1) (by omega) (by omega)]
    · intro c hc t ht htt
      have hnd : ¬ 83 ^ k ∣ A * 83 ^ k + v + (c * 83 ^ k + t) + 1 := by
        by_cases hlt : v + t + 1 < 83 ^ k
        · exact not_dvd_of_rem (m := A + c) (x := v + t + 1)
            (ar_split0 A c _ v t) (by omega) hlt
        · have hge : 83 ^ k ≤ v + t + 1 := by omega
          exact not_dvd_of_rem (m := A + c + 1) (x := v + t + 1 - 83 ^ k)
            (ar_split1 A c _ v t hge) (by qomega) (by qomega)
      rw [qdiv_cast_zero k _ (by omega) hnd]
  rw [hsum]
  ring

/-- The reduced seed entry of the C block. -/
def YC (A b : ℕ) : F83 :=
  if A = b then -YU A * ∑ c ∈ range 16, (((A + c + 1 : ℕ) : F83))⁻¹
  else (YU A - YU b) * ((((b : ℤ) - (A : ℤ) : ℤ) : F83))⁻¹

theorem decomp_ne_of_ne_rem {q A b v w : ℕ} (hv : v < q) (hw : w < q)
    (hvw : v ≠ w) : A * q + v ≠ b * q + w := by
  intro h
  apply hvw
  have h' : (A * q + v) % q = (b * q + w) % q := by rw [h]
  rwa [mod_of_decomp hv, mod_of_decomp hw] at h'

theorem decomp_ne_of_ne_quot {q A b v : ℕ} (hq : 0 < q) (hAb : A ≠ b) :
    A * q + v ≠ b * q + v := by
  intro h
  apply hAb
  exact Nat.eq_of_mul_eq_mul_right hq (by omega)

theorem EC (k A b v w : ℕ) (hA : A < 40) (hb : b < 64)
    (hv : v < 83 ^ k) (hw : w < 83 ^ k) :
    ((qRat k * p0CQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v)
        (b * 83 ^ k + w) : ℚ) : F83) =
      if v = w then (2 : F83) ^ v * YC A b else 0 := by
  have hq : 0 < 83 ^ k := by positivity
  have hi : A * 83 ^ k + v < 64 * 83 ^ k := ar_lt A v _ 64 (by omega) hv
  have hj : b * 83 ^ k + w < 64 * 83 ^ k := ar_lt b w _ 64 hb hw
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl]
    by_cases hAb : A = b
    · subst hAb
      rw [cast_qC_diag k A v hA hv, YC, if_pos rfl]
    · have hij := decomp_ne_of_ne_quot (v := v) hq hAb
      have hmax : max (A * 83 ^ k + v) (b * 83 ^ k + v) < 83 * 83 ^ k :=
        max_lt (ar_lt83 _ _ 64 hi (by norm_num)) (ar_lt83 _ _ 64 hj (by norm_num))
      rw [qC_off_decomp k _ _ _ hij,
        cast_mul' (Good83.sub_mem (mem_U _ _) (mem_U _ _))
          (q_div_diff_good k _ _ hij hmax),
        cast_sub' (mem_U _ _) (mem_U _ _), cast_U k A v hv, cast_U k b v hv,
        qdiff_eq_unit k A b v hAb,
        cast_inv_int (by omega) (small_diff (by omega) hb), YC, if_neg hAb]
      ring
  · rw [if_neg hvw]
    have hij := decomp_ne_of_ne_rem (A := A) (b := b) hv hw hvw
    have hmax : max (A * 83 ^ k + v) (b * 83 ^ k + w) < 83 * 83 ^ k :=
      max_lt (ar_lt83 _ _ 64 hi (by norm_num)) (ar_lt83 _ _ 64 hj (by norm_num))
    rw [qC_off_decomp k _ _ _ hij,
      cast_mul' (Good83.sub_mem (mem_U _ _) (mem_U _ _))
        (q_div_diff_good k _ _ hij hmax),
      qdiff_cast_zero k _ _ hij (by rw [mod_of_decomp hv, mod_of_decomp hw]; exact hvw),
      mul_zero]

theorem qRat_zero : qRat 0 = 1 := by
  rw [qRat_eq]
  norm_num

/-- The literal seed C entries are the `k = 0` case of `EC`. -/
theorem seedC (A b : ℕ) (hA : A < 40) (hb : b < 64) :
    ((p0CQ (2 : ℚ) 16 A b : ℚ) : F83) = YC A b := by
  have h := EC 0 A b 0 0 hA hb (by norm_num) (by norm_num)
  simpa only [qRat_zero, pow_zero, mul_one, add_zero, one_mul, if_true] using h

/-! ## The scaled B entries `q² B_ij` -/

theorem sum_Icc_two_eq {M' : Type*} [AddCommMonoid M'] (g : ℕ) (f : ℕ → M')
    (h1 : f 1 = 0) :
    ∑ s ∈ Icc 2 g, f s = ∑ s ∈ range g, f (s + 1) := by
  induction g with
  | zero => simp
  | succ g ih =>
      rw [Finset.sum_range_succ, ← ih]
      rcases Nat.eq_zero_or_pos g with hg | hg
      · subst hg
        simp [h1]
      · rw [Finset.sum_Icc_succ_top (by omega)]

/-- Outer factor of the second part of the diagonal second moment. -/
def B2 (g i s : ℕ) : ℚ :=
  (2 : ℚ) ^ i * (-1 : ℚ) ^ (s + 1) * (Nat.choose (i + g) (g - (s + 1)) : ℚ)

/-- Inner sum of the second part of the diagonal second moment, scaled. -/
def BI (k s : ℕ) : ℚ :=
  ∑ r ∈ range s, p0Q (2 : ℚ) (r + 1) * (qRat k / ((r + 1 : ℕ) : ℚ))

theorem mem_B2 (g i s : ℕ) : B2 g i s ∈ Good83 :=
  Good83.mul_mem (Good83.mul_mem (mem_two_pow i) (mem_neg_one_pow _)) (mem_nat _)

theorem mem_BI (k s : ℕ) (hs : s < 83 * 83 ^ k) : BI k s ∈ Good83 := by
  apply Good83.sum_mem
  intro r hr
  have hr' := Finset.mem_range.mp hr
  exact Good83.mul_mem (mem_Q _) (qdiv_mem k _ (by omega) (by qomega))

theorem qqBB_decomp (k g i : ℕ) :
    (qRat k) ^ 2 * p0BQQ (2 : ℚ) g i =
      (∑ r ∈ range i, p0UQ (2 : ℚ) g (i - (r + 1)) *
          (qRat k / ((r + 1 : ℕ) : ℚ)) * (qRat k / ((r + 1 : ℕ) : ℚ))) -
        ∑ s ∈ range g, B2 g i s * (qRat k / ((s + 1 : ℕ) : ℚ)) * BI k s := by
  unfold p0BQQ
  rw [mul_sub]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    simp only [div_eq_mul_inv, ← inv_pow]
    ring
  · rw [sum_Icc_two_eq g _ (by simp), ← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    have hBI : BI k s = qRat k *
        ∑ r ∈ range s, p0Q (2 : ℚ) (r + 1) / ((r : ℚ) + 1) := by
      unfold BI
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro r hr
      push_cast
      ring
    rw [hBI]
    simp only [B2, Nat.add_sub_cancel]
    push_cast
    ring

/-- The reduced seed value of the diagonal second moment. -/
def YBB (A : ℕ) : F83 :=
  (∑ c ∈ range A, YU (A - (c + 1)) * (((c + 1 : ℕ) : F83))⁻¹ *
      (((c + 1 : ℕ) : F83))⁻¹) -
    (2 : F83) ^ A * ∑ c ∈ range 16,
      (-1 : F83) ^ (c + 1) * ((Nat.choose (A + 16) (16 - (c + 1)) : ℕ) : F83) *
        (((c + 1 : ℕ) : F83))⁻¹ *
        ∑ d ∈ range c, ((2 : F83) ^ (d + 1) - 1) * (((d + 1 : ℕ) : F83))⁻¹

theorem cast_B2_block (k A v c : ℕ) (hv : v < 83 ^ k) (hc : c < 16) :
    ((B2 (16 * 83 ^ k) (A * 83 ^ k + v) (c * 83 ^ k + (83 ^ k - 1)) : ℚ) : F83) =
      (2 : F83) ^ v * ((2 : F83) ^ A * ((-1 : F83) ^ (c + 1) *
        ((Nat.choose (A + 16) (16 - (c + 1)) : ℕ) : F83))) := by
  have hq : 0 < 83 ^ k := by positivity
  unfold B2
  rw [cast_mul' (Good83.mul_mem (mem_two_pow _) (mem_neg_one_pow _)) (mem_nat _),
    cast_mul' (mem_two_pow _) (mem_neg_one_pow _),
    Rat.cast_natCast, cast_two_pow_frob, cast_neg_one_pow,
    ar_last c _ hq, neg_one_pow_frob]
  have hch : Nat.choose (A * 83 ^ k + v + 16 * 83 ^ k)
      (16 * 83 ^ k - (c + 1) * 83 ^ k) =
      Nat.choose ((A + 16) * 83 ^ k + v) ((16 - (c + 1)) * 83 ^ k) := by
    rw [Nat.sub_mul]
    congr 1
    ring
  rw [hch, cast_choose_lucas k (A + 16) (16 - (c + 1)) v hv]
  ring

theorem cast_BI_block (k c : ℕ) (hc : c < 16) :
    ((BI k (c * 83 ^ k + (83 ^ k - 1)) : ℚ) : F83) =
      ∑ d ∈ range c, ((2 : F83) ^ (d + 1) - 1) * (((d + 1 : ℕ) : F83))⁻¹ := by
  have hq : 0 < 83 ^ k := by positivity
  have hcq : c * 83 ^ k + (83 ^ k - 1) < 16 * 83 ^ k := ar_lt c _ _ 16 hc (by omega)
  have hm : ∀ r ∈ range (c * 83 ^ k + (83 ^ k - 1)),
      p0Q (2 : ℚ) (r + 1) * (qRat k / ((r + 1 : ℕ) : ℚ)) ∈ Good83 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    exact Good83.mul_mem (mem_Q _)
      (qdiv_mem k _ (by omega) (ar_lt83 _ _ 16 (by omega) (by norm_num)))
  unfold BI
  rw [cast_sum' _ _ hm, block_sum (83 ^ k) c (83 ^ k - 1) (83 ^ k - 1) _ (by omega)]
  · apply Finset.sum_congr rfl
    intro d hd
    have hd' := Finset.mem_range.mp hd
    have hlt : d * 83 ^ k + (83 ^ k - 1) < 16 * 83 ^ k :=
      ar_lt d _ _ 16 (by omega) (by omega)
    rw [cast_mul' (mem_Q _) (qdiv_mem k _ (by omega)
        (ar_lt83 _ _ 17 (by qomega) (by norm_num))),
      ar_last d _ hq, cast_Q_scaled, qdiv_cast_unit k (d + 1) (by omega) (by omega)]
  · intro d hd t ht htt
    have hlt : d * 83 ^ k + t < 16 * 83 ^ k := ar_lt d t _ 16 (by omega) ht
    have ht1 : t + 1 < 83 ^ k := by qomega
    rw [cast_mul' (mem_Q _) (qdiv_mem k _ (by omega)
        (ar_lt83 _ _ 17 (by qomega) (by norm_num))),
      qdiv_cast_zero k _ (by omega)
        (not_dvd_of_rem (m := d) (x := t + 1) (by ring) (by omega) ht1),
      mul_zero]
  · intro t ht
    have ht1 : t + 1 < 83 ^ k := by qomega
    rw [cast_mul' (mem_Q _) (qdiv_mem k _ (by omega)
        (ar_lt83 _ _ 17 (by qomega) (by norm_num))),
      qdiv_cast_zero k _ (by omega)
        (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by omega) ht1),
      mul_zero]

theorem cast_qqBB (k A v : ℕ) (hA : A < 40) (hv : v < 83 ^ k) :
    (((qRat k) ^ 2 * p0BQQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v) : ℚ) : F83) =
      (2 : F83) ^ v * YBB A := by
  have hq : 0 < 83 ^ k := by positivity
  have hiq : A * 83 ^ k + v < 40 * 83 ^ k := ar_lt A v _ 40 hA hv
  rw [qqBB_decomp]
  have hm1 : ∀ r ∈ range (A * 83 ^ k + v),
      p0UQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v - (r + 1)) *
        (qRat k / ((r + 1 : ℕ) : ℚ)) * (qRat k / ((r + 1 : ℕ) : ℚ)) ∈ Good83 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    have hd := qdiv_mem k (r + 1) (by omega) (ar_lt83 _ _ 40 (by omega) (by norm_num))
    exact Good83.mul_mem (Good83.mul_mem (mem_U _ _) hd) hd
  have hm2 : ∀ s ∈ range (16 * 83 ^ k),
      B2 (16 * 83 ^ k) (A * 83 ^ k + v) s * (qRat k / ((s + 1 : ℕ) : ℚ)) *
        BI k s ∈ Good83 := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    exact Good83.mul_mem (Good83.mul_mem (mem_B2 _ _ _)
      (qdiv_mem k _ (by omega) (ar_lt83 _ _ 17 (by qomega) (by norm_num))))
      (mem_BI k s (ar_lt83 _ _ 16 hs' (by norm_num)))
  rw [cast_sub' (Good83.sum_mem hm1) (Good83.sum_mem hm2),
    cast_sum' _ _ hm1, cast_sum' _ _ hm2]
  have hS1 : (∑ r ∈ range (A * 83 ^ k + v),
      ((p0UQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v - (r + 1)) *
        (qRat k / ((r + 1 : ℕ) : ℚ)) * (qRat k / ((r + 1 : ℕ) : ℚ)) : ℚ) : F83)) =
      (2 : F83) ^ v * ∑ c ∈ range A, YU (A - (c + 1)) *
        (((c + 1 : ℕ) : F83))⁻¹ * (((c + 1 : ℕ) : F83))⁻¹ := by
    rw [block_sum (83 ^ k) A v (83 ^ k - 1) _ (by qomega)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * 83 ^ k + (83 ^ k - 1) < A * 83 ^ k :=
        ar_lt c _ _ A hc' (by qomega)
      have hd := qdiv_mem k (c * 83 ^ k + (83 ^ k - 1) + 1) (by omega)
        (ar_lt83 _ _ 40 (by qomega) (by norm_num))
      rw [cast_mul' (Good83.mul_mem (mem_U _ _) hd) hd, cast_mul' (mem_U _ _) hd,
        ar_shift A c _ v hc' hq, ar_last c _ hq, cast_U k _ v hv,
        qdiv_cast_unit k (c + 1) (by omega) (by omega)]
      ring
    · intro c hc t ht htt
      have hlt : c * 83 ^ k + t < A * 83 ^ k := ar_lt c t _ A hc ht
      have ht1 : t + 1 < 83 ^ k := by qomega
      have hd := qdiv_mem k (c * 83 ^ k + t + 1) (by omega)
        (ar_lt83 _ _ 40 (by qomega) (by norm_num))
      rw [cast_mul' (Good83.mul_mem (mem_U _ _) hd) hd, cast_mul' (mem_U _ _) hd,
        qdiv_cast_zero k _ (by omega)
          (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by omega) ht1),
        mul_zero]
    · intro t ht
      have ht1 : t + 1 < 83 ^ k := by qomega
      have hd := qdiv_mem k (A * 83 ^ k + t + 1) (by omega)
        (ar_lt83 _ _ 40 (by qomega) (by norm_num))
      rw [cast_mul' (Good83.mul_mem (mem_U _ _) hd) hd, cast_mul' (mem_U _ _) hd,
        qdiv_cast_zero k _ (by omega)
          (not_dvd_of_rem (m := A) (x := t + 1) (by ring) (by omega) ht1),
        mul_zero]
  have hS2 : (∑ s ∈ range (16 * 83 ^ k),
      ((B2 (16 * 83 ^ k) (A * 83 ^ k + v) s * (qRat k / ((s + 1 : ℕ) : ℚ)) *
        BI k s : ℚ) : F83)) =
      (2 : F83) ^ v * ((2 : F83) ^ A * ∑ c ∈ range 16,
        (-1 : F83) ^ (c + 1) * ((Nat.choose (A + 16) (16 - (c + 1)) : ℕ) : F83) *
          (((c + 1 : ℕ) : F83))⁻¹ *
          ∑ d ∈ range c, ((2 : F83) ^ (d + 1) - 1) * (((d + 1 : ℕ) : F83))⁻¹) := by
    rw [block_sum_full (83 ^ k) (83 ^ k - 1) _ (by qomega) 16]
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * 83 ^ k + (83 ^ k - 1) < 16 * 83 ^ k :=
        ar_lt c _ _ 16 hc' (by qomega)
      have hd := qdiv_mem k (c * 83 ^ k + (83 ^ k - 1) + 1) (by omega)
        (ar_lt83 _ _ 17 (by qomega) (by norm_num))
      rw [cast_mul' (Good83.mul_mem (mem_B2 _ _ _) hd)
          (mem_BI k _ (ar_lt83 _ _ 16 hlt (by norm_num))),
        cast_mul' (mem_B2 _ _ _) hd, cast_B2_block k A v c hv hc',
        cast_BI_block k c hc', ar_last c _ hq,
        qdiv_cast_unit k (c + 1) (by omega) (by omega)]
      ring
    · intro c hc t ht htt
      have hlt : c * 83 ^ k + t < 16 * 83 ^ k := ar_lt c t _ 16 hc ht
      have ht1 : t + 1 < 83 ^ k := by qomega
      have hd := qdiv_mem k (c * 83 ^ k + t + 1) (by omega)
        (ar_lt83 _ _ 17 (by qomega) (by norm_num))
      rw [cast_mul' (Good83.mul_mem (mem_B2 _ _ _) hd)
          (mem_BI k _ (ar_lt83 _ _ 16 hlt (by norm_num))),
        cast_mul' (mem_B2 _ _ _) hd,
        qdiv_cast_zero k _ (by omega)
          (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by omega) ht1),
        mul_zero, zero_mul]
  rw [hS1, hS2, YBB]
  ring

theorem qqB_off_decomp (k g i j : ℕ) (hij : i ≠ j) :
    (qRat k) ^ 2 * p0BQ (2 : ℚ) g i j =
      (qRat k * p0TQ (2 : ℚ) g i - qRat k * p0TQ (2 : ℚ) g j) *
        (qRat k / ((j : ℚ) - (i : ℚ))) := by
  unfold p0BQ
  rw [if_neg hij]
  ring

/-- The reduced seed entry of the B block. -/
def YB (A b : ℕ) : F83 :=
  if A = b then YBB A
  else (YT A - YT b) * ((((b : ℤ) - (A : ℤ) : ℤ) : F83))⁻¹

theorem EB (k A b v w : ℕ) (hA : A < 40) (hb : b < 64)
    (hv : v < 83 ^ k) (hw : w < 83 ^ k) :
    (((qRat k) ^ 2 * p0BQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v)
        (b * 83 ^ k + w) : ℚ) : F83) =
      if v = w then (2 : F83) ^ v * YB A b else 0 := by
  have hq : 0 < 83 ^ k := by positivity
  have hi : A * 83 ^ k + v < 64 * 83 ^ k := ar_lt A v _ 64 (by omega) hv
  have hj : b * 83 ^ k + w < 64 * 83 ^ k := ar_lt b w _ 64 hb hw
  by_cases hvw : v = w
  · subst hvw
    rw [if_pos rfl]
    by_cases hAb : A = b
    · subst hAb
      unfold p0BQ
      rw [if_pos rfl, cast_qqBB k A v hA hv, YB, if_pos rfl]
    · have hij := decomp_ne_of_ne_quot (v := v) hq hAb
      have hmax : max (A * 83 ^ k + v) (b * 83 ^ k + v) < 83 * 83 ^ k :=
        max_lt (ar_lt83 _ _ 64 hi (by norm_num)) (ar_lt83 _ _ 64 hj (by norm_num))
      rw [qqB_off_decomp k _ _ _ hij,
        cast_mul' (Good83.sub_mem (mem_qT k A v (by omega) hv) (mem_qT k b v hb hv))
          (q_div_diff_good k _ _ hij hmax),
        cast_sub' (mem_qT k A v (by omega) hv) (mem_qT k b v hb hv),
        cast_qT k A v (by omega) hv, cast_qT k b v hb hv,
        qdiff_eq_unit k A b v hAb,
        cast_inv_int (by omega) (small_diff (by omega) hb), YB, if_neg hAb]
      ring
  · rw [if_neg hvw]
    have hij := decomp_ne_of_ne_rem (A := A) (b := b) hv hw hvw
    have hmax : max (A * 83 ^ k + v) (b * 83 ^ k + w) < 83 * 83 ^ k :=
      max_lt (ar_lt83 _ _ 64 hi (by norm_num)) (ar_lt83 _ _ 64 hj (by norm_num))
    rw [qqB_off_decomp k _ _ _ hij,
      cast_mul' (Good83.sub_mem (mem_qT k A v (by omega) hv) (mem_qT k b w hb hw))
        (q_div_diff_good k _ _ hij hmax),
      qdiff_cast_zero k _ _ hij (by rw [mod_of_decomp hv, mod_of_decomp hw]; exact hvw),
      mul_zero]

/-- The literal seed B entries are the `k = 0` case of `EB`. -/
theorem seedB (A b : ℕ) (hA : A < 40) (hb : b < 64) :
    ((p0BQ (2 : ℚ) 16 A b : ℚ) : F83) = YB A b := by
  have h := EB 0 A b 0 0 hA hb (by norm_num) (by norm_num)
  simpa only [qRat_zero, pow_zero, mul_one, add_zero, one_mul, one_pow,
    if_true] using h

end

end ScaledLucas
end Li2Lean.P0
