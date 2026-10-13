/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.FrequencyEllipse
import Li2Lean.P0.FrequencyLimit
import Li2Lean.P0.FrequencyLiteralRowENNReal

namespace Li2Lean.P0

open MeasureTheory Filter Topology
open scoped BigOperators ENNReal

noncomputable section

private theorem p0EllipsePoint32_re (u : ℝ) :
    (p0EllipsePoint 32 u).re =
      32 * ((11281 : ℝ) / 10000 + (12783 : ℝ) / 10000 * Real.cos u) := by
  simp only [p0EllipsePoint, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem p0EllipsePoint32_im (u : ℝ) :
    (p0EllipsePoint 32 u).im =
      32 * ((229 : ℝ) / 200 * Real.sin u) := by
  simp only [p0EllipsePoint, Complex.mul_re, Complex.mul_im, Complex.add_re,
    Complex.add_im, Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring

private theorem endpoint_right_gap (a : ℕ) :
    3 / 625 ≤ |(a : ℝ) - (48128 : ℝ) / 625| := by
  by_cases ha : a ≤ 77
  · have ha' : (a : ℝ) ≤ 77 := by exact_mod_cast ha
    have hsign : (a : ℝ) - (48128 : ℝ) / 625 ≤ 0 := by norm_num; linarith
    rw [abs_of_nonpos hsign]
    have hgap : (3 : ℝ) / 625 ≤ (48128 : ℝ) / 625 - 77 := by norm_num
    linarith
  · have haNat : 78 ≤ a := by omega
    have ha' : 78 ≤ (a : ℝ) := by exact_mod_cast haNat
    have hsign : 0 ≤ (a : ℝ) - (48128 : ℝ) / 625 := by norm_num; linarith
    rw [abs_of_nonneg hsign]
    have hgap : (3 : ℝ) / 625 ≤ 78 - (48128 : ℝ) / 625 := by norm_num
    linarith

private theorem endpoint_left_gap (a : ℕ) :
    3 / 625 ≤ |(a : ℝ) - (-(3004 : ℝ) / 625)| := by
  have hpos : 0 ≤ (a : ℝ) - (-(3004 : ℝ) / 625) := by
    have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
    norm_num at ha ⊢
    linarith
  rw [abs_of_nonneg hpos]
  have ha : 0 ≤ (a : ℝ) := Nat.cast_nonneg a
  norm_num at ha ⊢
  linarith

/-- The actual scaled ellipse stays at least `1/1000` from every natural pole.
The exact closest endpoint gap is `3/625`, attained at the integer 77. -/
theorem p0EllipsePoint32_distance_nat (u : ℝ) (a : ℕ) :
    (1 / 1000 : ℝ) ≤ ‖p0EllipsePoint 32 u - (a : ℂ)‖ := by
  by_contra h
  have hnear : ‖p0EllipsePoint 32 u - (a : ℂ)‖ < (1 / 1000 : ℝ) := by
    exact lt_of_not_ge h
  let z := p0EllipsePoint 32 u
  have hre : |z.re - (a : ℝ)| < (1 / 1000 : ℝ) := by
    have h' := lt_of_le_of_lt (Complex.abs_re_le_norm (z - (a : ℂ))) hnear
    simpa [z, Complex.sub_re, Complex.ofReal_re] using h'
  have him : |z.im| < (1 / 1000 : ℝ) := by
    have h' := lt_of_le_of_lt (Complex.abs_im_le_norm (z - (a : ℂ))) hnear
    simpa [z, Complex.sub_im, Complex.ofReal_im] using h'
  rw [p0EllipsePoint32_im] at him
  have hcoeff : 1 ≤ 32 * ((229 : ℝ) / 200) := by norm_num
  have hsin : |Real.sin u| < (1 / 1000 : ℝ) := by
    have hmul : (32 * ((229 : ℝ) / 200)) * |Real.sin u| < (1 / 1000 : ℝ) := by
      have h' := him
      norm_num [abs_mul] at h'
      convert h' using 1 <;> ring
    calc
      |Real.sin u| = 1 * |Real.sin u| := by ring
      _ ≤ (32 * ((229 : ℝ) / 200)) * |Real.sin u| :=
        mul_le_mul_of_nonneg_right hcoeff (abs_nonneg _)
      _ < (1 / 1000 : ℝ) := hmul
  have hsin2 : (Real.sin u) ^ 2 < (1 / 1000000 : ℝ) := by
    have hs := abs_lt.mp hsin
    nlinarith
  have htrig : (Real.sin u) ^ 2 =
      (1 - Real.cos u) * (1 + Real.cos u) := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  have hApos : 0 < 32 * ((12783 : ℝ) / 10000) := by norm_num
  have hAupper : 32 * ((12783 : ℝ) / 10000) < 41 := by norm_num
  have hleftEndpoint :
      32 * ((11281 : ℝ) / 10000 - (12783 : ℝ) / 10000) =
        -(3004 : ℝ) / 625 := by norm_num
  have hrightEndpoint :
      32 * ((11281 : ℝ) / 10000 + (12783 : ℝ) / 10000) =
        (48128 : ℝ) / 625 := by norm_num
  by_cases hc : 0 ≤ Real.cos u
  · have hcosle : Real.cos u ≤ 1 := Real.cos_le_one u
    have hfac : 0 ≤ 1 - Real.cos u := by linarith
    have hbound : 1 - Real.cos u ≤ (Real.sin u) ^ 2 := by
      have hmul := mul_nonneg hfac hc
      nlinarith
    have hgapEq : (48128 : ℝ) / 625 - z.re =
        (32 * ((12783 : ℝ) / 10000)) * (1 - Real.cos u) := by
      rw [p0EllipsePoint32_re, ← hrightEndpoint]
      ring
    have hgapSmall : (48128 : ℝ) / 625 - z.re < (1 / 1000 : ℝ) := by
      rw [hgapEq]
      have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt hApos)
      have hmul' := mul_lt_mul_of_pos_left hsin2 hApos
      nlinarith [hmul', hAupper]
    have hnearEndpoint :
        |z.re - (48128 : ℝ) / 625| < (1 / 1000 : ℝ) := by
      rw [abs_of_nonpos (by linarith)]
      linarith
    have htri : |(a : ℝ) - (48128 : ℝ) / 625| ≤
        |(a : ℝ) - z.re| + |z.re - (48128 : ℝ) / 625| := by
      calc
      |(a : ℝ) - (48128 : ℝ) / 625| =
            |((a : ℝ) - z.re) + (z.re - (48128 : ℝ) / 625)| := by congr 1 <;> ring
        _ ≤ |(a : ℝ) - z.re| + |z.re - (48128 : ℝ) / 625| := abs_add_le _ _
    have hnear' : |(a : ℝ) - z.re| < (1 / 1000 : ℝ) := by
      simpa [abs_sub_comm] using hre
    have hgap := endpoint_right_gap a
    linarith
  · have hcosge : -1 ≤ Real.cos u := Real.neg_one_le_cos u
    have hfac : 0 ≤ 1 + Real.cos u := by linarith
    have hbound : 1 + Real.cos u ≤ (Real.sin u) ^ 2 := by
      have hmul := mul_nonneg hfac (show 0 ≤ -Real.cos u by linarith)
      nlinarith [htrig]
    have hgapEq : z.re - (-(3004 : ℝ) / 625) =
        (32 * ((12783 : ℝ) / 10000)) * (1 + Real.cos u) := by
      rw [p0EllipsePoint32_re, ← hleftEndpoint]
      ring
    have hgapSmall : z.re - (-(3004 : ℝ) / 625) < (1 / 1000 : ℝ) := by
      rw [hgapEq]
      have hmul := mul_le_mul_of_nonneg_left hbound (le_of_lt hApos)
      have hmul' := mul_lt_mul_of_pos_left hsin2 hApos
      nlinarith [hmul', hAupper]
    have hnearEndpoint :
        |z.re - (-(3004 : ℝ) / 625)| < (1 / 1000 : ℝ) := by
      rw [abs_of_nonneg (by rw [hgapEq]; positivity)]
      linarith
    have htri : |(a : ℝ) - (-(3004 : ℝ) / 625)| ≤
        |(a : ℝ) - z.re| + |z.re - (-(3004 : ℝ) / 625)| := by
      calc
        |(a : ℝ) - (-(3004 : ℝ) / 625)| =
            |((a : ℝ) - z.re) + (z.re - (-(3004 : ℝ) / 625))| := by congr 1 <;> ring
        _ ≤ |(a : ℝ) - z.re| + |z.re - (-(3004 : ℝ) / 625)| := abs_add_le _ _
    have hnear' : |(a : ℝ) - z.re| < (1 / 1000 : ℝ) := by
      simpa [abs_sub_comm] using hre
    have hgap := endpoint_left_gap a
    linarith

private theorem norm_det_le_factorial_mul_pow {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℂ) (B : ℝ)
    (hentry : ∀ i j, ‖M i j‖ ≤ B) :
    ‖M.det‖ ≤ (Nat.factorial n : ℝ) * B ^ n := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm (Fin n),
        (↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, M (σ i) i‖ ≤
        ∑ σ : Equiv.Perm (Fin n),
          ‖(↑↑(Equiv.Perm.sign σ) : ℂ) * ∏ i, M (σ i) i‖ := by
            exact norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin n), B ^ n := by
      apply Finset.sum_le_sum
      intro σ hσ
      rw [norm_mul]
      have hsign : ‖(↑↑(Equiv.Perm.sign σ) : ℂ)‖ = 1 := by
        rw [Complex.norm_intCast]
        exact_mod_cast Equiv.Perm.sign_abs σ
      rw [hsign, norm_prod]
      simp only [one_mul]
      calc
        (∏ i : Fin n, ‖M (σ i) i‖) ≤ ∏ _i : Fin n, B := by
          apply Finset.prod_le_prod₀
          · intro i hi
            exact norm_nonneg _
          · intro i hi
            exact hentry (σ i) i
        _ = B ^ n := by simp
    _ = (Nat.factorial n : ℝ) * B ^ n := by simp [Fintype.card_perm]

private theorem inverse_norm_le_1000 {z : ℂ}
    (hz : (1 / 1000 : ℝ) ≤ ‖z‖) : ‖z⁻¹‖ ≤ 1000 := by
  have hzpos : 0 < ‖z‖ := lt_of_lt_of_le (by norm_num) hz
  rw [norm_inv, ← one_div]
  exact (div_le_iff₀ hzpos).2 (by nlinarith)

private theorem inverse_norm_le_1000_of_one_le {z : ℂ}
    (hz : 1 ≤ ‖z‖) : ‖z⁻¹‖ ≤ 1000 :=
  inverse_norm_le_1000 (by linarith)

private def determinantCap : ℝ :=
  (Nat.factorial 64 : ℝ) * (1000 : ℝ) ^ 64

private theorem norm_det_le_determinantCap {n : ℕ}
    (hn : n ≤ 64) (M : Matrix (Fin n) (Fin n) ℂ)
    (hentry : ∀ i j, ‖M i j‖ ≤ 1000) : ‖M.det‖ ≤ determinantCap := by
  have hsmall := norm_det_le_factorial_mul_pow M 1000 hentry
  have hfact : (Nat.factorial n : ℝ) ≤ (Nat.factorial 64 : ℝ) := by
    exact_mod_cast Nat.factorial_le hn
  have hpow : (1000 : ℝ) ^ n ≤ 1000 ^ 64 := by
    exact pow_le_pow_right₀ (by norm_num) hn
  unfold determinantCap
  exact hsmall.trans (mul_le_mul hfact hpow (by positivity) (by positivity))

private theorem ellipse_nat_inverse_norm_le_1000 (u : ℝ) (a : ℕ) :
    ‖((a : ℂ) - p0EllipsePoint 32 u)⁻¹‖ ≤ 1000 := by
  apply inverse_norm_le_1000
  simpa only [norm_sub_rev] using p0EllipsePoint32_distance_nat u a

private theorem cauchyDet_norm_le_determinantCap {n : ℕ} (hn : n ≤ 64)
    (x y : Fin n → ℂ)
    (hentry : ∀ i j, ‖(x i + y j)⁻¹‖ ≤ 1000) :
    ‖cauchyDet x y‖ ≤ determinantCap := by
  unfold cauchyDet
  apply norm_det_le_determinantCap hn
  intro i j
  exact hentry i j

private theorem contourQLeftMinor_m32_bound (S : Finset ℕ)
    (hSI : S ⊆ Iset 32) (u : Fin (32 - S.card) → ℝ) :
    ‖contourQLeftMinor S hSI (fun i => p0EllipsePoint 32 (u i))‖ ≤
      determinantCap := by
  classical
  let d := 32 - S.card
  let Ic := Iset 32 \ S
  have hcard : S.card ≤ 32 := by
    rw [← Iset_card 32]
    exact Finset.card_le_card hSI
  have hIc : Ic.card = d := by
    dsimp [Ic, d]
    rw [Finset.card_sdiff_of_subset hSI, Iset_card]
  change ‖cauchyDet
      (fun i : Fin d => ((orderedElem Ic (Fin.cast hIc.symm i) : ℕ) : ℂ))
      (fun i => -p0EllipsePoint 32 (u i))‖ ≤ determinantCap
  apply cauchyDet_norm_le_determinantCap (by omega)
  intro i j
  let a := orderedElem Ic (Fin.cast hIc.symm i)
  have ha : a ∈ Iset 32 := by
    have hm : orderedElem Ic (Fin.cast hIc.symm i) ∈ Ic :=
      (Finset.orderIsoOfFin Ic rfl _).property
    exact (Finset.mem_sdiff.mp hm).1
  have hinv := ellipse_nat_inverse_norm_le_1000 (u j) a
  simpa [a, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hinv

private theorem contourQMiddleMinor_m32_bound (R : Fin 32 → ℕ)
    (hR : StrictMono R) (hRg : ∀ i, 16 < R i) :
    ‖cauchyDet (fun i : Fin 32 => ((rowIndex 32 i : ℕ) : ℂ))
      (fun i => (R i : ℂ))‖ ≤ determinantCap := by
  classical
  apply cauchyDet_norm_le_determinantCap (by norm_num)
  intro i j
  apply inverse_norm_le_1000_of_one_le
  have hrow : 8 ≤ rowIndex 32 i := by
    dsimp [rowIndex]
    omega
  have hRj := hRg j
  have hfreq : 17 ≤ R j := by omega
  have hsum : 1 ≤ rowIndex 32 i + R j := by omega
  have hcast : ((rowIndex 32 i : ℕ) : ℂ) + (R j : ℂ) =
      ((rowIndex 32 i + R j : ℕ) : ℂ) := by simp
  rw [hcast, Complex.norm_natCast]
  exact_mod_cast hsum

private theorem contourQRightMinor_m32_bound (S : Finset ℕ)
    (hSI : S ⊆ Iset 32) (R : Fin 32 → ℕ)
    (hR : StrictMono R) (hRg : ∀ i, 16 < R i)
    (u : Fin (32 - S.card) → ℝ) :
    ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
        (fun i => p0EllipsePoint 32 (u i))).2.2‖ ≤ determinantCap := by
  classical
  let d := 32 - S.card
  let Jc := Jset 32 \ S
  have hScard : S.card ≤ 32 := by
    rw [← Iset_card 32]
    exact Finset.card_le_card hSI
  have hSJ : S ⊆ Jset 32 := hSI.trans (Iset_subset_Jset 32 (by norm_num))
  have hJc : Jc.card = d + 32 := by
    dsimp [Jc, d]
    rw [Finset.card_sdiff_of_subset hSJ]
    simp [Jset, Finset.card_range]
    omega
  change ‖Matrix.det (fun i : Fin (d + 32) => fun j : Fin (d + 32) =>
    ((if hi : i.val < d then -p0EllipsePoint 32 (u ⟨i.val, hi⟩) else
        (R ⟨i.val - d, by omega⟩ : ℂ)) +
      ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ))⁻¹)‖ ≤ determinantCap
  apply norm_det_le_determinantCap (by omega)
  intro i j
  let a := orderedElem Jc (Fin.cast hJc.symm j)
  have ha : a ∈ Jset 32 := by
    have hm : orderedElem Jc (Fin.cast hJc.symm j) ∈ Jc :=
      (Finset.orderIsoOfFin Jc rfl _).property
    exact (Finset.mem_sdiff.mp hm).1
  by_cases hi : i.val < d
  · have hinv := ellipse_nat_inverse_norm_le_1000 (u ⟨i.val, hi⟩) a
    simpa [a, hi, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using hinv
  · apply inverse_norm_le_1000_of_one_le
    have hfreq : 17 ≤ R ⟨i.val - d, by omega⟩ := by
      have := hRg ⟨i.val - d, by omega⟩
      omega
    have hsum : 1 ≤ R ⟨i.val - d, by omega⟩ + a := by omega
    have hcast : (R ⟨i.val - d, by omega⟩ : ℂ) + (a : ℂ) =
        ((R ⟨i.val - d, by omega⟩ + a : ℕ) : ℂ) := by simp
    simp only [dite_eq_right hi]
    rw [hcast, Complex.norm_natCast]
    exact_mod_cast hsum

private theorem p0EllipsePoint32_re_upper (u : ℝ) :
    (p0EllipsePoint 32 u).re ≤ 78 := by
  rw [p0EllipsePoint32_re]
  have hc := Real.cos_le_one u
  norm_num at hc ⊢
  nlinarith

private theorem p0EllipsePoint32_norm_upper (u : ℝ) :
    ‖p0EllipsePoint 32 u‖ < 80 := by
  have h := Li2Lean.P0.FrequencyLeaf.p0EllipsePoint_norm_upper
    (m := 32) (by norm_num) u
  norm_num at h ⊢
  exact h

private theorem p0Entire16_norm_bound (u : ℝ) :
    ‖p0Entire 16 (p0EllipsePoint 32 u)‖ ≤
      (2 : ℝ) ^ 78 * 140 ^ 16 := by
  let z := p0EllipsePoint 32 u
  have hzre : z.re ≤ 78 := p0EllipsePoint32_re_upper u
  have hzabs : ‖z‖ < 80 := p0EllipsePoint32_norm_upper u
  have hlog0 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlog1 : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hexp : Real.exp ((z * Complex.ofReal (Real.log 2)).re) ≤
      (2 : ℝ) ^ 78 := by
    have hre : (z * Complex.ofReal (Real.log 2)).re = z.re * Real.log 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    have harg : z.re * Real.log 2 ≤ 78 * Real.log 2 :=
      mul_le_mul_of_nonneg_right hzre hlog0
    calc
      Real.exp (z.re * Real.log 2) ≤ Real.exp (78 * Real.log 2) :=
        Real.exp_le_exp.mpr harg
      _ = (2 : ℝ) ^ 78 := by
        rw [show (78 : ℝ) = (78 : ℕ) by norm_num, Real.exp_nat_mul,
          Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  have hprod :
      ‖∏ r ∈ Finset.range 16, (z + (r + 1 : ℕ))‖ ≤ (140 : ℝ) ^ 16 := by
    rw [norm_prod]
    calc
      (∏ r ∈ Finset.range 16, ‖z + (r + 1 : ℕ)‖) ≤
          ∏ r ∈ Finset.range 16, (140 : ℝ) := by
        apply Finset.prod_le_prod₀
        · intro r hr
          exact norm_nonneg _
        · intro r hr
          have hrlt : r < 16 := Finset.mem_range.mp hr
          have hnat : r + 1 ≤ 16 := by omega
          have hcast : (r + 1 : ℕ) ≤ (16 : ℝ) := by exact_mod_cast hnat
          calc
            ‖z + (r + 1 : ℕ)‖ ≤ ‖z‖ + ‖((r + 1 : ℕ) : ℂ)‖ := norm_add_le _ _
            _ = ‖z‖ + ((r + 1 : ℕ) : ℝ) := by
              rw [Complex.norm_natCast]
            _ ≤ 80 + 16 := by linarith [hzabs, hcast]
            _ ≤ 140 := by norm_num
      _ = (140 : ℝ) ^ 16 := by simp
  have hfac : 1 ≤ (Nat.factorial 16 : ℝ) := by norm_num
  have hnorm : ‖p0Entire 16 z‖ =
      Real.exp ((z * Complex.ofReal (Real.log 2)).re) *
        ‖∏ r ∈ Finset.range 16, (z + (r + 1 : ℕ))‖ /
          (Nat.factorial 16 : ℝ) := by
    simp [p0Entire, Complex.norm_exp, norm_prod, div_eq_mul_inv,
      Complex.norm_natCast, Real.norm_eq_abs, abs_of_nonneg]
  rw [hnorm]
  have hfacinv : (Nat.factorial 16 : ℝ)⁻¹ ≤ 1 := by
    exact inv_le_one_of_one_le₀ hfac
  have hmul :
      Real.exp ((z * Complex.ofReal (Real.log 2)).re) *
          ‖∏ r ∈ Finset.range 16, (z + (r + 1 : ℕ))‖ ≤
        (2 : ℝ) ^ 78 * 140 ^ 16 := by
    exact mul_le_mul hexp hprod (norm_nonneg _) (by positivity)
  calc
    Real.exp ((z * Complex.ofReal (Real.log 2)).re) *
        ‖∏ r ∈ Finset.range 16, (z + (r + 1 : ℕ))‖ /
          (Nat.factorial 16 : ℝ) =
      (Real.exp ((z * Complex.ofReal (Real.log 2)).re) *
        ‖∏ r ∈ Finset.range 16, (z + (r + 1 : ℕ))‖) *
          (Nat.factorial 16 : ℝ)⁻¹ := by ring
    _ ≤ ((2 : ℝ) ^ 78 * 140 ^ 16) * 1 :=
      mul_le_mul hmul hfacinv (by positivity) (by positivity)
    _ = (2 : ℝ) ^ 78 * 140 ^ 16 := by ring

private theorem p0EllipseTangent32_norm_bound (u : ℝ) :
    ‖p0EllipseTangent 32 u‖ ≤ 41 := by
  let e : ℂ := Complex.ofReal (-((12783 : ℝ) / 10000) * Real.sin u) +
    Complex.I * Complex.ofReal (((229 : ℝ) / 200) * Real.cos u)
  have he_re : e.re = -((12783 : ℝ) / 10000) * Real.sin u := by
    simp only [e, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_re, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, sub_zero, add_zero]
  have he_im : e.im = ((229 : ℝ) / 200) * Real.cos u := by
    simp only [e, Complex.add_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.mul_im, Complex.sin_ofReal_re, Complex.cos_ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, one_mul, zero_add]
  have he_sq : ‖e‖ ^ 2 =
      (-((12783 : ℝ) / 10000) * Real.sin u) ^ 2 +
        (((229 : ℝ) / 200) * Real.cos u) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, he_re, he_im]
    ring
  have htrig := Real.sin_sq_add_cos_sq u
  have hbase : ‖e‖ ^ 2 ≤ ((12783 : ℝ) / 10000) ^ 2 := by
    rw [he_sq]
    have haxes : ((229 : ℝ) / 200) ^ 2 ≤ ((12783 : ℝ) / 10000) ^ 2 := by norm_num
    nlinarith [sq_nonneg (Real.sin u), sq_nonneg (Real.cos u), haxes]
  have hnorm : ‖e‖ ≤ (12783 : ℝ) / 10000 := by
    nlinarith [norm_nonneg e, sq_nonneg (‖e‖ - (12783 : ℝ) / 10000)]
  have houter : ‖p0EllipseTangent 32 u‖ = 32 * ‖e‖ := by
    simp [p0EllipseTangent, e, norm_mul, Complex.norm_real, abs_of_nonneg]
  rw [houter]
  calc
    32 * ‖e‖ ≤ 32 * ((12783 : ℝ) / 10000) := by nlinarith
    _ ≤ 41 := by norm_num

private theorem contourArcDensity32_le_41 (u : ℝ) :
    contourArcDensity 32 u ≤ 41 := by
  unfold contourArcDensity
  apply (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * Real.pi)).2
  have hden : 1 ≤ 2 * Real.pi := by nlinarith [Real.pi_gt_three]
  have htan := p0EllipseTangent32_norm_bound u
  nlinarith

private theorem frequencyWeightReal_le_one {r : ℕ} (hr : 16 < r) :
    0 ≤ frequencyWeightReal 16 r ∧ frequencyWeightReal 16 r ≤ 1 := by
  have hrpos : 0 < r := by omega
  have hchooseNat := Nat.choose_le_two_pow (r - 1) 16
  have hchoose : (Nat.choose (r - 1) 16 : ℝ) ≤ (2 : ℝ) ^ (r - 1) := by
    exact_mod_cast hchooseNat
  have hpow : (2 : ℝ) ^ (r - 1) ≤ (2 : ℝ) ^ r := by
    exact pow_le_pow_right₀ (by norm_num) (Nat.sub_le r 1)
  constructor
  · unfold frequencyWeightReal
    exact div_nonneg (by positivity) (by positivity)
  · unfold frequencyWeightReal
    apply (div_le_iff₀ (by positivity : (0 : ℝ) < (2 : ℝ) ^ r)).2
    simpa only [one_mul] using hchoose.trans hpow

private theorem pinnedFactor32_le (a : ℕ) (ha : a ∈ Iset 32) :
    0 ≤ ell * UReal 16 a ∧ ell * UReal 16 a ≤ (2 : ℝ) ^ 94 := by
  have ha' : a ∈ Finset.Ico 8 40 := by
    rw [Iset_eq_paper_interval 32 (by norm_num)] at ha
    simpa using ha
  have haLo : 8 ≤ a := (Finset.mem_Ico.mp ha').1
  have haHi : a < 40 := (Finset.mem_Ico.mp ha').2
  have hell0 : 0 ≤ ell := by
    unfold ell
    exact Real.log_nonneg (by norm_num)
  have hell1 : ell ≤ 1 := by
    unfold ell
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hchooseNat := Nat.choose_le_two_pow (a + 16) 16
  have hchoose : (Nat.choose (a + 16) 16 : ℝ) ≤ (2 : ℝ) ^ (a + 16) := by
    exact_mod_cast hchooseNat
  have hpow : (2 : ℝ) ^ a * (Nat.choose (a + 16) 16 : ℝ) ≤
      (2 : ℝ) ^ (2 * a + 16) := by
    calc
      (2 : ℝ) ^ a * (Nat.choose (a + 16) 16 : ℝ) ≤
          (2 : ℝ) ^ a * (2 : ℝ) ^ (a + 16) :=
        mul_le_mul_of_nonneg_left hchoose (by positivity)
      _ = (2 : ℝ) ^ (2 * a + 16) := by
        rw [← pow_add]
        congr 1
        omega
  have hexp : 2 * a + 16 ≤ 94 := by omega
  have hpow' : (2 : ℝ) ^ (2 * a + 16) ≤ (2 : ℝ) ^ 94 :=
    pow_le_pow_right₀ (by norm_num) hexp
  have hU : UReal 16 a ≤ (2 : ℝ) ^ 94 := by
    unfold UReal
    exact hpow.trans hpow'
  have hU0 : 0 ≤ UReal 16 a := by
    unfold UReal
    exact mul_nonneg (by positivity) (Nat.cast_nonneg _)
  constructor
  · exact mul_nonneg hell0 hU0
  · calc
      ell * UReal 16 a ≤ 1 * UReal 16 a :=
        mul_le_mul_of_nonneg_right hell1 hU0
      _ = UReal 16 a := one_mul _
      _ ≤ (2 : ℝ) ^ 94 := hU

private theorem prod_fin_le_pow {n : ℕ} (f : Fin n → ℝ) (B : ℝ)
    (hf0 : ∀ i, 0 ≤ f i) (hfb : ∀ i, f i ≤ B) :
    (∏ i : Fin n, f i) ≤ B ^ n := by
  calc
    (∏ i : Fin n, f i) ≤ ∏ _i : Fin n, B := by
      apply Finset.prod_le_prod₀
      · intro i hi
        exact hf0 i
      · intro i hi
        exact hfb i
    _ = B ^ n := by simp

private theorem prod_set_le_pow_card {s : Finset ℕ} (f : ℕ → ℝ) (B : ℝ)
    (hf0 : ∀ a ∈ s, 0 ≤ f a) (hfb : ∀ a ∈ s, f a ≤ B) :
    (∏ a ∈ s, f a) ≤ B ^ s.card := by
  calc
    (∏ a ∈ s, f a) ≤ ∏ a ∈ s, B := by
      apply Finset.prod_le_prod₀
      · intro a ha
        exact hf0 a ha
      · intro a ha
        exact hfb a ha
    _ = B ^ s.card := by simp

private def entireCap : ℝ := (2 : ℝ) ^ 2496 * 140 ^ 512

private def qCap : ℝ :=
  (2 : ℝ) ^ 5504 * 140 ^ 512 * determinantCap ^ 3

private theorem contourQValue_m32_bound (S : Finset ℕ)
    (hSI : S ⊆ Iset 32) (R : Fin 32 → ℕ)
    (hR : StrictMono R) (hRg : ∀ i, 16 < R i)
    (u : Fin (32 - S.card) → ℝ) :
    contourQValue S (by norm_num : 4 ∣ 32) hSI R hR
      (fun i => p0EllipsePoint 32 (u i)) ≤ qCap := by
  classical
  let d := 32 - S.card
  let Z : Fin d → ℂ := fun i => p0EllipsePoint 32 (u i)
  let minors := contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR Z
  have hScard : S.card ≤ 32 := by
    rw [← Iset_card 32]
    exact Finset.card_le_card hSI
  have hd : d ≤ 32 := by dsimp [d]; omega
  have hpinned : (∏ a ∈ S, ell * UReal 16 a) ≤ (2 : ℝ) ^ 3008 := by
    calc
      (∏ a ∈ S, ell * UReal 16 a) ≤ ((2 : ℝ) ^ 94) ^ S.card := by
        apply prod_set_le_pow_card
        · intro a ha
          exact (pinnedFactor32_le a (hSI ha)).1
        · intro a ha
          exact (pinnedFactor32_le a (hSI ha)).2
      _ ≤ ((2 : ℝ) ^ 94) ^ 32 := by
        exact pow_le_pow_right₀ (by norm_num) hScard
      _ = (2 : ℝ) ^ 3008 := by
        rw [← pow_mul]
  have hpinned0 : 0 ≤ ∏ a ∈ S, ell * UReal 16 a := by
    apply Finset.prod_nonneg
    intro a ha
    exact (pinnedFactor32_le a (hSI ha)).1
  have hweights : (∏ i : Fin 32, frequencyWeightReal 16 (R i)) ≤ 1 := by
    calc
      (∏ i : Fin 32, frequencyWeightReal 16 (R i)) ≤ (1 : ℝ) ^ 32 := by
        apply prod_fin_le_pow
        · intro i
          exact (frequencyWeightReal_le_one (hRg i)).1
        · intro i
          exact (frequencyWeightReal_le_one (hRg i)).2
      _ = 1 := by norm_num
  have hweights0 : 0 ≤ ∏ i : Fin 32, frequencyWeightReal 16 (R i) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (frequencyWeightReal_le_one (hRg i)).1
  have hentire : (∏ i : Fin d, ‖p0Entire 16 (Z i)‖) ≤ entireCap := by
    calc
      (∏ i : Fin d, ‖p0Entire 16 (Z i)‖) ≤
          ((2 : ℝ) ^ 78 * 140 ^ 16) ^ d := by
        apply prod_fin_le_pow
        · intro i
          exact norm_nonneg _
        · intro i
          exact p0Entire16_norm_bound (u i)
      _ ≤ ((2 : ℝ) ^ 78 * 140 ^ 16) ^ 32 := by
        apply pow_le_pow_right₀
        · norm_num
        · exact hd
      _ = entireCap := by
        unfold entireCap
        rw [mul_pow, ← pow_mul, ← pow_mul]
  have hentire0 : 0 ≤ ∏ i : Fin d, ‖p0Entire 16 (Z i)‖ := by
    apply Finset.prod_nonneg
    intro i hi
    exact norm_nonneg _
  have hleft : ‖minors.1‖ ≤ determinantCap := by
    dsimp [minors, contourQMinors]
    change ‖contourQLeftMinor S hSI Z‖ ≤ determinantCap
    exact contourQLeftMinor_m32_bound S hSI u
  have hmiddle : ‖minors.2.1‖ ≤ determinantCap := by
    dsimp [minors]
    change ‖cauchyDet (fun i : Fin 32 => ((rowIndex 32 i : ℕ) : ℂ))
      (fun i => (R i : ℂ))‖ ≤ determinantCap
    exact contourQMiddleMinor_m32_bound R hR hRg
  have hright : ‖minors.2.2‖ ≤ determinantCap := by
    dsimp [minors, Z, d]
    exact contourQRightMinor_m32_bound S hSI R hR hRg u
  have hdet : ‖minors.1 * minors.2.1 * minors.2.2‖ ≤ determinantCap ^ 3 := by
    rw [norm_mul, norm_mul]
    have hfirst : ‖minors.1‖ * ‖minors.2.1‖ ≤ determinantCap ^ 2 := by
      calc
        ‖minors.1‖ * ‖minors.2.1‖ ≤ determinantCap * determinantCap :=
          calc
            ‖minors.1‖ * ‖minors.2.1‖ ≤ determinantCap * ‖minors.2.1‖ :=
              mul_le_mul_of_nonneg_right hleft (norm_nonneg _)
            _ ≤ determinantCap * determinantCap :=
              mul_le_mul_of_nonneg_left hmiddle (by unfold determinantCap; positivity)
        _ = determinantCap ^ 2 := by ring
    calc
      ‖minors.1‖ * ‖minors.2.1‖ * ‖minors.2.2‖ ≤
          determinantCap ^ 2 * determinantCap :=
        calc
          ‖minors.1‖ * ‖minors.2.1‖ * ‖minors.2.2‖ ≤
              determinantCap ^ 2 * ‖minors.2.2‖ :=
            mul_le_mul_of_nonneg_right hfirst (norm_nonneg _)
          _ ≤ determinantCap ^ 2 * determinantCap :=
            mul_le_mul_of_nonneg_left hright (by unfold determinantCap; positivity)
      _ = determinantCap ^ 3 := by ring
  have hdet0 : 0 ≤ ‖minors.1 * minors.2.1 * minors.2.2‖ := norm_nonneg _
  change
    (∏ a ∈ S, ell * UReal 16 a) *
        (∏ i : Fin 32, frequencyWeightReal 16 (R i)) *
        (∏ i : Fin (32 - S.card), ‖p0Entire 16 (p0EllipsePoint 32 (u i))‖) *
        ‖minors.1 * minors.2.1 * minors.2.2‖ ≤ qCap
  calc
    (∏ a ∈ S, ell * UReal 16 a) *
        (∏ i : Fin 32, frequencyWeightReal 16 (R i)) *
        (∏ i : Fin (32 - S.card), ‖p0Entire 16 (p0EllipsePoint 32 (u i))‖) *
        ‖minors.1 * minors.2.1 * minors.2.2‖ ≤
        (2 : ℝ) ^ 3008 * 1 * entireCap * determinantCap ^ 3 := by
      apply mul_le_mul
      · apply mul_le_mul
        · exact mul_le_mul hpinned hweights hweights0 (by norm_num)
        · exact hentire
        · exact hentire0
        · positivity
      · exact hdet
      · exact hdet0
      · norm_num [entireCap]
    _ = qCap := by
      unfold qCap entireCap
      simp only [mul_one]
      have hpow : (2 : ℝ) ^ 3008 * (2 : ℝ) ^ 2496 =
          (2 : ℝ) ^ 5504 := by
        convert (pow_add (2 : ℝ) 3008 2496).symm using 1 <;> norm_num
      calc
        (2 : ℝ) ^ 3008 * ((2 : ℝ) ^ 2496 * 140 ^ 512) * determinantCap ^ 3 =
            ((2 : ℝ) ^ 3008 * (2 : ℝ) ^ 2496) * 140 ^ 512 * determinantCap ^ 3 := by ring
        _ = (2 : ℝ) ^ 5504 * 140 ^ 512 * determinantCap ^ 3 := by rw [hpow]

theorem contourQMinorFrequencyProduct_m32_bound (S : Finset ℕ)
    (hSI : S ⊆ Iset 32) (R : Fin 32 → ℕ)
    (hR : StrictMono R) (hRg : ∀ i, 16 < R i)
    (u : Fin (32 - S.card) → ℝ) :
    contourQMinorFrequencyProduct S (by norm_num) hSI R hR
        (fun i => p0EllipsePoint 32 (u i)) ≤ determinantCap ^ 2 := by
  have hweights0 : 0 ≤ ∏ i : Fin 32, frequencyWeightReal 16 (R i) := by
    apply Finset.prod_nonneg
    intro i hi
    exact (frequencyWeightReal_le_one (hRg i)).1
  have hweights1 : ∏ i : Fin 32, frequencyWeightReal 16 (R i) ≤ 1 := by
    calc
      (∏ i : Fin 32, frequencyWeightReal 16 (R i)) ≤ (1 : ℝ) ^ 32 := by
        apply prod_fin_le_pow
        · intro i
          exact (frequencyWeightReal_le_one (hRg i)).1
        · intro i
          exact (frequencyWeightReal_le_one (hRg i)).2
      _ = 1 := by norm_num
  have hmiddle := contourQMiddleMinor_m32_bound R hR hRg
  have hright := contourQRightMinor_m32_bound S hSI R hR hRg u
  have hright0 : 0 ≤ ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
      (fun i => p0EllipsePoint 32 (u i))).2.2‖ := norm_nonneg _
  have hmiddle0 : 0 ≤ ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
      (fun i => p0EllipsePoint 32 (u i))).2.1‖ := norm_nonneg _
  change
    (∏ i : Fin 32, frequencyWeightReal 16 (R i)) *
        ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
            (fun i => p0EllipsePoint 32 (u i))).2.1‖ *
        ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
            (fun i => p0EllipsePoint 32 (u i))).2.2‖ ≤ determinantCap ^ 2
  calc
    (∏ i : Fin 32, frequencyWeightReal 16 (R i)) *
        ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
            (fun i => p0EllipsePoint 32 (u i))).2.1‖ *
        ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
            (fun i => p0EllipsePoint 32 (u i))).2.2‖ ≤
        1 * determinantCap * determinantCap := by
      calc
        _ ≤ (1 * ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
              (fun i => p0EllipsePoint 32 (u i))).2.1‖) *
              ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
                (fun i => p0EllipsePoint 32 (u i))).2.2‖ := by
          apply mul_le_mul_of_nonneg_right
          exact mul_le_mul_of_nonneg_right hweights1 hmiddle0
          exact hright0
        _ ≤ (1 * determinantCap) *
              ‖(contourQMinors S (by norm_num : 4 ∣ 32) hSI R hR
                (fun i => p0EllipsePoint 32 (u i))).2.2‖ := by
          apply mul_le_mul_of_nonneg_right
          exact mul_le_mul_of_nonneg_left hmiddle (by norm_num)
          exact hright0
        _ ≤ (1 * determinantCap) * determinantCap :=
          mul_le_mul_of_nonneg_left hright (by unfold determinantCap; positivity)
    _ = determinantCap ^ 2 := by ring

private theorem contourProductMeasure_real_univ_le (d : ℕ) :
    ((ContourKit.productMeasure (d := d) contourParameterMeasure).real Set.univ) ≤
      (8 : ℝ) ^ d := by
  letI : SigmaFinite contourParameterMeasure := by
    unfold contourParameterMeasure
    infer_instance
  rw [Measure.real_def]
  rw [ContourKit.productMeasure, Measure.pi_univ]
  rw [ENNReal.toReal_prod]
  calc
    (∏ i : Fin d, (contourParameterMeasure Set.univ).toReal) =
        (∏ i ∈ (Finset.univ : Finset (Fin d)),
          (contourParameterMeasure Set.univ).toReal) := by simp
    _ ≤ (∏ i ∈ (Finset.univ : Finset (Fin d)), (8 : ℝ)) := by
      apply Finset.prod_le_prod₀
      · intro i hi
        positivity
      · intro i hi
        rw [contourParameterMeasure, Measure.restrict_apply_univ, Real.volume_Icc]
        have hpi : 2 * Real.pi ≤ 8 := by nlinarith [Real.pi_lt_four]
        have hmass : ENNReal.ofReal (2 * Real.pi) ≤ ENNReal.ofReal (8 : ℝ) := by
          exact ENNReal.ofReal_le_ofReal hpi
        simpa using ENNReal.toReal_mono (by simp) hmass
    _ = (8 : ℝ) ^ d := by simp

private theorem contourArcDensity32_prod_bound (d : ℕ) (u : Fin d → ℝ) :
    0 ≤ (∏ i : Fin d, contourArcDensity 32 (u i)) ∧
      (∏ i : Fin d, contourArcDensity 32 (u i)) ≤ (41 : ℝ) ^ d := by
  have h0 : ∀ i : Fin d, 0 ≤ contourArcDensity 32 (u i) := by
    intro i
    unfold contourArcDensity
    positivity
  have h1 : ∀ i : Fin d, contourArcDensity 32 (u i) ≤ 41 := by
    intro i
    exact contourArcDensity32_le_41 (u i)
  constructor
  · exact Finset.prod_nonneg (fun i hi => h0 i)
  · exact prod_fin_le_pow _ 41 h0 h1

private theorem cutoffTuples32_card_le :
    (FrequencyCutoff.cutoffTuples 16 32 640).card ≤ 641 ^ 32 := by
  classical
  unfold FrequencyCutoff.cutoffTuples
  calc
    (Finset.univ.image (@FrequencyCutoff.forgetCutoff 16 32 640)).card ≤
        Finset.univ.card := Finset.card_image_le
    _ = Fintype.card (FrequencyCutoff.TruncatedTuple 16 32 640) := by simp
    _ ≤ Fintype.card (Fin 32 → Fin 641) := by
      exact Fintype.card_le_of_injective Subtype.val Subtype.val_injective
    _ = 641 ^ 32 := by simp [Fintype.card_fun]

private theorem envelopeTerm32_bound (S : Finset ℕ) (hSI : S ⊆ Iset 32)
    (r : FrequencyCutoff.IncreasingTuple 16 32)
    (u : Fin (32 - S.card) → ℝ) :
    FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u ≤
      qCap * (41 : ℝ) ^ 32 := by
  have hR : StrictMono r.val := r.property.1
  have hRg : ∀ i, 16 < r.val i := r.property.2
  have hq := contourQValue_m32_bound S hSI r.val hR hRg u
  have hd : 32 - S.card ≤ 32 := by
    have hScard : S.card ≤ 32 := by
      rw [← Iset_card 32]
      exact Finset.card_le_card hSI
    omega
  have hp := contourArcDensity32_prod_bound (32 - S.card) u
  have hp32 : (∏ i : Fin (32 - S.card), contourArcDensity 32 (u i)) ≤
      (41 : ℝ) ^ 32 := by
    exact hp.2.trans (pow_le_pow_right₀ (by norm_num) hd)
  have hq0 : 0 ≤ qCap := by
    unfold qCap determinantCap
    positivity
  change contourQValue S (by norm_num) hSI r.val hR
      (fun i => p0EllipsePoint 32 (u i)) *
      (∏ i : Fin (32 - S.card), contourArcDensity 32 (u i)) ≤ _
  calc
    contourQValue S (by norm_num) hSI r.val hR
          (fun i => p0EllipsePoint 32 (u i)) *
        (∏ i : Fin (32 - S.card), contourArcDensity 32 (u i)) ≤
      qCap * (∏ i : Fin (32 - S.card), contourArcDensity 32 (u i)) :=
        mul_le_mul_of_nonneg_right hq hp.1
    _ ≤ qCap * (41 : ℝ) ^ 32 :=
      mul_le_mul_of_nonneg_left hp32 hq0

private theorem contourEContribution32_640_bound (S : Finset ℕ)
    (hSI : S ⊆ Iset 32) :
    contourEContribution 32 640 (by norm_num) S hSI ≤
      (641 : ℝ) ^ 32 * qCap * (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
  letI : SigmaFinite contourParameterMeasure := by
    unfold contourParameterMeasure
    infer_instance
  letI : IsFiniteMeasure contourParameterMeasure := by
    unfold contourParameterMeasure
    infer_instance
  letI : IsFiniteMeasure
      (ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure) := by
    unfold ContourKit.productMeasure
    infer_instance
  rw [FrequencyLimit.contourEContribution_eq_cutoff 32 640 (by norm_num) S hSI]
  let B : ℝ := qCap * (41 : ℝ) ^ 32
  let C : ℝ := (641 : ℝ) ^ 32 * B
  have hB0 : 0 ≤ B := by
    dsimp [B]
    unfold qCap determinantCap
    positivity
  have hC0 : 0 ≤ C := by
    dsimp [C]
    exact mul_nonneg (by positivity) hB0
  have hI : Integrable
      (fun u : Fin (32 - S.card) → ℝ =>
        ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
          FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u)
      (ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure) := by
    exact FrequencyLimit.integrable_finite_envelope 32 640 (by norm_num) (by norm_num)
      S hSI
  have hCint : Integrable
      (fun _ : Fin (32 - S.card) → ℝ => C)
      (ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure) := by
    exact integrable_const _
  have hcardR : ((FrequencyCutoff.cutoffTuples 16 32 640).card : ℝ) ≤
      (641 : ℝ) ^ 32 := by
    exact_mod_cast cutoffTuples32_card_le
  have hpoint : ∀ u : Fin (32 - S.card) → ℝ,
      (∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
        FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u) ≤ C := by
    intro u
    calc
      (∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
          FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u) ≤
          ∑ _r ∈ FrequencyCutoff.cutoffTuples 16 32 640, B := by
        apply Finset.sum_le_sum
        intro r hr
        exact envelopeTerm32_bound S hSI r u
      _ = ((FrequencyCutoff.cutoffTuples 16 32 640).card : ℝ) * B := by
        simp [nsmul_eq_mul]
      _ ≤ C := by
        dsimp [C]
        exact mul_le_mul_of_nonneg_right hcardR hB0
  have hint :
      (∫ u : Fin (32 - S.card) → ℝ,
        ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
          FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u
        ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) ≤
      ∫ _u : Fin (32 - S.card) → ℝ, C
        ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure) :=
    integral_mono_ae hI hCint (Filter.Eventually.of_forall hpoint)
  have hmass :
      ((ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure).real
        Set.univ) ≤ (8 : ℝ) ^ 32 := by
    exact (contourProductMeasure_real_univ_le (32 - S.card)).trans
      (pow_le_pow_right₀ (by norm_num) (by omega))
  have hconst :
      (∫ _u : Fin (32 - S.card) → ℝ, C
        ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) ≤
      (8 : ℝ) ^ 32 * C := by
    rw [integral_const]
    change
      (ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure).real
          Set.univ * C ≤ (8 : ℝ) ^ 32 * C
    exact mul_le_mul_of_nonneg_right hmass hC0
  have htotal :
      (∫ u : Fin (32 - S.card) → ℝ,
        ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
          FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u
        ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) ≤
      (8 : ℝ) ^ 32 * C := hint.trans hconst
  have hInt0 : 0 ≤
      (∫ u : Fin (32 - S.card) → ℝ,
        ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
          FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u
        ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) := by
    apply integral_nonneg
    intro u
    apply Finset.sum_nonneg
    intro r hr
    exact FrequencyLimit.envelopeTerm_nonneg 32 (by norm_num) S hSI r u
  have hfac1 : (Nat.factorial (32 - S.card) : ℝ)⁻¹ ≤ 1 := by
    apply inv_le_one_of_one_le₀
    have hfacNat : 1 ≤ (32 - S.card).factorial := by
      have hpos := Nat.factorial_pos (32 - S.card)
      omega
    exact_mod_cast hfacNat
  calc
    (Nat.factorial (32 - S.card) : ℝ)⁻¹ *
        (∫ u : Fin (32 - S.card) → ℝ,
          ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
            FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u
          ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) ≤
      1 * (∫ u : Fin (32 - S.card) → ℝ,
          ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
            FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u
          ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) :=
      mul_le_mul_of_nonneg_right hfac1 hInt0
    _ = (∫ u : Fin (32 - S.card) → ℝ,
          ∑ r ∈ FrequencyCutoff.cutoffTuples 16 32 640,
            FrequencyLimit.envelopeTerm 32 (by norm_num) S hSI r u
          ∂(ContourKit.productMeasure (d := 32 - S.card) contourParameterMeasure)) := by ring
    _ ≤ (8 : ℝ) ^ 32 * C := htotal
    _ = (641 : ℝ) ^ 32 * qCap * (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
      dsimp [C, B]
      ring

theorem E32_640_rational_bound :
    E 32 640 (by norm_num) ≤
      (2 : ℝ) ^ 32 * (641 : ℝ) ^ 32 * (2 : ℝ) ^ 5504 *
        (140 : ℝ) ^ 512 *
        ((Nat.factorial 64 : ℝ) * (1000 : ℝ) ^ 64) ^ 3 *
        (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
  have hE : E 32 640 (by norm_num) ≤
      (2 : ℝ) ^ 32 * (641 : ℝ) ^ 32 * qCap *
        (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
    classical
    unfold E
    calc
      (∑ S ∈ (Iset 32).powerset,
          if hSI : S ⊆ Iset 32 then contourEContribution 32 640 (by norm_num) S hSI
          else 0) ≤
          ∑ _S ∈ (Iset 32).powerset,
            (641 : ℝ) ^ 32 * qCap * (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
        apply Finset.sum_le_sum
        intro S hS
        have hSI : S ⊆ Iset 32 := Finset.mem_powerset.mp hS
        simp only [dif_pos hSI]
        exact contourEContribution32_640_bound S hSI
      _ = ((Iset 32).powerset.card : ℝ) *
            ((641 : ℝ) ^ 32 * qCap * (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32) := by
        simp [nsmul_eq_mul]
      _ = (2 : ℝ) ^ 32 * (641 : ℝ) ^ 32 * qCap *
            (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
        rw [Finset.card_powerset, Iset_card]
        ring
  calc
    E 32 640 (by norm_num) ≤
        (2 : ℝ) ^ 32 * (641 : ℝ) ^ 32 * qCap *
          (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := hE
    _ = (2 : ℝ) ^ 32 * (641 : ℝ) ^ 32 * (2 : ℝ) ^ 5504 *
          (140 : ℝ) ^ 512 *
          ((Nat.factorial 64 : ℝ) * (1000 : ℝ) ^ 64) ^ 3 *
          (41 : ℝ) ^ 32 * (8 : ℝ) ^ 32 := by
      unfold qCap determinantCap
      ring

end

end Li2Lean.P0

#print axioms Li2Lean.P0.p0EllipsePoint32_distance_nat
#print axioms Li2Lean.P0.FrequencyLimit.contourQMinorFrequencyProduct_m32_ellipse
#print axioms Li2Lean.P0.contourQValue_eq_frequencyFactor_ellipse
#print axioms Li2Lean.P0.contourQMinorFrequencyProduct_m32_bound
#print axioms Li2Lean.P0.E32_640_rational_bound
