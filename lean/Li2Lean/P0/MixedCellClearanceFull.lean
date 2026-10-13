/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Config

namespace Li2Lean.P0.Config

open Li2Lean

private lemma clearance_core {C y : ℝ}
    (hClo : -(1 : ℝ) ≤ C) (hChi : C ≤ 1)
    (hy0 : 0 ≤ y) (hyc : y ≤ (11281 / 10000 : ℝ)) :
    (751 / 5000 : ℝ) ^ 2 ≤
      ((12783 / 10000 : ℝ) * C + y) ^ 2 +
        (229 / 200 : ℝ) ^ 2 * (1 - C ^ 2) := by
  have haa : 0 < (12783 / 10000 : ℝ) := by norm_num
  have hdelta : 0 < (12783 / 10000 : ℝ) ^ 2 -
      (229 / 200 : ℝ) ^ 2 := by norm_num
  by_cases hleft : C < -(11281 / 10000 : ℝ) / (12783 / 10000 : ℝ)
  · have hsum : (12783 / 10000 : ℝ) * C +
        (11281 / 10000 : ℝ) < 0 := by
      have hmul := (lt_div_iff₀ haa).mp hleft
      nlinarith
    have hdiff : 0 ≤
        (((12783 / 10000 : ℝ) * C + y) ^ 2 +
          (229 / 200 : ℝ) ^ 2 * (1 - C ^ 2)) -
          ((12783 / 10000 : ℝ) * C +
            (11281 / 10000 : ℝ)) ^ 2 -
          (229 / 200 : ℝ) ^ 2 * (1 - C ^ 2) := by
      have hfirst : 0 ≤ (11281 / 10000 : ℝ) - y := by linarith
      have hsecond : 0 ≤ -(2 * (12783 / 10000 : ℝ) * C +
          (11281 / 10000 : ℝ) + y) := by
        nlinarith [hsum, hyc]
      have hfac := mul_nonneg hfirst hsecond
      nlinarith
    have hendpoint : (751 / 5000 : ℝ) ^ 2 ≤
        ((12783 / 10000 : ℝ) * C +
          (11281 / 10000 : ℝ)) ^ 2 +
          (229 / 200 : ℝ) ^ 2 * (1 - C ^ 2) := by
      have hplus : 0 ≤ C + 1 := by linarith
      have hbr : 0 ≤
          ((12783 / 10000 : ℝ) ^ 2 - (229 / 200 : ℝ) ^ 2) * (C - 1) +
            2 * (12783 / 10000 : ℝ) * (11281 / 10000 : ℝ) := by
        have hp : 0 ≤
            ((12783 / 10000 : ℝ) ^ 2 - (229 / 200 : ℝ) ^ 2) * (C + 1) :=
          mul_nonneg (le_of_lt hdelta) hplus
        nlinarith
      have hfac := mul_nonneg hplus hbr
      nlinarith
    nlinarith
  · by_cases hcentral : -(11281 / 10000 : ℝ) /
      (12783 / 10000 : ℝ) ≤ C
    · by_cases hnonneg : 0 ≤ C
      · have hquad : 0 ≤
            ((12783 / 10000 : ℝ) * C + y) ^ 2 -
              ((12783 / 10000 : ℝ) * C) ^ 2 := by
          have hinner : 0 ≤ 2 * (12783 / 10000 : ℝ) * C + y := by
            nlinarith
          have hp := mul_nonneg hy0 hinner
          nlinarith
        have hbbd : (751 / 5000 : ℝ) ^ 2 < (229 / 200 : ℝ) ^ 2 := by
          norm_num
        nlinarith [sq_nonneg C]
      · have hCnonpos : C ≤ 0 := le_of_not_ge hnonneg
        have hlow : -(11281 / 10000 : ℝ) ≤
            (12783 / 10000 : ℝ) * C := by
          have hapos : 0 < (12783 / 10000 : ℝ) := haa
          have hcentral' := (div_le_iff₀ hapos).mp hcentral
          nlinarith
        have hupper : (12783 / 10000 : ℝ) * C ≤ 0 :=
          mul_nonpos_of_nonneg_of_nonpos (le_of_lt haa) hCnonpos
        have hprod : 0 ≤
            ((12783 / 10000 : ℝ) * C + (11281 / 10000 : ℝ)) *
              ((11281 / 10000 : ℝ) - (12783 / 10000 : ℝ) * C) := by
          exact mul_nonneg (by linarith) (by linarith)
        have hsq : ((12783 / 10000 : ℝ) * C) ^ 2 ≤
            (11281 / 10000 : ℝ) ^ 2 := by
          nlinarith
        have hC2 : C ^ 2 ≤
            ((11281 / 10000 : ℝ) / (12783 / 10000 : ℝ)) ^ 2 := by
          have hC2' : C ^ 2 ≤
              (11281 / 10000 : ℝ) ^ 2 /
                (12783 / 10000 : ℝ) ^ 2 := by
            apply (le_div_iff₀ (sq_pos_of_pos haa)).2
            nlinarith [hsq]
          convert hC2' using 1 <;> field_simp <;> ring
        have hbase : (751 / 5000 : ℝ) ^ 2 <
            (229 / 200 : ℝ) ^ 2 *
              (1 - ((11281 / 10000 : ℝ) /
                (12783 / 10000 : ℝ)) ^ 2) := by
          norm_num
        nlinarith [sq_nonneg ((12783 / 10000 : ℝ) * C + y)]
    · exact False.elim (hleft (lt_of_not_ge hcentral))

private theorem ellipse_re (u : ℝ) :
    (p0EllipsePoint 1 u).re = (11281 / 10000 : ℝ) +
      (12783 / 10000 : ℝ) * Real.cos u := by
  simp only [p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
    Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]

private theorem ellipse_im (u : ℝ) :
    (p0EllipsePoint 1 u).im = (229 / 200 : ℝ) * Real.sin u := by
  simp only [p0EllipsePoint, Nat.cast_one, Complex.ofReal_one, one_mul,
    Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.I_re,
    Complex.I_im, Complex.ofReal_im, zero_mul, mul_zero, sub_zero, add_zero]
  ring

theorem s2_mixed_left_candidate :
    ∀ z ∈ baseEllipseSet, ∀ x ∈ Set.Icc (0 : ℝ) 2,
      dPlus ≤ ‖z - Complex.ofReal x‖ := by
  intro z hz x hx
  rcases hz with ⟨u, rfl⟩
  let w : ℂ := p0EllipsePoint 1 u - Complex.ofReal x
  change dPlus ≤ ‖w‖
  set C : ℝ := Real.cos u with hC
  set S : ℝ := Real.sin u with hS
  have hClo : -(1 : ℝ) ≤ C := by
    simpa [hC] using Real.neg_one_le_cos u
  have hChi : C ≤ 1 := by
    simpa [hC] using Real.cos_le_one u
  have htrig : S ^ 2 + C ^ 2 = 1 := by
    simpa [hS, hC] using Real.sin_sq_add_cos_sq u
  have hcomp_re : w.re =
      (11281 / 10000 : ℝ) + (12783 / 10000 : ℝ) * C - x := by
    simp [w, ellipse_re, hC]
  have hcomp_im : w.im = (229 / 200 : ℝ) * S := by
    simp [w, ellipse_im, hS]
  have hx0 : 0 ≤ x := hx.1
  have hx2 : x ≤ 2 := hx.2
  have hq : (dPlus : ℝ) ^ 2 ≤ w.re ^ 2 + w.im ^ 2 := by
    by_cases hxc : x ≤ (11281 / 10000 : ℝ)
    · have hy0 : 0 ≤ (11281 / 10000 : ℝ) - x := by linarith
      have hyc : (11281 / 10000 : ℝ) - x ≤
          (11281 / 10000 : ℝ) := by linarith
      have hcore := clearance_core hClo hChi hy0 hyc
      rw [hcomp_re, hcomp_im]
      norm_num [dPlus] at hcore ⊢
      nlinarith [hcore, htrig]
    · have hy0 : 0 ≤ x - (11281 / 10000 : ℝ) := by linarith
      have hyc : x - (11281 / 10000 : ℝ) ≤
          (11281 / 10000 : ℝ) := by linarith
      have hClo' : -(1 : ℝ) ≤ -C := by linarith [hChi]
      have hChi' : -C ≤ 1 := by linarith [hClo]
      have hcore := clearance_core (C := -C) hClo' hChi' hy0 hyc
      rw [hcomp_re, hcomp_im]
      norm_num [dPlus] at hcore ⊢
      nlinarith [hcore, htrig]
  have hnormsq : ‖w‖ ^ 2 = w.re ^ 2 + w.im ^ 2 := by
    rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, pow_two]
  have hdp : 0 ≤ dPlus := by norm_num [dPlus]
  nlinarith [norm_nonneg w]

#print axioms s2_mixed_left_candidate

theorem s2_mixed_right_candidate2 :
    ∀ z ∈ baseEllipseSet, ∀ t : ℝ, (1 / 2 : ℝ) ≤ t →
      dMinus ≤ ‖z + Complex.ofReal t‖ := by
  intro z hz t ht
  rcases hz with ⟨u, rfl⟩
  let w : ℂ := p0EllipsePoint 1 u + Complex.ofReal t
  change dMinus ≤ ‖w‖
  have hcos : -(1 : ℝ) ≤ Real.cos u := Real.neg_one_le_cos u
  have hre : dMinus ≤ w.re := by
    rw [show w.re = (p0EllipsePoint 1 u).re + t by simp [w]]
    rw [ellipse_re]
    dsimp [dMinus]
    nlinarith
  have hreal_nonneg : 0 ≤ w.re := le_trans (by norm_num [dMinus]) hre
  have habs : |w.re| = w.re := abs_of_nonneg hreal_nonneg
  have hnorm : |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm w
  rw [habs] at hnorm
  exact hre.trans hnorm

theorem mixedCellClearance_full : MixedCellClearance := by
  constructor
  · exact s2_mixed_left_candidate
  · exact s2_mixed_right_candidate2

#print axioms mixedCellClearance_full

end Li2Lean.P0.Config
