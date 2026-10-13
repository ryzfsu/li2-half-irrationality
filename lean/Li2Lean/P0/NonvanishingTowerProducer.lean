/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.NonvanishingTower
import Li2Lean.P0.PencilAlgebra
import Li2Lean.P0.ControlledResidue
import Li2Lean.P0.NonvanishingLocalResidue

namespace Li2Lean.P0

noncomputable section

open Li2Lean
open ControlledResidue

local instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

def qRat (k : ℕ) : ℚ := ((83 ^ k : ℕ) : ℚ)

lemma natRat_good (n : ℕ) : (n : ℚ) ∈ Good83 := by
  change Nat.Coprime ((n : ℚ).den) 83
  simp

lemma intRat_good (z : ℤ) : (z : ℚ) ∈ Good83 := by
  change Nat.Coprime ((z : ℚ).den) 83
  simp

lemma pow_two_good (i : ℕ) : ((2 : ℚ) ^ i) ∈ Good83 := by
  change Nat.Coprime ((2 : ℚ) ^ i).den 83
  norm_num [Rat.den_pow]

lemma qRat_good (k : ℕ) : qRat k ∈ Good83 := by
  change Nat.Coprime (qRat k).den 83
  simp [qRat]

lemma q_div_good (k d : ℕ) (hd : 0 < d)
    (hbound : d < 83 * 83 ^ k) : qRat k / (d : ℚ) ∈ Good83 := by
  change Nat.Coprime (qRat k / (d : ℚ)).den 83
  exact pow83_div_den_coprime k d hd hbound

lemma q_sq_div_prod_good (k d₁ d₂ : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hb₁ : d₁ < 83 * 83 ^ k) (hb₂ : d₂ < 83 * 83 ^ k) :
    (qRat k)^2 / ((d₁ * d₂ : ℕ) : ℚ) ∈ Good83 := by
  change Nat.Coprime ((qRat k)^2 / ((d₁ * d₂ : ℕ) : ℚ)).den 83
  exact pow83_sq_div_prod_den_coprime k d₁ d₂ hd₁ hd₂ hb₁ hb₂

lemma q_sq_div_sq_good (k d : ℕ) (hd : 0 < d)
    (hbound : d < 83 * 83 ^ k) : (qRat k)^2 / (d : ℚ)^2 ∈ Good83 := by
  rw [show (qRat k)^2 / (d : ℚ)^2 =
      (qRat k / (d : ℚ)) * (qRat k / (d : ℚ)) by field_simp]
  exact Good83.mul_mem (q_div_good k d hd hbound) (q_div_good k d hd hbound)

lemma q_sq_div_good (k d : ℕ) (hd : 0 < d)
    (hbound : d < 83 * 83 ^ k) : (qRat k)^2 / (d : ℚ) ∈ Good83 := by
  rw [show (qRat k)^2 / (d : ℚ) =
      qRat k * (qRat k / (d : ℚ)) by field_simp]
  exact Good83.mul_mem (qRat_good k) (q_div_good k d hd hbound)

lemma q_div_diff_good (k i j : ℕ) (hij : i ≠ j)
    (hbound : max i j < 83 * 83 ^ k) :
    qRat k / ((j : ℚ) - (i : ℚ)) ∈ Good83 := by
  by_cases hji : j < i
  · have hd : 0 < i - j := Nat.sub_pos_of_lt hji
    have hbd : i - j < 83 * 83 ^ k := lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_le_of_lt (Nat.le_max_left _ _) hbound)
    have hcast : ((i - j : ℕ) : ℚ) = (i : ℚ) - (j : ℚ) := by
      exact_mod_cast Nat.cast_sub hji.le
    rw [show ((j : ℚ) - (i : ℚ)) = -((i - j : ℕ) : ℚ) by rw [hcast]; ring]
    rw [div_neg]
    exact Good83.neg_mem (q_div_good k (i-j) hd hbd)
  · have hij' : i < j := lt_of_le_of_ne (Nat.le_of_not_gt hji) hij
    have hd : 0 < j - i := Nat.sub_pos_of_lt hij'
    have hbd : j - i < 83 * 83 ^ k := lt_of_le_of_lt (Nat.sub_le _ _)
      (lt_of_le_of_lt (Nat.le_max_right _ _) hbound)
    have hcast : ((j - i : ℕ) : ℚ) = (j : ℚ) - (i : ℚ) := by
      exact_mod_cast Nat.cast_sub hij'.le
    rw [← hcast]
    exact q_div_good k (j-i) hd hbd

lemma p0U_good_general (g i : ℕ) : p0UQ (2 : ℚ) g i ∈ Good83 := by
  change Nat.Coprime (p0UQ (2 : ℚ) g i).den 83
  norm_num [p0UQ, Rat.den_mul]

lemma p0Q_good_general (s : ℕ) : p0Q (2 : ℚ) s ∈ Good83 := by
  change Nat.Coprime (p0Q (2 : ℚ) s).den 83
  norm_num [p0Q]

lemma q_mul_p0T_good (k g i : ℕ) (hi : i < 83 * 83 ^ k)
    (hg : g < 83 * 83 ^ k) :
    qRat k * p0TQ (2 : ℚ) g i ∈ Good83 := by
  unfold p0TQ
  have hsum1 : qRat k *
      (∑ r ∈ Finset.range i,
        p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) ∈ Good83 := by
    rw [Finset.mul_sum]
    apply Good83.sum_mem
    intro r hr
    have hrlt : r < i := Finset.mem_range.mp hr
    have hd : 0 < r + 1 := by omega
    have hbd : r + 1 < 83 * 83 ^ k := by omega
    have hterm : qRat k *
        (p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) ∈ Good83 := by
      rw [show qRat k *
          (p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) =
          (qRat k / (r + 1 : ℚ)) * p0UQ (2 : ℚ) g (i - (r + 1)) by
            field_simp]
      exact Good83.mul_mem (by
        simpa only [Nat.cast_add, Nat.cast_one] using
          (q_div_good k (r+1) hd hbd))
        (p0U_good_general g (i - (r+1)))
    exact hterm
  have hsum2 : qRat k *
      (2 ^ i *
        ∑ s ∈ Finset.range g,
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (2 : ℚ) (s + 1))) ∈ Good83 := by
    have hsum_expand : qRat k * (2 ^ i *
        ∑ s ∈ Finset.range g,
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (2 : ℚ) (s + 1))) =
      ∑ s ∈ Finset.range g,
        (qRat k * (2 ^ i) *
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (2 : ℚ) (s + 1))) := by
      calc
        _ = (qRat k * (2 : ℚ)^i) *
            (∑ s ∈ Finset.range g,
              (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
                (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
                p0Q (2 : ℚ) (s + 1))) := by ring
        _ = ∑ s ∈ Finset.range g,
            (qRat k * (2 : ℚ)^i) *
              (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
                (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
                p0Q (2 : ℚ) (s + 1)) := by rw [Finset.mul_sum]
        _ = _ := by
          apply Finset.sum_congr rfl
          intro s hs
          ring
    rw [hsum_expand]
    apply Good83.sum_mem
    intro s hs
    have hslt : s < g := Finset.mem_range.mp hs
    have hd : 0 < s + 1 := by omega
    have hbd : s + 1 < 83 * 83 ^ k := by omega
    rw [show qRat k * (2 : ℚ)^i *
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (2 : ℚ) (s + 1)) =
        (qRat k / ((s + 1 : ℕ) : ℚ)) *
          (((-1 : ℚ) ^ s) *
            (2 : ℚ)^i *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (2 : ℚ) (s + 1)) by
      field_simp
      push_cast
      ring]
    apply Good83.mul_mem (q_div_good k (s+1) hd hbd)
    rw [show ((-1 : ℚ) ^ s) * (2 : ℚ)^i *
          (Nat.choose (i + g) (g - (s + 1)) : ℚ) * p0Q (2 : ℚ) (s + 1) =
        ((-1 : ℚ) ^ s) * ((2 : ℚ)^i *
          ((Nat.choose (i + g) (g - (s + 1)) : ℚ) * p0Q (2 : ℚ) (s + 1))) by ring]
    exact Good83.mul_mem (by
      change Nat.Coprime ((-1 : ℚ) ^ s).den 83
      norm_num [Rat.den_pow])
      (Good83.mul_mem (pow_two_good i)
        (Good83.mul_mem (natRat_good _) (p0Q_good_general _)))
  have hadd :
      qRat k * (∑ r ∈ Finset.range i,
        p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)) +
      qRat k * (2 ^ i * ∑ s ∈ Finset.range g,
          (((-1 : ℚ) ^ s / ((s : ℚ) + 1)) *
            (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
            p0Q (2 : ℚ) (s + 1))) ∈ Good83 :=
    Good83.add_mem hsum1 hsum2
  convert hadd using 1 <;> ring

lemma q_sq_mul_p0BQQ_good (k g i : ℕ)
    (hi : i < 83 * 83 ^ k) (hg : g < 83 * 83 ^ k) :
    (qRat k)^2 * p0BQQ (2 : ℚ) g i ∈ Good83 := by
  unfold p0BQQ
  have hsum1 : (qRat k)^2 *
      (∑ r ∈ Finset.range i,
        p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)^2) ∈ Good83 := by
    rw [Finset.mul_sum]
    apply Good83.sum_mem
    intro r hr
    have hrlt : r < i := Finset.mem_range.mp hr
    have hd : 0 < r + 1 := by omega
    have hbd : r + 1 < 83 * 83 ^ k := by omega
    rw [show (qRat k)^2 *
          (p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)^2) =
        ((qRat k)^2 / ((r + 1 : ℕ) : ℚ)^2) *
          p0UQ (2 : ℚ) g (i - (r + 1)) by
      field_simp
      push_cast
      ring]
    exact Good83.mul_mem
      (by simpa only [Nat.cast_add, Nat.cast_one] using
        q_sq_div_sq_good k (r+1) hd hbd)
      (p0U_good_general g (i - (r+1)))
  have hsum2 : (qRat k)^2 *
      (2 ^ i *
        ∑ s ∈ Finset.Icc 2 g,
          (((-1 : ℚ)^s / (s : ℚ)) *
            (Nat.choose (i + g) (g - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1),
              p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ)))) ∈ Good83 := by
    have hdouble : (qRat k)^2 *
        (2 ^ i *
          ∑ s ∈ Finset.Icc 2 g,
            (((-1 : ℚ)^s / (s : ℚ)) *
              (Nat.choose (i + g) (g - s) : ℚ) *
              (∑ r ∈ Finset.range (s - 1),
                p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ)))) =
      ∑ s ∈ Finset.Icc 2 g, ∑ r ∈ Finset.range (s - 1),
        (((qRat k)^2 / ((s * (r + 1) : ℕ) : ℚ)) *
          (((-1 : ℚ)^s) * (2 : ℚ)^i *
            (Nat.choose (i + g) (g - s) : ℚ) *
            p0Q (2 : ℚ) (r + 1))) := by
      calc
        _ = ((qRat k)^2 * (2 : ℚ)^i) *
              (∑ s ∈ Finset.Icc 2 g,
                (-1 : ℚ)^s / (s : ℚ) *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  (∑ r ∈ Finset.range (s - 1),
                    p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ))) := by ring
        _ = ∑ s ∈ Finset.Icc 2 g,
              ((qRat k)^2 * (2 : ℚ)^i) *
                ((-1 : ℚ)^s / (s : ℚ) *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  (∑ r ∈ Finset.range (s - 1),
                    p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ))) := by
          rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.Icc 2 g, ∑ r ∈ Finset.range (s - 1),
              ((qRat k)^2 * (2 : ℚ)^i) *
                ((-1 : ℚ)^s / (s : ℚ) *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  (p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ))) := by
          apply Finset.sum_congr rfl
          intro s hs
          rw [Finset.mul_sum]
          rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.Icc 2 g, ∑ r ∈ Finset.range (s - 1),
              ((qRat k)^2 / ((s * (r + 1) : ℕ) : ℚ)) *
                ((-1 : ℚ)^s * (2 : ℚ)^i *
                  (Nat.choose (i + g) (g - s) : ℚ) *
                  p0Q (2 : ℚ) (r + 1)) := by
          apply Finset.sum_congr rfl
          intro s hs
          apply Finset.sum_congr rfl
          intro r hr
          have hspos : 0 < s := by
            have := Finset.mem_Icc.mp hs
            omega
          have hrpos : 0 < r + 1 := by omega
          have hcast : ((s * (r + 1) : ℕ) : ℚ) =
              (s : ℚ) * ((r + 1 : ℕ) : ℚ) := by norm_num
          rw [hcast]
          push_cast
          field_simp
    rw [hdouble]
    apply Good83.sum_mem
    intro s hs
    apply Good83.sum_mem
    intro r hr
    have hslo : 2 ≤ s := Finset.mem_Icc.mp hs |>.1
    have hshi : s ≤ g := Finset.mem_Icc.mp hs |>.2
    have hspos : 0 < s := by omega
    have hrlt : r < s - 1 := Finset.mem_range.mp hr
    have hrpos : 0 < r + 1 := by omega
    have hbs : s < 83 * 83 ^ k := lt_of_le_of_lt hshi hg
    have hbr : r + 1 < 83 * 83 ^ k := by omega
    have hchoose : (Nat.choose (i + g) (g - s) : ℚ) ∈ Good83 :=
      natRat_good (Nat.choose (i + g) (g - s))
    have hp0 : p0Q (2 : ℚ) (r + 1) ∈ Good83 :=
      p0Q_good_general (r + 1)
    have hterm := Good83.mul_mem
      (q_sq_div_prod_good k s (r+1) hspos hrpos hbs hbr)
      (Good83.mul_mem
        (by change Nat.Coprime ((-1 : ℚ)^s).den 83; norm_num [Rat.den_pow])
        (Good83.mul_mem (pow_two_good i)
          (Good83.mul_mem hchoose hp0)))
    convert hterm using 1 <;> ring
  have hsub :
      (qRat k)^2 *
        ((∑ r ∈ Finset.range i,
          p0UQ (2 : ℚ) g (i - (r + 1)) / (r + 1 : ℚ)^2) -
        2 ^ i * ∑ s ∈ Finset.Icc 2 g,
          (((-1 : ℚ)^s / (s : ℚ)) *
            (Nat.choose (i + g) (g - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1),
              p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ)))) ∈ Good83 := by
    rw [mul_sub]
    exact Good83.sub_mem hsum1 hsum2
  exact hsub

lemma q_mul_p0CQ_good (k g i j : ℕ)
    (hbound : max i j + g < 83 * 83 ^ k) :
    qRat k * p0CQ (2 : ℚ) g i j ∈ Good83 := by
  unfold p0CQ
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    have hdiag :
        qRat k * (-p0UQ (2 : ℚ) g i *
          ∑ s ∈ Finset.range g, ((i + s + 1 : ℚ)⁻¹)) =
        ∑ s ∈ Finset.range g,
          (-p0UQ (2 : ℚ) g i) *
            (qRat k / ((i + s + 1 : ℕ) : ℚ)) := by
      calc
        _ = (-p0UQ (2 : ℚ) g i) *
              (qRat k * ∑ s ∈ Finset.range g,
                ((i + s + 1 : ℚ)⁻¹)) := by ring
        _ = (-p0UQ (2 : ℚ) g i) *
              (∑ s ∈ Finset.range g,
                qRat k * ((i + s + 1 : ℚ)⁻¹)) := by rw [Finset.mul_sum]
        _ = ∑ s ∈ Finset.range g,
              (-p0UQ (2 : ℚ) g i) *
                (qRat k / ((i + s + 1 : ℕ) : ℚ)) := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro s hs
          have hcast : ((i + s + 1 : ℕ) : ℚ) =
              (i : ℚ) + (s : ℚ) + 1 := by push_cast; ring
          rw [hcast]
          field_simp
    change qRat k * (-p0UQ (2 : ℚ) g i *
      ∑ s ∈ Finset.range g, ((i + s + 1 : ℚ)⁻¹)) ∈ Good83
    rw [hdiag]
    apply Good83.sum_mem
    intro s hs
    have hslt : s < g := Finset.mem_range.mp hs
    have hdpos : 0 < i + s + 1 := by omega
    have hdbound : i + s + 1 < 83 * 83 ^ k := by
      have : i ≤ max i i + g := by omega
      omega
    exact Good83.mul_mem (Good83.neg_mem (p0U_good_general g i))
      (q_div_good k (i + s + 1) hdpos hdbound)
  · simp only [if_neg hij]
    have hdiff : max i j < 83 * 83 ^ k := by omega
    rw [show qRat k *
        ((p0UQ (2 : ℚ) g i - p0UQ (2 : ℚ) g j) /
          ((j : ℚ) - (i : ℚ))) =
        (qRat k / ((j : ℚ) - (i : ℚ))) *
          (p0UQ (2 : ℚ) g i - p0UQ (2 : ℚ) g j) by field_simp]
    exact Good83.mul_mem (q_div_diff_good k i j hij hdiff)
      (Good83.sub_mem (p0U_good_general g i) (p0U_good_general g j))

lemma q_mul_rat_good (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) : qRat k * r ∈ Good83 := by
  let d := r.den
  let p : ℚ := qRat k
  let t : ℚ := p / (d : ℚ)
  let u : ℚ := (r.num : ℚ)
  have hdenpos : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
  have hpowpos : 1 ≤ 83 ^ k := Nat.one_le_pow _ _ (by norm_num)
  have hdenbound : r.den < 83 * 83 ^ k := by omega
  have ht : t ∈ Good83 := by
    change Nat.Coprime t.den 83
    dsimp [t, p, d]
    exact pow83_div_den_coprime k r.den hdenpos hdenbound
  have hu : u ∈ Good83 := by
    change Nat.Coprime u.den 83
    simp [u, Rat.den_intCast]
  have hrrepr : r = (r.num : ℚ) / (r.den : ℚ) :=
    (Rat.num_div_den r).symm
  have hscale : p * r = t * u := by
    calc
      p * r = p * ((r.num : ℚ) / (r.den : ℚ)) :=
        congrArg (fun x : ℚ => p * x) hrrepr
      _ = t * u := by
        dsimp [t, u, d]
        field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdenpos)]
  rw [show qRat k = p by rfl, hscale]
  exact Good83.mul_mem ht hu

lemma q_sq_mul_rat_good (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) : (qRat k)^2 * r ∈ Good83 := by
  rw [show (qRat k)^2 * r = qRat k * (qRat k * r) by ring]
  exact Good83.mul_mem (qRat_good k) (q_mul_rat_good k r hbound)

lemma q_sq_mul_p0BQ_good (k g i j : ℕ)
    (hg : g < 83 * 83 ^ k)
    (hi : i < 83 * 83 ^ k) (hj : j < 83 * 83 ^ k) :
    (qRat k)^2 * p0BQ (2 : ℚ) g i j ∈ Good83 := by
  unfold p0BQ
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    exact q_sq_mul_p0BQQ_good k g i hi hg
  · simp only [if_neg hij]
    have hdiff : max i j < 83 * 83 ^ k := max_lt_iff.mpr ⟨hi, hj⟩
    rw [show (qRat k)^2 *
        ((p0TQ (2 : ℚ) g i - p0TQ (2 : ℚ) g j) /
          ((j : ℚ) - (i : ℚ))) =
        (qRat k / ((j : ℚ) - (i : ℚ))) *
          (qRat k * p0TQ (2 : ℚ) g i - qRat k * p0TQ (2 : ℚ) g j) by
            field_simp]
    exact Good83.mul_mem (q_div_diff_good k i j hij hdiff)
      (Good83.sub_mem (q_mul_p0T_good k g i hi hg)
        (q_mul_p0T_good k g j hj hg))

lemma p0AQ_good (g i j : ℕ) : p0AQ (2 : ℚ) g i j ∈ Good83 := by
  unfold p0AQ
  split
  · exact p0U_good_general g i
  · exact Good83.zero_mem

def p0A2ScaledMatrixQ (k : ℕ) (r : ℚ) :
    Matrix (Fin (2 * (32 * 83 ^ k))) (Fin (2 * (32 * 83 ^ k))) ℚ :=
  fun row col =>
    let q := 83 ^ k
    let m := 32 * q
    let i := 8 * q + (if row.val < m then row.val else row.val - m)
    if row.val < m then
      qRat k * p0CQ (2 : ℚ) (16 * q) i col.val
    else
      (qRat k)^2 * p0BQ (2 : ℚ) (16 * q) i col.val -
        ((qRat k)^2 * r) * p0AQ (2 : ℚ) (16 * q) i col.val

lemma p0A2ScaledMatrixQ_good (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) :
    ∀ row col, p0A2ScaledMatrixQ k r row col ∈ Good83 := by
  intro row col
  let q := 83 ^ k
  let m := 32 * q
  let i := 8 * q + (if row.val < m then row.val else row.val - m)
  have hqpos : 0 < q := by dsimp [q]; positivity
  have hq83 : q < 83 * q := by omega
  have hg : 16 * q < 83 * q := by omega
  have hi : i < 83 * q := by
    dsimp [i, m]
    split_ifs <;> omega
  have hj : col.val < 83 * q := by
    have hsize : col.val < 64 * q := by
      have := col.isLt
      omega
    omega
  by_cases hr : row.val < m
  · simp only [p0A2ScaledMatrixQ, q, m, i, hr]
    have hidx : i = 8 * q + row.val := by
      simp [i, m, hr]
    have hcol64 : col.val < 64 * q := by
      have := col.isLt
      omega
    have hrow32 : row.val < 32 * q := by simpa [m] using hr
    have hleft : 8 * q + row.val < 40 * q := by omega
    have hmaxlt : max (8 * q + row.val) col.val < 64 * q :=
      max_lt_iff.mpr ⟨by omega, hcol64⟩
    have hmax : max (8 * q + row.val) col.val + 16 * q < 83 * q := by omega
    have hmem := q_mul_p0CQ_good k (16 * q) (8 * q + row.val) col.val
      (by simpa [q] using hmax)
    simpa [q] using hmem
  · simp only [p0A2ScaledMatrixQ, q, m, i, hr, if_false]
    let i' : ℕ := 8 * q + (row.val - m)
    have hidx : i' = i := by
      dsimp [i', i, m]
      have hr' : ¬ row.val < 32 * q := by simpa [m] using hr
      rw [if_neg hr']
    apply Good83.sub_mem
    · have hi' : i' < 83 * 83 ^ k := by rw [hidx]; simpa [q] using hi
      have hj' : col.val < 83 * 83 ^ k := by simpa [q] using hj
      have hg' : 16 * q < 83 * 83 ^ k := by simpa [q] using hg
      have hmem := q_sq_mul_p0BQ_good k (16 * q) i' col.val hg' hi' hj'
      simpa [q, m, i'] using hmem
    · exact Good83.mul_mem (q_sq_mul_rat_good k r hbound)
        (by
          have hmem := p0AQ_good (16 * q) i' col.val
          simpa [q, m, i', hidx] using hmem)

def p0A2ScaledMatrixGood (k : ℕ) (r : ℚ)
  (hbound : r.den < 83 ^ k) :
    Matrix (Fin (2 * (32 * 83 ^ k))) (Fin (2 * (32 * 83 ^ k))) Good83 :=
  fun row col => ⟨p0A2ScaledMatrixQ k r row col,
    p0A2ScaledMatrixQ_good k r hbound row col⟩

theorem p0A2ScaledMatrixGood_coe (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) :
    (Good83.subtype.mapMatrix (p0A2ScaledMatrixGood k r hbound)) =
      p0A2ScaledMatrixQ k r := by
  ext row col
  rfl

theorem p0A2ScaledMatrixQ_eq_eval (k : ℕ) (r : ℚ) :
    p0A2ScaledMatrixQ k r =
      (p0ScaledPencilMatrixQ (2 : ℚ) (32 * 83 ^ k) (83 ^ k)).map
        (fun p => Polynomial.eval ((qRat k)^2 * r) p) := by
  ext row col
  let q := 83 ^ k
  let m := 32 * q
  have hq : (q : ℚ) = qRat k := by simp [q, qRat]
  have hm4 : m / 4 = 8 * q := by dsimp [m]; omega
  have hm2 : m / 2 = 16 * q := by dsimp [m]; omega
  by_cases hr : row.val < m
  · simp only [p0A2ScaledMatrixQ, p0ScaledPencilMatrixQ, q, m, hm4, hm2,
      if_pos hr, Matrix.map_apply, Polynomial.eval_C]
    rw [hq]
  · simp only [p0A2ScaledMatrixQ, p0ScaledPencilMatrixQ, q, m, hm4, hm2,
      if_neg hr, if_false, Matrix.map_apply, Polynomial.eval_sub,
      Polynomial.eval_mul, Polynomial.eval_X, Polynomial.eval_C]
    rw [hq]

theorem p0A2ScaledMatrixGood_det_value (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) :
    ((Matrix.det (p0A2ScaledMatrixGood k r hbound) : Good83) : ℚ) =
      Matrix.det (p0A2ScaledMatrixQ k r) := by
  change Good83.subtype
      (Matrix.det (p0A2ScaledMatrixGood k r hbound)) =
    Matrix.det (Good83.subtype.mapMatrix
      (p0A2ScaledMatrixGood k r hbound))
  calc
    _ = Matrix.det (Good83.subtype.mapMatrix
          (p0A2ScaledMatrixGood k r hbound)) :=
      RingHom.map_det Good83.subtype (p0A2ScaledMatrixGood k r hbound)
    _ = Matrix.det (p0A2ScaledMatrixQ k r) := by
      rw [p0A2ScaledMatrixGood_coe]

theorem p0A2ScaledMatrix_det_eq_source_eval
    {F : P0Family} (hbase : F.a = 2) (k : ℕ) (r : ℚ) :
    Matrix.det (p0A2ScaledMatrixQ k r) =
      (qRat k) ^ (3 * (32 * 83 ^ k)) *
        p0SourceEvalQ F (32 * 83 ^ k) r := by
  let q := 83 ^ k
  let m := 32 * q
  have hqne : q ≠ 0 := by dsimp [q]; positivity
  have hscaled0 := p0_scaled_pencil_det (2 : ℤ) m q
    (by dsimp [m]; exact ⟨8 * q, by ring⟩) hqne
  have hscaled : (p0ScaledPencilMatrixQ (2 : ℚ) m q).det =
      Polynomial.C ((q : ℚ) ^ (3 * m)) *
        Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
          (p0CanonicalPolynomial (2 : ℤ) m) := by
    simpa using hscaled0
  have hEval := congrArg (fun p : Polynomial ℚ =>
      p.eval ((qRat k)^2 * r)) hscaled
  have hmat : Matrix.det (p0A2ScaledMatrixQ k r) =
      (Matrix.det (p0ScaledPencilMatrixQ (2 : ℚ) m q)).eval
        ((qRat k)^2 * r) := by
    rw [p0A2ScaledMatrixQ_eq_eval]
    exact (RingHom.map_det (Polynomial.evalRingHom ((qRat k)^2 * r))
      (p0ScaledPencilMatrixQ (2 : ℚ) m q)).symm
  have hqcast : (q : ℚ) = qRat k := by simp [q, qRat]
  have hqneQ : (qRat k : ℚ) ≠ 0 := by
    apply Nat.cast_ne_zero.mpr
    dsimp [qRat]
    positivity
  have hcomp :
      (Polynomial.evalRingHom ((qRat k)^2 * r)).comp
        (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)) =
      Polynomial.evalRingHom r := by
    apply Polynomial.ringHom_ext
    · intro a
      simp [RingHom.comp_apply]
    · simp only [RingHom.comp_apply, Polynomial.evalRingHom,
        Polynomial.eval₂RingHom, Polynomial.eval₂_X, Polynomial.eval_X]
      simp [p0PencilSubstitution, Polynomial.eval_mul, Polynomial.eval_X,
        Polynomial.eval_C]
      rw [hqcast]
      field_simp [hqneQ]
  have hsubEval :
      (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
        (p0CanonicalPolynomial (2 : ℤ) m)).eval ((qRat k)^2 * r) =
      (p0CanonicalPolynomial (2 : ℤ) m).eval r := by
    change ((Polynomial.evalRingHom ((qRat k)^2 * r)).comp
      (Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)))
      (p0CanonicalPolynomial (2 : ℤ) m) =
      (Polynomial.evalRingHom r) (p0CanonicalPolynomial (2 : ℤ) m)
    rw [hcomp]
  have hcanon : p0CanonicalPolynomial F.a m =
      p0CanonicalPolynomial (2 : ℤ) m := by rw [hbase]
  have hEval' :
      (Matrix.det (p0ScaledPencilMatrixQ (2 : ℚ) m q)).eval
        ((qRat k)^2 * r) =
      (q : ℚ) ^ (3 * m) *
        (p0CanonicalPolynomial (2 : ℤ) m).eval r := by
    calc
      _ = (Polynomial.C ((q : ℚ) ^ (3 * m)) *
            Polynomial.eval₂RingHom Polynomial.C (p0PencilSubstitution q)
              (p0CanonicalPolynomial (2 : ℤ) m)).eval ((qRat k)^2 * r) :=
        congrArg (fun p : Polynomial ℚ => p.eval ((qRat k)^2 * r)) hscaled
      _ = _ := by
        rw [Polynomial.eval_mul, Polynomial.eval_C, hsubEval]
  calc
    Matrix.det (p0A2ScaledMatrixQ k r) =
        (Matrix.det (p0ScaledPencilMatrixQ (2 : ℚ) m q)).eval
          ((qRat k)^2 * r) := hmat
    _ = (q : ℚ) ^ (3 * m) *
          (p0CanonicalPolynomial (2 : ℤ) m).eval r := hEval'
    _ = (qRat k) ^ (3 * m) *
          (p0CanonicalPolynomial F.a m).eval r := by
      rw [hqcast]
      congr 1
      exact congrArg (fun p : Polynomial ℚ => p.eval r) hcanon.symm
    _ = (qRat k) ^ (3 * (32 * 83 ^ k)) *
          p0SourceEvalQ F (32 * 83 ^ k) r := by
      rfl

def p0A2ScaledMatrixResidue (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) :
    Matrix (Fin (64 * 83 ^ k)) (Fin (64 * 83 ^ k))
      ControlledResidue.F83 :=
  let M := p0A2ScaledMatrixGood k r hbound
  Matrix.reindex
    (finCongr (by ring : 2 * (32 * 83 ^ k) = 64 * 83 ^ k))
    (finCongr (by ring : 2 * (32 * 83 ^ k) = 64 * 83 ^ k))
    (ControlledResidue.residueHom.mapMatrix M)

def p0A2SourceSeedResidue :
    Matrix (Fin 64) (Fin 64) ControlledResidue.F83 :=
  ControlledResidue.residueHom.mapMatrix ControlledResidue.sourceSeedGood

/-- The remaining entrywise Lucas transport for the scaled pencil. It says
that the actual Good83-scaled matrix reduces to the 83-residue block matrix
of the literal 64-by-64 source seed. This is an explicit obligation, not an
assumed instance or an unconditional theorem. -/
def p0A2ScaledMatrixLucasObligation (k : ℕ) (r : ℚ)
    (hbound : r.den < 83 ^ k) (_hk : 0 < k) : Prop :=
  p0A2ScaledMatrixResidue k r hbound =
    residueBlockMatrix p0A2SourceSeedResidue (2 : ControlledResidue.F83)
      (83 ^ k)

theorem p0A2ScaledMatrix_det_residue_of_lucas
    (k : ℕ) (r : ℚ) (hbound : r.den < 83 ^ k) (hk : 0 < k)
    (hLucas : p0A2ScaledMatrixLucasObligation k r hbound hk) :
    ControlledResidue.residueHom
        (Matrix.det (p0A2ScaledMatrixGood k r hbound)) =
      (Matrix.det p0A2SourceSeedResidue) ^ (83 ^ k) := by
  have hcongr :
      (p0A2ScaledMatrixResidue k r hbound).det =
        (ControlledResidue.residueHom.mapMatrix
          (p0A2ScaledMatrixGood k r hbound)).det := by
    unfold p0A2ScaledMatrixResidue
    rw [Matrix.det_reindex_self]
  calc
    ControlledResidue.residueHom
        (Matrix.det (p0A2ScaledMatrixGood k r hbound)) =
        (p0A2ScaledMatrixResidue k r hbound).det := by
      rw [hcongr]
      exact (RingHom.map_det ControlledResidue.residueHom
        (p0A2ScaledMatrixGood k r hbound))
    _ = (residueBlockMatrix p0A2SourceSeedResidue
          (2 : ControlledResidue.F83) (83 ^ k)).det := by
      exact congrArg Matrix.det hLucas
    _ = (Matrix.det p0A2SourceSeedResidue) ^ (83 ^ k) :=
      det_p0ResidueBlockMatrix_83 32 k p0A2SourceSeedResidue

end
end Li2Lean.P0
