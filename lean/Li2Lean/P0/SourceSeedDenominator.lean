/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.NonvanishingLiteralBridge

namespace Li2Lean.P0.ControlledResidue

set_option maxHeartbeats 5000000
set_option maxRecDepth 1000000

private theorem coprime_nat_lt (d : ℕ) (hdpos : 0 < d) (hdlt : d < 83) :
    Nat.Coprime d 83 := by
  exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt hdpos) hdlt
    (by norm_num : Nat.Prime 83)).symm

private theorem den_coprime_inv_nat (d : ℕ) (hdpos : 0 < d) (hdlt : d < 83) :
    Nat.Coprime ((d : ℚ)⁻¹).den 83 := by
  rw [Rat.inv_def, Rat.den_divInt]
  simp [show d ≠ 0 by omega]
  exact coprime_nat_lt d hdpos hdlt

private theorem den_coprime_div_nat_of_coprime (x : ℚ) (d : ℕ)
    (hx : Nat.Coprime x.den 83) (hdcop : Nat.Coprime d 83)
    (hdpos : 0 < d) :
    Nat.Coprime (x / (d : ℚ)).den 83 := by
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hdpos)
  have hxrepr : x = (x.num : ℚ) / (x.den : ℚ) := by
    exact ((Rat.intCast_div_eq_divInt x.num (x.den : ℤ)).trans
      (Rat.num_divInt_den x)).symm
  have hrepr : x / (d : ℚ) = Rat.divInt x.num (x.den * (d : ℤ)) := by
    calc
      x / (d : ℚ) = ((x.num : ℚ) / (x.den : ℚ)) / (d : ℚ) :=
        congrArg (fun y : ℚ => y / (d : ℚ)) hxrepr
      _ = (x.num : ℚ) / ((x.den : ℚ) * (d : ℚ)) := by rw [div_div]
      _ = (x.num : ℚ) / ((x.den * (d : ℤ) : ℤ) : ℚ) := by norm_num
      _ = Rat.divInt x.num (x.den * (d : ℤ)) := Rat.intCast_div_eq_divInt _ _
  rw [hrepr, Rat.den_divInt]
  split
  · simp
  · apply Nat.Coprime.of_dvd_left
      (show (x.den * (d : ℤ)).natAbs /
          (x.den * (d : ℤ)).gcd x.num ∣ x.den * d by
        have hApos : 0 < (x.den * (d : ℤ)).natAbs := by
          simp [Int.natAbs_mul]
          exact ⟨Nat.pos_of_ne_zero (Rat.den_nz x), hdpos⟩
        have hgd : (x.den * (d : ℤ)).gcd x.num ∣
            (x.den * (d : ℤ)).natAbs := Nat.gcd_dvd_left _ _
        have hgpos : 0 < (x.den * (d : ℤ)).gcd x.num :=
          Nat.gcd_pos_of_pos_left _ hApos
        apply (Nat.div_dvd_iff_dvd_mul hgd hgpos).2
        rw [show (x.den * (d : ℤ)).natAbs = x.den * d by
          simp [Int.natAbs_mul]]
        exact Nat.dvd_mul_left _ _)
    exact Nat.Coprime.mul_left hx hdcop

private theorem den_coprime_div_nat (x : ℚ) (d : ℕ)
    (hx : Nat.Coprime x.den 83) (hdpos : 0 < d) (hdlt : d < 83) :
    Nat.Coprime (x / (d : ℚ)).den 83 := by
  exact den_coprime_div_nat_of_coprime x d hx
    (coprime_nat_lt d hdpos hdlt) hdpos

example (d : Fin 40) :
    Nat.Coprime (((d.val + 1 : ℕ) : ℚ)⁻¹).den 83 := by
  apply den_coprime_inv_nat
  · omega
  · omega

private theorem den_coprime_add {x y : ℚ}
    (hx : Nat.Coprime x.den 83) (hy : Nat.Coprime y.den 83) :
    Nat.Coprime (x + y).den 83 := by
  apply Nat.Coprime.of_dvd_left (Rat.add_den_dvd x y)
  exact Nat.Coprime.mul_left hx hy

private theorem den_coprime_sub {x y : ℚ}
    (hx : Nat.Coprime x.den 83) (hy : Nat.Coprime y.den 83) :
    Nat.Coprime (x - y).den 83 := by
  apply Nat.Coprime.of_dvd_left (Rat.sub_den_dvd x y)
  exact Nat.Coprime.mul_left hx hy

private theorem den_coprime_mul {x y : ℚ}
    (hx : Nat.Coprime x.den 83) (hy : Nat.Coprime y.den 83) :
    Nat.Coprime (x * y).den 83 := by
  apply Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y)
  exact Nat.Coprime.mul_left hx hy

private theorem den_coprime_neg {x : ℚ}
    (hx : Nat.Coprime x.den 83) :
    Nat.Coprime (-x).den 83 := by
  simpa using hx

private theorem den_coprime_sum {ι : Type} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, Nat.Coprime (f i).den 83) :
    Nat.Coprime (∑ i ∈ s, f i).den 83 := by
  apply Finset.sum_induction f (fun q => Nat.Coprime q.den 83)
  · intro a b ha hb
    exact den_coprime_add ha hb
  · simp
  · intro i hi
    exact h i hi

private theorem den_coprime_prod {ι : Type} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, Nat.Coprime (f i).den 83) :
    Nat.Coprime (∏ i ∈ s, f i).den 83 := by
  apply Finset.prod_induction f (fun q => Nat.Coprime q.den 83)
  · intro a b ha hb
    exact den_coprime_mul ha hb
  · simp
  · intro i hi
    exact h i hi

private theorem den_coprime_int (z : ℤ) :
    Nat.Coprime (z : ℚ).den 83 := by
  simp [Rat.den_intCast]

private theorem p0UQ_den_coprime (i : ℕ) :
    Nat.Coprime (p0UQ (2 : ℚ) 16 i).den 83 := by
  rw [p0UQ]
  apply den_coprime_mul
  · rw [Rat.den_pow]
    have hbase : Nat.Coprime (2 : ℚ).den 83 := by norm_num
    exact Nat.Coprime.pow i 1 hbase
  · exact den_coprime_int _

private theorem p0Q_den_coprime (s : ℕ) :
    Nat.Coprime (p0Q (2 : ℚ) s).den 83 := by
  rw [p0Q]
  have hbase : (2 : ℚ) / (2 - 1) = 2 := by norm_num
  rw [hbase]
  apply den_coprime_sub
  · rw [Rat.den_pow]
    have hbase : Nat.Coprime (2 : ℚ).den 83 := by norm_num
    exact Nat.Coprime.pow s 1 hbase
  · exact den_coprime_int _

private theorem den_coprime_pow {x : ℚ} (hx : Nat.Coprime x.den 83)
    (n : ℕ) : Nat.Coprime (x ^ n).den 83 := by
  rw [Rat.den_pow]
  exact Nat.Coprime.pow n 1 hx

private theorem den_coprime_nat_cast (n : ℕ) :
    Nat.Coprime (n : ℚ).den 83 := by
  simpa using den_coprime_int (n : ℤ)

theorem p0TQ_den_coprime_test (i : ℕ) (hi : i < 64) :
    Nat.Coprime (p0TQ (2 : ℚ) 16 i).den 83 := by
  unfold p0TQ
  apply den_coprime_add
  · apply den_coprime_sum
    intro r hr
    have hterm := den_coprime_div_nat (p0UQ (2 : ℚ) 16 (i - (r + 1)))
      (r + 1) (p0UQ_den_coprime _) (by omega)
      (by have hr_lt : r < i := Finset.mem_range.mp hr; omega)
    simpa [Nat.cast_add, Nat.cast_one] using hterm
  · apply den_coprime_mul
    · apply den_coprime_pow
      norm_num
    · apply den_coprime_sum
      intro s hs
      apply den_coprime_mul
      · apply den_coprime_mul
        · have hterm := den_coprime_div_nat ((-1 : ℚ) ^ s)
            (s + 1) (den_coprime_pow (by norm_num) _)
            (by omega)
            (by have hs_lt : s < 16 := Finset.mem_range.mp hs; omega)
          simpa [Nat.cast_add, Nat.cast_one] using hterm
        · exact den_coprime_nat_cast _
      · exact p0Q_den_coprime _

theorem p0BQQ_den_coprime_test (i : ℕ) (hi : i < 40) :
    Nat.Coprime (p0BQQ (2 : ℚ) 16 i).den 83 := by
  unfold p0BQQ
  apply den_coprime_sub
  · apply den_coprime_sum
    intro r hr
    have hr_lt : r < i := Finset.mem_range.mp hr
    have hbase : Nat.Coprime (r + 1) 83 :=
      coprime_nat_lt (r + 1) (by omega) (by omega)
    have hterm := den_coprime_div_nat_of_coprime
      (p0UQ (2 : ℚ) 16 (i - (r + 1))) ((r + 1) ^ 2)
      (p0UQ_den_coprime _) (Nat.Coprime.pow 2 1 hbase) (by positivity)
    simpa [Nat.cast_pow, Nat.cast_add, Nat.cast_one] using hterm
  · apply den_coprime_mul
    · apply den_coprime_pow
      norm_num
    · apply den_coprime_sum
      intro s hs
      have hs_mem := Finset.mem_Icc.mp hs
      apply den_coprime_mul
      · apply den_coprime_mul
        · have hterm := den_coprime_div_nat
            ((-1 : ℚ) ^ s) s (den_coprime_pow (by norm_num) _)
            (by omega) (by omega)
          simpa using hterm
        · exact den_coprime_nat_cast _
      · apply den_coprime_sum
        intro r hr
        have hr_lt : r < s - 1 := Finset.mem_range.mp hr
        have hterm := den_coprime_div_nat
          (p0Q (2 : ℚ) (r + 1)) (r + 1) (p0Q_den_coprime _)
          (by omega) (by omega)
        simpa [Nat.cast_add, Nat.cast_one] using hterm

theorem p0CQ_diag_den_coprime_test (i : ℕ) (hi : i < 40) :
    Nat.Coprime (p0CQ (2 : ℚ) 16 i i).den 83 := by
  rw [p0CQ]
  simp only [if_pos rfl]
  apply den_coprime_mul
  · apply den_coprime_neg
    exact p0UQ_den_coprime _
  · apply den_coprime_sum
    intro s hs
    have hs_lt : s < 16 := Finset.mem_range.mp hs
    have hterm := den_coprime_inv_nat (i + s + 1) (by omega) (by omega)
    simpa [Nat.cast_add, Nat.cast_one] using hterm

private theorem den_coprime_div_diff (x : ℚ) (i j : ℕ)
    (hx : Nat.Coprime x.den 83) (hi : i < 40) (hj : j < 64)
    (hne : i ≠ j) :
    Nat.Coprime (x / ((j : ℚ) - (i : ℚ))).den 83 := by
  by_cases hij : i < j
  · have hd : Nat.Coprime (j - i) 83 :=
      coprime_nat_lt (j - i) (by omega) (by omega)
    have hterm := den_coprime_div_nat_of_coprime x (j - i) hx hd (by omega)
    have heq : (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub (Nat.le_of_lt hij)]
    rw [heq]
    exact hterm
  · have hji : j < i := by omega
    have hd : Nat.Coprime (i - j) 83 :=
      coprime_nat_lt (i - j) (by omega) (by omega)
    have hterm := den_coprime_div_nat_of_coprime (-x) (i - j)
      (den_coprime_neg hx) hd (by omega)
    have heq : x / ((j : ℚ) - (i : ℚ)) =
        (-x) / ((i - j : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub (Nat.le_of_lt hji)]
      rw [show (j : ℚ) - (i : ℚ) = -((i : ℚ) - (j : ℚ)) by ring,
        div_neg]
      ring
    rw [heq]
    exact hterm

theorem p0CQ_den_coprime_test (i j : ℕ) (hi : i < 40) (hj : j < 64) :
    Nat.Coprime (p0CQ (2 : ℚ) 16 i j).den 83 := by
  rw [p0CQ]
  by_cases hij : i = j
  · subst j
    exact p0CQ_diag_den_coprime_test i hi
  · simp only [if_neg hij]
    apply den_coprime_div_diff
    · apply den_coprime_sub
      exact p0UQ_den_coprime _
      exact p0UQ_den_coprime _
    · exact hi
    · exact hj
    · exact hij

theorem p0BQ_den_coprime_test (i j : ℕ) (hi : i < 40) (hj : j < 64) :
    Nat.Coprime (p0BQ (2 : ℚ) 16 i j).den 83 := by
  rw [p0BQ]
  by_cases hij : i = j
  · subst j
    simp only [if_pos rfl]
    exact p0BQQ_den_coprime_test i hi
  · simp only [if_neg hij]
    apply den_coprime_div_diff
    · apply den_coprime_sub
      · exact p0TQ_den_coprime_test i (by omega)
      · exact p0TQ_den_coprime_test j hj
    · exact hi
    · exact hj
    · exact hij

theorem sourceSeedQ_den_coprime_test (r c : Fin 64) :
    Nat.Coprime (sourceSeedQ r c).den 83 := by
  unfold sourceSeedQ
  by_cases hr : r.val < 32
  · simp only [if_pos hr]
    apply p0CQ_den_coprime_test
    · omega
    · exact c.isLt
  · simp only [if_neg hr]
    apply p0BQ_den_coprime_test
    · omega
    · exact c.isLt

theorem det_den_coprime_of_entries_83 {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ)
    (h : ∀ i j, Nat.Coprime (M i j).den 83) :
    Nat.Coprime M.det.den 83 := by
  rw [Matrix.det_apply']
  have hsum : ∀ (σ : Equiv.Perm (Fin n)),
      Nat.Coprime ((Equiv.Perm.sign σ : ℚ) *
        (∏ i : Fin n, M (σ i) i)).den 83 := by
    intro σ
    apply den_coprime_mul
    · exact den_coprime_int _
    · apply den_coprime_prod
      intro i hi
      exact h (σ i) i
  apply den_coprime_sum (s := Finset.univ)
  intro σ hσ
  exact hsum σ

theorem sourceSeedQ_det_den_coprime_test :
    Nat.Coprime (Matrix.det sourceSeedQ).den 83 := by
  apply det_den_coprime_of_entries_83
  intro r c
  exact sourceSeedQ_den_coprime_test r c

end Li2Lean.P0.ControlledResidue
