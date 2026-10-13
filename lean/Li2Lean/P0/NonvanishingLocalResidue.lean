/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.ResidueCast

namespace Li2Lean.P0.ControlledResidue

local instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

private theorem prime83 : Nat.Prime 83 := by norm_num

private theorem pow83_dvd_mul_of_not_dvd_left {n a b : ℕ}
    (ha : ¬ 83 ∣ a) (h : 83 ^ n ∣ a * b) : 83 ^ n ∣ b := by
  induction n generalizing b with
  | zero => simp
  | succ n ih =>
      have hlow : 83 ^ n ∣ a * b := (pow_dvd_pow 83 (Nat.le_succ n)).trans h
      have hbLow : 83 ^ n ∣ b := ih hlow
      obtain ⟨c, rfl⟩ := hbLow
      have hcancel : 83 ∣ a * c := by
        have hdiv : 83 ^ n * 83 ∣ 83 ^ n * (a * c) := by
          simpa [pow_succ, Nat.mul_assoc, Nat.mul_left_comm, Nat.mul_comm] using h
        exact (Nat.mul_dvd_mul_iff_left
          (show 0 < (83 : ℕ) ^ n by positivity)).mp hdiv
      have hpc : 83 ∣ c := (prime83.dvd_mul.mp hcancel).resolve_left ha
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hpc

/-- A prime-power numerator absorbs every 83-factor in a smaller denominator. -/
theorem pow83_div_den_coprime (k d : ℕ) (hd : 0 < d)
    (hbound : d < 83 * 83 ^ k) :
    Nat.Coprime (((83 ^ k : ℕ) : ℚ) / (d : ℚ)).den 83 := by
  let z : ℚ := ((83 ^ k : ℕ) : ℚ) / (d : ℚ)
  have hzpos : 0 < z := by
    dsimp [z]
    positivity
  have hnumPos : 0 < z.num := Rat.num_pos.mpr hzpos
  have hnumAbsCast : (z.num.natAbs : ℤ) = z.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hrepr : (z.num : ℚ) / (z.den : ℚ) = z := by
    calc
      (z.num : ℚ) / (z.den : ℚ) =
          (z.num : ℚ) / ((z.den : ℤ) : ℚ) := by norm_num
      _ = Rat.divInt z.num (z.den : ℤ) := Rat.intCast_div_eq_divInt _ _
      _ = z := Rat.num_divInt_den z
  have hcrossQ : ((83 ^ k : ℕ) : ℚ) * (z.den : ℚ) =
      (d : ℚ) * (z.num : ℚ) := by
    have hrat : ((83 ^ k : ℕ) : ℚ) / (d : ℚ) =
        (z.num : ℚ) / (z.den : ℚ) := by
      calc
        _ = z := rfl
        _ = _ := hrepr.symm
    have hrat' := hrat
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), Rat.den_nz z] at hrat'
    nlinarith [hrat']
  have hcrossZ : (83 ^ k : ℤ) * (z.den : ℤ) =
      (d : ℤ) * z.num := by
    exact_mod_cast hcrossQ
  have hcrossN : 83 ^ k * z.den = d * z.num.natAbs := by
    rw [← hnumAbsCast] at hcrossZ
    exact_mod_cast hcrossZ
  have hdenCop : Nat.Coprime 83 z.den := (prime83.coprime_iff_not_dvd).2 (by
    intro hpden
    have hcopred : Nat.Coprime z.num.natAbs z.den := z.reduced
    have hpnum : ¬ 83 ∣ z.num.natAbs := by
      intro h
      have hg : 83 ∣ Nat.gcd z.num.natAbs z.den := Nat.dvd_gcd h hpden
      rw [hcopred.gcd_eq_one] at hg
      norm_num at hg
    have hpowdiv : 83 ^ (k + 1) ∣ 83 ^ k * z.den := by
      rw [pow_succ]
      exact Nat.mul_dvd_mul_left _ hpden
    have hpowdiv' : 83 ^ (k + 1) ∣ d * z.num.natAbs := by
      rw [hcrossN] at hpowdiv
      exact hpowdiv
    have hdvd : 83 ^ (k + 1) ∣ d := by
      exact pow83_dvd_mul_of_not_dvd_left hpnum
        (by simpa [Nat.mul_comm] using hpowdiv')
    have hle : 83 ^ (k + 1) ≤ d := Nat.le_of_dvd hd hdvd
    rw [pow_succ] at hle
    omega)
  exact hdenCop.symm

/-- If the denominator is not divisible by the prime-power numerator, its
reduced residue is zero. -/
theorem pow83_div_den_residue_eq_zero (k d : ℕ) (hd : 0 < d)
    (hbound : d < 83 * 83 ^ k) (hno : ¬ 83 ^ k ∣ d) :
    residueOf (((83 ^ k : ℕ) : ℚ) / (d : ℚ))
      (pow83_div_den_coprime k d hd hbound) = 0 := by
  let z : ℚ := ((83 ^ k : ℕ) : ℚ) / (d : ℚ)
  have hzpos : 0 < z := by
    dsimp [z]
    positivity
  have hnumPos : 0 < z.num := Rat.num_pos.mpr hzpos
  have hnumAbsCast : (z.num.natAbs : ℤ) = z.num :=
    Int.natAbs_of_nonneg hnumPos.le
  have hrepr : (z.num : ℚ) / (z.den : ℚ) = z := by
    calc
      (z.num : ℚ) / (z.den : ℚ) =
          (z.num : ℚ) / ((z.den : ℤ) : ℚ) := by norm_num
      _ = Rat.divInt z.num (z.den : ℤ) := Rat.intCast_div_eq_divInt _ _
      _ = z := Rat.num_divInt_den z
  have hcrossQ : ((83 ^ k : ℕ) : ℚ) * (z.den : ℚ) =
      (d : ℚ) * (z.num : ℚ) := by
    have hrat : ((83 ^ k : ℕ) : ℚ) / (d : ℚ) =
        (z.num : ℚ) / (z.den : ℚ) := by
      calc
        _ = z := rfl
        _ = _ := hrepr.symm
    have hrat' := hrat
    field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd), Rat.den_nz z] at hrat'
    nlinarith [hrat']
  have hcrossZ : (83 ^ k : ℤ) * (z.den : ℤ) =
      (d : ℤ) * z.num := by
    exact_mod_cast hcrossQ
  have hcrossN : 83 ^ k * z.den = d * z.num.natAbs := by
    rw [← hnumAbsCast] at hcrossZ
    exact_mod_cast hcrossZ
  have hpnum : 83 ∣ z.num.natAbs := by
    by_contra hnot
    have hpowdiv : 83 ^ k ∣ 83 ^ k * z.den := dvd_mul_right _ _
    have hpowdiv' : 83 ^ k ∣ d * z.num.natAbs := by
      rw [hcrossN] at hpowdiv
      exact hpowdiv
    have hdvd : 83 ^ k ∣ d :=
      pow83_dvd_mul_of_not_dvd_left hnot
        (by simpa [Nat.mul_comm] using hpowdiv')
    exact hno hdvd
  have hpnumInt : (83 : ℤ) ∣ z.num := by
    apply Int.dvd_natAbs.mp
    exact_mod_cast hpnum
  have hnumZero : (z.num : F83) = 0 :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd z.num 83).2 hpnumInt
  change (z.num : F83) * (z.den : F83)⁻¹ = 0
  rw [hnumZero]
  simp

/-- Multiplication keeps a rational denominator prime to 83. -/
theorem mul_den_coprime {x y : ℚ} (hx : Nat.Coprime x.den 83)
    (hy : Nat.Coprime y.den 83) : Nat.Coprime (x * y).den 83 := by
  apply Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y)
  exact Nat.Coprime.mul_left hx hy

/-- The residue of a product of 83-integral rationals is the product of the
residues. -/
theorem residueOf_mul {x y : ℚ} (hx : Nat.Coprime x.den 83)
    (hy : Nat.Coprime y.den 83) :
    residueOf (x * y) (mul_den_coprime hx hy) =
      residueOf x hx * residueOf y hy := by
  rw [residueOf_eq_ratCast (x * y) (mul_den_coprime hx hy),
    residueOf_eq_ratCast x hx, residueOf_eq_ratCast y hy]
  exact Rat.cast_mul_of_ne_zero
    (natCast_ne_zero_of_coprime hx) (natCast_ne_zero_of_coprime hy)

/-- The rational `q^2/(d₁d₂)` is the product of its two `q/dᵢ` factors. -/
private theorem pow83_sq_div_prod_value_eq_mul (k d₁ d₂ : ℕ) :
    (((83 ^ k : ℕ) : ℚ) ^ 2 / ((d₁ * d₂ : ℕ) : ℚ)) =
      (((83 ^ k : ℕ) : ℚ) / (d₁ : ℚ)) *
        (((83 ^ k : ℕ) : ℚ) / (d₂ : ℚ)) := by
  push_cast
  field_simp

/-- Two denominator factors of size less than `83q` give a 83-integral
`q^2/(d₁d₂)` term after reducing each `q/dᵢ` factor. -/
theorem pow83_sq_div_prod_den_coprime (k d₁ d₂ : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hb₁ : d₁ < 83 * 83 ^ k) (hb₂ : d₂ < 83 * 83 ^ k) :
    Nat.Coprime (((83 ^ k : ℕ) : ℚ) ^ 2 /
        ((d₁ * d₂ : ℕ) : ℚ)).den 83 := by
  rw [pow83_sq_div_prod_value_eq_mul]
  exact mul_den_coprime
    (pow83_div_den_coprime k d₁ hd₁ hb₁)
    (pow83_div_den_coprime k d₂ hd₂ hb₂)

/-- The residue of a two-denominator `q^2` term is the product of the
residues of `q/d₁` and `q/d₂`. -/
theorem pow83_sq_div_prod_residue_eq_mul (k d₁ d₂ : ℕ)
    (hd₁ : 0 < d₁) (hd₂ : 0 < d₂)
    (hb₁ : d₁ < 83 * 83 ^ k) (hb₂ : d₂ < 83 * 83 ^ k) :
    residueOf (((83 ^ k : ℕ) : ℚ) / (d₁ : ℚ))
        (pow83_div_den_coprime k d₁ hd₁ hb₁) *
      residueOf (((83 ^ k : ℕ) : ℚ) / (d₂ : ℚ))
        (pow83_div_den_coprime k d₂ hd₂ hb₂) =
      residueOf (((83 ^ k : ℕ) : ℚ) ^ 2 /
          ((d₁ * d₂ : ℕ) : ℚ))
        (pow83_sq_div_prod_den_coprime k d₁ d₂ hd₁ hd₂ hb₁ hb₂) := by
  let x : ℚ := ((83 ^ k : ℕ) : ℚ) / (d₁ : ℚ)
  let y : ℚ := ((83 ^ k : ℕ) : ℚ) / (d₂ : ℚ)
  have hx : Nat.Coprime x.den 83 := by
    exact pow83_div_den_coprime k d₁ hd₁ hb₁
  have hy : Nat.Coprime y.den 83 := by
    exact pow83_div_den_coprime k d₂ hd₂ hb₂
  have hxy : (((83 ^ k : ℕ) : ℚ) ^ 2 /
      ((d₁ * d₂ : ℕ) : ℚ)) = x * y := by
    dsimp [x, y]
    exact pow83_sq_div_prod_value_eq_mul k d₁ d₂
  have hnum : (((83 ^ k : ℕ) : ℚ) ^ 2 /
      ((d₁ * d₂ : ℕ) : ℚ)).num = (x * y).num := congrArg Rat.num hxy
  have hden : (((83 ^ k : ℕ) : ℚ) ^ 2 /
      ((d₁ * d₂ : ℕ) : ℚ)).den = (x * y).den := congrArg Rat.den hxy
  calc
    _ = residueOf (x * y) (mul_den_coprime hx hy) :=
      (residueOf_mul hx hy).symm
    _ = residueOf (((83 ^ k : ℕ) : ℚ) ^ 2 /
        ((d₁ * d₂ : ℕ) : ℚ))
        (pow83_sq_div_prod_den_coprime k d₁ d₂ hd₁ hd₂ hb₁ hb₂) := by
      unfold residueOf
      rw [← hnum, ← hden]

end Li2Lean.P0.ControlledResidue
