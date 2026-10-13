/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Integerization

namespace Li2Lean.P0.Integerization

noncomputable section

/-- The least common multiple of the positive indices up to `U`. -/
def denominatorLcm (U : ℕ) : ℕ := (Finset.Icc 1 U).lcm id

theorem dvd_denominatorLcm {U s : ℕ} (hs : 1 ≤ s) (hsU : s ≤ U) :
    s ∣ denominatorLcm U := by
  apply Finset.dvd_lcm
  simp [hs, hsU]

/-- The v10 denominator cutoff `U=2m-1` in the paper's index convention. -/
def p0DenominatorU (m : ℕ) : ℕ := 2 * m - 1

/-- The v10 common denominator `d_U = lcm(1,...,2m-1)`. -/
def p0DenominatorLcm (m : ℕ) : ℕ := denominatorLcm (p0DenominatorU m)

/-- Every positive denominator index up to the v10 cutoff divides `d_U`. -/
theorem p0_dvd_denominatorLcm {m s : ℕ} (hs : 1 ≤ s)
    (hsU : s ≤ p0DenominatorU m) :
    s ∣ p0DenominatorLcm m := by
  exact dvd_denominatorLcm hs hsU

/-- The row index used by the frozen P0 matrix. -/
def p0_v10_row_index (m : ℕ) (r : Fin (2 * m)) : ℕ :=
  m / 4 + (if r.val < m then r.val else r.val - m)

theorem p0_v10_row_index_lt (m : ℕ) (r : Fin (2 * m)) :
    p0_v10_row_index m r < m / 4 + m := by
  unfold p0_v10_row_index
  by_cases hr : r.val < m
  · simp [hr]
  · have hsub : r.val - m < m := by omega
    simp only [hr, ↓reduceIte]
    exact Nat.add_lt_add_left hsub _

/-
The unconditional arithmetic coverage needed by the v10 source formulas. The
formula-index bounds are explicit; no integrality of a matrix entry is claimed.
-/
theorem p0_v10_parameterized_denominator_coverage
    {m i j : ℕ} (hi : i < m / 4 + m) (hj : j < 2 * m) :
    (∀ r, r < i → r + 1 ∣ p0DenominatorLcm m) ∧
    (∀ s, s < m / 2 → s + 1 ∣ p0DenominatorLcm m) ∧
    (∀ s, 2 ≤ s → s ≤ m / 2 → s ∣ p0DenominatorLcm m) ∧
    (∀ s, s < m / 2 → i + s + 1 ∣ p0DenominatorLcm m) ∧
    (i < j → j - i ∣ p0DenominatorLcm m) ∧
    (j < i → i - j ∣ p0DenominatorLcm m) := by
  have hm4 : m / 4 ≤ m := Nat.div_le_self m 4
  have hm2 : m / 2 ≤ m := Nat.div_le_self m 2
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r hr
    apply p0_dvd_denominatorLcm
    · omega
    · unfold p0DenominatorU
      omega
  · intro s hs
    apply p0_dvd_denominatorLcm
    · omega
    · unfold p0DenominatorU
      omega
  · intro s hslo hshi
    apply p0_dvd_denominatorLcm
    · omega
    · unfold p0DenominatorU
      omega
  · intro s hs
    apply p0_dvd_denominatorLcm
    · omega
    · unfold p0DenominatorU
      omega
  · intro hij
    apply p0_dvd_denominatorLcm
    · omega
    · unfold p0DenominatorU
      omega
  · intro hji
    apply p0_dvd_denominatorLcm
    · omega
    · unfold p0DenominatorU
      omega

theorem p0_v10_matrix_denominator_coverage {m : ℕ} (r c : Fin (2 * m)) :
    (∀ u, u < p0_v10_row_index m r → u + 1 ∣ p0DenominatorLcm m) ∧
    (∀ s, s < m / 2 → s + 1 ∣ p0DenominatorLcm m) ∧
    (∀ s, 2 ≤ s → s ≤ m / 2 → s ∣ p0DenominatorLcm m) ∧
    (∀ s, s < m / 2 → p0_v10_row_index m r + s + 1 ∣ p0DenominatorLcm m) ∧
    (p0_v10_row_index m r < c.val → c.val - p0_v10_row_index m r ∣ p0DenominatorLcm m) ∧
    (c.val < p0_v10_row_index m r → p0_v10_row_index m r - c.val ∣ p0DenominatorLcm m) := by
  exact p0_v10_parameterized_denominator_coverage
    (p0_v10_row_index_lt m r) c.isLt

/-- A rational whose reduced denominator divides `d` becomes integral after scaling. -/
theorem rat_mul_natCast_is_int_of_den_dvd (q : ℚ) (d : ℕ)
    (hd : q.den ∣ d) :
    ∃ z : ℤ, (d : ℚ) * q = z := by
  let k : ℕ := d / q.den
  refine ⟨(k : ℤ) * q.num, ?_⟩
  have hkNat : k * q.den = d := by
    dsimp [k]
    exact Nat.mul_comm (d / q.den) q.den ▸ Nat.div_mul_cancel hd
  have hk : (k : ℚ) * (q.den : ℚ) = d := by
    exact_mod_cast hkNat
  have hq : (q.num : ℚ) = q * (q.den : ℚ) := by
    calc
      (q.num : ℚ) = ((q.num : ℚ) / (q.den : ℚ)) * q.den := by
        have hnz : (q.den : ℚ) ≠ 0 := by exact_mod_cast q.den_nz
        field_simp
      _ = q * q.den := by rw [Rat.num_div_den]
  calc
    (d : ℚ) * q = ((k : ℚ) * q.den) * q := by rw [hk]
    _ = (k : ℚ) * q.num := by
      rw [mul_assoc, mul_comm (q.den : ℚ) q, ← hq]
    _ = (((k : ℤ) * q.num : ℤ) : ℚ) := by push_cast; ring

end

end Li2Lean.P0.Integerization
