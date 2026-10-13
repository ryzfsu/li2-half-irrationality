/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationDenominators

namespace Li2Lean.P0.Integerization

noncomputable section

/-- A rational is integral after multiplication by the natural scale `d`. -/
def IsIntMultiple (d : ℕ) (q : ℚ) : Prop :=
  ∃ z : ℤ, (d : ℚ) * q = z

theorem intMultiple_natCast (d z : ℕ) : IsIntMultiple d (z : ℚ) := by
  refine ⟨(d * z : ℕ), ?_⟩
  push_cast
  ring

theorem intMultiple_intCast (d : ℕ) (z : ℤ) : IsIntMultiple d (z : ℚ) := by
  refine ⟨(d : ℤ) * z, ?_⟩
  push_cast
  ring

theorem intMultiple_add {d : ℕ} {x y : ℚ}
    (hx : IsIntMultiple d x) (hy : IsIntMultiple d y) :
    IsIntMultiple d (x + y) := by
  rcases hx with ⟨zx, hx⟩
  rcases hy with ⟨zy, hy⟩
  refine ⟨zx + zy, ?_⟩
  rw [mul_add, hx, hy]
  norm_cast

theorem intMultiple_neg {d : ℕ} {x : ℚ}
    (hx : IsIntMultiple d x) : IsIntMultiple d (-x) := by
  rcases hx with ⟨z, hz⟩
  refine ⟨-z, ?_⟩
  rw [mul_neg, hz]
  norm_cast

theorem intMultiple_sub {d : ℕ} {x y : ℚ}
    (hx : IsIntMultiple d x) (hy : IsIntMultiple d y) :
    IsIntMultiple d (x - y) := by
  simpa only [sub_eq_add_neg] using intMultiple_add hx (intMultiple_neg hy)

theorem intMultiple_mul {d e : ℕ} {x y : ℚ}
    (hx : IsIntMultiple d x) (hy : IsIntMultiple e y) :
    IsIntMultiple (d * e) (x * y) := by
  rcases hx with ⟨zx, hx⟩
  rcases hy with ⟨zy, hy⟩
  refine ⟨zx * zy, ?_⟩
  calc
    ((d * e : ℕ) : ℚ) * (x * y) = ((d : ℚ) * x) * ((e : ℚ) * y) := by
      push_cast
      ring
    _ = (zx : ℚ) * (zy : ℚ) := by rw [hx, hy]
    _ = ((zx * zy : ℤ) : ℚ) := by push_cast; ring

theorem intMultiple_sum {α : Type} (d : ℕ) (s : Finset α)
    (f : α → ℚ) (hf : ∀ i ∈ s, IsIntMultiple d (f i)) :
    IsIntMultiple d (∑ i ∈ s, f i) := by
  classical
  let z : α → ℤ := fun i =>
    if hi : i ∈ s then Classical.choose (hf i hi) else 0
  have hz (i : α) (hi : i ∈ s) : (d : ℚ) * f i = z i := by
    dsimp [z]
    rw [dif_pos hi]
    exact Classical.choose_spec (hf i hi)
  refine ⟨∑ i ∈ s, z i, ?_⟩
  rw [Finset.mul_sum]
  have hs : (∑ i ∈ s, (d : ℚ) * f i) = (∑ i ∈ s, (z i : ℚ)) := by
    apply Finset.sum_congr rfl
    intro i hi
    exact hz i hi
  rw [hs]
  norm_cast

theorem intMultiple_div_int_of_dvd {d n : ℕ} (hn : 0 < n)
    (hnd : n ∣ d) (z : ℤ) : IsIntMultiple d ((z : ℚ) / n) := by
  rcases hnd with ⟨k, hk⟩
  have hkq : (n : ℚ) * (k : ℚ) = (d : ℚ) := by exact_mod_cast hk.symm
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  refine ⟨(k : ℤ) * z, ?_⟩
  calc
    (d : ℚ) * ((z : ℚ) / n) = ((n : ℚ) * k) * ((z : ℚ) / n) := by rw [← hkq]
    _ = (k : ℚ) * z := by field_simp [hnq]
    _ = (((k : ℤ) * z : ℤ) : ℚ) := by push_cast; ring

theorem intMultiple_div_one_of_dvd {d n : ℕ} (hn : 0 < n)
    (hnd : n ∣ d) : IsIntMultiple d (1 / (n : ℚ)) := by
  simpa using intMultiple_div_int_of_dvd hn hnd (1 : ℤ)

theorem intMultiple_div_of_scaled {d n : ℕ} {q : ℚ} (hn : 0 < n)
    (hnd : n ∣ d) (hq : IsIntMultiple d q) :
    IsIntMultiple (d * d) (q / n) := by
  rcases hq with ⟨z, hz⟩
  have hdiv := intMultiple_div_int_of_dvd hn hnd z
  rcases hdiv with ⟨w, hw⟩
  refine ⟨w, ?_⟩
  have hnq : (n : ℚ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  calc
    ((d * d : ℕ) : ℚ) * (q / n) = (d : ℚ) * ((d : ℚ) * q / n) := by
      push_cast
      field_simp [hnq]
    _ = (d : ℚ) * ((z : ℚ) / n) := by rw [hz]
    _ = w := hw

theorem intMultiple_mul_intCast {d : ℕ} {q : ℚ} (hq : IsIntMultiple d q)
    (z : ℤ) : IsIntMultiple d (q * z) := by
  simpa using intMultiple_mul hq (intMultiple_intCast 1 z)

theorem intMultiple_mul_natCast {d : ℕ} {q : ℚ} (hq : IsIntMultiple d q)
    (z : ℕ) : IsIntMultiple d (q * z) := by
  simpa using intMultiple_mul hq (intMultiple_natCast 1 z)

/-- The literal v10 binomial moment specializes to an integer at `a=2`. -/
theorem p0UQ_two_eq_natCast (g i : ℕ) :
    Li2Lean.p0UQ 2 g i =
      ((2 ^ i * Nat.choose (i + g) g : ℕ) : ℚ) := by
  simp [Li2Lean.p0UQ, Nat.cast_mul, Nat.cast_pow]

/-- The v10 `Q_s(a)` factor is integral at the paper's specialization `a=2`. -/
theorem p0Q_two_eq_intCast (s : ℕ) :
    Li2Lean.p0Q 2 s = (((2 : ℤ) ^ s - 1 : ℤ) : ℚ) := by
  norm_num [Li2Lean.p0Q]

/-- The first moment in the literal P0 matrix has denominator dividing `d_U`. -/
theorem p0TQ_two_isIntMultiple {m i : ℕ}
    (hi : i < 2 * m) :
    IsIntMultiple (p0DenominatorLcm m)
      (Li2Lean.p0TQ 2 (m / 2) i) := by
  let d := p0DenominatorLcm m
  have hfirst : IsIntMultiple d
      (∑ r ∈ Finset.range i,
        Li2Lean.p0UQ 2 (m / 2) (i - (r + 1)) / (r + 1 : ℚ)) := by
    apply intMultiple_sum d (Finset.range i)
    intro r hr
    have hrlt : r < i := Finset.mem_range.mp hr
    have hrdiv : r + 1 ∣ d := by
      apply p0_dvd_denominatorLcm (by omega)
      unfold p0DenominatorU
      omega
    let u := 2 ^ (i - (r + 1)) * Nat.choose (i - (r + 1) + m / 2) (m / 2)
    have hu : Li2Lean.p0UQ 2 (m / 2) (i - (r + 1)) = (u : ℚ) := by
      dsimp [u]
      rw [p0UQ_two_eq_natCast]
    simpa [hu] using intMultiple_div_int_of_dvd (by omega) hrdiv (u : ℤ)
  have hsecond : IsIntMultiple d
      (∑ s ∈ Finset.range (m / 2),
        (((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
          (Nat.choose (i + m / 2) (m / 2 - (s + 1)) : ℚ) *
          Li2Lean.p0Q 2 (s + 1))) := by
    apply intMultiple_sum d (Finset.range (m / 2))
    intro s hs
    have hslt : s < m / 2 := Finset.mem_range.mp hs
    have hsdiv : s + 1 ∣ d := by
      apply p0_dvd_denominatorLcm (by omega)
      unfold p0DenominatorU
      omega
    let z : ℤ := (-1 : ℤ) ^ s *
      (Nat.choose (i + m / 2) (m / 2 - (s + 1)) : ℤ) *
      ((2 : ℤ) ^ (s + 1) - 1)
    have hterm :
        (((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
          (Nat.choose (i + m / 2) (m / 2 - (s + 1)) : ℚ) *
          Li2Lean.p0Q 2 (s + 1)) = (z : ℚ) / (s + 1 : ℚ) := by
      dsimp [z]
      rw [p0Q_two_eq_intCast]
      push_cast
      ring
    rw [hterm]
    simpa [Nat.cast_add, Nat.cast_one] using
      intMultiple_div_int_of_dvd (by omega) hsdiv z
  have hscaled := intMultiple_mul_natCast hsecond (2 ^ i)
  simpa [d, Li2Lean.p0TQ, mul_comm] using intMultiple_add hfirst hscaled

/-- The diagonal B moment uses at most two denominator factors. -/
theorem p0BQQ_two_isIntMultiple {m i : ℕ}
    (hi : i < m / 4 + m) :
    IsIntMultiple (p0DenominatorLcm m * p0DenominatorLcm m)
      (Li2Lean.p0BQQ 2 (m / 2) i) := by
  let d := p0DenominatorLcm m
  have hcov := p0_v10_parameterized_denominator_coverage hi (by omega : i < 2 * m)
  have hfirst : IsIntMultiple (d * d)
      (∑ r ∈ Finset.range i,
        Li2Lean.p0UQ 2 (m / 2) (i - (r + 1)) / (r + 1 : ℚ) ^ 2) := by
    apply intMultiple_sum (d * d) (Finset.range i)
    intro r hr
    have hrdiv : r + 1 ∣ d := hcov.1 r (Finset.mem_range.mp hr)
    let u := 2 ^ (i - (r + 1)) * Nat.choose (i - (r + 1) + m / 2) (m / 2)
    have hu : Li2Lean.p0UQ 2 (m / 2) (i - (r + 1)) = (u : ℚ) := by
      dsimp [u]
      rw [p0UQ_two_eq_natCast]
    have hn : 0 < r + 1 := by omega
    have hnum := intMultiple_div_int_of_dvd hn hrdiv (u : ℤ)
    have hone := intMultiple_div_one_of_dvd hn hrdiv
    have hterm := intMultiple_mul hnum hone
    have heq : (u : ℚ) / (r + 1 : ℚ) ^ 2 =
        ((u : ℚ) / (r + 1 : ℚ)) * (1 / (r + 1 : ℚ)) := by
      field_simp
    rw [hu, heq]
    simpa [Nat.cast_add, Nat.cast_one] using hterm
  have hsecond : IsIntMultiple (d * d)
      (2 ^ i *
        ∑ s ∈ Finset.Icc 2 (m / 2),
          ((-1 : ℚ) ^ s / (s : ℚ)) *
            (Nat.choose (i + m / 2) (m / 2 - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1),
              Li2Lean.p0Q 2 (r + 1) / (r + 1 : ℚ))) := by
    have hsum : IsIntMultiple (d * d)
        (∑ s ∈ Finset.Icc 2 (m / 2),
          ((-1 : ℚ) ^ s / (s : ℚ)) *
            (Nat.choose (i + m / 2) (m / 2 - s) : ℚ) *
            (∑ r ∈ Finset.range (s - 1),
              Li2Lean.p0Q 2 (r + 1) / (r + 1 : ℚ))) := by
      apply intMultiple_sum (d * d) (Finset.Icc 2 (m / 2))
      intro s hs
      have hsIcc := Finset.mem_Icc.mp hs
      have hsdiv : s ∣ d := hcov.2.2.1 s hsIcc.1 hsIcc.2
      have hinner : IsIntMultiple d
          (∑ r ∈ Finset.range (s - 1),
            Li2Lean.p0Q 2 (r + 1) / (r + 1 : ℚ)) := by
        apply intMultiple_sum d (Finset.range (s - 1))
        intro r hr
        have hrmem := Finset.mem_range.mp hr
        have hrlt : r < m / 2 := by omega
        have hrdiv : r + 1 ∣ d := hcov.2.1 r hrlt
        have hterm : Li2Lean.p0Q 2 (r + 1) / (r + 1 : ℚ) =
            ((((2 : ℤ) ^ (r + 1) - 1) : ℤ) : ℚ) /
              (r + 1 : ℚ) := by
          rw [p0Q_two_eq_intCast]
        rw [hterm]
        simpa [Nat.cast_add, Nat.cast_one] using
          intMultiple_div_int_of_dvd (by omega) hrdiv
            (((2 : ℤ) ^ (r + 1) - 1) : ℤ)
      have hcoeff : IsIntMultiple d ((-1 : ℚ) ^ s / (s : ℚ)) := by
        have h := intMultiple_div_int_of_dvd (by omega) hsdiv ((-1 : ℤ) ^ s)
        simpa using h
      have hcoeff_choose := intMultiple_mul_intCast hcoeff
        (Nat.choose (i + m / 2) (m / 2 - s) : ℤ)
      have hterm := intMultiple_mul hcoeff_choose hinner
      simpa [mul_assoc] using hterm
    have hscaled := intMultiple_mul_natCast hsum (2 ^ i)
    simpa [mul_comm, mul_left_comm, mul_assoc, Nat.cast_pow] using hscaled
  have hresult := intMultiple_sub hfirst hsecond
  simpa [d, Li2Lean.p0BQQ] using hresult

/-- Divided differences of the first moment use one `d_U` factor. -/
theorem p0TQ_diff_two_isIntMultiple {m i j : ℕ}
    (hi : i < m / 4 + m) (hj : j < m / 4 + m) :
    IsIntMultiple (p0DenominatorLcm m)
      (Li2Lean.p0TQ 2 (m / 2) i - Li2Lean.p0TQ 2 (m / 2) j) := by
  exact intMultiple_sub
    (p0TQ_two_isIntMultiple (by omega)) (p0TQ_two_isIntMultiple (by omega))

/-- The off-diagonal bottom B entries use `d_U^2`, including the signed gap. -/
theorem p0BQ_offdiag_two_isIntMultiple {m i j : ℕ}
    (hi : i < m / 4 + m) (hj : j < 2 * m) (hij : i ≠ j) :
    IsIntMultiple (p0DenominatorLcm m * p0DenominatorLcm m)
      ((Li2Lean.p0TQ 2 (m / 2) i - Li2Lean.p0TQ 2 (m / 2) j) /
        ((j : ℚ) - (i : ℚ))) := by
  let d := p0DenominatorLcm m
  have hcov := p0_v10_parameterized_denominator_coverage hi hj
  have hdiff := intMultiple_sub
    (p0TQ_two_isIntMultiple (by omega : i < 2 * m))
    (p0TQ_two_isIntMultiple hj)
  by_cases hlt : i < j
  · have hdiv : j - i ∣ d := hcov.2.2.2.2.1 hlt
    have hscaled := intMultiple_div_of_scaled (d := d) (n := j - i)
      (by omega) hdiv hdiff
    have hden : (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub (by omega)]
    simpa [d, hden] using hscaled
  · have hgt : j < i := by omega
    have hdiv : i - j ∣ d := hcov.2.2.2.2.2 hgt
    have hscaled := intMultiple_div_of_scaled (d := d) (n := i - j)
      (by omega) hdiv hdiff
    have hden : (j : ℚ) - (i : ℚ) = -((i - j : ℕ) : ℚ) := by
      push_cast
      rw [Nat.cast_sub (by omega)]
      ring
    rw [hden]
    simpa [d, div_neg] using intMultiple_neg hscaled

/-- Every actual bottom-block B entry at `a=2` is cleared by `d_U^2`. -/
theorem p0BQ_two_isIntMultiple {m i j : ℕ}
    (hi : i < m / 4 + m) (hj : j < 2 * m) :
    IsIntMultiple (p0DenominatorLcm m * p0DenominatorLcm m)
      (Li2Lean.p0BQ 2 (m / 2) i j) := by
  by_cases hij : i = j
  · subst j
    unfold Li2Lean.p0BQ
    rw [if_pos rfl]
    exact p0BQQ_two_isIntMultiple hi
  · unfold Li2Lean.p0BQ
    rw [if_neg hij]
    exact p0BQ_offdiag_two_isIntMultiple hi hj hij

/-- The diagonal pencil bank is integral at `a=2` before scaling. -/
theorem p0AQ_two_isIntMultiple {d g i j : ℕ} :
    IsIntMultiple (d * d) (Li2Lean.p0AQ 2 g i j) := by
  unfold Li2Lean.p0AQ
  by_cases hij : i = j
  · rw [if_pos hij, p0UQ_two_eq_natCast]
    exact intMultiple_natCast (d * d) _
  · rw [if_neg hij]
    exact intMultiple_natCast (d * d) 0

/-- The actual top C block of the v10 matrix is cleared by its `d_U` row. -/
theorem p0_top_C_entry_integralized {m i j : ℕ}
    (hi : i < m / 4 + m) (hj : j < 2 * m) :
    IsIntMultiple (p0DenominatorLcm m)
      (Li2Lean.p0CQ 2 (m / 2) i j) := by
  let d := p0DenominatorLcm m
  have hcov := p0_v10_parameterized_denominator_coverage hi hj
  by_cases hij : i = j
  · subst j
    unfold Li2Lean.p0CQ
    rw [if_pos rfl]
    rw [neg_mul]
    apply intMultiple_neg
    have hU : IsIntMultiple 1 (Li2Lean.p0UQ 2 (m / 2) i) := by
      rw [p0UQ_two_eq_natCast]
      exact intMultiple_natCast 1 _
    have hsum : IsIntMultiple d
        (∑ s ∈ Finset.range (m / 2), ((i + s + 1 : ℕ) : ℚ)⁻¹) := by
      apply intMultiple_sum d (Finset.range (m / 2))
      intro s hs
      have hsdiv : i + s + 1 ∣ d := hcov.2.2.2.1 s (Finset.mem_range.mp hs)
      have hterm := intMultiple_div_one_of_dvd (by omega) hsdiv
      simpa [one_div, Nat.cast_add, Nat.cast_one] using hterm
    have hprod := intMultiple_mul hU hsum
    simpa [d, mul_comm, Nat.cast_add, Nat.cast_one] using hprod
  · simp only [Li2Lean.p0CQ, if_neg hij]
    have hdiff : IsIntMultiple 1
        (Li2Lean.p0UQ 2 (m / 2) i - Li2Lean.p0UQ 2 (m / 2) j) := by
      rw [p0UQ_two_eq_natCast, p0UQ_two_eq_natCast]
      exact intMultiple_sub (intMultiple_natCast 1 _) (intMultiple_natCast 1 _)
    rcases hdiff with ⟨z, hdiff⟩
    have hdiff' : Li2Lean.p0UQ 2 (m / 2) i - Li2Lean.p0UQ 2 (m / 2) j = z := by
      simpa using hdiff
    have hresult : IsIntMultiple d
        ((Li2Lean.p0UQ 2 (m / 2) i - Li2Lean.p0UQ 2 (m / 2) j) /
          ((j : ℚ) - (i : ℚ))) := by
      by_cases hlt : i < j
      · have hk : (j - i : ℕ) ∣ d := by
          exact hcov.2.2.2.2.1 (by omega)
        have htmp := intMultiple_div_int_of_dvd (by omega) hk z
        have hden_cast : (j : ℚ) - (i : ℚ) = ((j - i : ℕ) : ℚ) := by
          push_cast
          rw [Nat.cast_sub (by omega)]
        simpa [hdiff', hden_cast] using htmp
      · have hgt : j < i := by omega
        have hk : (i - j : ℕ) ∣ d := hcov.2.2.2.2.2 hgt
        have htmp := intMultiple_div_int_of_dvd (by omega) hk z
        have hden_cast : (j : ℚ) - (i : ℚ) = -((i - j : ℕ) : ℚ) := by
          push_cast
          rw [Nat.cast_sub (by omega)]
          ring
        have hneg := intMultiple_neg htmp
        rw [hden_cast]
        simp only [div_neg]
        simpa [hdiff'] using hneg
    simpa [Li2Lean.p0CQ, hij] using hresult

noncomputable def p0TopInt (m : ℕ) (r c : Fin (2 * m)) : ℤ :=
  Classical.choose (p0_top_C_entry_integralized
    (m := m) (i := p0_v10_row_index m r) (j := c.val)
    (p0_v10_row_index_lt m r) c.isLt)

theorem p0TopInt_spec {m : ℕ} (r c : Fin (2 * m)) :
    (p0DenominatorLcm m : ℚ) *
      Li2Lean.p0CQ 2 (m / 2) (p0_v10_row_index m r) c.val =
      p0TopInt m r c :=
  Classical.choose_spec (p0_top_C_entry_integralized
    (m := m) (i := p0_v10_row_index m r) (j := c.val)
    (p0_v10_row_index_lt m r) c.isLt)

noncomputable def p0BottomInt (m : ℕ) (r c : Fin (2 * m)) : ℤ :=
  Classical.choose (p0BQ_two_isIntMultiple
    (m := m) (i := p0_v10_row_index m r) (j := c.val)
    (p0_v10_row_index_lt m r) c.isLt)

theorem p0BottomInt_spec {m : ℕ} (r c : Fin (2 * m)) :
    (p0DenominatorLcm m : ℚ) ^ 2 *
      Li2Lean.p0BQ 2 (m / 2) (p0_v10_row_index m r) c.val =
      p0BottomInt m r c := by
  have h := Classical.choose_spec (p0BQ_two_isIntMultiple
    (m := m) (i := p0_v10_row_index m r) (j := c.val)
    (p0_v10_row_index_lt m r) c.isLt)
  calc
    (p0DenominatorLcm m : ℚ) ^ 2 *
        Li2Lean.p0BQ 2 (m / 2) (p0_v10_row_index m r) c.val =
        ((p0DenominatorLcm m : ℚ) * (p0DenominatorLcm m : ℚ)) *
          Li2Lean.p0BQ 2 (m / 2) (p0_v10_row_index m r) c.val := by rw [pow_two]
    _ = ((p0DenominatorLcm m * p0DenominatorLcm m : ℕ) : ℚ) *
          Li2Lean.p0BQ 2 (m / 2) (p0_v10_row_index m r) c.val := by norm_cast
    _ = p0BottomInt m r c := by
      exact_mod_cast h

noncomputable def p0AInt (m : ℕ) (r c : Fin (2 * m)) : ℤ :=
  Classical.choose (p0AQ_two_isIntMultiple
    (d := p0DenominatorLcm m) (g := m / 2)
    (i := p0_v10_row_index m r) (j := c.val))

theorem p0AInt_spec {m : ℕ} (r c : Fin (2 * m)) :
    (p0DenominatorLcm m : ℚ) ^ 2 *
      Li2Lean.p0AQ 2 (m / 2) (p0_v10_row_index m r) c.val =
      p0AInt m r c := by
  have h := Classical.choose_spec
    (p0AQ_two_isIntMultiple
      (d := p0DenominatorLcm m) (g := m / 2)
      (i := p0_v10_row_index m r) (j := c.val))
  calc
    (p0DenominatorLcm m : ℚ) ^ 2 *
        Li2Lean.p0AQ 2 (m / 2) (p0_v10_row_index m r) c.val =
        ((p0DenominatorLcm m : ℚ) * (p0DenominatorLcm m : ℚ)) *
          Li2Lean.p0AQ 2 (m / 2) (p0_v10_row_index m r) c.val := by rw [pow_two]
    _ = ((p0DenominatorLcm m * p0DenominatorLcm m : ℕ) : ℚ) *
          Li2Lean.p0AQ 2 (m / 2) (p0_v10_row_index m r) c.val := by norm_cast
    _ = p0AInt m r c := h

/-- The actual integer polynomial matrix for the specialized `a=2` pencil.

This is a finite coefficientwise extraction: top C rows use one `d_U`, while
bottom B and A rows use `d_U^2`. The formal parameter remains the polynomial
variable `T`; this does not claim formal coefficient extraction in `a`.
-/
noncomputable def p0IntegerizedMatrixTwo (m : ℕ) :
    Matrix (Fin (2 * m)) (Fin (2 * m)) (Polynomial ℤ) := fun r c =>
  let i := p0_v10_row_index m r
  let j := c.val
  if hr : r.val < m then
    Polynomial.C (p0TopInt m r c)
  else
    Polynomial.C (p0BottomInt m r c) -
      Polynomial.X * Polynomial.C (p0AInt m r c)

theorem p0_integerizedRows_two (m : ℕ) :
    IntegerizedRows (Li2Lean.p0MatrixQ 2 m)
      (p0RowScale 2 m (p0DenominatorLcm m)) := by
  classical
  refine ⟨p0IntegerizedMatrixTwo m, ?_⟩
  intro r c
  by_cases hr : r.val < m
  · simp only [p0IntegerizedMatrixTwo, p0RowScale, Li2Lean.p0MatrixQ,
      p0_v10_row_index, dif_pos hr, if_pos hr, Polynomial.map_C]
    have hspec := congrArg (Polynomial.C : ℚ → Polynomial ℚ)
      (p0TopInt_spec r c).symm
    simpa [Polynomial.C_mul, p0_v10_row_index, hr] using hspec
  · simp only [p0IntegerizedMatrixTwo, p0RowScale, Li2Lean.p0MatrixQ,
      p0_v10_row_index, dif_neg hr, if_neg hr, Polynomial.map_sub,
      Polynomial.map_mul, Polynomial.map_X, Polynomial.map_C]
    norm_num
    have hB := p0BottomInt_spec r c
    have hA := p0AInt_spec r c
    have hBpoly : Polynomial.C (p0BottomInt m r c : ℚ) =
        Polynomial.C (p0DenominatorLcm m : ℚ) ^ 2 *
          Polynomial.C (Li2Lean.p0BQ 2 (m / 2)
            (p0_v10_row_index m r) c.val) := by
      calc
        _ = Polynomial.C ((p0DenominatorLcm m : ℚ) ^ 2 *
              Li2Lean.p0BQ 2 (m / 2) (p0_v10_row_index m r) c.val) :=
                congrArg Polynomial.C hB.symm
        _ = _ := by simp [Polynomial.C_mul]
    have hApoly : Polynomial.C (p0AInt m r c : ℚ) =
        Polynomial.C (p0DenominatorLcm m : ℚ) ^ 2 *
          Polynomial.C (Li2Lean.p0AQ 2 (m / 2)
            (p0_v10_row_index m r) c.val) := by
      calc
        _ = Polynomial.C ((p0DenominatorLcm m : ℚ) ^ 2 *
              Li2Lean.p0AQ 2 (m / 2) (p0_v10_row_index m r) c.val) :=
                congrArg Polynomial.C hA.symm
        _ = _ := by simp [Polynomial.C_mul]
    have hBpoly' : Polynomial.C (p0BottomInt m r c : ℚ) =
        Polynomial.C (p0DenominatorLcm m : ℚ) ^ 2 *
          Polynomial.C (Li2Lean.p0BQ 2 (m / 2)
            (m / 4 + (r.val - m)) c.val) := by
      simpa [p0_v10_row_index, hr] using hBpoly
    have hApoly' : Polynomial.C (p0AInt m r c : ℚ) =
        Polynomial.C (p0DenominatorLcm m : ℚ) ^ 2 *
          Polynomial.C (Li2Lean.p0AQ 2 (m / 2)
            (m / 4 + (r.val - m)) c.val) := by
      simpa [p0_v10_row_index, hr] using hApoly
    change Polynomial.C (p0BottomInt m r c : ℚ) -
        Polynomial.X * Polynomial.C (p0AInt m r c : ℚ) = _
    rw [hBpoly', hApoly']
    have hscale : (p0DenominatorLcm m : Polynomial ℚ) ^ 2 =
        Polynomial.C ((p0DenominatorLcm m : ℚ) ^ 2) := by
      simp [Polynomial.C_pow]
    rw [hscale]
    simp only [Polynomial.C_pow]
    ring

end

end Li2Lean.P0.Integerization
