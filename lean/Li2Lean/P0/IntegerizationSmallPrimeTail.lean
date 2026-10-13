/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationDeterminant
import Mathlib.Data.Nat.Choose.Factorization
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

namespace Li2Lean.P0.Integerization

noncomputable section

open Filter Topology

/-!
# The actual P0 squarefull-prime error

The paper v13 cutoff is `p^2 ≤ U+g`, with `U=2m-1` and `g=m/2`.
This module bounds the small-prime contribution to the reduced denominator
of every coefficient of the literal `a=2` determinant.  Its input is the
proved row integerization, not an abstract valuation certificate.  The
remaining large-prime valuation profile is a separate obligation.
-/

/-- The actual upper-index cutoff used in the v13 Kummer split. -/
def p0SquarefullCutoff (m : ℕ) : ℕ := p0DenominatorU m + m / 2

/-- All primes in the paper's squarefull range, including `2`.  Including
`2` is harmless for an upper error bound and avoids an exceptional omission. -/
def p0SquarefullPrimes (m : ℕ) : Finset ℕ :=
  (Finset.range (Nat.sqrt (p0SquarefullCutoff m) + 1)).filter Nat.Prime

theorem mem_p0SquarefullPrimes {m p : ℕ} :
    p ∈ p0SquarefullPrimes m ↔ p.Prime ∧ p ^ 2 ≤ p0SquarefullCutoff m := by
  simp only [p0SquarefullPrimes, Finset.mem_filter, Finset.mem_range,
    Nat.lt_succ_iff, Nat.le_sqrt']
  exact and_comm

theorem p0SquarefullCutoff_le (m : ℕ) : p0SquarefullCutoff m ≤ 3 * m := by
  unfold p0SquarefullCutoff p0DenominatorU
  have hm2 := Nat.div_le_self m 2
  omega

private theorem lcm_factorization_le_log (s : Finset ℕ) (p U : ℕ)
    (hp : p.Prime) (hs : ∀ n ∈ s, n ≠ 0 ∧ n ≤ U) :
    (s.lcm id).factorization p ≤ Nat.log p U := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    have has := hs a (Finset.mem_insert_self a s)
    have hss : ∀ n ∈ s, n ≠ 0 ∧ n ≤ U := fun n hn =>
      hs n (Finset.mem_insert_of_mem hn)
    have hs0 : s.lcm id ≠ 0 := by
      rw [Finset.lcm_ne_zero_iff]
      exact fun n hn => (hss n hn).1
    rw [Finset.lcm_insert]
    change (a.lcm (s.lcm id)).factorization p ≤ _
    rw [Nat.factorization_lcm has.1 hs0]
    change max (a.factorization p) ((s.lcm id).factorization p) ≤ _
    refine max_le ?_ (ih hss)
    rw [Nat.factorization_def a hp]
    exact (padicValNat_le_nat_log a).trans (Nat.log_mono_right has.2)

/-- The prime valuation of the actual common denominator is at most the
number of admissible prime-power layers. -/
theorem p0DenominatorLcm_factorization_le_log (m p : ℕ) (hp : p.Prime) :
    (p0DenominatorLcm m).factorization p ≤ Nat.log p (p0DenominatorU m) := by
  apply lcm_factorization_le_log (Finset.Icc 1 (p0DenominatorU m)) p
    (p0DenominatorU m) hp
  intro n hn
  have h := Finset.mem_Icc.mp hn
  exact ⟨by omega, h.2⟩

private theorem rat_den_dvd_of_int_multiple {q : ℚ} {d : ℕ}
    (hd : d ≠ 0) (hq : ∃ z : ℤ, (d : ℚ) * q = z) : q.den ∣ d := by
  obtain ⟨z, hz⟩ := hq
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have heq : q = (z : ℚ) / (d : ℚ) := by
    apply (eq_div_iff hdQ).2
    simpa [mul_comm] using hz
  rw [heq]
  have hden : (((z : ℚ) / (d : ℚ)).den : ℤ) ∣ (d : ℤ) := by
    simpa [Rat.divInt_eq_div] using Rat.den_dvd z (d : ℤ)
  exact Int.natCast_dvd_natCast.mp hden

/-- A literal coefficient's reduced denominator divides the already proved
row-scale product `d_U^(3m)`.  This also covers zero coefficients. -/
theorem p0A2_coeff_den_dvd_baseline {m : ℕ} (h4 : 4 ∣ m) (n : ℕ) :
    ((p0CanonicalPolynomial 2 m).coeff n).den ∣
      (p0DenominatorLcm m) ^ (3 * m) := by
  have hd : p0DenominatorLcm m ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  apply rat_den_dvd_of_int_multiple (pow_ne_zero _ hd)
  obtain ⟨P, hP⟩ := p0_canonical_integerized_two m h4
  have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff n) hP
  refine ⟨P.coeff n, ?_⟩
  rw [Polynomial.coeff_C_mul] at hc
  simpa using hc.symm

/-- Actual source-linked small-prime valuation bound for every coefficient. -/
theorem p0A2_coeff_den_factorization_le {m p : ℕ} (h4 : 4 ∣ m)
    (hp : p.Prime) (n : ℕ) :
    ((p0CanonicalPolynomial 2 m).coeff n).den.factorization p ≤
      (3 * m) * Nat.log p (p0DenominatorU m) := by
  have hd0 : (p0DenominatorLcm m) ^ (3 * m) ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    apply pow_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  calc
    _ ≤ ((p0DenominatorLcm m) ^ (3 * m)).factorization p :=
      Nat.factorization_le_factorization_of_dvd_right
        (p0A2_coeff_den_dvd_baseline h4 n) (Rat.den_nz _) hd0
    _ = (3 * m) * (p0DenominatorLcm m).factorization p := by
      simp [Nat.factorization_pow, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (p0DenominatorLcm_factorization_le_log m p hp)

/-- The full binomial valuation bound required for the squarefull range.
The upper index is the actual source index `i+g`, not a replaced scale. -/
theorem p0_source_choose_padicVal_le_log {m i k p : ℕ}
    (hm : 0 < m) (hi : i < 2 * m) (hp : p.Prime) :
    padicValNat p (Nat.choose (i + m / 2) k) ≤ Nat.log p (p0SquarefullCutoff m) := by
  rw [← Nat.factorization_def _ hp]
  apply Nat.factorization_choose_le_log.trans
  apply Nat.log_mono_right
  unfold p0SquarefullCutoff p0DenominatorU
  omega

/-- Multiplying the prime-power layer count by `log p` costs at most one
copy of `log U`.  This proof needs no prime number theorem. -/
theorem natLog_mul_realLog_le {p U : ℕ} (hp : 0 < p) (hU : 0 < U) :
    (Nat.log p U : ℝ) * Real.log (p : ℝ) ≤ Real.log (U : ℝ) := by
  have hpow := Nat.pow_log_le_self p (Nat.ne_of_gt hU)
  have hpowR : (p : ℝ) ^ Nat.log p U ≤ (U : ℝ) := by exact_mod_cast hpow
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have hlog := Real.log_le_log (pow_pos hpR _) hpowR
  simpa only [Real.log_pow] using hlog

/-- Log-weighted version for an actual source binomial.  All shifted lower
upper indices are also covered by replacing `i` with their smaller index. -/
theorem p0_source_choose_padicLog_le {m i k p : ℕ}
    (hm : 0 < m) (hi : i < 2 * m) (hp : p.Prime) :
    (padicValNat p (Nat.choose (i + m / 2) k) : ℝ) * Real.log (p : ℝ) ≤
      Real.log (p0SquarefullCutoff m : ℝ) := by
  have hX : 0 < p0SquarefullCutoff m := by
    unfold p0SquarefullCutoff p0DenominatorU
    omega
  have hpLog : 0 ≤ Real.log (p : ℝ) := by
    apply Real.log_nonneg
    exact_mod_cast hp.one_lt.le
  calc
    _ ≤ (Nat.log p (p0SquarefullCutoff m) : ℝ) * Real.log (p : ℝ) :=
      mul_le_mul_of_nonneg_right (by exact_mod_cast p0_source_choose_padicVal_le_log hm hi hp) hpLog
    _ ≤ _ := natLog_mul_realLog_le hp.pos hX

/-- The generic squarefull exponent budget from v13. -/
def p0SquarefullPrimeLayerCost (m : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) * Real.log (p : ℝ)

/-- The squarefull-prime log contribution of an actual coefficient's
reduced denominator.  No valuation of a model polynomial is substituted. -/
def p0SquarefullCoefficientDenCost (m n : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((((p0CanonicalPolynomial 2 m).coeff n).den.factorization p : ℕ) : ℝ) *
      Real.log (p : ℝ)

/-- An elementary quantitative envelope, `O(m^(3/2) log m)`. -/
def p0SquarefullErrorBound (x : ℝ) : ℝ :=
  3 * x * (Real.sqrt (3 * x) + 1) * Real.log (2 * x)

theorem p0SquarefullPrimeLayerCost_nonneg (m : ℕ) :
    0 ≤ p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast hprime.one_lt.le

theorem p0SquarefullCoefficientDenCost_nonneg (m n : ℕ) :
    0 ≤ p0SquarefullCoefficientDenCost m n := by
  apply Finset.sum_nonneg
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_nonneg (Nat.cast_nonneg _)
  apply Real.log_nonneg
  exact_mod_cast hprime.one_lt.le

theorem p0SquarefullCoefficientDenCost_le_layerCost {m : ℕ}
    (h4 : 4 ∣ m) (n : ℕ) :
    p0SquarefullCoefficientDenCost m n ≤ p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast p0A2_coeff_den_factorization_le h4 hprime n
  · apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le

/-- Quantitative squarefull-prime error with the paper's actual cutoff.
This bound uses only the count of integers below the square root; it needs
neither PNT nor an independently supplied theta bound. -/
theorem p0SquarefullPrimeLayerCost_le_errorBound {m : ℕ} (hm : 0 < m) :
    p0SquarefullPrimeLayerCost m ≤ p0SquarefullErrorBound (m : ℝ) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hU : 0 < p0DenominatorU m := by unfold p0DenominatorU; omega
  have hUle : (p0DenominatorU m : ℝ) ≤ 2 * (m : ℝ) := by
    have : p0DenominatorU m ≤ 2 * m := by unfold p0DenominatorU; omega
    exact_mod_cast this
  have hlogUle : Real.log (p0DenominatorU m : ℝ) ≤ Real.log (2 * (m : ℝ)) :=
    Real.log_le_log (by exact_mod_cast hU) hUle
  have hlognonneg : 0 ≤ Real.log (2 * (m : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hterm (p : ℕ) (hp : p ∈ p0SquarefullPrimes m) :
      ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) * Real.log (p : ℝ) ≤
        3 * (m : ℝ) * Real.log (2 * (m : ℝ)) := by
    have hprime := (mem_p0SquarefullPrimes.mp hp).1
    have h := (natLog_mul_realLog_le hprime.pos hU).trans hlogUle
    push_cast
    nlinarith [mul_le_mul_of_nonneg_left h (by positivity : 0 ≤ 3 * (m : ℝ))]
  have hcard : (p0SquarefullPrimes m).card ≤ Nat.sqrt (p0SquarefullCutoff m) + 1 := by
    unfold p0SquarefullPrimes
    exact (Finset.card_filter_le _ _).trans_eq (Finset.card_range _)
  have hsqrt : (Nat.sqrt (p0SquarefullCutoff m) : ℝ) ≤ Real.sqrt (3 * (m : ℝ)) := by
    apply Real.le_sqrt_of_sq_le
    have hsq := (Nat.sqrt_le' (p0SquarefullCutoff m)).trans (p0SquarefullCutoff_le m)
    exact_mod_cast hsq
  have hcardR : ((p0SquarefullPrimes m).card : ℝ) ≤ Real.sqrt (3 * (m : ℝ)) + 1 := by
    have hc : ((p0SquarefullPrimes m).card : ℝ) ≤
        (Nat.sqrt (p0SquarefullCutoff m) : ℝ) + 1 := by exact_mod_cast hcard
    linarith
  calc
    p0SquarefullPrimeLayerCost m ≤
        ∑ p ∈ p0SquarefullPrimes m, 3 * (m : ℝ) * Real.log (2 * (m : ℝ)) :=
      Finset.sum_le_sum hterm
    _ = ((p0SquarefullPrimes m).card : ℝ) *
        (3 * (m : ℝ) * Real.log (2 * (m : ℝ))) := by simp
    _ ≤ (Real.sqrt (3 * (m : ℝ)) + 1) *
        (3 * (m : ℝ) * Real.log (2 * (m : ℝ))) :=
      mul_le_mul_of_nonneg_right hcardR (by positivity)
    _ = p0SquarefullErrorBound (m : ℝ) := by unfold p0SquarefullErrorBound; ring

private theorem log_scaled_div_sqrt_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log (2 * x) / Real.sqrt x) atTop (𝓝 0) := by
  have hlog : Tendsto (fun x : ℝ => Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa only [Real.sqrt_eq_rpow] using
      (isLittleO_log_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 2)).tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => (Real.sqrt x)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp Real.tendsto_sqrt_atTop
  have hsum : Tendsto (fun x : ℝ => Real.log 2 * (Real.sqrt x)⁻¹ +
      Real.log x / Real.sqrt x) atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv).add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]
  simp [div_eq_mul_inv]

private theorem log_scaled_div_tendsto_zero :
    Tendsto (fun x : ℝ => Real.log (2 * x) / x) atTop (𝓝 0) := by
  have hlog := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hinv : Tendsto (fun x : ℝ => x⁻¹) atTop (𝓝 0) := tendsto_inv_atTop_zero
  have hsum : Tendsto (fun x : ℝ => Real.log 2 * x⁻¹ + Real.log x / x)
      atTop (𝓝 0) := by
    simpa using (tendsto_const_nhds.mul hinv).add hlog
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  rw [Real.log_mul (by norm_num) hx.ne', add_div]
  simp [div_eq_mul_inv]

/-- The normalized explicit error envelope tends to zero. -/
theorem p0SquarefullErrorBound_div_sq_tendsto_zero :
    Tendsto (fun x : ℝ => p0SquarefullErrorBound x / x ^ 2) atTop (𝓝 0) := by
  have hsum : Tendsto (fun x : ℝ =>
      (3 * Real.sqrt 3) * (Real.log (2 * x) / Real.sqrt x) +
        3 * (Real.log (2 * x) / x)) atTop (𝓝 0) := by
    simpa using
      (tendsto_const_nhds.mul log_scaled_div_sqrt_tendsto_zero).add
        (tendsto_const_nhds.mul log_scaled_div_tendsto_zero)
  apply hsum.congr'
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
  unfold p0SquarefullErrorBound
  rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
  have hs : Real.sqrt x ≠ 0 := (Real.sqrt_pos.2 hx).ne'
  have hsq := Real.sq_sqrt hx.le
  field_simp [hx.ne', hs]
  ring_nf
  rw [Real.sq_sqrt hx.le]
  ring

/-- The paper's exact generic small-prime budget is negligible after the
same `m^2` normalization used by the weighted-prime rate. -/
theorem p0SquarefullPrimeLayerCost_div_sq_tendsto_zero :
    Tendsto (fun m : ℕ => p0SquarefullPrimeLayerCost m / (m : ℝ) ^ 2)
      atTop (𝓝 0) := by
  have hlim : Tendsto (fun m : ℕ => p0SquarefullErrorBound (m : ℝ) / (m : ℝ) ^ 2)
      atTop (𝓝 0) :=
    p0SquarefullErrorBound_div_sq_tendsto_zero.comp tendsto_natCast_atTop_atTop
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hlim ?_ ?_
  · filter_upwards [] with m
    exact div_nonneg (p0SquarefullPrimeLayerCost_nonneg m) (sq_nonneg _)
  · filter_upwards [eventually_gt_atTop (0 : ℕ)] with m hm
    exact div_le_div_of_nonneg_right (p0SquarefullPrimeLayerCost_le_errorBound hm) (sq_nonneg _)

/-- Uniform coefficient statement on the actual P0 sequence.  The index
`n` is quantified after the common threshold, so increasing determinant
degree incurs no extra small-prime factor. -/
theorem p0A2_coeff_squarefull_error_uniform (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m n : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0SquarefullCoefficientDenCost m n / (m : ℝ) ^ 2 < ε := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (p0SquarefullPrimeLayerCost_div_sq_tendsto_zero.eventually_lt_const hε)
  refine ⟨M, ?_⟩
  intro m n hm _hpos h4
  exact (div_le_div_of_nonneg_right
    (p0SquarefullCoefficientDenCost_le_layerCost h4 n) (sq_nonneg _)).trans_lt (hM m hm)

/-- A single actual common denominator, formed from the literal polynomial's
finite support.  This definition makes the absence of a degree factor in the
small-prime budget explicit. -/
def p0A2CoefficientDenominator (m : ℕ) : ℕ :=
  (p0CanonicalPolynomial 2 m).support.lcm
    (fun n => ((p0CanonicalPolynomial 2 m).coeff n).den)

theorem p0A2CoefficientDenominator_pos (m : ℕ) :
    0 < p0A2CoefficientDenominator m := by
  apply Nat.pos_of_ne_zero
  unfold p0A2CoefficientDenominator
  rw [Finset.lcm_ne_zero_iff]
  exact fun n _ => Rat.den_nz _

theorem p0A2CoefficientDenominator_dvd_baseline {m : ℕ} (h4 : 4 ∣ m) :
    p0A2CoefficientDenominator m ∣ (p0DenominatorLcm m) ^ (3 * m) := by
  apply Finset.lcm_dvd
  exact fun n _ => p0A2_coeff_den_dvd_baseline h4 n

theorem p0A2CoefficientDenominator_factorization_le {m p : ℕ}
    (h4 : 4 ∣ m) (hp : p.Prime) :
    (p0A2CoefficientDenominator m).factorization p ≤
      (3 * m) * Nat.log p (p0DenominatorU m) := by
  have hd0 : (p0DenominatorLcm m) ^ (3 * m) ≠ 0 := by
    unfold p0DenominatorLcm denominatorLcm
    apply pow_ne_zero
    rw [Finset.lcm_ne_zero_iff]
    intro s hs
    exact Nat.ne_of_gt ((Finset.mem_Icc.mp hs).1)
  calc
    _ ≤ ((p0DenominatorLcm m) ^ (3 * m)).factorization p :=
      Nat.factorization_le_factorization_of_dvd_right
        (p0A2CoefficientDenominator_dvd_baseline h4)
        (Nat.ne_of_gt (p0A2CoefficientDenominator_pos m)) hd0
    _ = (3 * m) * (p0DenominatorLcm m).factorization p := by
      simp [Nat.factorization_pow, mul_comm]
    _ ≤ _ := Nat.mul_le_mul_left _ (p0DenominatorLcm_factorization_le_log m p hp)

def p0SquarefullDenominatorCost (m : ℕ) : ℝ :=
  ∑ p ∈ p0SquarefullPrimes m,
    ((p0A2CoefficientDenominator m).factorization p : ℝ) * Real.log (p : ℝ)

theorem p0SquarefullDenominatorCost_le_layerCost {m : ℕ} (h4 : 4 ∣ m) :
    p0SquarefullDenominatorCost m ≤ p0SquarefullPrimeLayerCost m := by
  apply Finset.sum_le_sum
  intro p hp
  have hprime := (mem_p0SquarefullPrimes.mp hp).1
  apply mul_le_mul_of_nonneg_right
  · exact_mod_cast p0A2CoefficientDenominator_factorization_le h4 hprime
  · apply Real.log_nonneg
    exact_mod_cast hprime.one_lt.le

/-- The actual common denominator obeys the same vanishing error budget.
The finite support is combined by LCM, so no extra factor of `m` is paid. -/
theorem p0A2_denominator_squarefull_error (ε : ℝ) (hε : 0 < ε) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      p0SquarefullDenominatorCost m / (m : ℝ) ^ 2 < ε := by
  obtain ⟨M, hM⟩ := Filter.eventually_atTop.mp
    (p0SquarefullPrimeLayerCost_div_sq_tendsto_zero.eventually_lt_const hε)
  refine ⟨M, ?_⟩
  intro m hm _hpos h4
  exact (div_le_div_of_nonneg_right
    (p0SquarefullDenominatorCost_le_layerCost h4) (sq_nonneg _)).trans_lt (hM m hm)

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0A2_coeff_den_factorization_le
#print axioms Li2Lean.P0.Integerization.p0_source_choose_padicVal_le_log
#print axioms Li2Lean.P0.Integerization.p0_source_choose_padicLog_le
#print axioms Li2Lean.P0.Integerization.natLog_mul_realLog_le
#print axioms Li2Lean.P0.Integerization.p0SquarefullCoefficientDenCost_le_layerCost
#print axioms Li2Lean.P0.Integerization.p0SquarefullPrimeLayerCost_le_errorBound
#print axioms Li2Lean.P0.Integerization.p0SquarefullErrorBound_div_sq_tendsto_zero
#print axioms Li2Lean.P0.Integerization.p0SquarefullPrimeLayerCost_div_sq_tendsto_zero
#print axioms Li2Lean.P0.Integerization.p0A2_coeff_squarefull_error_uniform
#print axioms Li2Lean.P0.Integerization.p0A2CoefficientDenominator_factorization_le
#print axioms Li2Lean.P0.Integerization.p0A2_denominator_squarefull_error
