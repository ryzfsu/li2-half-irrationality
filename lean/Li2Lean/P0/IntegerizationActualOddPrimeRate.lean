/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFeatureRate
import Li2Lean.P0.A2DegreeBound
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Algebra.Polynomial.Lifts

/-!
# The actual primewise settled integerizer at `a = 2`

The row-scale integerizer `d_U^(3m)` and its quotient by the two-adic
feature factor do not have the paper's sharp rate.  This module constructs
the rational prime product with the paper's odd-prime settlement, and proves
that sufficient zero-aware coefficient valuation bounds integerize the
literal canonical polynomial.  No exact content or gcd extraction is used.
-/

namespace Li2Lean.P0.Integerization

noncomputable section

open Filter Topology

/-- A finite prime product with signed exponents. -/
def rationalPrimeProduct (s : Finset ℕ) (E : ℕ → ℤ) : ℚ :=
  ∏ p ∈ s, (p : ℚ) ^ E p

theorem rationalPrimeProduct_pos (s : Finset ℕ) (E : ℕ → ℤ)
    (hs : ∀ p ∈ s, p.Prime) : 0 < rationalPrimeProduct s E := by
  unfold rationalPrimeProduct
  apply Finset.prod_pos
  intro p hp
  exact zpow_pos (by exact_mod_cast (hs p hp).pos) _

theorem padicValRat_finset_prod {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (f : ℕ → ℚ) (hf : ∀ n ∈ s, f n ≠ 0) :
    padicValRat p (∏ n ∈ s, f n) = ∑ n ∈ s, padicValRat p (f n) := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert n s hn ih =>
    rw [Finset.prod_insert hn, Finset.sum_insert hn,
      padicValRat.mul (hf n (Finset.mem_insert_self n s))
        (Finset.prod_ne_zero_iff.mpr (fun i hi => hf i (Finset.mem_insert_of_mem hi)))]
    rw [ih (fun i hi => hf i (Finset.mem_insert_of_mem hi))]

theorem rationalPrimeProduct_padicVal {p : ℕ} (hp : p.Prime)
    (s : Finset ℕ) (E : ℕ → ℤ) (hs : ∀ r ∈ s, r.Prime) :
    padicValRat p (rationalPrimeProduct s E) = if p ∈ s then E p else 0 := by
  letI : Fact p.Prime := ⟨hp⟩
  classical
  unfold rationalPrimeProduct
  rw [padicValRat_finset_prod hp s _ (fun r hr =>
    zpow_ne_zero _ (by exact_mod_cast (hs r hr).ne_zero))]
  have hterm (r : ℕ) (hr : r ∈ s) :
      padicValRat p ((r : ℚ) ^ E r) = if r = p then E p else 0 := by
    rw [padicValRat.zpow]
    by_cases hrp : r = p
    · subst r
      simp [padicValRat.self hp.one_lt]
    · have hnot : ¬p ∣ r := by
        intro hd
        exact hrp ((Nat.prime_dvd_prime_iff_eq hp (hs r hr)).mp hd).symm
      simp [hrp, padicValNat.eq_zero_of_not_dvd hnot]
  rw [Finset.sum_congr rfl hterm]
  by_cases hps : p ∈ s
  · rw [if_pos hps, Finset.sum_eq_single p]
    · simp
    · intro r hr hrp
      simp [hrp]
    · intro h
      exact (h hps).elim
  · rw [if_neg hps]
    apply Finset.sum_eq_zero
    intro r hr
    have hrp : r ≠ p := by
      intro h
      exact hps (h ▸ hr)
    simp [hrp]

theorem rationalPrimeProduct_log (s : Finset ℕ) (E : ℕ → ℤ)
    (hs : ∀ p ∈ s, p.Prime) :
    Real.log (rationalPrimeProduct s E : ℝ) =
      ∑ p ∈ s, (E p : ℝ) * Real.log p := by
  unfold rationalPrimeProduct
  push_cast
  rw [Real.log_prod (fun p hp =>
    zpow_ne_zero _ (by exact_mod_cast (hs p hp).ne_zero))]
  apply Finset.sum_congr rfl
  intro p hp
  exact Real.log_zpow _ _

/-- A rational is integral whenever all its prime valuations are nonnegative.
The proof uses the reduced denominator, including the zero rational. -/
theorem rat_is_int_of_prime_padic_nonneg (q : ℚ)
    (hq : ∀ p : ℕ, p.Prime → 0 ≤ padicValRat p q) :
    ∃ z : ℤ, q = z := by
  have hden : q.den = 1 := by
    by_contra hne
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hne
    have hv : 0 < padicValNat p q.den := by
      have hpd1 : p ^ (1 : ℕ) ∣ q.den := by simpa using hpd
      have h := (padicValNat_dvd_iff_le_of_ne_one hp.ne_one q.den_nz).mp hpd1
      omega
    rcases Rat.num_or_den_zero_padicVal q hp with hnum | hzero
    · have hqv := hq p hp
      simp only [padicValRat_def, hnum, Nat.cast_zero, zero_sub] at hqv
      omega
    · omega
  exact ⟨q.num, (Rat.coe_int_num_of_den_eq_one hden).symm⟩

/-- Sufficient valuation bounds yield an integral scaled rational. -/
theorem rat_mul_is_int_of_prime_padic_lower (D q : ℚ) (hD : D ≠ 0)
    (hq : ∀ p : ℕ, p.Prime → q = 0 ∨ -padicValRat p D ≤ padicValRat p q) :
    ∃ z : ℤ, D * q = z := by
  apply rat_is_int_of_prime_padic_nonneg
  intro p hp
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hq0 : q = 0
  · simp [hq0]
  · rw [padicValRat.mul hD hq0]
    have h := (hq p hp).resolve_left hq0
    omega

def p0A2FeatureExponent (m : ℕ) : ℕ :=
  13 * (m / 4) ^ 2 - 4 * (m / 4)

/-- The actual signed exponent: the two-adic feature credit, and the minimum
of the moving-prime and baseline bounds at every odd prime. -/
def p0A2SettledPrimeExponent (m : ℕ) (W : ℕ → ℕ → ℤ) (p : ℕ) : ℤ :=
  if p = 2 then
    ((3 * m * Nat.log 2 (p0DenominatorU m) : ℕ) : ℤ) -
      (p0A2FeatureExponent m : ℤ)
  else
    min (W m p) ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℤ)

/-- The primewise settled scalar for the literal `a = 2` determinant.  The
finite support is sufficient since the baseline has no primes above `U`. -/
def p0A2SettledD (m : ℕ) (W : ℕ → ℕ → ℤ) : ℚ :=
  rationalPrimeProduct (Nat.primesLE (p0DenominatorU m))
    (p0A2SettledPrimeExponent m W)

theorem p0A2SettledD_pos (m : ℕ) (W : ℕ → ℕ → ℤ) : 0 < p0A2SettledD m W := by
  exact rationalPrimeProduct_pos _ _ (fun p hp => Nat.prime_of_mem_primesLE hp)

theorem p0A2SettledD_padicVal {p : ℕ} (hp : p.Prime)
    (m : ℕ) (W : ℕ → ℕ → ℤ) :
    padicValRat p (p0A2SettledD m W) =
      if p ≤ p0DenominatorU m then p0A2SettledPrimeExponent m W p else 0 := by
  rw [p0A2SettledD, rationalPrimeProduct_padicVal hp _ _
    (fun r hr => Nat.prime_of_mem_primesLE hr)]
  simp only [Nat.mem_primesLE, hp, and_true]

theorem p0A2SettledD_log (m : ℕ) (W : ℕ → ℕ → ℤ) :
    Real.log (p0A2SettledD m W : ℝ) =
      ∑ p ∈ Nat.primesLE (p0DenominatorU m),
        (p0A2SettledPrimeExponent m W p : ℝ) * Real.log p := by
  exact rationalPrimeProduct_log _ _ (fun p hp => Nat.prime_of_mem_primesLE hp)

theorem p0A2BaselineD_padicVal {p : ℕ} (hp : p.Prime) (m : ℕ) :
    padicValRat p (p0A2BaselineD m) =
      (3 * m * Nat.log p (p0DenominatorU m) : ℕ) := by
  letI : Fact p.Prime := ⟨hp⟩
  rw [p0A2BaselineD, padicValRat.pow, padicValRat.of_nat]
  have h := Nat.factorization_lcmUpto (p0DenominatorU m) hp
  rw [Nat.factorization_def _ hp] at h
  change padicValNat p (p0DenominatorLcm m) = Nat.log p (p0DenominatorU m) at h
  rw [h]
  push_cast
  ring

/-- The actual baseline supplies the coarse prime bound, without any
assumption that it has the sharp denominator rate. -/
theorem p0A2_baseline_coeff_valuation_lower (m : ℕ) (hm : 0 < m)
    (h4 : 4 ∣ m) (n p : ℕ) (hp : p.Prime) :
    (p0CanonicalPolynomial 2 m).coeff n = 0 ∨
      -((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℤ) ≤
        padicValRat p ((p0CanonicalPolynomial 2 m).coeff n) := by
  letI : Fact p.Prime := ⟨hp⟩
  by_cases hc : (p0CanonicalPolynomial 2 m).coeff n = 0
  · exact Or.inl hc
  · right
    obtain ⟨z, hz⟩ := p0A2_baseline_coeff_is_int m h4 n
    have hval := congrArg (padicValRat p) hz
    rw [padicValRat.mul (ne_of_gt (p0A2BaselineD_pos hm)) hc,
      p0A2BaselineD_padicVal hp, padicValRat.of_int] at hval
    omega

/-- The scalar feature assertion is explicitly about the actual baseline
polynomial, not a separate or abstract coefficient family. -/
def P0A2ActualTwoFeatureDivisibility (m : ℕ) : Prop :=
  ∃ P : Polynomial ℤ,
    Polynomial.C ((2 : ℤ) ^ p0A2FeatureExponent m) ∣ P ∧
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (p0A2BaselineD m) * p0CanonicalPolynomial 2 m

/-- Descend an actual real coefficient-map witness from the existing feature
bridge to the rational polynomial used in the primewise settlement. -/
theorem p0A2ActualTwoFeatureDivisibility_of_real_witness (m : ℕ) (h4 : 4 ∣ m)
    (P : Polynomial ℤ)
    (hdiv : Polynomial.C (p0A2TwoFeatureFactor m : ℤ) ∣ P)
    (hmap : Polynomial.map (Int.castRingHom ℝ) P =
      Polynomial.C (p0A2BaselineD m : ℝ) * p0A2CanonicalFamily.G m) :
    P0A2ActualTwoFeatureDivisibility m := by
  refine ⟨P, ?_, ?_⟩
  · simpa [p0A2TwoFeatureFactor, p0A2FeatureExponent, h4] using hdiv
  · apply Polynomial.map_injective (algebraMap ℚ ℝ) Rat.cast_injective
    have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
      ext z
      simp
    rw [Polynomial.map_map, hcomp]
    simpa [p0A2CanonicalFamily] using hmap

/-- The signed two-adic coefficient estimate follows from divisibility of
the actual baseline coefficients by the actual feature factor. -/
theorem p0A2_two_feature_coeff_valuation_lower (m : ℕ) (hm : 0 < m)
    (hfeature : P0A2ActualTwoFeatureDivisibility m) (n : ℕ) :
    (p0CanonicalPolynomial 2 m).coeff n = 0 ∨
      -(((3 * m * Nat.log 2 (p0DenominatorU m) : ℕ) : ℤ) -
          (p0A2FeatureExponent m : ℤ)) ≤
        padicValRat 2 ((p0CanonicalPolynomial 2 m).coeff n) := by
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  by_cases hc : (p0CanonicalPolynomial 2 m).coeff n = 0
  · exact Or.inl hc
  · right
    obtain ⟨P, ⟨Q, hPQ⟩, hP⟩ := hfeature
    have heq := congrArg (fun R : Polynomial ℚ => R.coeff n) hP
    rw [hPQ, Polynomial.map_mul, Polynomial.map_C,
      Polynomial.coeff_C_mul, Polynomial.coeff_map,
      Polynomial.coeff_C_mul] at heq
    rw [map_pow] at heq
    change (2 : ℚ) ^ p0A2FeatureExponent m * (Q.coeff n : ℚ) =
      p0A2BaselineD m * (p0CanonicalPolynomial 2 m).coeff n at heq
    have hz : (Q.coeff n : ℚ) ≠ 0 := by
      intro hz
      rw [hz, mul_zero] at heq
      exact mul_ne_zero (ne_of_gt (p0A2BaselineD_pos hm)) hc heq.symm
    have hpow : (2 : ℚ) ^ p0A2FeatureExponent m ≠ 0 := by positivity
    have hself : padicValRat 2 (2 : ℚ) = 1 := by
      simpa only [Nat.cast_ofNat] using
        (padicValRat.self (by decide : 1 < (2 : ℕ)))
    have hval := congrArg (padicValRat 2) heq
    rw [padicValRat.mul hpow hz,
      padicValRat.mul (ne_of_gt (p0A2BaselineD_pos hm)) hc,
      p0A2BaselineD_padicVal (by decide), padicValRat.pow,
      hself, mul_one, padicValRat.of_int] at hval
    omega

/-- The moving-prime source obligation for the literal determinant.  Zero
coefficients need no lower bound because `padicValRat 0` defaults to zero.
Only supported primes need the moving-prime input. -/
def P0A2ActualOddPrimeValuationBound (m : ℕ) (W : ℕ → ℕ → ℤ) : Prop :=
  ∀ p : ℕ, p.Prime → p ≠ 2 → p ≤ p0DenominatorU m → ∀ n : ℕ,
    (p0CanonicalPolynomial 2 m).coeff n = 0 ∨
      -(W m p) ≤ padicValRat p ((p0CanonicalPolynomial 2 m).coeff n)

theorem p0A2_settled_coeff_is_int (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (W : ℕ → ℕ → ℤ) (hfeature : P0A2ActualTwoFeatureDivisibility m)
    (hodd : P0A2ActualOddPrimeValuationBound m W) (n : ℕ) :
    ∃ z : ℤ, p0A2SettledD m W * (p0CanonicalPolynomial 2 m).coeff n = z := by
  apply rat_mul_is_int_of_prime_padic_lower _ _ (ne_of_gt (p0A2SettledD_pos m W))
  intro p hp
  have hbase := p0A2_baseline_coeff_valuation_lower m hm h4 n p hp
  by_cases hc : (p0CanonicalPolynomial 2 m).coeff n = 0
  · exact Or.inl hc
  · right
    have hbase' := hbase.resolve_left hc
    rw [p0A2SettledD_padicVal hp]
    by_cases hpU : p ≤ p0DenominatorU m
    · rw [if_pos hpU]
      by_cases hp2 : p = 2
      · subst p
        simp only [p0A2SettledPrimeExponent, ↓reduceIte]
        exact (p0A2_two_feature_coeff_valuation_lower m hm hfeature n).resolve_left hc
      · have hodd' := (hodd p hp hp2 hpU n).resolve_left hc
        rw [p0A2SettledPrimeExponent, if_neg hp2]
        omega
    · rw [if_neg hpU]
      have hpgt : p0DenominatorU m < p := lt_of_not_ge hpU
      have hlog : Nat.log p (p0DenominatorU m) = 0 := Nat.log_of_lt hpgt
      simpa [hlog] using hbase'

/-- Sufficient coefficient valuations integerize the actual settled prime
product.  This theorem does not require exact gcd extraction. -/
theorem p0A2_settled_integerizer (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (W : ℕ → ℕ → ℤ) (hfeature : P0A2ActualTwoFeatureDivisibility m)
    (hodd : P0A2ActualOddPrimeValuationBound m W) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (p0A2SettledD m W) * p0CanonicalPolynomial 2 m := by
  rw [← Polynomial.mem_lifts, Polynomial.lifts_iff_coeff_lifts]
  intro n
  rw [Polynomial.coeff_C_mul]
  obtain ⟨z, hz⟩ := p0A2_settled_coeff_is_int m hm h4 W hfeature hodd n
  exact ⟨z, hz.symm⟩

theorem p0A2_settled_integerizer_real (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (W : ℕ → ℕ → ℤ) (hfeature : P0A2ActualTwoFeatureDivisibility m)
    (hodd : P0A2ActualOddPrimeValuationBound m W) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℝ) P =
        Polynomial.C (p0A2SettledD m W : ℝ) * p0A2CanonicalFamily.G m := by
  obtain ⟨P, hP⟩ := p0A2_settled_integerizer m hm h4 W hfeature hodd
  refine ⟨P, ?_⟩
  have hmap := congrArg (Polynomial.map (algebraMap ℚ ℝ)) hP
  have hcomp : (algebraMap ℚ ℝ).comp (Int.castRingHom ℚ) = Int.castRingHom ℝ := by
    ext z
    simp
  rw [Polynomial.map_map, hcomp] at hmap
  simpa [p0A2CanonicalFamily] using hmap

/-- Endpoint assembly with the concrete settled scalar.  The finite
prime-sum rate input is intentionally separate from the coefficient input;
neither is an assumed integerizer conclusion. -/
theorem p0A2_integerizer_bound_at_of_actual_prime_inputs
    (W : ℕ → ℕ → ℤ) (rate : ℝ)
    (hfeature : ∀ m, 0 < m → 4 ∣ m → P0A2ActualTwoFeatureDivisibility m)
    (hodd : ∀ m, 0 < m → 4 ∣ m → P0A2ActualOddPrimeValuationBound m W)
    (hprimeSum : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (p0DenominatorU m),
        (p0A2SettledPrimeExponent m W p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤
          rate + ε) :
    P0IntegerizerBoundAt p0A2CanonicalFamily rate := by
  refine ⟨fun m => p0A2SettledD m W, ?_, p0A2CanonicalFamily_degree_bound, ?_, ?_⟩
  · intro m hm h4
    exact p0A2SettledD_pos m W
  · intro m hm h4
    exact p0A2_settled_integerizer_real m hm h4 W (hfeature m hm h4) (hodd m hm h4)
  · intro ε hε
    obtain ⟨M, hM⟩ := hprimeSum ε hε
    refine ⟨M, ?_⟩
    intro m hMm hm h4
    rw [p0A2SettledD_log]
    exact hM m hMm hm h4

theorem p0A2_integerizer_bound_of_actual_prime_inputs
    (W : ℕ → ℕ → ℤ)
    (hfeature : ∀ m, 0 < m → 4 ∣ m → P0A2ActualTwoFeatureDivisibility m)
    (hodd : ∀ m, 0 < m → 4 ∣ m → P0A2ActualOddPrimeValuationBound m W)
    (hprimeSum : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      (∑ p ∈ Nat.primesLE (p0DenominatorU m),
        (p0A2SettledPrimeExponent m W p : ℝ) * Real.log p) / (m : ℝ) ^ 2 ≤
          p0TauSharp 2 + ε) :
    P0IntegerizerBound p0A2CanonicalFamily := by
  exact (p0IntegerizerBound_iff_at_tau p0A2CanonicalFamily).2
    (p0A2_integerizer_bound_at_of_actual_prime_inputs W (p0TauSharp 2)
      hfeature hodd hprimeSum)

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.rationalPrimeProduct_padicVal
#print axioms Li2Lean.P0.Integerization.rat_is_int_of_prime_padic_nonneg
#print axioms Li2Lean.P0.Integerization.p0A2SettledD_padicVal
#print axioms Li2Lean.P0.Integerization.p0A2_baseline_coeff_valuation_lower
#print axioms Li2Lean.P0.Integerization.p0A2ActualTwoFeatureDivisibility_of_real_witness
#print axioms Li2Lean.P0.Integerization.p0A2_two_feature_coeff_valuation_lower
#print axioms Li2Lean.P0.Integerization.p0A2_settled_integerizer
#print axioms Li2Lean.P0.Integerization.p0A2_integerizer_bound_of_actual_prime_inputs
