/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationDeterminant
import Li2Lean.P0.IntegerizationTables
import Li2Lean.Kit.PNTAdapter

namespace Li2Lean.P0.Integerization

noncomputable section

open Filter Topology

/-- The baseline denominator product for the literal `a = 2` P0 determinant.

The source-level row proof uses `d_U` on the top block and `d_U^2` on the
bottom block, so the determinant multiplier is `d_U^(3m)`.  This is the
fully instantiated specialization of `p0RowScale`, rather than a formal
coefficientwise statement in the base parameter `a`.
-/
def p0A2BaselineD (m : ℕ) : ℚ :=
  (p0DenominatorLcm m : ℚ) ^ (3 * m)

theorem p0DenominatorLcm_pos {m : ℕ} (hm : 0 < m) :
    0 < p0DenominatorLcm m := by
  unfold p0DenominatorLcm denominatorLcm p0DenominatorU
  apply Nat.pos_of_ne_zero
  rw [Finset.lcm_ne_zero_iff]
  intro s hs
  have hspos : 0 < s := by
    exact (Finset.mem_Icc.mp hs).1
  exact Nat.ne_of_gt hspos

theorem p0A2BaselineD_pos {m : ℕ} (hm : 0 < m) :
    0 < p0A2BaselineD m := by
  unfold p0A2BaselineD
  have hd : 0 < p0DenominatorLcm m := p0DenominatorLcm_pos hm
  exact pow_pos (by exact_mod_cast hd) _

/-- Actual `a = 2` determinant integerization with its exact row-scale product. -/
theorem p0A2_baseline_integerizer (m : ℕ) (hm : 4 ∣ m) :
    ∃ P : Polynomial ℤ,
      Polynomial.map (Int.castRingHom ℚ) P =
        Polynomial.C (p0A2BaselineD m) *
          p0CanonicalPolynomial 2 m := by
  simpa [p0A2BaselineD] using p0_canonical_integerized_two m hm

/-- Coefficientwise form of the actual baseline denominator statement. -/
theorem p0A2_baseline_coeff_is_int (m : ℕ) (hm : 4 ∣ m) (n : ℕ) :
    ∃ z : ℤ,
      p0A2BaselineD m * (p0CanonicalPolynomial 2 m).coeff n = z := by
  rcases p0A2_baseline_integerizer m hm with ⟨P, hP⟩
  have hc := congrArg (fun Q : Polynomial ℚ => Q.coeff n) hP
  refine ⟨P.coeff n, ?_⟩
  rw [Polynomial.coeff_C_mul] at hc
  simpa [p0A2BaselineD] using hc.symm

/-- The exponent used by the formal feature divisibility bookkeeping at `a=2`.

This is the exact `13h^2-4h` count from the v10 construction; it is kept
separate from the baseline row-scale integerizer above.
-/
theorem p0A2_feature_exponent (h : ℕ) :
    2 * (∑ k ∈ Finset.range h, k) +
        3 * (∑ k ∈ Finset.Ico h (3 * h), k) =
      13 * h ^ 2 - 4 * h :=
  p0_feature_exponent h

theorem p0A2_feature_exponent_m (m h : ℕ) (hm : m = 4 * h) :
    2 * (∑ k ∈ Finset.range h, k) +
        3 * (∑ k ∈ Finset.Ico h (3 * h), k) =
      13 * h ^ 2 - 4 * h ∧ 13 * h ^ 2 - 4 * h = 13 * m ^ 2 / 16 - m :=
  p0_feature_exponent_m m h hm

/-! ### The concrete positive-strip profile used by the C-D table

The integer-potential certificate stores the nine displayed affine pieces as
eleven copy-geometry cells.  The aggregate upper profile is the following
nine-piece rational profile.  Its integral is checked in Lean and is exactly
the stored `p0HighIntegralClaim = 287/192`.
-/

def p0A2HighProfile : PrimeAffineProfile where
  pieces :=
    [ { lo := (1 : ℚ) / 2, hi := (7 : ℚ) / 12,
        slope := 0, intercept := 1,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := (7 : ℚ) / 12, hi := (5 : ℚ) / 8,
        slope := 3, intercept := -(3 : ℚ) / 4,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := (5 : ℚ) / 8, hi := (2 : ℚ) / 3,
        slope := 1, intercept := 1 / 2,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := (2 : ℚ) / 3, hi := (3 : ℚ) / 4,
        slope := 4, intercept := -(3 : ℚ) / 2,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := (3 : ℚ) / 4, hi := (5 : ℚ) / 6,
        slope := 3, intercept := -(3 : ℚ) / 4,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := (5 : ℚ) / 6, hi := 1,
        slope := 0, intercept := 7 / 4,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := 1, hi := 7 / 4,
        slope := -2, intercept := 15 / 4,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := 7 / 4, hi := 2,
        slope := -1, intercept := 2,
        lo_pos := by norm_num, lo_lt_hi := by norm_num },
      { lo := 2, hi := 5 / 2,
        slope := 0, intercept := 0,
        lo_pos := by norm_num, lo_lt_hi := by norm_num } ]

theorem p0A2HighProfile_integral :
    (∫ t : ℝ, p0A2HighProfile.eval t) =
      (IntegerizationTables.p0HighIntegralClaim : ℝ) := by
  rw [primeAffineProfile_integral_eq_sum_singletons]
  norm_num [p0A2HighProfile, singletonPrimeAffineProfile_integral,
    IntegerizationTables.p0HighIntegralClaim]

theorem p0A2HighProfile_integral_value :
    (∫ t : ℝ, p0A2HighProfile.eval t) = (287 / 192 : ℝ) := by
  calc
    (∫ t : ℝ, p0A2HighProfile.eval t) =
        (IntegerizationTables.p0HighIntegralClaim : ℝ) :=
      p0A2HighProfile_integral
    _ = (287 / 192 : ℝ) := by
      norm_num [IntegerizationTables.p0HighIntegralClaim]

/-- The merged L3 weighted-prime limit, instantiated at the actual C-D profile. -/
theorem p0A2HighProfile_weightedPrime_limit :
    Tendsto
      (fun x : ℝ => weightedPrimeSum p0A2HighProfile x / x)
      atTop (𝓝 (∫ t : ℝ, p0A2HighProfile.eval t)) := by
  exact l3WeightedPrimeLimit_unconditional p0A2HighProfile

theorem p0A2HighProfile_weightedPrime_limit_value :
    Tendsto
      (fun x : ℝ => weightedPrimeSum p0A2HighProfile x / x)
      atTop (𝓝 (287 / 192 : ℝ)) := by
  simpa only [p0A2HighProfile_integral_value] using
    p0A2HighProfile_weightedPrime_limit

/-- The finite table and logarithmic 2-adic comparison are unconditional. -/
theorem p0A2_finite_table_rate :
    (IntegerizationTables.lowPieces.length = 756 ∧
      IntegerizationTables.affineChain (1 / 128) (1 / 2)
        IntegerizationTables.lowPieces = true ∧
      IntegerizationTables.lowPieces.foldl
        (fun acc f => acc + f.integral) 0 =
        IntegerizationTables.p0LowIntegralClaim) ∧
    (IntegerizationTables.p0HighCertificates.length = 11 ∧
      IntegerizationTables.p0HighIntervalChain (1 / 2) (5 / 2)
        IntegerizationTables.p0HighCertificates = true ∧
      IntegerizationTables.p0HighIntegralFromData =
        IntegerizationTables.p0HighIntegralClaim) ∧
    (∀ C : IntegerizationTables.PotentialCertificate,
      C ∈ IntegerizationTables.p0HighCertificates → C.valid) ∧
    IntegerizationTables.p0HighConstraintCount = 1942 ∧
    IntegerizationTables.p0BasicIntegerizerRateClaim < 1979 / 1000 :=
  integerizationTableCertificateBundle

theorem p0A2_finite_table_rate_numeric :
    IntegerizationTables.p0BasicIntegerizerRateClaim < 1979 / 1000 := by
  exact IntegerizationTables.p0BasicIntegerizerRate_lt_1979_over_1000

/-!
The remaining D_m gap is deliberately recorded here rather than hidden in a
certificate hypothesis.  The proved ingredients above give the actual
`a=2` baseline multiplier `d_U^(3m)`, the exact feature count, the checked
finite potential tables, and the unconditional L3 limit.  What is still
needed for the sharp `tau_basic < 1.979` chain is a theorem connecting each
table entry to the actual odd-prime valuations of every coefficient of
`p0CanonicalPolynomial 2 m`, followed by the finite product assembly of the
resulting exponents.  No such coefficientwise valuation/potential bridge is
present in the canonical source, so this file does not claim the sharp D_m
rate or the formal `a`-parameter polynomial identity.
-/

end

end Li2Lean.P0.Integerization
