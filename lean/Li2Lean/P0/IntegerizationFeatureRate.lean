/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationFeatureBridge

namespace Li2Lean.P0.Integerization

noncomputable section

/-- The logarithmic size of the paper's explicit two-adic feature factor.

This is one actual rate contribution, not a bound for the full integerizer:
the odd-prime valuation profile and coefficientwise feature divisibility are
still separate obligations. -/
theorem p0A2TwoFeatureFactor_log_eq {m h : ℕ} (hm : m = 4 * h)
    (hmpos : 0 < m) :
    Real.log (p0A2TwoFeatureFactor m : ℝ) =
      ((13 / 16 : ℝ) * (m : ℝ) ^ 2 - m) * Real.log 2 := by
  rw [p0A2TwoFeatureFactor_eq_explicit hm]
  have hexp :
      ((13 * h ^ 2 - 4 * h : ℕ) : ℝ) =
        (13 / 16 : ℝ) * (m : ℝ) ^ 2 - m := by
    subst m
    have hhpos : 0 < h := by omega
    have hsub : 4 * h ≤ 13 * h ^ 2 := by
      nlinarith [Nat.le_mul_self h]
    rw [Nat.cast_sub hsub]
    push_cast
    ring
  have hcast :
      ((2 ^ (13 * h ^ 2 - 4 * h) : ℕ) : ℝ) =
        (2 : ℝ) ^ (13 * h ^ 2 - 4 * h) := by
    norm_cast
  rw [hcast, Real.log_pow, hexp]

/-- Exact 2-adic valuation of the feature factor from the paper's rank-one
feature count. This is the valuation input before coefficientwise divisibility
is descended to the specialized determinant. -/
theorem p0A2TwoFeatureFactor_padicVal_two {m h : ℕ}
    (hm : m = 4 * h) :
    padicValNat 2 (p0A2TwoFeatureFactor m) = 13 * h ^ 2 - 4 * h := by
  rw [p0A2TwoFeatureFactor_eq_explicit hm]
  exact padicValNat_base_pow (by norm_num : 1 < (2 : ℕ)) _

/-- Exact normalized asymptotic of the gain from the rank-one feature factor.
The error is precisely `log 2 / m`, so this contributes `13/16 log 2` to
the exponent rate once the coefficientwise divisibility is established. -/
theorem p0A2TwoFeatureFactor_logRate_identity {m h : ℕ}
    (hm : m = 4 * h) (hmpos : 0 < m) :
    Real.log (p0A2TwoFeatureFactor m : ℝ) / (m : ℝ) ^ 2 =
      ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2 := by
  rw [p0A2TwoFeatureFactor_log_eq hm hmpos]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  field_simp

/-- The remaining denominator log is the baseline log minus the explicit
feature log. This is the exact arithmetic interface used by the eventual
coefficientwise valuation producer. -/
theorem p0A2TwoFeatureD_logRate_identity {m h : ℕ}
    (hm : m = 4 * h) (hmpos : 0 < m) :
    Real.log (p0A2TwoFeatureD m : ℝ) / (m : ℝ) ^ 2 =
      Real.log (p0A2BaselineD m : ℝ) / (m : ℝ) ^ 2 -
        ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2 := by
  have hbase : 0 < p0A2BaselineD m := p0A2BaselineD_pos hmpos
  have hfeat : 0 < p0A2TwoFeatureFactor m :=
    p0A2TwoFeatureFactor_pos (by
      subst m
      simpa using (show 4 ∣ 4 * h by exact dvd_mul_right 4 h))
  have hbaseR : 0 < (p0A2BaselineD m : ℝ) := by exact_mod_cast hbase
  have hfeatR : 0 < (p0A2TwoFeatureFactor m : ℝ) := by exact_mod_cast hfeat
  have hdiv :
      (p0A2TwoFeatureD m : ℝ) =
        (p0A2BaselineD m : ℝ) / (p0A2TwoFeatureFactor m : ℝ) := by
    simp only [p0A2TwoFeatureD]
    norm_cast
  rw [hdiv, Real.log_div (ne_of_gt hbaseR) (ne_of_gt hfeatR),
    p0A2TwoFeatureFactor_log_eq hm hmpos]
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hmpos)
  field_simp [hmR]

/-- Conditional rate transfer for the actual remaining denominator.

If the baseline row-scale product has the paper's `13/16 * log 2` feature
credit (with the finite lower table `p0LogTwoLower`), this theorem removes the
explicit feature factor and gives the desired eventual rate. The premise is
the still-open coefficientwise valuation/table producer; it is intentionally
visible here rather than hidden in `P0IntegerizerBound`. -/
theorem p0A2TwoFeatureD_rate_of_baseline_rate (rate : ℝ)
    (hloglower :
      ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) ≤ Real.log 2)
    (hbase : ∀ η : ℝ, 0 < η → ∃ M : ℕ, ∀ m : ℕ,
      M ≤ m → 0 < m → 4 ∣ m →
        Real.log (p0A2BaselineD m : ℝ) / (m : ℝ) ^ 2 ≤
          rate + (13 / 16 : ℝ) *
            (IntegerizationTables.p0LogTwoLower : ℝ) + η) :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m h : ℕ,
      M ≤ m → 0 < m → m = 4 * h →
        Real.log (p0A2TwoFeatureD m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε := by
  intro ε hε
  have hε2 : 0 < ε / 2 := by linarith
  obtain ⟨M₀, hM₀⟩ := hbase (ε / 2) hε2
  obtain ⟨M₁, hM₁⟩ := exists_nat_gt (2 / ε)
  let M : ℕ := max M₀ M₁
  refine ⟨M, ?_⟩
  intro m h Mle hmpos hmEq
  have hM₀le : M₀ ≤ m := le_trans (Nat.le_max_left _ _) Mle
  have hM₁le : M₁ ≤ m := le_trans (Nat.le_max_right _ _) Mle
  have h4 : 4 ∣ m := by
    subst m
    simp
  have hbase_m := hM₀ m hM₀le hmpos h4
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmRlarge : (2 / ε) < (m : ℝ) := by
    have hM₁R : (2 / ε) < (M₁ : ℝ) := by exact_mod_cast hM₁
    have hM₁mR : (M₁ : ℝ) ≤ (m : ℝ) := by exact_mod_cast hM₁le
    exact lt_of_lt_of_le hM₁R hM₁mR
  have hinv : (1 : ℝ) / (m : ℝ) < ε / 2 := by
    rw [div_lt_iff₀ hmRpos]
    have hprod : (2 : ℝ) < ε * (m : ℝ) := by
      simpa [mul_comm] using (div_lt_iff₀ hε).mp hmRlarge
    nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  have hLle :
      ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) ≤ 1 :=
    hloglower.trans hlog2le
  have hfeature_lower :
      (13 / 16 : ℝ) * Real.log 2 -
          (1 / (m : ℝ)) * Real.log 2 ≥
        (13 / 16 : ℝ) *
            ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) -
          1 / (m : ℝ) := by
    have hmul₁ :
        (13 / 16 : ℝ) *
            ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) ≤
          (13 / 16 : ℝ) * Real.log 2 := by
      gcongr
    have hmul₂ :
        (1 / (m : ℝ)) * Real.log 2 ≤ 1 / (m : ℝ) := by
      have := mul_le_mul_of_nonneg_left hlog2le (by positivity :
        0 ≤ (1 / (m : ℝ)))
      simpa [mul_comm] using this
    linarith
  have hD := p0A2TwoFeatureD_logRate_identity hmEq hmpos
  rw [hD]
  have hfeature_rw :
      ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2 =
        (13 / 16 : ℝ) * Real.log 2 -
          (1 / (m : ℝ)) * Real.log 2 := by ring
  rw [hfeature_rw]
  have hLm :
      (1 / (m : ℝ)) *
          ((IntegerizationTables.p0LogTwoLower : ℚ) : ℝ) ≤
        1 / (m : ℝ) := by
    have := mul_le_mul_of_nonneg_left hLle (by positivity :
      0 ≤ (1 / (m : ℝ)))
    simpa [mul_comm] using this
  linarith

/-- The feature contribution converges to the exact quadratic rate along the
paper's indices `4 ∣ m`. This does not establish a rate for `D_m`. -/
theorem p0A2TwoFeatureFactor_logRate_tendsto :
    ∀ ε : ℝ, 0 < ε → ∃ M : ℕ, ∀ m h : ℕ, M ≤ m → 0 < m →
      m = 4 * h →
      |Real.log (p0A2TwoFeatureFactor m : ℝ) / (m : ℝ) ^ 2 -
          (13 / 16 : ℝ) * Real.log 2| < ε := by
  intro ε hε
  obtain ⟨M, hM⟩ := exists_nat_gt (1 / ε)
  refine ⟨M, ?_⟩
  intro m h Mle hmpos hm
  have hmRpos : 0 < (m : ℝ) := by exact_mod_cast hmpos
  have hmRlarge : (1 / ε) < (m : ℝ) := by
    have hMR : (1 / ε) < (M : ℝ) := by exact_mod_cast hM
    have hMleR : (M : ℝ) ≤ (m : ℝ) := by exact_mod_cast Mle
    exact lt_of_lt_of_le hMR hMleR
  have hεm : 1 < ε * (m : ℝ) := by
    have := (div_lt_iff₀ hε).mp hmRlarge
    nlinarith
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hlog2le : Real.log 2 ≤ 1 := by
    have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    exact h
  rw [p0A2TwoFeatureFactor_logRate_identity hm hmpos]
  have hsmall : (1 : ℝ) / (m : ℝ) < ε := by
    rw [div_lt_iff₀ hmRpos]
    nlinarith
  have heq :
      ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2 -
          (13 / 16 : ℝ) * Real.log 2 =
        -(1 / (m : ℝ)) * Real.log 2 := by ring
  rw [heq]
  have hnonneg : 0 ≤ (1 / (m : ℝ)) * Real.log 2 :=
    mul_nonneg (by positivity) hlog2pos.le
  have hterm : |-(1 / (m : ℝ)) * Real.log 2| =
      (1 / (m : ℝ)) * Real.log 2 := by
    rw [neg_mul, abs_neg, abs_mul, abs_of_pos (by positivity), abs_of_pos hlog2pos]
  rw [hterm]
  have hmul : (1 / (m : ℝ)) * Real.log 2 < ε := by
    calc
      (1 / (m : ℝ)) * Real.log 2 ≤ (1 / (m : ℝ)) * 1 :=
        mul_le_mul_of_nonneg_left hlog2le (by positivity)
      _ = 1 / (m : ℝ) := by ring
      _ < ε := hsmall
  exact hmul

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureFactor_log_eq
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureFactor_padicVal_two
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureFactor_logRate_identity
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureD_logRate_identity
#print axioms Li2Lean.P0.Integerization.p0A2TwoFeatureFactor_logRate_tendsto
