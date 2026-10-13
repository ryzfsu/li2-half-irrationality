/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.IntegerizationChain

namespace Li2Lean

noncomputable section

/-! A parameterized form of the L2 integerizer contract.  The endpoint
argument only needs some rate strictly below its analytic decay; tying the
rate to `p0TauSharp` is stronger than that downstream use. -/
def P0IntegerizerBoundAt (F : P0Family) (rate : ℝ) : Prop :=
  ∃ D : ℕ → ℚ,
    (∀ m, 0 < m → 4 ∣ m → 0 < D m) ∧
    (∀ m, 0 < m → 4 ∣ m → (F.G m).natDegree ≤ m) ∧
    (∀ m, 0 < m → 4 ∣ m → ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℝ) = Polynomial.C (D m : ℝ) * F.G m) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε)

theorem p0IntegerizerBound_iff_at_tau (F : P0Family) :
    P0IntegerizerBound F ↔ P0IntegerizerBoundAt F (p0TauSharp F.a) := by
  rfl

end

namespace P0.Integerization

noncomputable section

/-! This certificate separates the finite coefficient/feature bridge from the
rate arithmetic.  In particular, `oddPrimeValuationRate` is an explicit
remaining source obligation, not an axiom hidden inside the target bound. -/
structure P0IntegerizerFeatureRateCertificate
    (F : P0Family) (rate : ℝ) where
  D : ℕ → ℚ
  featureFactor : ℕ → ℕ
  featureFactor_pos : ∀ m, 0 < m → 4 ∣ m → 0 < featureFactor m
  baseline_factorization : ∀ m, 0 < m → 4 ∣ m →
    p0A2BaselineD m = D m * featureFactor m
  featureDivisibility : ∀ m, 0 < m → 4 ∣ m →
    ∃ P : Polynomial ℤ,
      Polynomial.C (featureFactor m : ℤ) ∣ P ∧
        Polynomial.map (Int.castRingHom ℝ) P =
          Polynomial.C (p0A2BaselineD m : ℝ) * F.G m
  oddPrimeValuationRate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m →
    0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε

theorem p0IntegerizerBoundAt_of_feature_rate_certificate
    {rate : ℝ}
    (F : P0Family) (_hbase : F.a = 2)
    (hdegree : ∀ m, 0 < m → 4 ∣ m → (F.G m).natDegree ≤ m)
    (certificate : P0IntegerizerFeatureRateCertificate F rate) :
    P0IntegerizerBoundAt F rate := by
  refine ⟨certificate.D, ?_, hdegree, ?_, certificate.oddPrimeValuationRate⟩
  · intro m hm h4
    have hfactor := certificate.featureFactor_pos m hm h4
    have hscale := certificate.baseline_factorization m hm h4
    have hbaseline : 0 < p0A2BaselineD m := p0A2BaselineD_pos hm
    have hfactorQ : 0 < (certificate.featureFactor m : ℚ) := by
      exact_mod_cast hfactor
    have hD : certificate.D m = p0A2BaselineD m /
        (certificate.featureFactor m : ℚ) := by
      rw [hscale]
      field_simp
    rw [hD]
    exact div_pos hbaseline hfactorQ
  · intro m hm h4
    obtain ⟨P, hdiv, hP⟩ := certificate.featureDivisibility m hm h4
    obtain ⟨Q, hPQ⟩ := hdiv
    refine ⟨Q, ?_⟩
    have hmap : Polynomial.map (Int.castRingHom ℝ) P =
        Polynomial.C (certificate.featureFactor m : ℝ) *
          Polynomial.map (Int.castRingHom ℝ) Q := by
      rw [hPQ, Polynomial.map_mul, Polynomial.map_C]
      norm_num
    have hscale : (certificate.featureFactor m : ℝ) *
        (certificate.D m : ℝ) = (p0A2BaselineD m : ℝ) := by
      exact_mod_cast (by
        rw [mul_comm]
        exact (certificate.baseline_factorization m hm h4).symm)
    have hscalePoly : Polynomial.C (certificate.featureFactor m : ℝ) *
        Polynomial.C (certificate.D m : ℝ) =
        Polynomial.C (p0A2BaselineD m : ℝ) := by
      calc
        _ = Polynomial.C ((certificate.featureFactor m : ℝ) *
            (certificate.D m : ℝ)) := by simp [Polynomial.C_mul]
        _ = _ := congrArg Polynomial.C hscale
    have htarget : Polynomial.C (certificate.featureFactor m : ℝ) *
        Polynomial.map (Int.castRingHom ℝ) Q =
        Polynomial.C (certificate.featureFactor m : ℝ) *
          (Polynomial.C (certificate.D m : ℝ) * F.G m) := by
      calc
        _ = Polynomial.map (Int.castRingHom ℝ) P := hmap.symm
        _ = Polynomial.C (p0A2BaselineD m : ℝ) * F.G m := hP
        _ = Polynomial.C (certificate.featureFactor m : ℝ) *
              (Polynomial.C (certificate.D m : ℝ) * F.G m) := by
                rw [← hscalePoly]
                ring
    have hfactorR : 0 < (certificate.featureFactor m : ℝ) := by
      exact_mod_cast certificate.featureFactor_pos m hm h4
    have hC : Polynomial.C (certificate.featureFactor m : ℝ) ≠ 0 :=
      Polynomial.C_ne_zero.mpr (ne_of_gt hfactorR)
    exact mul_left_cancel₀ hC htarget

/-! The numerical table target leaves a positive margin below the C-A slack
rate.  This is arithmetic only; it does not discharge the feature/valuation
certificate above. -/
theorem p0_table_rate_lt_ca_slack :
    ((1979 / 1000 : ℚ) : ℝ) < ((397 / 200 : ℚ) : ℝ) := by
  norm_num

end

end P0.Integerization

end Li2Lean
