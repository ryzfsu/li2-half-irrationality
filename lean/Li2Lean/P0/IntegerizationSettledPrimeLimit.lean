/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationPaidPrimeLimit
import Li2Lean.P0.IntegerizationActualOddPrimeRate
import Li2Lean.P0.IntegerizationSmallPrimeTail

/-! The literal settled integerizer: exact feature-credit identity and rate
from a finite, unnormalized prime-sum majorant. All asymptotic inputs here
are proved. The actual finite valuation/profile majorant and actual two-adic
coefficient divisibility remain visible producer obligations. -/
namespace Li2Lean.P0.Integerization
noncomputable section
open Filter Topology

/-- The odd-prime sum uses the actual minimum defining the settled scalar. -/
def p0A2SettledOddLogSum (m : ℕ) (W : ℕ → ℕ → ℤ) : ℝ :=
  ∑ p ∈ (Nat.primesLE (p0DenominatorU m)).erase 2,
    ((min (W m p) ((3*m*Nat.log p (p0DenominatorU m) : ℕ) : ℤ) : ℤ) : ℝ) *
      Real.log p

/-- The positive two-adic baseline cost is retained before subtracting the
feature factor. It will be covered by the square-root-prime budget. -/
def p0A2SettledUncreditedPrimeCost (m : ℕ) (W : ℕ → ℕ → ℤ) : ℝ :=
  p0A2SettledOddLogSum m W +
    ((3*m*Nat.log 2 (p0DenominatorU m) : ℕ) : ℝ) * Real.log 2

theorem p0A2SettledD_log_split (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (W : ℕ → ℕ → ℤ) :
    Real.log (p0A2SettledD m W : ℝ) =
      p0A2SettledUncreditedPrimeCost m W -
        (p0A2FeatureExponent m : ℝ) * Real.log 2 := by
  have hm4 : 4 ≤ m := Nat.le_of_dvd hm h4
  have h2 : 2 ∈ Nat.primesLE (p0DenominatorU m) := by
    rw [Nat.mem_primesLE]
    exact ⟨by unfold p0DenominatorU; omega, by decide⟩
  rw [p0A2SettledD_log, ← Finset.sum_erase_add _ _ h2]
  have hs : (∑ p ∈ (Nat.primesLE (p0DenominatorU m)).erase 2,
      (p0A2SettledPrimeExponent m W p : ℝ) * Real.log p) =
      p0A2SettledOddLogSum m W := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [p0A2SettledPrimeExponent, if_neg (Finset.mem_erase.mp hp).1]
  rw [hs]
  norm_num [p0A2SettledUncreditedPrimeCost, p0A2SettledPrimeExponent]
  ring

theorem p0A2FeatureExponent_cast (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    (p0A2FeatureExponent m : ℝ) = (13 / 16 : ℝ) * (m : ℝ)^2 - m := by
  obtain ⟨h, rfl⟩ := h4
  have hh : 0 < h := by omega
  have hn : 4*h ≤ 13*h^2 := by nlinarith [Nat.le_mul_self h]
  simp only [p0A2FeatureExponent, Nat.mul_div_cancel_left _ (by decide : 0 < 4)]
  rw [Nat.cast_sub hn]
  push_cast
  ring

theorem p0A2SettledD_logRate_split (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (W : ℕ → ℕ → ℤ) :
    Real.log (p0A2SettledD m W : ℝ) / (m : ℝ)^2 =
      p0A2SettledUncreditedPrimeCost m W / (m : ℝ)^2 -
        ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2 := by
  rw [p0A2SettledD_log_split m hm h4 W, p0A2FeatureExponent_cast m hm h4]
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  field_simp

/-- The remaining source obligation is a finite sum bound for the literal
settled exponents. It includes every positive cost, including the prime 2,
and has no asymptotic or integerizer-rate conclusion as a field. -/
def P0A2FiniteProfilePrimeBound (W : ℕ → ℕ → ℤ) (wallCount : ℕ) : Prop :=
  ∀ m : ℕ, 0 < m → 4 ∣ m →
    p0A2SettledUncreditedPrimeCost m W ≤
      p0SquarefullPrimeLayerCost m +
      ((3*wallCount*m : ℕ) : ℝ) * Real.log (3*(m : ℝ)) +
      (m : ℝ) * (weightedPrimeSum p0A2LowProfile m +
        weightedPrimeSum p0A2HighProfile m +
        weightedPrimeSum p0FiniteTailProfile m +
        3 * Chebyshev.theta ((1/256 : ℝ)*m))

theorem p0A2SettledD_le_paidBudget (W : ℕ → ℕ → ℤ) (wallCount : ℕ)
    (hfinite : P0A2FiniteProfilePrimeBound W wallCount)
    (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    Real.log (p0A2SettledD m W : ℝ) / (m : ℝ)^2 ≤
      p0FinitePaidProfileBudget m + p0SquarefullPrimeLayerCost m / (m : ℝ)^2 +
        p0FiniteWallBudget wallCount m := by
  rw [p0A2SettledD_logRate_split m hm h4 W]
  have h := div_le_div_of_nonneg_right (hfinite m hm h4) (sq_nonneg (m : ℝ))
  have hn : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  have he : (p0SquarefullPrimeLayerCost m +
      ((3*wallCount*m : ℕ) : ℝ) * Real.log (3*(m : ℝ)) +
      (m : ℝ) * (weightedPrimeSum p0A2LowProfile m +
        weightedPrimeSum p0A2HighProfile m +
        weightedPrimeSum p0FiniteTailProfile m +
        3 * Chebyshev.theta ((1/256 : ℝ)*m))) / (m : ℝ)^2 -
        ((13 / 16 : ℝ) - 1 / (m : ℝ)) * Real.log 2 =
      p0FinitePaidProfileBudget m + p0SquarefullPrimeLayerCost m / (m : ℝ)^2 +
        p0FiniteWallBudget wallCount m := by
    unfold p0FinitePaidProfileBudget p0FiniteTailBudget p0FiniteWallBudget
    push_cast
    field_simp
    <;> ring
  rw [← he]
  linarith

theorem p0A2SettledD_rate_of_finite_profile (W : ℕ → ℕ → ℤ) (wallCount : ℕ)
    (hfinite : P0A2FiniteProfilePrimeBound W wallCount) :
    ∃ M : ℕ, ∀ m : ℕ, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (p0A2SettledD m W : ℝ) / (m : ℝ)^2 ≤ (248 / 125 : ℝ) := by
  exact p0Scalar_rate_of_finitePaidBudget (fun m => p0A2SettledD m W)
    p0SquarefullPrimeLayerCost wallCount p0SquarefullPrimeLayerCost_div_sq_tendsto_zero
    (p0A2SettledD_le_paidBudget W wallCount hfinite)

/-- Actual scalar assembly at the relaxed rate 1.984. This keeps both the
actual coefficient feature divisor and actual finite profile domination
explicit; neither is supplied by a formal or table-only surrogate. -/
theorem p0A2_integerizer_bound_at_of_finite_profile
    (W : ℕ → ℕ → ℤ) (wallCount : ℕ)
    (hfeature : ∀ m, 0 < m → 4 ∣ m → P0A2ActualTwoFeatureDivisibility m)
    (hodd : ∀ m, 0 < m → 4 ∣ m → P0A2ActualOddPrimeValuationBound m W)
    (hfinite : P0A2FiniteProfilePrimeBound W wallCount) :
    P0IntegerizerBoundAt p0A2CanonicalFamily (248 / 125 : ℝ) := by
  apply p0A2_integerizer_bound_at_of_actual_prime_inputs W (248 / 125) hfeature hodd
  intro ε hε
  obtain ⟨M, hM⟩ := p0A2SettledD_rate_of_finite_profile W wallCount hfinite
  refine ⟨M, ?_⟩
  intro m hm hp h4
  have h := hM m hm hp h4
  rw [p0A2SettledD_log] at h
  linarith

end
end Li2Lean.P0.Integerization
#print axioms Li2Lean.P0.Integerization.p0A2SettledD_logRate_split
#print axioms Li2Lean.P0.Integerization.p0A2SettledD_rate_of_finite_profile
#print axioms Li2Lean.P0.Integerization.p0A2_integerizer_bound_at_of_finite_profile
