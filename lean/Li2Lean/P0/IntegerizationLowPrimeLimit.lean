/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.PNTAdapter
import Li2Lean.IntegerizationTables.Certificates

/-! The checked low table is realized as the literal finite affine profile
used by weightedPrimeSum. These theorems prove its analytic prime-sum limit;
the identification with actual determinant valuations remains separate. -/
namespace Li2Lean.P0.Integerization
noncomputable section
open Filter Topology MeasureTheory
open IntegerizationTables

private theorem affineChain_positive {xs : List AffinePiece} {a b : ℚ}
    (ha : 0 < a) (hc : affineChain a b xs = true) :
    ∀ f ∈ xs, 0 < f.lo ∧ f.lo < f.hi := by
  induction xs generalizing a with
  | nil => simp
  | cons f fs ih =>
    simp only [affineChain, Bool.and_eq_true, decide_eq_true_eq] at hc
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ⟨by simpa only [hc.1.1] using ha, hc.1.2⟩
    · exact ih (lt_trans (by simpa only [hc.1.1] using ha) hc.1.2) hc.2 x hx

/-- Total conversion; the harmless fallback is never used on the checked
low table, as proved by `p0LowPieces_positive`. -/
def arithmeticPrimePiece (f : AffinePiece) : PrimeAffinePiece :=
  if h : 0 < f.lo ∧ f.lo < f.hi then
    { lo := f.lo, hi := f.hi, intercept := f.intercept, slope := f.slope,
      lo_pos := h.1, lo_lt_hi := h.2 }
  else
    { lo := 1, hi := 2, intercept := 0, slope := 0,
      lo_pos := by norm_num, lo_lt_hi := by norm_num }

theorem p0LowPieces_positive :
    ∀ f ∈ lowPieces, 0 < f.lo ∧ f.lo < f.hi :=
  affineChain_positive (by norm_num) p0LowFiniteProfile_checked.2.1

def p0A2LowProfile : PrimeAffineProfile :=
  ⟨lowPieces.map arithmeticPrimePiece⟩

private theorem arithmeticPrimePiece_integral (f : AffinePiece)
    (hf : 0 < f.lo ∧ f.lo < f.hi) :
    (∫ t : ℝ, (singletonPrimeAffineProfile (arithmeticPrimePiece f)).eval t) =
      (f.integral : ℝ) := by
  rw [singletonPrimeAffineProfile_integral]
  simp only [arithmeticPrimePiece, dif_pos hf, AffinePiece.integral]
  push_cast
  ring

private theorem affine_foldl_eq (fs : List AffinePiece) (z : ℚ) :
    fs.foldl (fun acc f => acc + f.integral) z = z + (fs.map AffinePiece.integral).sum := by
  induction fs generalizing z with
  | nil => simp
  | cons f fs ih => simp [List.foldl, ih, add_assoc]

private theorem arithmeticProfile_integral (fs : List AffinePiece)
    (hf : ∀ f ∈ fs, 0 < f.lo ∧ f.lo < f.hi) :
    (∫ t : ℝ, (PrimeAffineProfile.mk (fs.map arithmeticPrimePiece)).eval t) =
      ((fs.map AffinePiece.integral).sum : ℚ) := by
  rw [primeAffineProfile_integral_eq_sum_singletons]
  induction fs with
  | nil => simp
  | cons f fs ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    rw [arithmeticPrimePiece_integral f (hf f (by simp))]
    rw [ih (fun x hx => hf x (List.mem_cons_of_mem f hx))]

theorem p0A2LowProfile_integral :
    (∫ t : ℝ, p0A2LowProfile.eval t) = (p0LowIntegralClaim : ℝ) := by
  rw [p0A2LowProfile, arithmeticProfile_integral lowPieces p0LowPieces_positive]
  have he := p0LowFiniteProfile_checked.2.2
  rw [affine_foldl_eq, zero_add] at he
  exact_mod_cast he

theorem p0A2LowProfile_weightedPrime_limit :
    Tendsto (fun x : ℝ => weightedPrimeSum p0A2LowProfile x / x)
      atTop (𝓝 (p0LowIntegralClaim : ℝ)) := by
  simpa only [p0A2LowProfile_integral] using
    l3WeightedPrimeLimit_unconditional p0A2LowProfile

theorem p0A2LowProfile_weightedPrime_nat_limit :
    Tendsto (fun m : ℕ => weightedPrimeSum p0A2LowProfile m / (m : ℝ))
      atTop (𝓝 (p0LowIntegralClaim : ℝ)) :=
  p0A2LowProfile_weightedPrime_limit.comp tendsto_natCast_atTop_atTop

end
end Li2Lean.P0.Integerization
#print axioms Li2Lean.P0.Integerization.p0A2LowProfile_integral
#print axioms Li2Lean.P0.Integerization.p0A2LowProfile_weightedPrime_nat_limit
