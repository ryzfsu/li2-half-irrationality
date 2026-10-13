/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateLowData
import Li2Lean.P0.RateHighData
import Li2Lean.P0.IntegerizationSettledPrimeLimit

/-!
# Profile facts used by the finite prime-sum majorant

Nonnegativity of the three affine profiles on their pieces, evaluation lower
bounds, finite support, partial sums against `weightedPrimeSum`, and chain
coverage of the low and high certificate intervals.
-/

namespace Li2Lean.P0.Integerization

open Finset IntegerizationTables

theorem p0Affine_nonneg_of_ends {lo hi a b y : ℝ} (h1 : 0 ≤ a * lo + b) (h2 : 0 ≤ a * hi + b)
    (hy1 : lo ≤ y) (hy2 : y ≤ hi) : 0 ≤ a * y + b := by
  rcases le_or_gt 0 a with ha | ha
  · nlinarith [mul_le_mul_of_nonneg_left hy1 ha]
  · nlinarith [mul_le_mul_of_nonpos_left hy2 ha.le]

/-- Every piece of a profile is nonnegative on its half-open domain. -/
def P0ProfileNonneg (P : PrimeAffineProfile) : Prop :=
  ∀ q ∈ P.pieces, ∀ y : ℝ, (q.lo : ℝ) ≤ y → y < q.hi → 0 ≤ (q.slope : ℝ) * y + q.intercept

theorem p0Profile_eval_nonneg {P : PrimeAffineProfile} (hnn : P0ProfileNonneg P) (x : ℝ) :
    0 ≤ P.eval x := by
  unfold PrimeAffineProfile.eval
  apply List.sum_nonneg
  intro z hz
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
  split
  · rename_i h
    exact hnn q hq x h.1 h.2
  · exact le_refl 0

theorem p0Profile_eval_ge {P : PrimeAffineProfile} (hnn : P0ProfileNonneg P)
    {q : PrimeAffinePiece} (hq : q ∈ P.pieces) {x : ℝ} (h1 : (q.lo : ℝ) ≤ x) (h2 : x < q.hi) :
    (q.slope : ℝ) * x + q.intercept ≤ P.eval x := by
  unfold PrimeAffineProfile.eval
  apply List.single_le_sum
  · intro z hz
    obtain ⟨q', hq', rfl⟩ := List.mem_map.mp hz
    split
    · rename_i h
      exact hnn q' hq' x h.1 h.2
    · exact le_refl 0
  · exact List.mem_map.mpr ⟨q, hq, by simp [h1, h2]⟩

theorem p0Profile_eval_zero {P : PrimeAffineProfile} (H : ℝ)
    (hH : ∀ q ∈ P.pieces, (q.hi : ℝ) ≤ H) {x : ℝ} (hx : H ≤ x) : P.eval x = 0 := by
  unfold PrimeAffineProfile.eval
  apply List.sum_eq_zero
  intro z hz
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hz
  have := hH q hq
  rw [if_neg (by intro h; linarith [h.2])]

/-- A finite partial weighted prime sum is at most the full weighted sum. -/
theorem p0_partial_le_weightedPrimeSum {P : PrimeAffineProfile} (hnn : P0ProfileNonneg P)
    (H : ℝ) (hH : ∀ q ∈ P.pieces, (q.hi : ℝ) ≤ H) {x : ℝ} (hx : 0 < x) (s : Finset ℕ)
    (hs : ∀ p ∈ s, p.Prime) :
    ∑ p ∈ s, P.eval ((p : ℝ) / x) * Real.log p ≤ weightedPrimeSum P x := by
  set f : ℕ → ℝ := fun p => if Nat.Prime p then P.eval ((p : ℝ) / x) * Real.log (p : ℝ) else 0
  have hf0 : ∀ p, 0 ≤ f p := by
    intro p
    simp only [f]
    split
    · rename_i hp
      exact mul_nonneg (p0Profile_eval_nonneg hnn _)
        (Real.log_nonneg (by exact_mod_cast hp.one_lt.le))
    · exact le_refl 0
  have hsum : Summable f := by
    apply summable_of_ne_finset_zero (s := range (⌈H * x⌉₊ + 1))
    intro p hp
    simp only [Finset.mem_range, not_lt] at hp
    simp only [f]
    split
    · have hge : H ≤ (p : ℝ) / x := by
        rw [le_div_iff₀ hx]
        have h1 : H * x ≤ (⌈H * x⌉₊ : ℝ) := Nat.le_ceil _
        have h2 : ((⌈H * x⌉₊ + 1 : ℕ) : ℝ) ≤ p := by exact_mod_cast hp
        push_cast at h2
        linarith
      rw [p0Profile_eval_zero H hH hge, zero_mul]
    · rfl
  have hle := hsum.sum_le_tsum s (fun p _ => hf0 p)
  have heq : ∑ p ∈ s, f p = ∑ p ∈ s, P.eval ((p : ℝ) / x) * Real.log p := by
    apply Finset.sum_congr rfl
    intro p hp
    simp [f, hs p hp]
  unfold weightedPrimeSum
  rw [← heq]
  exact hle

/-! ## Chain coverage -/

theorem p0_affineChain_cover :
    ∀ (fs : List AffinePiece) (lo hi x : ℚ), affineChain lo hi fs = true → lo ≤ x → x < hi →
      ∃ f ∈ fs, f.lo ≤ x ∧ x < f.hi := by
  intro fs
  induction fs with
  | nil =>
    intro lo hi x h h1 h2
    simp only [affineChain, decide_eq_true_eq] at h
    subst h
    exact absurd h2 (not_lt.mpr h1)
  | cons f rest ih =>
    intro lo hi x h h1 h2
    simp only [affineChain, Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hlo, _⟩, hrest⟩ := h
    by_cases hx : x < f.hi
    · exact ⟨f, by simp, hlo ▸ h1, hx⟩
    · obtain ⟨g, hg, hg1, hg2⟩ := ih f.hi hi x hrest (not_lt.mp hx) h2
      exact ⟨g, by simp [hg], hg1, hg2⟩

/-! ## The low profile -/

theorem p0LowPieces_ends_nonneg :
    lowPieces.all (fun f => decide (0 ≤ f.slope * f.lo + f.intercept) &&
      decide (0 ≤ f.slope * f.hi + f.intercept) && decide (f.hi ≤ 1 / 2)) = true := by
  decide +kernel

theorem p0ArithPiece_fields (f : AffinePiece) (hf : 0 < f.lo ∧ f.lo < f.hi) :
    (arithmeticPrimePiece f).lo = f.lo ∧ (arithmeticPrimePiece f).hi = f.hi ∧
      (arithmeticPrimePiece f).slope = f.slope ∧
      (arithmeticPrimePiece f).intercept = f.intercept := by
  simp [arithmeticPrimePiece, dif_pos hf]

theorem p0A2LowProfile_nonneg : P0ProfileNonneg p0A2LowProfile := by
  intro q hq y h1 h2
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
  have hpos := p0LowPieces_positive f hf
  obtain ⟨elo, ehi, esl, eic⟩ := p0ArithPiece_fields f hpos
  have hall := List.all_eq_true.mp p0LowPieces_ends_nonneg f hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨e1, e2⟩, _⟩ := hall
  rw [elo] at h1
  rw [ehi] at h2
  rw [esl, eic]
  have e1' : (0 : ℝ) ≤ (f.slope : ℝ) * f.lo + f.intercept := by exact_mod_cast e1
  have e2' : (0 : ℝ) ≤ (f.slope : ℝ) * f.hi + f.intercept := by exact_mod_cast e2
  exact p0Affine_nonneg_of_ends e1' e2' h1 h2.le

theorem p0A2LowProfile_hi_le : ∀ q ∈ p0A2LowProfile.pieces, (q.hi : ℝ) ≤ 1 / 2 := by
  intro q hq
  obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hq
  obtain ⟨_, ehi, _, _⟩ := p0ArithPiece_fields f (p0LowPieces_positive f hf)
  have hall := List.all_eq_true.mp p0LowPieces_ends_nonneg f hf
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  rw [ehi]
  have : (f.hi : ℝ) ≤ ((1 / 2 : ℚ) : ℝ) := by exact_mod_cast hall.2
  simpa using this

theorem p0A2LowProfile_eval_ge {f : AffinePiece} (hf : f ∈ lowPieces) {x : ℝ}
    (h1 : (f.lo : ℝ) ≤ x) (h2 : x < f.hi) :
    (f.slope : ℝ) * x + f.intercept ≤ p0A2LowProfile.eval x := by
  have hpos := p0LowPieces_positive f hf
  obtain ⟨elo, ehi, esl, eic⟩ := p0ArithPiece_fields f hpos
  have h := p0Profile_eval_ge p0A2LowProfile_nonneg
    (List.mem_map.mpr ⟨f, hf, rfl⟩ : arithmeticPrimePiece f ∈ p0A2LowProfile.pieces)
    (x := x) (by rw [elo]; exact h1) (by rw [ehi]; exact h2)
  rwa [esl, eic] at h

/-! ## The high profile -/

theorem p0A2HighProfile_ends :
    p0A2HighProfile.pieces.all (fun q => decide (0 ≤ q.slope * q.lo + q.intercept) &&
      decide (0 ≤ q.slope * q.hi + q.intercept) && decide (q.hi ≤ 5 / 2)) = true := by
  decide +kernel

theorem p0A2HighProfile_nonneg : P0ProfileNonneg p0A2HighProfile := by
  intro q hq y h1 h2
  have hall := List.all_eq_true.mp p0A2HighProfile_ends q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  obtain ⟨⟨e1, e2⟩, _⟩ := hall
  have e1' : (0 : ℝ) ≤ (q.slope : ℝ) * q.lo + q.intercept := by exact_mod_cast e1
  have e2' : (0 : ℝ) ≤ (q.slope : ℝ) * q.hi + q.intercept := by exact_mod_cast e2
  exact p0Affine_nonneg_of_ends e1' e2' h1 h2.le

theorem p0A2HighProfile_hi_le : ∀ q ∈ p0A2HighProfile.pieces, (q.hi : ℝ) ≤ 5 / 2 := by
  intro q hq
  have hall := List.all_eq_true.mp p0A2HighProfile_ends q hq
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hall
  have : (q.hi : ℝ) ≤ ((5 / 2 : ℚ) : ℝ) := by exact_mod_cast hall.2
  simpa using this

/-- Each certified high cell lies inside one profile piece with the same line. -/
theorem p0HighCells_in_profile :
    p0HighCellData.all (fun h => p0A2HighProfile.pieces.any (fun q =>
      decide (q.lo ≤ h.cell.lo ∧ h.cell.hi ≤ q.hi ∧ q.slope = h.slope ∧
        q.intercept = h.icpt))) = true := by
  decide +kernel

theorem p0HighCell_eval_ge {h : HCell} (hh : h ∈ p0HighCellData) {x : ℝ}
    (h1 : (h.cell.lo : ℝ) ≤ x) (h2 : x < h.cell.hi) :
    (h.slope : ℝ) * x + h.icpt ≤ p0A2HighProfile.eval x := by
  have hall := List.all_eq_true.mp p0HighCells_in_profile h hh
  obtain ⟨q, hq, hc⟩ := List.any_eq_true.mp hall
  simp only [decide_eq_true_eq] at hc
  obtain ⟨hlo, hhi, hs, hi⟩ := hc
  have hlo' : (q.lo : ℝ) ≤ h.cell.lo := by exact_mod_cast hlo
  have hhi' : (h.cell.hi : ℝ) ≤ q.hi := by exact_mod_cast hhi
  have := p0Profile_eval_ge p0A2HighProfile_nonneg hq (x := x) (by linarith) (by linarith)
  rwa [hs, hi] at this

theorem p0HighCells_chain :
    affineChain (1 / 2) (5 / 2)
      (p0HighCellData.map (fun h => (⟨h.cell.lo, h.cell.hi, h.icpt, h.slope⟩ : AffinePiece))) =
      true := by
  decide +kernel

/-! ## The finite tail profile -/

theorem p0FiniteTailPiece_lo (q : ℕ) :
    (p0FiniteTailPiece q).lo = 1 / (2 * ((q : ℚ) + 65)) := rfl
theorem p0FiniteTailPiece_hi (q : ℕ) :
    (p0FiniteTailPiece q).hi = 1 / (2 * ((q : ℚ) + 64)) := rfl
theorem p0FiniteTailPiece_slope (q : ℕ) :
    (p0FiniteTailPiece q).slope =
      2 + 1 / ((1 / (2 * ((q : ℚ) + 65)) + 1 / (2 * ((q : ℚ) + 64))) / 2) ^ 2 := rfl
theorem p0FiniteTailPiece_intercept (q : ℕ) :
    (p0FiniteTailPiece q).intercept =
      3 + 2 * ((q : ℚ) + 64) - 2 / ((1 / (2 * ((q : ℚ) + 65)) + 1 / (2 * ((q : ℚ) + 64))) / 2) :=
  rfl

theorem p0FiniteTailProfile_nonneg : P0ProfileNonneg p0FiniteTailProfile := by
  intro q hq y h1 _
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
  rw [p0FiniteTailPiece_lo] at h1
  rw [p0FiniteTailPiece_slope, p0FiniteTailPiece_intercept]
  push_cast at h1 ⊢
  set c : ℝ := (1 / (2 * ((k : ℝ) + 65)) + 1 / (2 * ((k : ℝ) + 64))) / 2 with hcdef
  have hk : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  have hlo : 0 < 1 / (2 * ((k : ℝ) + 65)) := by positivity
  have hy : 0 < y := lt_of_lt_of_le hlo h1
  have hc : 0 < c := by rw [hcdef]; positivity
  have htan := reciprocal_tangent_majorant hy hc
  have hinv : 1 / y ≤ 2 * ((k : ℝ) + 65) := by
    rw [div_le_iff₀ hy]
    have := (div_le_iff₀ (by positivity : (0 : ℝ) < 2 * ((k : ℝ) + 65))).mp h1
    linarith
  have e : (2 + 1 / c ^ 2) * y + (3 + 2 * ((k : ℝ) + 64) - 2 / c) =
      2 * y + 3 + 2 * ((k : ℝ) + 64) + (y / c ^ 2 - 2 / c) := by ring
  rw [e]
  linarith

theorem p0FiniteTailProfile_hi_le : ∀ q ∈ p0FiniteTailProfile.pieces, (q.hi : ℝ) ≤ 1 := by
  intro q hq
  obtain ⟨k, _, rfl⟩ := List.mem_map.mp hq
  rw [p0FiniteTailPiece_hi]
  push_cast
  rw [div_le_one (by positivity)]
  have : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  linarith

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0A2LowProfile_eval_ge
#print axioms Li2Lean.P0.Integerization.p0HighCell_eval_ge
#print axioms Li2Lean.P0.Integerization.p0FiniteTailProfile_nonneg
#print axioms Li2Lean.P0.Integerization.p0_partial_le_weightedPrimeSum
