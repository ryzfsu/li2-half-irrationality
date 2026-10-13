/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Pinned.LogEval
import Li2Lean.P0.PinnedRow1ClosedForm

/-!
# The actual contour potential on the pinned segment as a moment polynomial

For `x ∈ [1/4, 5/4]` the literal Fejer contour potential equals
`M log c - Σ_{n<49} m_n p_n(x)/n`, where `m_n = contourMoment n` and
`p_n = row1PairPowerSum x n` is the real power sum of the two Joukowski
preimages.  This removes the complex roots from every later bound.
-/

namespace Li2Lean.P0.CA.Pinned

open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigFejerLog
open Li2Lean.P0.ConfigInteriorContourPotential
open Li2Lean.P0.PinnedRow1ClosedForm

noncomputable section

/-- The real moment polynomial of the contour potential. -/
def contourQ (x : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 49, contourMoment n * (row1PairPowerSum x n / (n : ℝ))

theorem fejerLogPolynomial_pair_re (a b : ℂ) (p : ℕ → ℝ)
    (hp : ∀ n, a ^ n + b ^ n = (p n : ℂ)) (θ : ℝ) :
    (fejerLogPolynomial ((starRingEnd ℂ) a * phase θ)).re +
        (fejerLogPolynomial ((starRingEnd ℂ) b * phase θ)).re =
      ∑ n ∈ Finset.range 49,
        (1 - (n : ℝ) / 49) * (p n / (n : ℝ)) * Real.cos ((n : ℝ) * θ) := by
  unfold fejerLogPolynomial
  rw [← Complex.add_re, ← Finset.sum_add_distrib, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro n hn
  have hn49 : n ≤ 49 := by have := Finset.mem_range.mp hn; omega
  have hconj : (starRingEnd ℂ) a ^ n + (starRingEnd ℂ) b ^ n = (p n : ℂ) := by
    rw [← map_pow, ← map_pow, ← map_add, hp, Complex.conj_ofReal]
  have hsplit :
      ((49 - n : ℕ) : ℂ) / 49 * (((starRingEnd ℂ) a * phase θ) ^ n / (n : ℂ)) +
        ((49 - n : ℕ) : ℂ) / 49 * (((starRingEnd ℂ) b * phase θ) ^ n / (n : ℂ)) =
      (((((49 - n : ℕ) : ℝ) / 49) * (p n / (n : ℝ)) : ℝ) : ℂ) * phase θ ^ n := by
    rw [mul_pow, mul_pow]
    have : ((49 - n : ℕ) : ℂ) / 49 * ((starRingEnd ℂ) a ^ n * phase θ ^ n / (n : ℂ)) +
        ((49 - n : ℕ) : ℂ) / 49 * ((starRingEnd ℂ) b ^ n * phase θ ^ n / (n : ℂ)) =
        ((49 - n : ℕ) : ℂ) / 49 *
          (((starRingEnd ℂ) a ^ n + (starRingEnd ℂ) b ^ n) / (n : ℂ)) * phase θ ^ n := by
      ring
    rw [this, hconj]
    push_cast
    ring
  rw [hsplit, Complex.re_ofReal_mul, phase_pow_re, Nat.cast_sub hn49]
  push_cast
  ring

theorem contourLogPolynomial_pair (a b : ℂ) (p : ℕ → ℝ)
    (hp : ∀ n, a ^ n + b ^ n = (p n : ℂ)) :
    contourLogPolynomial ((starRingEnd ℂ) a) + contourLogPolynomial ((starRingEnd ℂ) b) =
      ∑ n ∈ Finset.range 49, contourMoment n * (p n / (n : ℝ)) := by
  unfold contourLogPolynomial
  rw [← Finset.sum_add_distrib]
  simp_rw [← mul_add, fejerLogPolynomial_pair_re a b p hp, Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro n _
  unfold contourMoment
  rw [Finset.mul_sum, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- The contour potential at a pinned real point, as a real polynomial. -/
theorem contourPotential_eq_poly (x : ℝ) (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 5 / 4) :
    contourReferencePotential (x : ℂ) =
      (267885951940 / 1000000000000 : ℝ) * Real.log contourScale - contourQ x := by
  rw [contourReferencePotential_pinned_interval x hxlo hxhi, sub_sub,
    contourLogPolynomial_pair _ _ _ (row1PairPowerSum_root_identity x)]
  rfl

end

/-! ## Exact power-sum polynomials in the local variable -/

def psW0 (x0 : ℚ) : ℚ := (x0 - 11281 / 10000) / (24233 / 20000)
def psK : ℚ := 1 / (24233 / 20000)
def psQ : ℚ := 1333 / 24233

/-- `(w0 + k t) * p`. -/
def mulTrace (x0 : ℚ) (p : List ℚ) : List ℚ :=
  addQ (p.map (fun a => psW0 x0 * a)) (0 :: p.map (fun a => psK * a))

def psNext (x0 : ℚ) (a b : List ℚ) : List ℚ :=
  addQ (mulTrace x0 b) (a.map (fun c => -psQ * c))


theorem hornerR_mulTrace (x0 : ℚ) (p : List ℚ) (t : ℝ) :
    hornerR (castL (mulTrace x0 p)) t =
      ((psW0 x0 : ℝ) + (psK : ℝ) * t) * hornerR (castL p) t := by
  rw [mulTrace, castL_addQ, hornerR_addR, castL_map_mul]
  have : castL (0 :: p.map (fun a => psK * a)) = mulX (scaleR (psK : ℝ) (castL p)) := by
    simp only [castL, mulX, Rat.cast_zero, castL_map_mul]
  rw [this, hornerR_mulX, hornerR_scaleR, hornerR_scaleR]
  ring

theorem trace_eq (x0 : ℚ) (t : ℝ) :
    ((x0 : ℝ) + t - 11281 / 10000) / (24233 / 20000) =
      (psW0 x0 : ℝ) + (psK : ℝ) * t := by
  simp only [psW0, psK]; push_cast; ring

end Li2Lean.P0.CA.Pinned
