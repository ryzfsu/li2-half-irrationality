/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.LayerInterfaces

open MeasureTheory Set Polynomial Real Filter Topology
open scoped Nat

namespace ContourKit

/-- A nonzero integer cannot have absolute value below one. -/
theorem no_nonzero_integer_abs_lt_one {z : ℤ} (hz : z ≠ 0) (habs : |z| < 1) : False := by
  have hz' : -1 < z ∧ z < 1 := abs_lt.mp habs
  omega

/-- Extract a numerator and positive denominator from rationality. -/
theorem endpoint_not_irrational_rep {x : ℝ} :
    ¬Irrational x → ∃ (a : ℤ) (b : ℕ), 0 < b ∧ x = a / b := by
  rw [Irrational, not_not, mem_range]
  rintro ⟨q, rfl⟩
  exact ⟨q.num, q.den, q.pos, by exact_mod_cast (Rat.num_div_den _).symm⟩

/-- Clear a rational denominator from an integer polynomial of bounded degree. -/
theorem endpoint_poly_eval_integer {p : ℤ[X]} (a b : ℤ) {k : ℕ}
    (hp : p.natDegree ≤ k) :
    ∃ z : ℤ, p.eval₂ (Int.castRingHom ℝ) (a / b) * b ^ k = z := by
  rcases eq_or_ne b 0 with rfl | hb
  · rcases k.eq_zero_or_pos with rfl | hk
    · exact ⟨p.coeff 0, by simp⟩
    exact ⟨0, by simp [hk.ne']⟩
  refine ⟨∑ i ∈ p.support, p.coeff i * a ^ i * b ^ (k - i), ?_⟩
  conv_lhs => rw [← sum_monomial_eq p]
  rw [eval₂_sum, sum, Finset.sum_mul, Int.cast_sum]
  simp only [eval₂_monomial, eq_intCast, div_pow, Int.cast_mul, Int.cast_pow]
  refine Finset.sum_congr rfl (fun i hi => ?_)
  have ik := (le_natDegree_of_mem_supp i hi).trans hp
  rw [mul_assoc, div_mul_comm, ← Int.cast_pow, ← Int.cast_pow, ← Int.cast_pow,
    ← pow_sub_mul_pow b ik, ← Int.cast_div_charZero, Int.mul_ediv_cancel _
      (pow_ne_zero _ hb), ← mul_assoc, mul_right_comm, ← Int.cast_pow]
  exact dvd_mul_left _ _

/-!
The criterion below packages docs/6333 §1: polynomial degree at most the
index, exact integerization, rational-point nonvanishing, and an analytic
exponent whose quadratic decay beats the integerizer rate.
-/
/--
The general endpoint contradiction criterion, with all estimates tied to the
same polynomial, integerizer, and increasing index sequence.
-/
theorem endpoint_criterion {x : ℝ} (c : Li2Lean.EndpointCertificate x) :
    Irrational x := by
  by_contra hrat
  obtain ⟨a, b, hb, hx⟩ := endpoint_not_irrational_rep hrat
  let r : ℚ := (a : ℚ) / b
  have hxR : x = (r : ℝ) := by
    dsimp [r]
    rw [hx]
    norm_cast
  let gap : ℝ := c.alpha - c.tau
  have hgap : 0 < gap := by dsimp [gap]; linarith [c.alpha_gt_tau]
  let br : ℝ := b
  have hbr : 0 < br := by dsimp [br]; exact_mod_cast hb
  have hIndex : Tendsto c.index atTop atTop := c.index_strictMono.tendsto_atTop
  have hM : Tendsto (fun k : ℕ => (c.index k : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp hIndex
  have hlog : Tendsto (fun y : ℝ => Real.log y / y) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  have hlogM : Tendsto (fun k : ℕ =>
      Real.log (c.index k : ℝ) / (c.index k : ℝ)) atTop (𝓝 0) := hlog.comp hM
  have hinv : Tendsto (fun k : ℕ => ((c.index k : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hM
  have hinvSq : Tendsto (fun k : ℕ => ((c.index k : ℝ)⁻¹) ^ 2) atTop (𝓝 0) := by
    simpa using hinv.pow 2
  let rem (k : ℕ) : ℝ :=
    c.cLog * (Real.log (c.index k : ℝ) / (c.index k : ℝ)) +
      (c.cLinear + Real.log br) * (c.index k : ℝ)⁻¹ +
        c.cConst * ((c.index k : ℝ)⁻¹) ^ 2
  have hrem : Tendsto rem atTop (𝓝 0) := by
    simpa [rem, add_assoc] using
      (hlogM.const_mul c.cLog).add
        ((hinv.const_mul (c.cLinear + Real.log br)).add
          (hinvSq.const_mul c.cConst))
  have hremEvent : ∀ᶠ k : ℕ in atTop, rem k < gap / 4 :=
    hrem.eventually_lt_const (by positivity)
  have hrateEvent : ∀ᶠ k : ℕ in atTop,
      Real.log (c.D (c.index k) : ℝ) / (c.index k : ℝ) ^ 2 ≤ c.tau + gap / 4 := by
    obtain ⟨k₀, hk₀⟩ := c.integerizer_rate (gap / 4) (by linarith [hgap])
    exact Filter.eventually_atTop.2 ⟨k₀, fun k hk => hk₀ k hk⟩
  have hnzEvent : ∀ᶠ k : ℕ in atTop, (c.G (c.index k)).eval (r : ℝ) ≠ 0 := by
    obtain ⟨k₀, hk₀⟩ := c.nonzero_at_rationals r
    exact Filter.eventually_atTop.2 ⟨k₀, fun k hk => hk₀ k hk⟩
  obtain ⟨k, ⟨hkRate, hkNz⟩, hkRem⟩ :=
    (hrateEvent.and hnzEvent).and hremEvent |>.exists
  let m : ℕ := c.index k
  let mR : ℝ := m
  have hmNat : 0 < m := by dsimp [m]; have h := c.index_ge_eight k; omega
  have hm : 0 < mR := by dsimp [mR]; exact_mod_cast hmNat
  have hmReal : 0 < (c.index k : ℝ) := by
    have h : 0 < c.index k := by omega
    exact_mod_cast h
  have hD : 0 < (c.D m : ℝ) := by exact_mod_cast c.integerizer_pos k
  obtain ⟨P, hP⟩ := c.integerizer_poly k
  have hPdeg : P.natDegree ≤ m := by
    calc
      P.natDegree = (P.map (Int.castRingHom ℝ)).natDegree := by
        symm
        exact Polynomial.natDegree_map_eq_of_injective Int.cast_injective P
      _ = (Polynomial.C (c.D m : ℝ) * c.G m).natDegree := by rw [hP]
      _ = (c.G m).natDegree := by rw [Polynomial.natDegree_C_mul (ne_of_gt hD)]
      _ ≤ m := c.degree_bound k
  have hPval :
      P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) =
        (c.D m : ℝ) * (c.G m).eval x := by
    have h := congrArg (fun Q : Polynomial ℝ => Q.eval ((a : ℝ) / b)) hP
    simpa [Polynomial.eval_map, hx] using h
  obtain ⟨z, hz⟩ := endpoint_poly_eval_integer (p := P) a (b : ℤ) hPdeg
  have hzReal :
      P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * (br : ℝ) ^ m = (z : ℝ) := by
    have h : P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * (b : ℝ) ^ m = (z : ℝ) := by
      exact_mod_cast hz
    simpa [br] using h
  have hzNe : z ≠ 0 := by
    have hEvalNe : P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) ≠ 0 := by
      rw [hPval]
      have hGne : (c.G m).eval x ≠ 0 := by
        have hEvalEq : (c.G m).eval x = (c.G m).eval (r : ℝ) :=
          congrArg (fun y : ℝ => (c.G m).eval y) hxR
        rw [hEvalEq]
        exact hkNz
      exact mul_ne_zero (by exact_mod_cast (ne_of_gt hD)) hGne
    have hbPow : (br : ℝ) ^ m ≠ 0 := pow_ne_zero _ (ne_of_gt hbr)
    intro hz0
    have hz0R : (z : ℝ) = 0 := by exact_mod_cast hz0
    have hzRealZero :
        P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * br ^ m = 0 := by
      rw [hzReal, hz0R]
    exact (mul_ne_zero hEvalNe hbPow) hzRealZero
  let analytic : ℝ :=
    -c.alpha * mR ^ 2 + c.cLog * mR * Real.log mR +
      c.cLinear * mR + c.cConst
  let exponent : ℝ := analytic + Real.log (c.D m : ℝ) + mR * Real.log br
  have hbpow : br ^ m = Real.exp (mR * Real.log br) := by
    calc
      br ^ m = (Real.exp (Real.log br)) ^ m := by rw [Real.exp_log hbr]
      _ = Real.exp (mR * Real.log br) := by rw [← Real.exp_nat_mul]
  have hzAbs : |(z : ℝ)| = (c.D m : ℝ) * |(c.G m).eval x| * br ^ m := by
    calc
      |(z : ℝ)| = |P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b) * br ^ m| := by
        rw [← hzReal]
      _ = |P.eval₂ (Int.castRingHom ℝ) ((a : ℝ) / b)| * |br ^ m| := abs_mul _ _
      _ = (c.D m : ℝ) * |(c.G m).eval x| * br ^ m := by
        rw [hPval, abs_mul, abs_of_pos hD, abs_of_pos (pow_pos hbr _)]
  have hzBound : |(z : ℝ)| ≤ Real.exp exponent := by
    calc
      |(z : ℝ)| ≤ (c.D m : ℝ) * Real.exp analytic * br ^ m := by
        rw [hzAbs]
        gcongr
        exact c.analytic_bound k
      _ = Real.exp exponent := by
        calc
          _ = Real.exp (Real.log (c.D m : ℝ)) * Real.exp analytic *
              Real.exp (mR * Real.log br) := by
            rw [hbpow]
            exact congrArg
              (fun t : ℝ => t * Real.exp analytic *
                Real.exp (mR * Real.log br))
              (Real.exp_log hD).symm
          _ = Real.exp (analytic + Real.log (c.D m : ℝ) +
              mR * Real.log br) := by
            rw [← Real.exp_add, ← Real.exp_add]
            congr 1 <;> ring
          _ = Real.exp exponent := rfl
  have hnorm : exponent / mR ^ 2 < 0 := by
    calc
      exponent / mR ^ 2 = -c.alpha +
          Real.log (c.D m : ℝ) / mR ^ 2 + rem k := by
            dsimp [exponent, analytic, rem, m, mR]
            field_simp [ne_of_gt hmReal]
            <;> ring_nf
      _ ≤ -c.alpha + (c.tau + gap / 4) + rem k := by linarith [hkRate]
      _ < 0 := by linarith [hgap, hkRem]
  have hexponent : exponent < 0 := by
    have hsq : 0 < mR ^ 2 := sq_pos_of_pos hm
    have h' := (div_lt_iff₀ hsq).mp hnorm
    nlinarith
  have hexp : Real.exp exponent < 1 := Real.exp_lt_one_iff.mpr hexponent
  have hzAbsLt : |(z : ℝ)| < 1 := lt_of_le_of_lt hzBound hexp
  have hzAbsInt : |z| < 1 := by exact_mod_cast hzAbsLt
  exact no_nonzero_integer_abs_lt_one hzNe hzAbsInt

end ContourKit
