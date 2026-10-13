/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourExternalPOC

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ConfigContourExternalFourier

noncomputable section

open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourExternalPOC

/-- The (unnormalized) cosine Fourier coefficient seen by the external
Joukowski factor.  The phase is the sum variable `u+v` forced by the
factorization of `jMap u - jMap v`. -/
def externalFourierCoefficient (n : ℕ) (v : ℝ) : ℝ :=
  ∫ u in (0 : ℝ)..(2 * Real.pi),
    contourDensity u * Real.cos ((n + 1 : ℝ) * (u + v))

/-- Each Abel-series term integrates exactly to its Fourier coefficient.
This is an unconditional identity; no value of the coefficient is assumed. -/
theorem externalTerm_integral_eq (q v : ℝ) (n : ℕ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * externalTerm q n v u) =
      -(q ^ (n + 1) / (n + 1 : ℝ)) * externalFourierCoefficient n v := by
  have hfun :
      (fun u : ℝ => contourDensity u * externalTerm q n v u) =
        (fun u : ℝ =>
          (-(q ^ (n + 1) / (n + 1 : ℝ))) *
            (contourDensity u * Real.cos ((n + 1 : ℝ) * (u + v)))) := by
    funext u
    dsimp [externalTerm]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  rfl

/-- Finite Abel truncations may be integrated term by term and each term is
identified with the corresponding external Fourier coefficient. -/
theorem externalFinite_integral_eq (q v : ℝ) (N : ℕ) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * ∑ n ∈ Finset.range N, externalTerm q n v u) =
      ∑ n ∈ Finset.range N,
        (-(q ^ (n + 1) / (n + 1 : ℝ))) * externalFourierCoefficient n v := by
  have hdist (u : ℝ) :
      contourDensity u * ∑ n ∈ Finset.range N, externalTerm q n v u =
        ∑ n ∈ Finset.range N, contourDensity u * externalTerm q n v u := by
    rw [Finset.mul_sum]
  simp_rw [hdist]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro n hn
    exact externalTerm_integral_eq q v n
  · intro n hn
    exact (contourDensity_continuous.mul (by
      unfold externalTerm
      fun_prop)).intervalIntegrable _ _

/-- The full external logarithmic correction has an unconditional Fourier
integral representation.  Absolute Abel summability and the integral/sum
exchange are provided by `externalLogKernel_integral_tsum`; this theorem only
rewrites every term as its explicit Fourier coefficient. -/
theorem externalLogKernel_integral_eq_tsum_fourier (q v : ℝ)
    (hq : ‖(q : ℂ)‖ < 1) :
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      contourDensity u * externalLogKernel q u v) =
      ∑' n : ℕ,
        (-(q ^ (n + 1) / (n + 1 : ℝ))) * externalFourierCoefficient n v := by
  rw [externalLogKernel_integral_tsum q v hq]
  apply tsum_congr
  intro n
  exact externalTerm_integral_eq q v n

end

end Li2Lean.P0.ConfigContourExternalFourier

namespace Li2Lean.P0.ConfigContourExternalFourier

noncomputable section

open Li2Lean.P0.ConfigContourAnalytic
open Li2Lean.P0.ConfigContourReference
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourExternalPOC

/-- Exact Fejer orthogonality input needed to turn the exposed coefficient
into the closed v10 moment.  It is stated for a shifted kernel so that the
remaining obligation is only the elementary degree-48 orthogonality proof. -/
structure Fejer48ShiftedOrthogonality : Prop where
  cosine : ∀ (k : ℕ), ∀ (theta v : ℝ),
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      fejer48 (u - theta) * Real.cos ((k : ℝ) * (u + v))) =
      2 * Real.pi * K48Coeff k * Real.cos ((k : ℝ) * (theta + v))

/-- Under the named Fejer orthogonality leaf, the external coefficient has
exactly the expected finite contour-moment value.  The sine moment vanishes by
the literal reflected 64-point weights (`sineMoment_eq_zero`). -/
theorem externalFourierCoefficient_eq_moment
    (H : Fejer48ShiftedOrthogonality) (k : ℕ) (hkpos : 1 ≤ k) (v : ℝ) :
    externalFourierCoefficient (k - 1) v =
      2 * Real.pi * contourFourierMoment k * Real.cos ((k : ℝ) * v) := by
  have hkpos' : 0 < k := by omega
  unfold externalFourierCoefficient
  rw [Nat.cast_sub hkpos]
  push_cast
  have hfreq : ((k - 1 : ℕ) : ℝ) + 1 = (k : ℝ) := by
    rw [Nat.cast_sub hkpos]
    push_cast
    ring
  rw [show (k : ℝ) - 1 + 1 = (k : ℝ) by ring]
  unfold contourDensity
  simp_rw [Finset.sum_mul]
  rw [intervalIntegral.integral_finsetSum]
  · unfold contourFourierMoment
    change (∑ j : Fin 64, ∫ u in (0 : ℝ)..(2 * Real.pi),
      contourWeight j * fejer48 (u - contourAngle j) *
        Real.cos ((k : ℝ) * (u + v))) =
      2 * Real.pi * (K48Coeff k *
        (∑ j : Fin 64, contourWeight j * Real.cos ((k : ℝ) * contourAngle j))) *
        Real.cos ((k : ℝ) * v)
    have hsum :
        2 * Real.pi * (K48Coeff k *
          (∑ j : Fin 64, contourWeight j * Real.cos ((k : ℝ) * contourAngle j))) *
            Real.cos ((k : ℝ) * v) =
          ∑ j : Fin 64,
            (2 * Real.pi * K48Coeff k *
              (contourWeight j * Real.cos ((k : ℝ) * contourAngle j))) *
                Real.cos ((k : ℝ) * v) := by
      calc
        _ = (2 * Real.pi * K48Coeff k) *
            ((∑ j : Fin 64, contourWeight j * Real.cos ((k : ℝ) * contourAngle j)) *
              Real.cos ((k : ℝ) * v)) := by ring
        _ = (2 * Real.pi * K48Coeff k) *
            (∑ j : Fin 64,
              (contourWeight j * Real.cos ((k : ℝ) * contourAngle j)) *
                Real.cos ((k : ℝ) * v)) := by rw [Finset.sum_mul]
        _ = _ := by
          rw [Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro j hj
          ring
    calc
      (∑ j : Fin 64, ∫ u in (0 : ℝ)..(2 * Real.pi),
          contourWeight j * fejer48 (u - contourAngle j) *
            Real.cos ((k : ℝ) * (u + v))) =
        ∑ j : Fin 64,
          contourWeight j *
            (2 * Real.pi * K48Coeff k *
              Real.cos ((k : ℝ) * (contourAngle j + v))) := by
          apply Finset.sum_congr rfl
          intro j hj
          have hfun : (fun u : ℝ => contourWeight j * fejer48 (u - contourAngle j) *
              Real.cos ((k : ℝ) * (u + v))) =
              (fun u : ℝ => contourWeight j *
                (fejer48 (u - contourAngle j) * Real.cos ((k : ℝ) * (u + v)))) := by
            funext u
            ring
          rw [hfun, intervalIntegral.integral_const_mul]
          rw [H.cosine k (contourAngle j) v]
      _ = 2 * Real.pi * (K48Coeff k *
          (∑ j : Fin 64, contourWeight j * Real.cos ((k : ℝ) * contourAngle j))) *
            Real.cos ((k : ℝ) * v) := by
          have hterm (j : Fin 64) :
              contourWeight j * (2 * Real.pi * K48Coeff k *
                Real.cos ((k : ℝ) * (contourAngle j + v))) =
                (2 * Real.pi * K48Coeff k * Real.cos ((k : ℝ) * v)) *
                  (contourWeight j * Real.cos ((k : ℝ) * contourAngle j)) -
                (2 * Real.pi * K48Coeff k * Real.sin ((k : ℝ) * v)) *
                  (contourWeight j * Real.sin ((k : ℝ) * contourAngle j)) := by
            have harg : (k : ℝ) * (contourAngle j + v) =
                (k : ℝ) * contourAngle j + (k : ℝ) * v := by ring
            rw [harg, Real.cos_add]
            ring
          rw [Finset.sum_congr rfl (fun j hj => hterm j)]
          rw [Finset.sum_sub_distrib]
          rw [← Finset.mul_sum, ← Finset.mul_sum]
          have hsine :
              (∑ j : Fin 64, contourWeight j * Real.sin ((k : ℝ) * contourAngle j)) = 0 := by
            let S : ℝ := ∑ j : Fin 64,
              contourWeight j * Real.sin ((k : ℝ) * contourAngle j)
            have hrev : S = ∑ j : Fin 64,
                contourWeight (reverseIndex j) *
                  Real.sin ((k : ℝ) * contourAngle (reverseIndex j)) := by
              dsimp [S]
              rw [← Equiv.sum_comp reverseIndex
                (fun j => contourWeight j * Real.sin ((k : ℝ) * contourAngle j))]
            have hneg :
                (∑ j : Fin 64, contourWeight (reverseIndex j) *
                  Real.sin ((k : ℝ) * contourAngle (reverseIndex j))) = -S := by
              dsimp [S]
              calc
                (∑ j : Fin 64, contourWeight (reverseIndex j) *
                    Real.sin ((k : ℝ) * contourAngle (reverseIndex j))) =
                    ∑ j : Fin 64, -(contourWeight j *
                      Real.sin ((k : ℝ) * contourAngle j)) := by
                  apply Finset.sum_congr rfl
                  intro j hj
                  rw [contourWeight_reverse, contourAngle_reverse]
                  have harg : (k : ℝ) * (2 * Real.pi - contourAngle j) =
                      -(k : ℝ) * contourAngle j + (k : ℤ) * (2 * Real.pi) := by
                    push_cast
                    ring
                  rw [harg, Real.sin_add_int_mul_two_pi]
                  have hnegarg : -(k : ℝ) * contourAngle j =
                      -((k : ℝ) * contourAngle j) := by ring
                  rw [hnegarg, Real.sin_neg]
                  ring
                _ = -S := by
                  rw [Finset.sum_neg_distrib]
            have hself : S = -S := hrev.trans hneg
            dsimp [S] at hself ⊢
            linarith
          rw [hsine]
          simp only [mul_assoc]
          ring
  · intro j hj
    exact ((continuous_const.mul (Li2Lean.P0.ConfigFejerMass.continuous_fejer48.comp
      (continuous_id.sub continuous_const))).mul (by fun_prop)).intervalIntegrable _ _

end

end Li2Lean.P0.ConfigContourExternalFourier
