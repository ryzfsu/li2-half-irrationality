/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.JoukowskiPoleRange

namespace Li2Lean
namespace P0ContourLeaf

noncomputable section

/-- The affine Joukowski map used in the contour pullback. -/
def affineJoukowski (xi alpha beta zeta : ℂ) : ℂ :=
  xi + alpha * zeta + beta / zeta

/-- Its derivative away from the origin. -/
def affineJoukowskiDeriv (alpha beta zeta : ℂ) : ℂ :=
  alpha - beta / zeta ^ 2

/-- Factorization by the two Vieta preimages of a pole. -/
theorem affineJoukowski_factorization {xi alpha beta w z1 z2 zeta : ℂ}
    (ha : alpha ≠ 0)
    (hsum : z1 + z2 = (w - xi) / alpha)
    (hprod : z1 * z2 = beta / alpha)
    (hz : zeta ≠ 0) :
    affineJoukowski xi alpha beta zeta - w =
      alpha / zeta * (zeta - z1) * (zeta - z2) := by
  unfold affineJoukowski
  have hsum' : alpha * (z1 + z2) = w - xi := by
    rw [hsum]
    field_simp [ha]
  have hprod' : alpha * (z1 * z2) = beta := by
    rw [hprod]
    field_simp [ha]
  field_simp [hz]
  calc
    zeta * (xi + alpha * zeta) + beta - zeta * w =
        alpha * zeta ^ 2 + beta - zeta * (w - xi) := by ring
    _ = alpha * zeta ^ 2 + alpha * (z1 * z2) -
        zeta * (alpha * (z1 + z2)) := by rw [← hprod', ← hsum']
    _ = alpha * (zeta - z1) * (zeta - z2) := by ring

/-- Partial fractions for the logarithmic derivative of a Joukowski pullback. -/
theorem affineJoukowski_log_deriv_decomp {xi alpha beta w z1 z2 zeta : ℂ}
    (ha : alpha ≠ 0)
    (hsum : z1 + z2 = (w - xi) / alpha)
    (hprod : z1 * z2 = beta / alpha)
    (hz : zeta ≠ 0)
    (h1 : zeta - z1 ≠ 0)
    (h2 : zeta - z2 ≠ 0) :
    affineJoukowskiDeriv alpha beta zeta /
        (affineJoukowski xi alpha beta zeta - w) =
      1 / (zeta - z1) + 1 / (zeta - z2) - 1 / zeta := by
  have hfac := affineJoukowski_factorization ha hsum hprod hz
  have hJ : affineJoukowski xi alpha beta zeta - w ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero ha hz) h1) h2
  unfold affineJoukowskiDeriv
  rw [hfac]
  field_simp [ha, hz, h1, h2, hJ]
  have hsum' : alpha * (z1 + z2) = w - xi := by
    rw [hsum]
    field_simp [ha]
  have hprod' : alpha * (z1 * z2) = beta := by
    rw [hprod]
    field_simp [ha]
  rw [← hprod']
  ring

/--
If both Vieta preimages are strictly inside the unit disk, the pulled-back
logarithmic derivative has normalized unit-circle integral `2*pi*I`. This is
the exact two-preimage residue calculation used for the contour normalization.
-/
theorem affineJoukowski_log_deriv_unitCircle {xi alpha beta w z1 z2 : ℂ}
    (ha : alpha ≠ 0)
    (hsum : z1 + z2 = (w - xi) / alpha)
    (hprod : z1 * z2 = beta / alpha)
    (h1in : ‖z1‖ < 1) (h2in : ‖z2‖ < 1) :
    ∮ z in C(0, 1),
      affineJoukowskiDeriv alpha beta z /
        (affineJoukowski xi alpha beta z - w) =
      2 * (Real.pi : ℂ) * Complex.I := by
  have hrad : (0 : ℝ) ≤ 1 := by norm_num
  have hzero : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    norm_num
  have hroot1 : z1 ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact h1in
  have hroot2 : z2 ∈ Metric.ball (0 : ℂ) 1 := by
    rw [Metric.mem_ball, dist_zero_right]
    exact h2in
  have hci (c : ℂ) (hc : c ∈ Metric.ball (0 : ℂ) 1) :
      CircleIntegrable (fun z : ℂ => (z - c)⁻¹) 0 1 := by
    apply ContinuousOn.circleIntegrable hrad
    apply (continuousOn_id.sub continuousOn_const).inv₀
    intro z hz hzc
    have hzc' : z = c := sub_eq_zero.mp hzc
    subst z
    rw [mem_sphere_zero_iff_norm] at hz
    rw [Metric.mem_ball, dist_zero_right] at hc
    linarith
  have hbase : CircleIntegrable
      (fun z : ℂ => (-1 : ℂ) * (z - 0)⁻¹) 0 1 :=
    (hci 0 hzero).const_mul (-1)
  have hsum12 : CircleIntegrable
      (fun z : ℂ => (-1 : ℂ) * (z - 0)⁻¹ + (z - z1)⁻¹) 0 1 :=
    hbase.add (hci z1 hroot1)
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      affineJoukowskiDeriv alpha beta z /
          (affineJoukowski xi alpha beta z - w) =
        (-1 : ℂ) * (z - 0)⁻¹ + (z - z1)⁻¹ + (z - z2)⁻¹ := by
    intro z hz
    rw [mem_sphere_zero_iff_norm] at hz
    have hz0 : z ≠ 0 := by
      intro hz0
      subst z
      norm_num at hz
    have hz1 : z - z1 ≠ 0 := by
      intro h
      have heq : z = z1 := sub_eq_zero.mp h
      rw [heq] at hz
      linarith
    have hz2 : z - z2 ≠ 0 := by
      intro h
      have heq : z = z2 := sub_eq_zero.mp h
      rw [heq] at hz
      linarith
    have hd := affineJoukowski_log_deriv_decomp ha hsum hprod hz0 hz1 hz2
    calc
      _ = 1 / (z - z1) + 1 / (z - z2) - 1 / z := hd
      _ = (-1 : ℂ) * (z - 0)⁻¹ + (z - z1)⁻¹ + (z - z2)⁻¹ := by
        simp only [one_div, sub_zero]
        ring
  rw [circleIntegral.integral_congr hrad hboundary]
  rw [circleIntegral.integral_add
      (f := fun z : ℂ => (-1 : ℂ) * (z - 0)⁻¹ + (z - z1)⁻¹)
      (g := fun z : ℂ => (z - z2)⁻¹) hsum12 (hci z2 hroot2)]
  rw [circleIntegral.integral_add
      (f := fun z : ℂ => (-1 : ℂ) * (z - 0)⁻¹)
      (g := fun z : ℂ => (z - z1)⁻¹) hbase (hci z1 hroot1)]
  rw [circleIntegral.integral_const_mul,
    circleIntegral.integral_sub_inv_of_mem_ball hzero,
    circleIntegral.integral_sub_inv_of_mem_ball hroot1,
    circleIntegral.integral_sub_inv_of_mem_ball hroot2]
  ring

/-- The scaled centre and axes for the paper contour `m Gamma`. -/
def xiScaled (m : ℕ) : ℝ := (m : ℝ) * xi

def alphaScaled (m : ℕ) : ℝ := (m : ℝ) * alpha

def betaScaled (m : ℕ) : ℝ := (m : ℝ) * beta

/--
The paper's exact two-preimage condition for a source pole of `m Gamma`.
The two roots satisfy the literal Vieta sums/products and both lie in the
open unit disk.
-/
def P0PolePreimageCondition (m i : ℕ) : Prop :=
  ∃ z₁ z₂ : ℂ,
    z₁ + z₂ = ((i : ℂ) - (xiScaled m : ℂ)) / (alphaScaled m : ℂ) ∧
    z₁ * z₂ = (betaScaled m : ℂ) / (alphaScaled m : ℂ) ∧
    ‖z₁‖ < 1 ∧ ‖z₂‖ < 1

/--
For every positive scale and every paper pole `i < 2m`, the literal scaled
quadratic has two Vieta preimages, both strictly inside the unit disk.
-/
theorem p0_pole_preimage_condition (m i : ℕ) (hm : 0 < m)
    (hi : i < 2 * m) : P0PolePreimageCondition m i := by
  let t : ℝ := (i : ℝ) / (m : ℝ)
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact div_nonneg (Nat.cast_nonneg i) (le_of_lt hmR)
  have hiR : (i : ℝ) < 2 * (m : ℝ) := by exact_mod_cast hi
  have ht2 : t ≤ 2 := by
    dsimp [t]
    exact (div_le_iff₀ hmR).2 hiR.le
  have haR : 0 < alpha := by norm_num [alpha, axisA, axisB]
  have ha : (alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt haR)
  have hbR : 0 < beta := by norm_num [beta, axisA, axisB]
  have hqdegree :
      (Polynomial.C (alpha : ℂ) * Polynomial.X ^ 2 +
        Polynomial.C ((xi - t : ℝ) : ℂ) * Polynomial.X +
        Polynomial.C (beta : ℂ)).degree = 2 := by
    exact Polynomial.degree_quadratic ha
  let q : Polynomial ℂ :=
    Polynomial.C (alpha : ℂ) * Polynomial.X ^ 2 +
      Polynomial.C ((xi - t : ℝ) : ℂ) * Polynomial.X +
      Polynomial.C (beta : ℂ)
  have hqdegree' : q.degree ≠ 0 := by
    rw [show q = Polynomial.C (alpha : ℂ) * Polynomial.X ^ 2 +
        Polynomial.C ((xi - t : ℝ) : ℂ) * Polynomial.X +
        Polynomial.C (beta : ℂ) by rfl, hqdegree]
    norm_num
  obtain ⟨z₁, hz₁⟩ := IsAlgClosed.exists_root q hqdegree'
  have hz₁root : polePolynomial t z₁ = 0 := by
    change q.eval z₁ = 0 at hz₁
    simpa [q, polePolynomial] using hz₁
  let z₂ : ℂ := ((Complex.ofReal t - (xi : ℂ)) / (alpha : ℂ)) - z₁
  have hsum : z₁ + z₂ =
      (Complex.ofReal t - (xi : ℂ)) / (alpha : ℂ) := by
    dsimp [z₂]
    ring
  have hprod : z₁ * z₂ = (beta : ℂ) / (alpha : ℂ) := by
    dsimp [z₂]
    have hroot : (alpha : ℂ) * z₁ ^ 2 +
        ((xi - t : ℝ) : ℂ) * z₁ + (beta : ℂ) = 0 := by
      simpa [polePolynomial] using hz₁root
    field_simp [ha]
    push_cast at hroot ⊢
    linear_combination -hroot
  have hz₂root : polePolynomial t z₂ = 0 := by
    have hlinear : ((xi - t : ℝ) : ℂ) =
        -(alpha : ℂ) * (z₁ + z₂) := by
      rw [hsum]
      field_simp [ha]
      push_cast
      ring
    have hconstant : (beta : ℂ) = (alpha : ℂ) * (z₁ * z₂) := by
      rw [hprod]
      field_simp [ha]
    dsimp [polePolynomial]
    rw [hlinear, hconstant]
    ring
  have hnorm₁ : ‖z₁‖ < 1 :=
    pole_preimage_mem_unitDisk ht0 ht2 z₁ hz₁root
  have hnorm₂ : ‖z₂‖ < 1 :=
    pole_preimage_mem_unitDisk ht0 ht2 z₂ hz₂root
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hsumScaled : z₁ + z₂ =
      ((i : ℂ) - (xiScaled m : ℂ)) / (alphaScaled m : ℂ) := by
    rw [hsum]
    dsimp [t, xiScaled, alphaScaled]
    push_cast
    field_simp [hmC, ha]
  have hprodScaled : z₁ * z₂ =
      (betaScaled m : ℂ) / (alphaScaled m : ℂ) := by
    rw [hprod]
    dsimp [betaScaled, alphaScaled]
    field_simp [hmC, ha]
    push_cast
    ring
  exact ⟨z₁, z₂, hsumScaled, hprodScaled, hnorm₁, hnorm₂⟩

/--
The v10 P0 pole integral after Joukowski pullback. This combines the exact
two-preimage construction with the unit-circle residue calculation.
-/
theorem p0_scaled_pole_residue (m i : ℕ) (hm : 0 < m)
    (hi : i < 2 * m) :
    ∮ z in C(0, 1),
      affineJoukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z /
        (affineJoukowski (xiScaled m : ℂ) (alphaScaled m : ℂ)
          (betaScaled m : ℂ) z - (i : ℂ)) =
      2 * (Real.pi : ℂ) * Complex.I := by
  rcases p0_pole_preimage_condition m i hm hi with
    ⟨z₁, z₂, hsum, hprod, h₁, h₂⟩
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have haR : 0 < alpha := by norm_num [alpha, axisA, axisB]
  have hαR : 0 < alphaScaled m := by
    dsimp [alphaScaled]
    exact mul_pos hmR haR
  have hα : (alphaScaled m : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt hαR)
  exact affineJoukowski_log_deriv_unitCircle hα hsum hprod h₁ h₂

end
end P0ContourLeaf
end Li2Lean
