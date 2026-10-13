/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
/-
Third-party attribution for the general Joukowski contour technique used in
the ellipse lemmas below:
Copyright (c) 2026 Bastiaan J Braams. All rights reserved.
Released under Apache 2.0 license as described in the upstream LICENSE.
Source: bjbraams/lean-codes@2b8cba1d0201:Carlson/Jacobi/EllipseContour.lean.
The statements and proofs in this file are independently written for Li2Lean.
-/

import Mathlib

open MeasureTheory

namespace Li2Lean
namespace ContourKit

noncomputable section

/-- Product of a fixed sigma-finite measure over finitely many coordinates. -/
def productMeasure {d : ℕ} (μ : Measure ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => μ)

/-- The two determinant factors in the finite-dimensional Andreief identity. -/
noncomputable def detProductIntegrand {d : ℕ} (f : Fin d → ℝ → ℂ)
    (g : ℝ → Fin d → ℂ) (x : Fin d → ℝ) : ℂ :=
  Matrix.det (fun i j => f i (x j)) * Matrix.det (fun i j => g (x i) j)

private def l5Sign {d : ℕ} (σ : Equiv.Perm (Fin d)) : ℂ :=
  ((Equiv.Perm.sign σ : ℤ) : ℂ)

private def l5CoordinateMonomial {d : ℕ} (f : Fin d → ℝ → ℂ)
    (g : ℝ → Fin d → ℂ) (σ τ : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) : ℂ :=
  ∏ i, f (σ i) (x i) * g (x i) (τ.symm i)

private def l5Summand {d : ℕ} (f : Fin d → ℝ → ℂ)
    (g : ℝ → Fin d → ℂ) (σ τ : Equiv.Perm (Fin d))
    (x : Fin d → ℝ) : ℂ :=
  l5Sign σ * l5Sign τ * l5CoordinateMonomial f g σ τ x

private theorem l5Sign_mul {d : ℕ} (σ τ : Equiv.Perm (Fin d)) :
    l5Sign (σ * τ) = l5Sign σ * l5Sign τ := by
  simp [l5Sign, Equiv.Perm.sign_mul]

private def l5RightMulEquiv {d : ℕ} (τ : Equiv.Perm (Fin d)) :
    Equiv.Perm (Fin d) ≃ Equiv.Perm (Fin d) where
  toFun σ := σ * τ
  invFun σ := σ * τ⁻¹
  left_inv σ := by simp
  right_inv σ := by simp

private theorem l5MomentProduct_reindex {d : ℕ}
    (M : Matrix (Fin d) (Fin d) ℂ) (σ τ : Equiv.Perm (Fin d)) :
    (∏ i, M (σ i) (τ.symm i)) = ∏ i, M ((σ * τ) i) i := by
  apply Fintype.prod_equiv τ.symm
  intro i
  simp [Equiv.Perm.mul_apply]

private theorem l5PermutationSum {d : ℕ} (M : Matrix (Fin d) (Fin d) ℂ) :
    (∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
      l5Sign σ * l5Sign τ * ∏ i, M (σ i) (τ.symm i)) =
      (Nat.factorial d : ℂ) * M.det := by
  let q : Equiv.Perm (Fin d) → ℂ := fun σ =>
    l5Sign σ * ∏ i, M (σ i) i
  calc
    (∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        l5Sign σ * l5Sign τ * ∏ i, M (σ i) (τ.symm i))
        = ∑ τ : Equiv.Perm (Fin d), ∑ σ : Equiv.Perm (Fin d),
            q (σ * τ) := by
          rw [Finset.sum_comm]
          apply Finset.sum_congr rfl
          intro τ hτ
          apply Finset.sum_congr rfl
          intro σ hσ
          dsimp [q]
          rw [← l5Sign_mul, l5MomentProduct_reindex]
          simp [Equiv.Perm.mul_apply]
    _ = ∑ τ : Equiv.Perm (Fin d), ∑ σ : Equiv.Perm (Fin d), q σ := by
          apply Finset.sum_congr rfl
          intro τ hτ
          exact Equiv.sum_comp (l5RightMulEquiv τ) q
    _ = (Fintype.card (Equiv.Perm (Fin d)) : ℂ) * ∑ σ : Equiv.Perm (Fin d), q σ := by
          simp [q, Finset.sum_const, nsmul_eq_mul]
    _ = (Nat.factorial d : ℂ) * M.det := by
          have hcard : Fintype.card (Equiv.Perm (Fin d)) = Nat.factorial d := by
            simp [Fintype.card_perm]
          rw [hcard]
          simp only [Nat.cast_factorial]
          rw [Matrix.det_apply']
          simp [q, l5Sign]

private theorem l5PairProducts_reindex {d : ℕ} (f : Fin d → ℝ → ℂ)
    (g : ℝ → Fin d → ℂ) (σ τ : Equiv.Perm (Fin d)) (x : Fin d → ℝ) :
    (∏ i, f (σ i) (x i)) * (∏ i, g (x (τ i)) i) =
      l5CoordinateMonomial f g σ τ x := by
  have hg : (∏ i, g (x (τ i)) i) = ∏ i, g (x i) (τ.symm i) := by
    apply Fintype.prod_equiv τ
    intro i
    simp
  rw [hg, ← Finset.prod_mul_distrib]
  rfl

private theorem l5IntegrandExpansion {d : ℕ} (f : Fin d → ℝ → ℂ)
    (g : ℝ → Fin d → ℂ) (x : Fin d → ℝ) :
    detProductIntegrand f g x =
      ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
        l5Summand f g σ τ x := by
  dsimp [detProductIntegrand]
  let A : Matrix (Fin d) (Fin d) ℂ := fun i j => f i (x j)
  let B : Matrix (Fin d) (Fin d) ℂ := fun i j => g (x i) j
  change A.det * B.det = _
  rw [Matrix.det_apply' A, Matrix.det_apply' B]
  rw [Fintype.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro σ hσ
  apply Finset.sum_congr rfl
  intro τ hτ
  dsimp [A, B, l5Summand, l5Sign, l5CoordinateMonomial]
  calc
    (((Equiv.Perm.sign σ : ℤ) : ℂ) * (∏ i, f (σ i) (x i))) *
        (((Equiv.Perm.sign τ : ℤ) : ℂ) * (∏ i, g (x (τ i)) i)) =
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          ((∏ i, f (σ i) (x i)) * (∏ i, g (x (τ i)) i)) := by ring
    _ = ((Equiv.Perm.sign σ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) *
          l5CoordinateMonomial f g σ τ x := by
            rw [l5PairProducts_reindex]

private theorem l5CoordinateMonomial_integrable {d : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] (f : Fin d → ℝ → ℂ) (g : ℝ → Fin d → ℂ)
    (σ τ : Equiv.Perm (Fin d))
    (hpair : ∀ i j, Integrable (fun x => f i x * g x j) μ) :
    Integrable (l5CoordinateMonomial f g σ τ)
      (Measure.pi (fun _ : Fin d => μ)) := by
  unfold l5CoordinateMonomial
  apply Integrable.fintype_prod (μ := fun _ : Fin d => μ)
    (f := fun i x => f (σ i) x * g x (τ.symm i))
  intro i
  exact hpair (σ i) (τ.symm i)

private theorem l5CoordinateMonomial_integral {d : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] (f : Fin d → ℝ → ℂ) (g : ℝ → Fin d → ℂ)
    (σ τ : Equiv.Perm (Fin d)) :
    (∫ x, l5CoordinateMonomial f g σ τ x ∂(Measure.pi (fun _ : Fin d => μ))) =
      ∏ i, ∫ x, f (σ i) x * g x (τ.symm i) ∂μ := by
  simpa [l5CoordinateMonomial] using
    (MeasureTheory.integral_fintype_prod_eq_prod
      (f := fun i x => f (σ i) x * g x (τ.symm i))
      (μ := fun _ : Fin d => μ))

private theorem l5Summand_integrable {d : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] (f : Fin d → ℝ → ℂ) (g : ℝ → Fin d → ℂ)
    (σ τ : Equiv.Perm (Fin d))
    (hpair : ∀ i j, Integrable (fun x => f i x * g x j) μ) :
    Integrable (l5Summand f g σ τ) (Measure.pi (fun _ : Fin d => μ)) := by
  unfold l5Summand
  exact (l5CoordinateMonomial_integrable f g σ τ hpair).const_mul _

private theorem l5Summand_integral {d : ℕ} {μ : Measure ℝ}
    [SigmaFinite μ] (f : Fin d → ℝ → ℂ) (g : ℝ → Fin d → ℂ)
    (σ τ : Equiv.Perm (Fin d)) (M : Matrix (Fin d) (Fin d) ℂ)
    (hM : ∀ i j, M i j = ∫ x, f i x * g x j ∂μ) :
    (∫ x, l5Summand f g σ τ x ∂(Measure.pi (fun _ : Fin d => μ))) =
      l5Sign σ * l5Sign τ * ∏ i, M (σ i) (τ.symm i) := by
  unfold l5Summand
  rw [integral_const_mul, l5CoordinateMonomial_integral]
  have hprod :
      (∏ i, ∫ x, f (σ i) x * g x (τ.symm i) ∂μ) =
        ∏ i, M (σ i) (τ.symm i) := by
    apply Finset.prod_congr rfl
    intro i hi
    rw [hM]
  rw [hprod]

/--
Finite-dimensional Andreief identity for a sigma-finite base measure. The
factorial is obtained by the two permutation expansions and the reindexing
`(sigma, tau) -> (sigma * tau, tau)`; no symmetry factor is suppressed.
-/
theorem l5Andreief_sigmaFinite {d : ℕ} (μ : Measure ℝ) [SigmaFinite μ]
    (f : Fin d → ℝ → ℂ) (g : ℝ → Fin d → ℂ)
    (hpair : ∀ i j, Integrable (fun x => f i x * g x j) μ)
    :
    Matrix.det (fun i j => ∫ x, f i x * g x j ∂μ) =
      (Nat.factorial d : ℂ)⁻¹ *
        ∫ x : Fin d → ℝ, detProductIntegrand f g x ∂(productMeasure μ) := by
  let M : Matrix (Fin d) (Fin d) ℂ := fun i j => ∫ x, f i x * g x j ∂μ
  have hfactor :
      (∫ x : Fin d → ℝ, detProductIntegrand f g x ∂(productMeasure μ)) =
        (Nat.factorial d : ℂ) * M.det := by
    have hterm : ∀ σ τ, Integrable (l5Summand f g σ τ)
        (Measure.pi (fun _ : Fin d => μ)) := by
      intro σ τ
      exact l5Summand_integrable f g σ τ hpair
    have hinner : ∀ σ : Equiv.Perm (Fin d),
        Integrable (fun x => ∑ τ : Equiv.Perm (Fin d), l5Summand f g σ τ x)
          (Measure.pi (fun _ : Fin d => μ)) := by
      intro σ
      exact integrable_finsetSum Finset.univ (by
        intro τ hτ
        exact hterm σ τ)
    calc
      _ = ∫ x, ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
          l5Summand f g σ τ x ∂(Measure.pi (fun _ : Fin d => μ)) := by
            apply integral_congr_ae
            filter_upwards [] with x
            exact l5IntegrandExpansion f g x
      _ = ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
          ∫ x, l5Summand f g σ τ x ∂(Measure.pi (fun _ : Fin d => μ)) := by
            rw [integral_finsetSum Finset.univ (fun σ hσ => hinner σ)]
            apply Finset.sum_congr rfl
            intro σ hσ
            rw [integral_finsetSum Finset.univ (fun τ hτ => hterm σ τ)]
      _ = ∑ σ : Equiv.Perm (Fin d), ∑ τ : Equiv.Perm (Fin d),
          l5Sign σ * l5Sign τ * ∏ i, M (σ i) (τ.symm i) := by
            apply Finset.sum_congr rfl
            intro σ hσ
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [l5Summand_integral f g σ τ M (by intro i j; rfl)]
      _ = (Nat.factorial d : ℂ) * M.det := by
            exact l5PermutationSum M
  have hfac : (Nat.factorial d : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero d
  change M.det = (Nat.factorial d : ℂ)⁻¹ *
    (∫ x : Fin d → ℝ, detProductIntegrand f g x ∂(productMeasure μ))
  rw [hfactor]
  field_simp

/-!
The following definitions package the Joukowski pullback used for the ellipse
in docs/6333 §3.  They are deliberately stated for arbitrary complex
parameters; the Li₂ application supplies the ellipse constants and the pole
`w = I` in its instance layer.  The algebraic proof uses only Vieta's two
relations and a primitive-free partial-fraction calculation.
-/

/-- Joukowski map with affine centre `xi` and coefficients `alpha`, `beta`. -/
def joukowski (xi alpha beta zeta : ℂ) : ℂ :=
  xi + alpha * zeta + beta / zeta

/-- Complex derivative of `joukowski` away from zero. -/
def joukowskiDeriv (alpha beta zeta : ℂ) : ℂ :=
  alpha - beta / zeta ^ 2

/-- The displayed derivative of the Joukowski map at every nonzero point. -/
theorem hasDerivAt_joukowski {xi alpha beta zeta : ℂ} (hz : zeta ≠ 0) :
    HasDerivAt (joukowski xi alpha beta) (joukowskiDeriv alpha beta zeta) zeta := by
  have hlinear : HasDerivAt (fun z : ℂ => alpha * z) alpha zeta := by
    simpa using (hasDerivAt_id zeta).const_mul alpha
  have hinverse : HasDerivAt (fun z : ℂ => beta / z) (-beta / zeta ^ 2) zeta := by
    convert (hasDerivAt_inv hz).const_mul beta using 1 <;> simp [div_eq_mul_inv] <;> ring
  unfold joukowski joukowskiDeriv
  convert (hlinear.const_add xi).add hinverse using 1 <;> ring

/-- Real ellipse parameterization with centre `xi` and semiaxes `A`, `B`. -/
def ellipsePoint (xi A B u : ℝ) : ℂ :=
  Complex.ofReal (xi + A * Real.cos u) +
    Complex.I * Complex.ofReal (B * Real.sin u)

/-- The oriented tangent vector of the real ellipse parameterization. -/
def ellipseTangent (xi A B u : ℝ) : ℂ :=
  Complex.ofReal (-A * Real.sin u) +
    Complex.I * Complex.ofReal (B * Real.cos u)

/-- The unit-circle Joukowski parameters corresponding to a real ellipse. -/
def ellipseJoukowski (xi A B : ℝ) (zeta : ℂ) : ℂ :=
  joukowski (xi : ℂ) (((A + B) / 2 : ℝ) : ℂ)
    (((A - B) / 2 : ℝ) : ℂ) zeta

/--
The Joukowski image of the standard unit-circle parameter is the real ellipse
parameterization. This identifies the generic circle model with the ellipses
used in docs/6333 §3, before that paper's scale is substituted.
-/
theorem ellipseJoukowski_param (xi A B u : ℝ) :
    ellipseJoukowski xi A B (Complex.exp (Complex.I * u)) = ellipsePoint xi A B u := by
  rw [ellipseJoukowski, ellipsePoint, joukowski]
  have hplus : Complex.exp (Complex.I * u) =
      Complex.ofReal (Real.cos u) + Complex.I * Complex.ofReal (Real.sin u) := by
    rw [show Complex.I * (u : ℂ) = (u : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I]
    ring
  have hminus : (Complex.exp (Complex.I * u))⁻¹ =
      Complex.ofReal (Real.cos u) - Complex.I * Complex.ofReal (Real.sin u) := by
    rw [← Complex.exp_neg,
      show -(Complex.I * (u : ℂ)) = ((-u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  simp only [div_eq_mul_inv]
  rw [hminus, hplus]
  push_cast
  ring

/--
The real-parameter tangent is the Joukowski derivative times the unit-circle
tangent. This is the geometric differential used when pulling back the
counterclockwise contour in docs/6333 §3.
-/
theorem ellipseTangent_eq_joukowski (xi A B u : ℝ) :
    ellipseTangent xi A B u =
      joukowskiDeriv (((A + B) / 2 : ℝ) : ℂ)
        (((A - B) / 2 : ℝ) : ℂ) (circleMap 0 1 u) *
          (circleMap 0 1 u * Complex.I) := by
  let w : ℂ := Complex.exp (Complex.I * (u : ℂ))
  have hw : w ≠ 0 := by
    simp [w]
  have hcircle : circleMap 0 1 u = w := by
    simp [circleMap, w]
    congr 1
    ring
  have hplus : w = Complex.ofReal (Real.cos u) +
      Complex.I * Complex.ofReal (Real.sin u) := by
    dsimp [w]
    rw [show Complex.I * (u : ℂ) = (u : ℂ) * Complex.I by ring,
      Complex.exp_ofReal_mul_I]
    ring
  have hminus : w⁻¹ = Complex.ofReal (Real.cos u) -
      Complex.I * Complex.ofReal (Real.sin u) := by
    dsimp [w]
    rw [← Complex.exp_neg,
      show -(Complex.I * (u : ℂ)) = ((-u : ℝ) : ℂ) * Complex.I by push_cast; ring,
      Complex.exp_ofReal_mul_I]
    simp [Real.cos_neg, Real.sin_neg]
    ring
  have hmul :
      ((((A + B) / 2 : ℝ) : ℂ) -
          (((A - B) / 2 : ℝ) : ℂ) / w ^ 2) * (w * Complex.I) =
        ((((A + B) / 2 : ℝ) : ℂ) * w -
          (((A - B) / 2 : ℝ) : ℂ) * w⁻¹) * Complex.I := by
    field_simp [hw] <;> ring
  calc
    ellipseTangent xi A B u =
        Complex.ofReal (-A * Real.sin u) +
          Complex.I * Complex.ofReal (B * Real.cos u) := rfl
    _ = (((A + B) / 2 : ℝ) : ℂ) * w * Complex.I -
          (((A - B) / 2 : ℝ) : ℂ) * w⁻¹ * Complex.I := by
      rw [hminus, hplus]
      push_cast
      ring_nf
      simp [Complex.I_sq]
    _ = ((((A + B) / 2 : ℝ) : ℂ) * w -
          (((A - B) / 2 : ℝ) : ℂ) * w⁻¹) * Complex.I := by ring
    _ = ((((A + B) / 2 : ℝ) : ℂ) -
          (((A - B) / 2 : ℝ) : ℂ) / w ^ 2) * (w * Complex.I) := hmul.symm
    _ = joukowskiDeriv (((A + B) / 2 : ℝ) : ℂ)
          (((A - B) / 2 : ℝ) : ℂ) (circleMap 0 1 u) *
          (circleMap 0 1 u * Complex.I) := by
      rw [joukowskiDeriv, hcircle]


private theorem joukowski_factorization {xi alpha beta w z1 z2 zeta : ℂ}
    (ha : alpha ≠ 0)
    (hsum : z1 + z2 = (w - xi) / alpha)
    (hprod : z1 * z2 = beta / alpha)
    (hz : zeta ≠ 0) :
    joukowski xi alpha beta zeta - w =
      alpha / zeta * (zeta - z1) * (zeta - z2) := by
  unfold joukowski
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

/--
Partial fractions for the logarithmic derivative of a Joukowski pullback.
This is the exact identity used in docs/6333 (3.1):
`J'/(J-w) = 1/(zeta-z1) + 1/(zeta-z2) - 1/zeta`.
The nonvanishing hypotheses state that the integration path avoids zero and
the two preimages of the pole.  No residue theorem is used.
-/
theorem joukowski_log_deriv_decomp {xi alpha beta w z1 z2 zeta : ℂ}
    (ha : alpha ≠ 0)
    (hsum : z1 + z2 = (w - xi) / alpha)
    (hprod : z1 * z2 = beta / alpha)
    (hz : zeta ≠ 0)
    (h1 : zeta - z1 ≠ 0)
    (h2 : zeta - z2 ≠ 0) :
    joukowskiDeriv alpha beta zeta /
        (joukowski xi alpha beta zeta - w) =
      1 / (zeta - z1) + 1 / (zeta - z2) - 1 / zeta := by
  have hfac := joukowski_factorization ha hsum hprod hz
  have hJ : joukowski xi alpha beta zeta - w ≠ 0 := by
    rw [hfac]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero ha hz) h1) h2
  unfold joukowskiDeriv
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
The unit-circle integral of a Joukowski logarithmic derivative is `2 * pi * I`
when both preimages of the pole lie strictly inside the circle. This supplies
the contour normalization needed in docs/6333 §3 after pulling the ellipse
back through `J`. The circle-pullback and simple-pole integration technique is
informed by the general, non-Li2 development in
`bjbraams/lean-codes@2b8cba1d0201:Carlson/Jacobi/EllipseContour.lean`
(Bastiaan J Braams, Apache-2.0); the statement and proof here are independently
written for our arbitrary affine Joukowski map.
-/
theorem joukowski_log_deriv_unitCircle {xi alpha beta w z1 z2 : ℂ}
    (ha : alpha ≠ 0)
    (hsum : z1 + z2 = (w - xi) / alpha)
    (hprod : z1 * z2 = beta / alpha)
    (h1in : ‖z1‖ < 1) (h2in : ‖z2‖ < 1) :
    ∮ z in C(0, 1),
      joukowskiDeriv alpha beta z / (joukowski xi alpha beta z - w) =
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
  have hbase : CircleIntegrable (fun z : ℂ => (-1 : ℂ) * (z - 0)⁻¹) 0 1 :=
    (hci 0 hzero).const_mul (-1)
  have hsum12 : CircleIntegrable
      (fun z : ℂ => (-1 : ℂ) * (z - 0)⁻¹ + (z - z1)⁻¹) 0 1 :=
    hbase.add (hci z1 hroot1)
  have hboundary : ∀ z ∈ Metric.sphere (0 : ℂ) 1,
      joukowskiDeriv alpha beta z / (joukowski xi alpha beta z - w) =
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
    have hd := joukowski_log_deriv_decomp ha hsum hprod hz0 hz1 hz2
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

end

end ContourKit

end Li2Lean
