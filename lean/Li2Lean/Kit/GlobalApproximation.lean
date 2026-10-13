/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Global polynomial and trigonometric approximation interfaces

This file packages the E1 evaluator plan for the literal C-A fields in paper
v10: every component is represented by an explicit rational polynomial or a
finite rational trigonometric polynomial, with a uniform rational error and a
rational derivative certificate on the cell domain.

The finite-sum error lemmas are deliberately problem-agnostic. Their intended
instantiations are the pinned x log x/atan pieces, the degree-48 Fejer
component, the external Fourier component, and the phi component in
ConfigRowCheck. Endpoint x log x terms remain separate endpoint
certificates.

The organization is informed by the evaluator pattern in
openai/math@fd4aeeb2ee4f (Catalan 005), especially its finite potential and
interval soundness layers. No source file or Li2-specific Lean code is copied.
-/

namespace Li2Lean.Kit.GlobalApproximation

open scoped BigOperators

noncomputable section

/-- A finite explicit rational polynomial, with coefficients in ascending
degree order. The empty list denotes zero. -/
def rationalPolynomial (coeffs : List ℚ) : Polynomial ℚ :=
  coeffs.foldr (fun a p => Polynomial.C a + Polynomial.X * p) 0

/-- Evaluation of a rational polynomial at a real point. -/
def rationalPolynomialEval (coeffs : List ℚ) (x : ℝ) : ℝ :=
  Polynomial.eval₂ (Rat.castHom ℝ) x (rationalPolynomial coeffs)

/-- A finite rational trigonometric polynomial. The coefficient at index
n multiplies cos ((n+1)x) or sin ((n+1)x). -/
def rationalTrigEval (constant : ℚ) (cosCoeffs sinCoeffs : List ℚ) (x : ℝ) : ℝ :=
  (constant : ℝ) +
    (∑ n ∈ Finset.range cosCoeffs.length,
      (cosCoeffs.getD n 0 : ℝ) *
        Real.cos (((n + 1 : ℕ) : ℝ) * x)) +
    (∑ n ∈ Finset.range sinCoeffs.length,
      (sinCoeffs.getD n 0 : ℝ) *
        Real.sin (((n + 1 : ℕ) : ℝ) * x))

/-- The two explicit forms used by the C-A evaluator. -/
inductive ExplicitField
  | polynomial (coeffs : List ℚ)
  | trigonometric (constant : ℚ) (cosCoeffs sinCoeffs : List ℚ)
  deriving DecidableEq, Repr

namespace ExplicitField

/-- Evaluation of an explicit rational field. -/
def eval : ExplicitField → ℝ → ℝ
  | .polynomial coeffs => rationalPolynomialEval coeffs
  | .trigonometric constant cosCoeffs sinCoeffs => rationalTrigEval constant cosCoeffs sinCoeffs

@[simp] theorem eval_polynomial (coeffs : List ℚ) (x : ℝ) :
    eval (.polynomial coeffs) x = rationalPolynomialEval coeffs x := rfl

@[simp] theorem eval_trigonometric (c : ℚ) (a b : List ℚ) (x : ℝ) :
    eval (.trigonometric c a b) x = rationalTrigEval c a b x := rfl

end ExplicitField

/-- A rational derivative bound for an explicit field on a specified domain. -/
structure DerivativeCertificate (P : ℝ → ℝ) (domain : Set ℝ) where
  bound : ℚ
  bound_nonneg : 0 ≤ bound
  sound : ∀ x, x ∈ domain → |deriv P x| ≤ (bound : ℝ)

/-- E1 global approximation certificate.

field is the exact finite rational/trigonometric expression used by the
checker; epsilon and derivativeBound are rational budgets. The error
bound is uniform on domain, and derivative is a separately checkable
rational certificate. -/
structure GlobalApproximation (f : ℝ → ℝ) (domain : Set ℝ) where
  field : ExplicitField
  epsilon : ℚ
  derivativeBound : ℚ
  epsilon_nonneg : 0 ≤ epsilon
  derivativeBound_nonneg : 0 ≤ derivativeBound
  error : ∀ x, x ∈ domain →
    |f x - field.eval x| ≤ (epsilon : ℝ)
  derivative : DerivativeCertificate field.eval domain
  derivative_bound_eq : derivative.bound = derivativeBound

/-- The component certificate used for one literal C-A summand. -/
abbrev ComponentApprox := GlobalApproximation

theorem componentApprox_sound
    {f : ℝ → ℝ} {domain : Set ℝ}
    (A : ComponentApprox f domain) {x : ℝ} (hx : x ∈ domain) :
    (A.field.eval x - (A.epsilon : ℝ) ≤ f x) ∧
      (f x ≤ A.field.eval x + (A.epsilon : ℝ)) := by
  have h := A.error x hx
  constructor <;> linarith [neg_abs_le (f x - A.field.eval x),
    le_abs_self (f x - A.field.eval x)]

theorem componentApprox_abs_error
    {f : ℝ → ℝ} {domain : Set ℝ}
    (A : ComponentApprox f domain) {x : ℝ} (hx : x ∈ domain) :
    |f x - A.field.eval x| ≤ (A.epsilon : ℝ) :=
  A.error x hx

theorem componentApprox_derivative_sound
    {f : ℝ → ℝ} {domain : Set ℝ}
    (A : ComponentApprox f domain) {x : ℝ} (hx : x ∈ domain) :
    |deriv A.field.eval x| ≤ (A.derivativeBound : ℝ) := by
  rw [← A.derivative_bound_eq]
  exact A.derivative.sound x hx

/-- Finite component errors add without any analytic assumption on the
component functions. This is the assembly lemma for Weta and Wmu. -/
theorem finite_sum_componentApprox_sound
    {ι : Type*} {s : Finset ι} {domain : Set ℝ}
    {f p : ι → ℝ → ℝ} {eps : ι → ℚ}
    (h : ∀ i ∈ s, ∀ x ∈ domain, |f i x - p i x| ≤ (eps i : ℝ))
    {x : ℝ} (hx : x ∈ domain) :
    |(∑ i ∈ s, f i x) - (∑ i ∈ s, p i x)| ≤
      ∑ i ∈ s, (eps i : ℝ) := by
  rw [← Finset.sum_sub_distrib]
  calc
    |∑ i ∈ s, (f i x - p i x)| ≤
        ∑ i ∈ s, |f i x - p i x| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (eps i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact h i hi x hx

/-- Rational derivative budgets add when component derivative certificates are
available. This is the derivative half of the E1 assembly step. -/
theorem finite_sum_derivative_bound
    {ι : Type*} {s : Finset ι} {domain : Set ℝ}
    {p : ι → ℝ → ℝ} {bounds : ι → ℚ}
    (h : ∀ i ∈ s, ∀ x ∈ domain, |deriv (p i) x| ≤ (bounds i : ℝ))
    {x : ℝ} (hx : x ∈ domain)
    (hsum :
      HasDerivAt (fun y => ∑ i ∈ s, p i y)
        (∑ i ∈ s, deriv (p i) x) x) :
    |deriv (fun y => ∑ i ∈ s, p i y) x| ≤
      ∑ i ∈ s, (bounds i : ℝ) := by
  rw [hsum.deriv]
  calc
    |∑ i ∈ s, deriv (p i) x| ≤
        ∑ i ∈ s, |deriv (p i) x| := by
          exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ s, (bounds i : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact h i hi x hx

/-- A direct lower enclosure from a component approximation. -/
theorem componentApprox_lower
    {f : ℝ → ℝ} {domain : Set ℝ}
    (A : ComponentApprox f domain) {x : ℝ} (hx : x ∈ domain)
    {lower : ℝ} (hlower : lower ≤ A.field.eval x - (A.epsilon : ℝ)) :
    lower ≤ f x :=
  hlower.trans (componentApprox_sound A hx).1

/-- A direct upper enclosure from a component approximation. -/
theorem componentApprox_upper
    {f : ℝ → ℝ} {domain : Set ℝ}
    (A : ComponentApprox f domain) {x : ℝ} (hx : x ∈ domain)
    {upper : ℝ} (hupper : A.field.eval x + (A.epsilon : ℝ) ≤ upper) :
    f x ≤ upper :=
  (componentApprox_sound A hx).2.trans hupper

end

end Li2Lean.Kit.GlobalApproximation

