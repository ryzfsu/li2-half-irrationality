/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.GlobalApproximation
import Li2Lean.P0.ConfigRowCheck

/-!
# E1 certificates for the literal C-A fields

The paper-v10 fields are the three functions selected by
ConfigRowCheck.targetFunction: contour Weta, pinned Weta, and frequency Wmu.
This adapter keeps the global approximation certificate independent of the
row checker while fixing those literal functions as its downstream inputs.
The actual certificates remain to be supplied by the four component workers
(pinned, Fejer contour, external Fourier, and phi).
-/

namespace Li2Lean.P0.ConfigEvaluatorPolynomial

open Li2Lean.Kit.GlobalApproximation
open Li2Lean.P0.ConfigRowCheck

noncomputable section

/-- An E1 certificate for one of the literal C-A W fields on a cell domain. -/
abbrev LiteralCAApproximation (k : CellKind) (domain : Set ℝ) :=
  ComponentApprox (targetFunction k) domain

/-- The semantic lower enclosure consumed by a regular C-A row. -/
theorem literalCA_lower
    {k : CellKind} {domain : Set ℝ}
    (A : LiteralCAApproximation k domain) {x : ℝ} (hx : x ∈ domain)
    {lower : ℝ}
    (hlower : lower ≤ A.field.eval x - (A.epsilon : ℝ)) :
    lower ≤ targetFunction k x :=
  componentApprox_lower A hx hlower

/-- The semantic upper enclosure consumed by a regular C-A row. -/
theorem literalCA_upper
    {k : CellKind} {domain : Set ℝ}
    (A : LiteralCAApproximation k domain) {x : ℝ} (hx : x ∈ domain)
    {upper : ℝ}
    (hupper : A.field.eval x + (A.epsilon : ℝ) ≤ upper) :
    targetFunction k x ≤ upper :=
  componentApprox_upper A hx hupper

/-- The component error budget for a literal C-A field. -/
theorem literalCA_error
    {k : CellKind} {domain : Set ℝ}
    (A : LiteralCAApproximation k domain) {x : ℝ} (hx : x ∈ domain) :
    |targetFunction k x - A.field.eval x| ≤ (A.epsilon : ℝ) :=
  componentApprox_abs_error A hx

/-- The rational derivative budget exposed to the row checker. -/
theorem literalCA_derivative
    {k : CellKind} {domain : Set ℝ}
    (A : LiteralCAApproximation k domain) {x : ℝ} (hx : x ∈ domain) :
    |deriv A.field.eval x| ≤ (A.derivativeBound : ℝ) :=
  componentApprox_derivative_sound A hx

end

end Li2Lean.P0.ConfigEvaluatorPolynomial
