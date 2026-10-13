/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.FrequencyLimit

namespace Li2Lean.P0

noncomputable section

/-! The complex contour notation `GmBeta` is exactly the complexification of
the real polynomial value consumed by L1 for any literal family with `a = 2`.
This is the first bridge needed before applying the contour and envelope
identities. -/

theorem ofReal_eval_map_rat (p : Polynomial ℚ) (x : ℝ) :
    Complex.ofReal ((p.map (algebraMap ℚ ℝ)).eval x) =
      Polynomial.eval₂ (algebraMap ℚ ℂ) (Complex.ofReal x) p := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.map_add, Polynomial.eval_add, Complex.ofReal_add,
        Polynomial.eval₂_add, hp, hq]
  | monomial n a =>
      simp [Polynomial.map_monomial, Polynomial.eval_monomial,
        Polynomial.eval₂_monomial]

theorem GmBeta_eq_ofReal_eval {F : P0Family} (hbase : F.a = 2)
    {m : ℕ} (hm4 : 4 ∣ m) :
    GmBeta m = Complex.ofReal ((F.G m).eval (li2InvValue (2 : ℤ))) := by
  rw [F.G_source m hm4, hbase]
  symm
  simpa [GmBeta] using
    (ofReal_eval_map_rat (p0CanonicalPolynomial 2 m)
      (li2InvValue (2 : ℤ)))

theorem norm_GmBeta_eq_eval_abs {F : P0Family} (hbase : F.a = 2)
    {m : ℕ} (hm4 : 4 ∣ m) :
    ‖GmBeta m‖ = |(F.G m).eval (li2InvValue (2 : ℤ))| := by
  rw [GmBeta_eq_ofReal_eval hbase hm4, Complex.norm_real]
  exact Real.norm_eq_abs _

/-!
The signed contour statement and the positive `E` envelope are different
objects.  This interface keeps their bridge explicit instead of replacing the
continuous integral by a finite configuration list.  The field
`signedEnvelope_le` is the actual analytic estimate still needed from the
Andreief, determinant, and C-A bounds.
-/
structure ContinuousCoefficientEnvelopeData (F : P0Family) : Prop where
  base_eq_two : F.a = 2
  signed_formula : ∀ m : ℕ, 0 < m → 4 ∣ m →
    GmBeta m = signedContourRhs m
  signedEnvelope_le : ∀ (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m),
    ‖signedContourRhs m‖ ≤ FrequencyLimit.EInfinity m h4

theorem signed_formula_of_statement
    (hstatement : signedContourStatement) {m : ℕ}
    (hm : 0 < m) (h4 : 4 ∣ m) :
    GmBeta m = signedContourRhs m :=
  (hstatement m hm h4).2

theorem eval_abs_le_EInfinity_of_continuousEnvelope
    {F : P0Family} (D : ContinuousCoefficientEnvelopeData F)
    {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m) :
    |(F.G m).eval (li2InvValue (2 : ℤ))| ≤
      FrequencyLimit.EInfinity m h4 := by
  rw [← norm_GmBeta_eq_eval_abs D.base_eq_two h4]
  rw [D.signed_formula m hm h4]
  exact D.signedEnvelope_le m hm h4

/-! The finite-cutoff conclusion has the paper's replacement factor.  In
particular, it cannot be weakened to `abs(GmBeta) ≤ E m H` without an
additional tail theorem; `E m H` is only a finite frequency cutoff. -/
theorem eval_abs_le_cutoff_of_continuousEnvelope
    {F : P0Family} (D : ContinuousCoefficientEnvelopeData F)
    {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m)
    (hfinite : ∀ H : ℕ, 20 * m ≤ H →
      E m H h4 ≤
        (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4) :
    |(F.G m).eval (li2InvValue (2 : ℤ))| ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) * E m (20 * m) h4 := by
  have hfull := eval_abs_le_EInfinity_of_continuousEnvelope D hm h4
  exact hfull.trans (FrequencyLimit.EInfinity_le_cutoff_of_finiteCutoff
    m hm h4 hfinite)

theorem signed_formula_of_contourStatement
    {F : P0Family} (hbase : F.a = 2)
    (hstatement : signedContourStatement) {m : ℕ}
    (hm : 0 < m) (h4 : 4 ∣ m) :
    GmBeta m = signedContourRhs m := by
  exact signed_formula_of_statement hstatement hm h4

end

end Li2Lean.P0

#print axioms Li2Lean.P0.ofReal_eval_map_rat
#print axioms Li2Lean.P0.GmBeta_eq_ofReal_eval
#print axioms Li2Lean.P0.norm_GmBeta_eq_eval_abs
