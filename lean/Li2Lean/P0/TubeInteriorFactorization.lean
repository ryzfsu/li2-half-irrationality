/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInterior

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- The exact algebraic relation for the two v10 Joukowski coefficients. -/
theorem ellipseD_eq_ellipseC_mul_ratio : ellipseD = ellipseC * (annulusRatio : ℂ) := by
  norm_num [ellipseD, ellipseC, annulusRatio, semiMajor, semiMinor]

/-- Interchanging the two roots leaves the actual ellipse point unchanged. -/
theorem joukowski_annulus_involution (w : ℂ) (hw : w ≠ 0) :
    joukowski ((annulusRatio : ℂ) / w) = joukowski w := by
  have hρ : (annulusRatio : ℂ) ≠ 0 := by exact_mod_cast annulusRatio_pos.ne'
  unfold joukowski
  rw [ellipseD_eq_ellipseC_mul_ratio]
  field_simp [hw, hρ]
  ring

/-- The inner circle of the preimage annulus covers the same v10 ellipse,
with the opposite angle. This is the second boundary used by the sweep. -/
theorem joukowski_inner_circle_eq_gammaPoint (u : ℝ) :
    joukowski ((annulusRatio : ℂ) * Complex.exp (Complex.I * (u : ℂ))) =
      gammaPoint (-u) := by
  have hexp : Complex.exp (Complex.I * ((-u : ℝ) : ℂ)) =
      (Complex.exp (Complex.I * (u : ℂ)))⁻¹ := by
    rw [← Complex.exp_neg]
    congr 1
    push_cast
    ring
  have h := joukowski_annulus_involution
    (Complex.exp (Complex.I * ((-u : ℝ) : ℂ))) (Complex.exp_ne_zero _)
  calc
    joukowski ((annulusRatio : ℂ) * Complex.exp (Complex.I * (u : ℂ))) =
        joukowski (Complex.exp (Complex.I * ((-u : ℝ) : ℂ))) := by
          simpa only [hexp, div_inv_eq_mul] using h
    _ = gammaPoint (-u) := joukowski_unit_circle_eq_gammaPoint (-u)

/-- Two-root factorization for the literal v10 Joukowski map. A repeated
root at either focus is retained with its multiplicity. -/
theorem joukowski_sub_twoRoot_factorization (w a : ℂ) (hw : w ≠ 0) (ha : a ≠ 0) :
    joukowski w - joukowski a =
      ellipseC * (w - a) * (w - (annulusRatio : ℂ) / a) / w := by
  unfold joukowski
  rw [ellipseD_eq_ellipseC_mul_ratio]
  field_simp [hw, ha]
  ring

/-- Norm form of the exact two-root factorization; no logarithm or
noncollision premise is required. -/
theorem norm_joukowski_sub_twoRoot (w a : ℂ) (hw : w ≠ 0) (ha : a ≠ 0) :
    ‖joukowski w - joukowski a‖ =
      coeffC * ‖w - a‖ * ‖w - (annulusRatio : ℂ) / a‖ / ‖w‖ := by
  rw [joukowski_sub_twoRoot_factorization w a hw ha]
  have hc : ‖ellipseC‖ = coeffC := by
    norm_num [ellipseC, coeffC, semiMajor, semiMinor]
  simp only [norm_div, norm_mul, hc]

/-- Logarithmic decomposition that accounts for both preimage poles and
the annular correction. Noncollision is exactly the stated finite-log case. -/
theorem log_norm_joukowski_sub_twoRoot (w a : ℂ) (hw : w ≠ 0) (ha : a ≠ 0)
    (hneq : joukowski w ≠ joukowski a) :
    Real.log ‖joukowski w - joukowski a‖ =
      Real.log coeffC + Real.log ‖w - a‖ +
        Real.log ‖w - (annulusRatio : ℂ) / a‖ - Real.log ‖w‖ := by
  have hab : w - a ≠ 0 := by
    intro h
    exact hneq (congrArg joukowski (sub_eq_zero.mp h))
  have hother : w - (annulusRatio : ℂ) / a ≠ 0 := by
    intro h
    have hf := joukowski_sub_twoRoot_factorization w a hw ha
    rw [h, mul_zero, zero_div] at hf
    exact hneq (sub_eq_zero.mp hf)
  rw [norm_joukowski_sub_twoRoot w a hw ha,
    Real.log_div (mul_ne_zero (mul_ne_zero coeffC_pos.ne' (norm_ne_zero_iff.mpr hab))
      (norm_ne_zero_iff.mpr hother)) (norm_ne_zero_iff.mpr hw),
    Real.log_mul (mul_ne_zero coeffC_pos.ne' (norm_ne_zero_iff.mpr hab))
      (norm_ne_zero_iff.mpr hother),
    Real.log_mul coeffC_pos.ne' (norm_ne_zero_iff.mpr hab)]

end
end Li2Lean.P0.TubeInterior
