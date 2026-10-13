/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces

/-!
# Elementary regularity for the frequency-envelope integral

The actual ellipse stays disjoint from the real interval `[0,2m]`.
This supplies continuity, and hence finite-cutoff integrability, without
assuming the convergence of the full frequency envelope.
-/

namespace Li2Lean.P0.FrequencyRegularity

noncomputable section

/-- Continuity of the exact scaled parameterization from v10. -/
theorem continuous_ellipsePoint (m : ℕ) : Continuous (p0EllipsePoint m) := by
  unfold p0EllipsePoint
  fun_prop

/-- Continuity of the exact scaled tangent from v10. -/
theorem continuous_ellipseTangent (m : ℕ) : Continuous (p0EllipseTangent m) := by
  unfold p0EllipseTangent
  fun_prop

/-- The actual `F_g(z)=2^z binom(z+g,g)` is continuous everywhere. -/
theorem continuous_entire (g : ℕ) : Continuous (p0Entire g) := by
  unfold p0Entire
  fun_prop

/-- No point of the exact ellipse meets the real interval containing every source pole. -/
theorem ellipsePoint_ne_real (m : ℕ) (hm : 0 < m) (u a : ℝ)
    (ha0 : 0 ≤ a) (ha2 : a ≤ 2 * (m : ℝ)) : p0EllipsePoint m u ≠ (a : ℂ) := by
  intro heq
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hi := congrArg Complex.im heq
  have hr := congrArg Complex.re heq
  norm_num [p0EllipsePoint] at hi hr
  simp only [Complex.sin_ofReal_re, Complex.cos_ofReal_re] at hi hr
  have hsin : Real.sin u = 0 := hi.resolve_left (by omega)
  have hcos : (Real.cos u - 1) * (Real.cos u + 1) = 0 := by
    nlinarith [Real.sin_sq_add_cos_sq u]
  rcases mul_eq_zero.mp hcos with hc | hc <;> nlinarith

/-- Any continuous finite-parameter integrand is integrable on the exact parameter box. -/
theorem integrable_parameter {d : ℕ} {f : (Fin d → ℝ) → ℝ} (hf : Continuous f) :
    MeasureTheory.Integrable f (MeasureTheory.Measure.pi
      (fun _ : Fin d => MeasureTheory.volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi)))) := by
  rw [← MeasureTheory.Measure.restrict_pi_pi]
  exact hf.continuousOn.integrableOn_compact
    (isCompact_univ_pi (fun _ => isCompact_Icc))

end

end Li2Lean.P0.FrequencyRegularity
