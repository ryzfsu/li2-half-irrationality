/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorMean
import Li2Lean.P0.TubeCollarVariance
import Li2Lean.P0.TubeVarianceSupport

open MeasureTheory ProbabilityTheory

namespace Li2Lean.P0.TubeInterior

noncomputable section

/-- The actual interior Cauchy sweep satisfies the ellipse variance bound. -/
theorem interiorSweep_variance_le {z : ℂ} (hz : z ∈ ellipseInterior) :
    (∫ y, ‖y - z‖ ^ 2 ∂interiorSweep z) ≤
      semiMajor ^ 2 * ellipseLevel z := by
  let μ : Measure ℂ := interiorSweep z
  haveI : IsProbabilityMeasure μ := interiorSweep_isProbability z
  have hμ : ∀ᵐ y ∂μ, y ∈ Gamma := by
    rw [ae_iff]
    change μ Gammaᶜ = 0
    exact interiorSweep_boundary_support z
  exact TubeVariance.variance_le_ellipseLevel μ hμ
    (interiorSweep_barycenter hz)

end
end Li2Lean.P0.TubeInterior
