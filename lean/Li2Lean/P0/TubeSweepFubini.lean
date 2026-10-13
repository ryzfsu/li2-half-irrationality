/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Tube
import Mathlib.Probability.Kernel.Composition.IntegralCompProd

open MeasureTheory ProbabilityTheory

namespace Li2Lean.P0

noncomputable section

/-- Signed integration through the paper's actual `Measure.bind` sweep.
Mathlib's composition theorem does not require s-finiteness of either kernel;
an a.e. measurable family is replaced only on a source-null set. -/
theorem integral_sweptMeasure (ν : Measure ℂ) (ω : ℂ → Measure ℂ) (f : ℂ → ℝ)
    (hω : AEMeasurable ω ν) (hf : Integrable f (sweptMeasure ν ω)) :
    (∫ y, f y ∂sweptMeasure ν ω) = ∫ z, (∫ y, f y ∂ω z) ∂ν := by
  let κ : Kernel ℂ ℂ := ⟨hω.mk ω, hω.measurable_mk⟩
  have hbind : sweptMeasure ν ω = sweptMeasure ν κ :=
    Measure.bind_congr_right hω.ae_eq_mk
  have hf' : Integrable f (sweptMeasure ν κ) := by simpa only [← hbind] using hf
  have hcomp := ProbabilityTheory.Kernel.integral_comp
    (κ := Kernel.const Unit ν) (η := κ) (a := ()) hf'
  calc
    (∫ y, f y ∂sweptMeasure ν ω) = ∫ y, f y ∂sweptMeasure ν κ := by rw [hbind]
    _ = ∫ z, (∫ y, f y ∂κ z) ∂ν := hcomp
    _ = ∫ z, (∫ y, f y ∂ω z) ∂ν := by
      apply integral_congr_ae
      filter_upwards [hω.ae_eq_mk] with z hz
      change (∫ y, f y ∂hω.mk ω z) = ∫ y, f y ∂ω z
      rw [← hz]

/-- The pre-existing signed-sweep Fubini obligation of v10 `sec-tube.tex`,
with its original full quantifiers and no additional finiteness assumptions. -/
theorem signed_sweep_fubini : signedSweepFubini := by
  intro ν ω f hω _ _ _ hf
  exact integral_sweptMeasure ν ω f hω hf

end
end Li2Lean.P0
