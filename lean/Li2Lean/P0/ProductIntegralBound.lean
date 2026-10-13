/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour

open MeasureTheory

namespace Li2Lean.P0

noncomputable section

/-- The total mass of a finite product measure is the corresponding power
of the one-coordinate mass. -/
theorem pi_real_mass_eq_pow {ι α : Type*} [Fintype ι] [MeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasure μ] :
    (Measure.pi (fun _ : ι => μ)).real Set.univ = (μ.real Set.univ) ^ Fintype.card ι := by
  letI : SigmaFinite μ := IsFiniteMeasure.toSigmaFinite μ
  have hpi := Measure.pi_univ (fun _ : ι => μ)
  rw [Measure.real_def, hpi, ENNReal.toReal_prod]
  simp [Measure.real_def]

/-- A pointwise uniform bound controls the norm of the integral over a finite
product measure by the product-space mass times the same bound. -/
theorem norm_integral_pi_le_mass_pow_mul {ι α : Type*} [Fintype ι]
    [MeasurableSpace α] (μ : Measure α) [IsFiniteMeasure μ]
    (F : (ι → α) → ℂ) (B : ℝ)
    (hF : Integrable F (Measure.pi (fun _ : ι => μ)))
    (hbound : ∀ x, ‖F x‖ ≤ B) :
    ‖∫ x, F x ∂(Measure.pi (fun _ : ι => μ))‖ ≤
      (μ.real Set.univ) ^ Fintype.card ι * B := by
  let ν := Measure.pi (fun _ : ι => μ)
  letI : ∀ i : ι, SigmaFinite μ := fun _ => IsFiniteMeasure.toSigmaFinite μ
  have hnorm : Integrable (fun x => ‖F x‖) ν := hF.norm
  have hconst : Integrable (fun _ : (ι → α) => B) ν := integrable_const B
  calc
    ‖∫ x, F x ∂ν‖ ≤ ∫ x, ‖F x‖ ∂ν := norm_integral_le_integral_norm F
    _ ≤ ∫ _x, B ∂ν := integral_mono hnorm hconst hbound
    _ = ν.real Set.univ * B := by simp [ν, Measure.real_def, smul_eq_mul]
    _ = (μ.real Set.univ) ^ Fintype.card ι * B := by
      rw [pi_real_mass_eq_pow]

end

end Li2Lean.P0

#print axioms Li2Lean.P0.pi_real_mass_eq_pow
#print axioms Li2Lean.P0.norm_integral_pi_le_mass_pow_mul
