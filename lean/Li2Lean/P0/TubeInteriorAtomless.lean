/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeInteriorPotential

open MeasureTheory ProbabilityTheory Filter

namespace Li2Lean.P0

noncomputable section

/-- Equality of two points on the literal ellipse forces equality of their
parameters modulo its `2*pi` period. -/
theorem gammaPoint_eq_periodic {u v : ℝ} (h : gammaPoint u = gammaPoint v) :
    ∃ n : ℤ, u = v + (n : ℝ) * (2 * Real.pi) := by
  have hJ : joukowski (Complex.exp (Complex.I * (u : ℂ))) =
      joukowski (Complex.exp (Complex.I * (v : ℂ))) := by
    rw [joukowski_unit_circle_eq_gammaPoint, joukowski_unit_circle_eq_gammaPoint, h]
  have hu : 1 ≤ ‖Complex.exp (Complex.I * (u : ℂ))‖ := by
    simp [Complex.norm_exp]
  have hv : 1 ≤ ‖Complex.exp (Complex.I * (v : ℂ))‖ := by
    simp [Complex.norm_exp]
  have hexp : Complex.exp (Complex.I * (u : ℂ)) =
      Complex.exp (Complex.I * (v : ℂ)) :=
    joukowski_injective_exterior hu hv hJ
  obtain ⟨n, hn⟩ := Complex.exp_eq_exp_iff_exists_int.mp hexp
  have him := congrArg Complex.im hn
  dsimp at him
  norm_num at him
  refine ⟨n, ?_⟩
  simpa [mul_add, add_mul, sub_eq_add_neg, mul_assoc] using him

/-- Every fiber of the literal ellipse parametrization is countable. -/
theorem countable_gammaPoint_fiber (x : ℂ) :
    {u : ℝ | gammaPoint u = x}.Countable := by
  classical
  by_cases hx : ∃ v, gammaPoint v = x
  · obtain ⟨v, hv⟩ := hx
    apply (Set.countable_range fun n : ℤ => v + (n : ℝ) * (2 * Real.pi)).mono
    intro u hu
    change gammaPoint u = x at hu
    obtain ⟨n, hn⟩ := gammaPoint_eq_periodic (hu.trans hv.symm)
    exact ⟨n, hn.symm⟩
  · have hEq : {u : ℝ | gammaPoint u = x} = ∅ := by
      ext u
      constructor
      · intro hu
        exact False.elim (hx ⟨u, hu⟩)
      · intro hu
        change False at hu
        exact hu.elim
    rw [hEq]
    exact Set.countable_empty

end

namespace TubeInterior

/-- Every fiber of the actual boundary map used by the strip construction is
countable. Its two nonzero branches invert the logarithmic boundary parameter;
the point zero is included separately because `Real.log 0 = 0`. -/
theorem countable_stripBoundaryPoint_fiber (x : ℂ) :
    {t : ℝ | stripBoundaryPoint t = x}.Countable := by
  classical
  let q : ℝ := annulusWidth / Real.pi
  let k : ℝ := Real.pi / annulusWidth
  let S : Set ℝ := {u | gammaPoint u = x}
  let f : ℝ → ℝ := fun u => Real.exp (k * u)
  let g : ℝ → ℝ := fun u => -Real.exp (-k * u)
  have hk : k * q = 1 := by
    dsimp [k, q]
    field_simp [annulusWidth_pos.ne', Real.pi_ne_zero]
  have hsub : {t : ℝ | stripBoundaryPoint t = x} ⊆
      insert 0 (f '' S ∪ g '' S) := by
    intro t ht
    by_cases ht0 : t = 0
    · exact Set.mem_insert_iff.mpr (Or.inl ht0)
    by_cases htpos : 0 ≤ t
    · let u : ℝ := q * Real.log |t|
      have hparam : gammaPoint u = x := by
        have heval : stripBoundaryPoint t = gammaPoint u := by
          simp [stripBoundaryPoint, u, q, htpos]
        exact heval.symm.trans ht
      have htu : f u = t := by
        dsimp [f, u]
        rw [← mul_assoc, hk, one_mul, abs_of_pos (lt_of_le_of_ne htpos (Ne.symm ht0)),
          Real.exp_log (lt_of_le_of_ne htpos (Ne.symm ht0))]
      exact Set.mem_insert_iff.mpr (Or.inr (Or.inl ⟨u, hparam, htu⟩))
    · have htneg : t < 0 := lt_of_not_ge htpos
      let u : ℝ := -(q * Real.log |t|)
      have hparam : gammaPoint u = x := by
        have heval : stripBoundaryPoint t = gammaPoint u := by
          simp [stripBoundaryPoint, u, q, htpos]
        exact heval.symm.trans ht
      have htu : g u = t := by
        dsimp [g, u]
        have he : Real.exp (-k * - (q * Real.log |t|)) = |t| := by
          rw [neg_mul_neg, ← mul_assoc, hk, one_mul,
            Real.exp_log (abs_pos.mpr (ne_of_lt htneg))]
        rw [he, abs_of_neg htneg]
        ring
      exact Set.mem_insert_iff.mpr (Or.inr (Or.inr ⟨u, hparam, htu⟩))
  exact (Set.countable_insert.mpr
    (((countable_gammaPoint_fiber x).image f).union
      ((countable_gammaPoint_fiber x).image g))).mono hsub

/-- For an interior source point, the actual Cauchy boundary sweep assigns
zero mass to every singleton. The positive scale makes the Cauchy law
absolutely continuous with respect to real Lebesgue measure, and each target
fiber of the literal boundary map is countable. -/
theorem interiorSweep_nullSingleton (z : ℂ) (hz : z ∈ ellipseInterior) :
    NullSingletonClass (interiorSweep z) := by
  constructor
  intro x
  rw [interiorSweep, Measure.map_apply measurable_stripBoundaryPoint
    (measurableSet_singleton x)]
  have hcount := countable_stripBoundaryPoint_fiber x
  have hcauchy : NullSingletonClass
      (cauchyMeasure (stripLocation z) (stripScale z)) := by
    rw [cauchyMeasure_of_scale_ne_zero (stripLocation z) (stripScale_pos hz).ne']
    infer_instance
  exact hcount.measure_zero _

/-- Binding the actual pointwise interior sweep against any source measure
concentrated in the ellipse interior preserves atomlessness. This theorem does
not assert preservation of pair self-energy integrability. -/
theorem swept_interior_nullSingleton (ν : Measure ℂ)
    (hν : ∀ᵐ z ∂ν, z ∈ ellipseInterior) :
    NullSingletonClass (sweptMeasure ν interiorSweep) := by
  constructor
  intro x
  rw [sweptMeasure, Measure.bind_apply (measurableSet_singleton x)
    measurable_interiorSweep.aemeasurable]
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hν] with z hz
  exact (interiorSweep_nullSingleton z hz).measure_singleton x

end TubeInterior
end Li2Lean.P0
