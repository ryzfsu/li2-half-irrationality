/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CAInteriorContourPotential
import Li2Lean.P0.ConfigReferenceSymmetry

/-!
# Continuity of the literal pinned first variation

The real segment potentials use the exact endpoint primitive, whose
continuity includes its zero and every density jump. The contour potential
uses the proved interior-root Fejer formula. Restricted to real arguments,
the principal complex square root is continuous even when the
discriminant changes sign or vanishes.
-/

open MeasureTheory Set

namespace Li2Lean.P0

noncomputable section

open Li2Lean.LogSegment
open ConfigSegment ConfigReferenceSymmetry ConfigContourReference
open ConfigInteriorContourPotential ConfigFejerLog

/-- Along the real axis the principal square root has a continuous
two-real-square-root expression, including the branch endpoint zero. -/
theorem continuous_complex_sqrt_ofReal :
    Continuous (fun x : ℝ => Complex.sqrt (x : ℂ)) := by
  simp_rw [Complex.sqrt_eq_real_add_ite]
  simp only [Complex.ofReal_re, Complex.ofReal_im, le_refl, ite_true, one_mul,
    Complex.norm_real, Real.norm_eq_abs]
  fun_prop

theorem continuous_pinnedRootPlus : Continuous pinnedRootPlus := by
  have hd : Continuous pinnedDiscriminant := by
    unfold pinnedDiscriminant
    fun_prop
  unfold pinnedRootPlus
  exact ((Complex.continuous_ofReal.comp
    (continuous_id.sub continuous_const)).add
      (continuous_complex_sqrt_ofReal.comp hd)).div_const _

theorem continuous_pinnedRootMinus : Continuous pinnedRootMinus := by
  have hd : Continuous pinnedDiscriminant := by
    unfold pinnedDiscriminant
    fun_prop
  unfold pinnedRootMinus
  exact ((Complex.continuous_ofReal.comp
    (continuous_id.sub continuous_const)).sub
      (continuous_complex_sqrt_ofReal.comp hd)).div_const _

theorem continuous_fejerLogPolynomial : Continuous fejerLogPolynomial := by
  unfold fejerLogPolynomial
  apply continuous_finsetSum
  intro n hn
  fun_prop

theorem continuous_contourLogPolynomial : Continuous contourLogPolynomial := by
  unfold contourLogPolynomial
  apply continuous_finsetSum
  intro j hj
  exact (Complex.continuous_re.comp
    (continuous_fejerLogPolynomial.comp
      (continuous_id.mul continuous_const))).const_mul _

/-- The actual Fejer contour potential is continuous on the entire real
interval enclosed by the reference ellipse. -/
theorem actualReference_contourPotential_continuousOn_inside :
    ContinuousOn
      (fun x : ℝ => contourReferencePotential (x : ℂ))
      (Set.Icc (0 : ℝ) 2) := by
  have hc : Continuous
      (fun x : ℝ =>
        (267885951940 / 1000000000000 : ℝ) *
          Real.log ConfigContourKernel.contourScale -
          contourLogPolynomial ((starRingEnd ℂ) (pinnedRootPlus x)) -
          contourLogPolynomial ((starRingEnd ℂ) (pinnedRootMinus x))) := by
    exact (continuous_const.sub
      (continuous_contourLogPolynomial.comp
        (Complex.continuous_conj.comp continuous_pinnedRootPlus))).sub
      (continuous_contourLogPolynomial.comp
        (Complex.continuous_conj.comp continuous_pinnedRootMinus))
  apply hc.continuousOn.congr
  intro x hx
  exact contourReferencePotential_inside x hx.1 hx.2

/-- Continuity of the literal first variation, with no regularity premise.
All pinned and segment density endpoints remain in the domain. -/
theorem actualReference_Weta_continuousOn_pinned :
    ContinuousOn
      (fun x : ℝ => Config.Weta actualReference (x : ℂ))
      (Set.Icc (1 / 4 : ℝ) (5 / 4)) := by
  have hA : Continuous (fun x : ℝ => Config.A0 (x : ℂ)) := by
    simp_rw [A0_ofReal_eq_endpoints]
    have hp := continuous_primitive
    fun_prop
  have hPhi : Continuous (fun x : ℝ => Config.phi (x : ℂ)) := by
    simp_rw [phi_ofReal_eq_endpoints]
    have hp := continuous_primitive
    fun_prop
  have hp : Continuous pinnedReferencePotential :=
    continuous_referencePotential (1 / 4) 32 ConfigData.pinnedMassUnits
  have hf : Continuous frequencyReferencePotential :=
    continuous_referencePotential (1 / 2) 160 ConfigData.frequencyMassUnits
  have hc : ContinuousOn
      (fun x : ℝ => contourReferencePotential (x : ℂ))
      (Set.Icc (1 / 4 : ℝ) (5 / 4)) :=
    actualReference_contourPotential_continuousOn_inside.mono
      (by intro x hx; constructor <;> linarith [hx.1, hx.2])
  have hwhole : ContinuousOn
      (fun x : ℝ => Config.A0 (x : ℂ) - Config.phi (x : ℂ) -
        2 * (pinnedReferencePotential x + contourReferencePotential (x : ℂ)) -
        frequencyReferencePotential (-x))
      (Set.Icc (1 / 4 : ℝ) (5 / 4)) :=
    ((hA.continuousOn.sub hPhi.continuousOn).sub
      ((hp.continuousOn.add hc).const_mul 2)).sub
        ((hf.comp continuous_id.neg).continuousOn)
  apply hwhole.congr
  intro x hx
  change Config.A0 (x : ℂ) - Config.phi (x : ℂ) -
      2 * (pinnedReferenceComplexPotential (x : ℂ) +
        contourReferencePotential (x : ℂ)) -
      frequencyReferenceComplexPotential (-(x : ℂ)) = _
  rw [pinnedReferenceComplexPotential_ofReal,
    ← Complex.ofReal_neg, frequencyReferenceComplexPotential_ofReal]

end

end Li2Lean.P0
