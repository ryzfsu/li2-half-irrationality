/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourFormula
import Li2Lean.P0.JoukowskiPoleRange

/-!
# C-A contour potential at pinned real points

The real pinned interval lies strictly inside the v10 ellipse.  Its two
Joukowski preimages are therefore strictly inside the unit disk, so the
actual contour potential is a finite Fejer moment expression obtained from
the Taylor-log transform.  This is separate from the diagonal-singular
boundary self-potential Fourier obligation.
-/

open MeasureTheory

namespace Li2Lean.P0.ConfigInteriorContourPotential

noncomputable section

open ConfigContourReference ConfigContourKernel ConfigFejerMass ConfigFejerLog

/-- The discriminant of the actual v10 Joukowski quadratic over a real point. -/
def pinnedDiscriminant (x : ℝ) : ℝ :=
  (P0ContourLeaf.xi - x) ^ 2 - 4 * P0ContourLeaf.alpha * P0ContourLeaf.beta

/-- The two literal quadratic preimages, retained with multiplicity. -/
def pinnedRootPlus (x : ℝ) : ℂ :=
  (((x - P0ContourLeaf.xi : ℝ) : ℂ) +
    Complex.sqrt (pinnedDiscriminant x : ℂ)) /
      (2 * (P0ContourLeaf.alpha : ℂ))

def pinnedRootMinus (x : ℝ) : ℂ :=
  (((x - P0ContourLeaf.xi : ℝ) : ℂ) -
    Complex.sqrt (pinnedDiscriminant x : ℂ)) /
      (2 * (P0ContourLeaf.alpha : ℂ))

theorem pinned_alpha_eq_contourScale :
    P0ContourLeaf.alpha = contourScale := by
  norm_num [P0ContourLeaf.alpha, P0ContourLeaf.axisA,
    P0ContourLeaf.axisB, ConfigContourKernel.contourScale]

theorem pinned_beta_eq_scale_mul_ratio :
    P0ContourLeaf.beta = contourScale * contourRatio := by
  norm_num [P0ContourLeaf.beta, P0ContourLeaf.axisA,
    P0ContourLeaf.axisB, ConfigContourKernel.contourScale,
    ConfigContourKernel.contourRatio]

theorem pinned_xi_eq_center : P0ContourLeaf.xi = 11281 / 10000 := by
  norm_num [P0ContourLeaf.xi]

theorem pinnedRootPlus_pole (x : ℝ) :
    P0ContourLeaf.polePolynomial x (pinnedRootPlus x) = 0 := by
  have hs : Complex.sqrt (pinnedDiscriminant x : ℂ) ^ 2 =
      (pinnedDiscriminant x : ℂ) := by
    simpa only [Complex.sqrt] using
      Complex.cpow_ofNat_inv_pow (pinnedDiscriminant x : ℂ) 2
  unfold pinnedDiscriminant at hs
  push_cast at hs
  have ha : (P0ContourLeaf.alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by norm_num [P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]))
  unfold P0ContourLeaf.polePolynomial pinnedRootPlus pinnedDiscriminant
  field_simp [ha]
  push_cast
  linear_combination hs

theorem pinnedRootMinus_pole (x : ℝ) :
    P0ContourLeaf.polePolynomial x (pinnedRootMinus x) = 0 := by
  have hs : Complex.sqrt (pinnedDiscriminant x : ℂ) ^ 2 =
      (pinnedDiscriminant x : ℂ) := by
    simpa only [Complex.sqrt] using
      Complex.cpow_ofNat_inv_pow (pinnedDiscriminant x : ℂ) 2
  unfold pinnedDiscriminant at hs
  push_cast at hs
  have ha : (P0ContourLeaf.alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by norm_num [P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]))
  unfold P0ContourLeaf.polePolynomial pinnedRootMinus pinnedDiscriminant
  field_simp [ha]
  push_cast
  linear_combination hs

theorem pinnedRootPlus_norm_lt_one {x : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) : ‖pinnedRootPlus x‖ < 1 :=
  P0ContourLeaf.pole_preimage_mem_unitDisk hx0 hx2 _ (pinnedRootPlus_pole x)

theorem pinnedRootMinus_norm_lt_one {x : ℝ}
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) : ‖pinnedRootMinus x‖ < 1 :=
  P0ContourLeaf.pole_preimage_mem_unitDisk hx0 hx2 _ (pinnedRootMinus_pole x)

theorem pinnedRoots_sum (x : ℝ) :
    pinnedRootPlus x + pinnedRootMinus x =
      ((x - P0ContourLeaf.xi : ℝ) : ℂ) /
        (P0ContourLeaf.alpha : ℂ) := by
  unfold pinnedRootPlus pinnedRootMinus
  have ha : (P0ContourLeaf.alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by norm_num [P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]))
  field_simp [ha]
  ring

theorem pinnedRoots_product (x : ℝ) :
    pinnedRootPlus x * pinnedRootMinus x =
      (P0ContourLeaf.beta : ℂ) / (P0ContourLeaf.alpha : ℂ) := by
  have hs : Complex.sqrt (pinnedDiscriminant x : ℂ) ^ 2 =
      (pinnedDiscriminant x : ℂ) := by
    simpa only [Complex.sqrt] using
      Complex.cpow_ofNat_inv_pow (pinnedDiscriminant x : ℂ) 2
  unfold pinnedDiscriminant at hs
  push_cast at hs
  unfold pinnedRootPlus pinnedRootMinus pinnedDiscriminant
  have ha : (P0ContourLeaf.alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by norm_num [P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]))
  field_simp [ha]
  push_cast
  linear_combination -1 * hs

theorem alpha_mul_root_sum (x : ℝ) :
    (P0ContourLeaf.alpha : ℂ) *
        (pinnedRootPlus x + pinnedRootMinus x) =
      ((x - P0ContourLeaf.xi : ℝ) : ℂ) := by
  rw [pinnedRoots_sum]
  have ha : (P0ContourLeaf.alpha : ℂ) ≠ 0 := by
    exact_mod_cast (ne_of_gt (by norm_num [P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]))
  field_simp [ha]

theorem alpha_mul_root_product (x : ℝ) :
    (P0ContourLeaf.alpha : ℂ) *
        pinnedRootPlus x * pinnedRootMinus x = (P0ContourLeaf.beta : ℂ) := by
  calc
    (P0ContourLeaf.alpha : ℂ) * pinnedRootPlus x * pinnedRootMinus x =
        (P0ContourLeaf.alpha : ℂ) *
          (pinnedRootPlus x * pinnedRootMinus x) := by ring
    _ = (P0ContourLeaf.alpha : ℂ) *
          ((P0ContourLeaf.beta : ℂ) / (P0ContourLeaf.alpha : ℂ)) := by
      rw [pinnedRoots_product]
    _ = (P0ContourLeaf.beta : ℂ) := by
      have ha : (P0ContourLeaf.alpha : ℂ) ≠ 0 := by
        exact_mod_cast (ne_of_gt (by norm_num [P0ContourLeaf.alpha,
          P0ContourLeaf.axisA, P0ContourLeaf.axisB]))
      field_simp

/-- Root factorization of the actual contour distance for real x. -/
theorem ellipse_difference_pinned_roots (x : ℝ) (v : ℝ) :
    Li2Lean.p0EllipsePoint 1 v - (x : ℂ) =
      (P0ContourLeaf.alpha : ℂ) * ConfigContourKernel.phase v *
        (1 - pinnedRootPlus x / ConfigContourKernel.phase v) *
        (1 - pinnedRootMinus x / ConfigContourKernel.phase v) := by
  have hs := alpha_mul_root_sum x
  have hp := alpha_mul_root_product x
  rw [pinned_alpha_eq_contourScale] at hs
  rw [pinned_alpha_eq_contourScale] at hp
  rw [ConfigContourKernel.ellipse_eq_joukowski]
  have hz := ConfigContourKernel.phase_ne_zero v
  rw [pinned_alpha_eq_contourScale]
  field_simp [hz]
  have hs' : (contourScale : ℂ) *
      (pinnedRootPlus x + pinnedRootMinus x) =
        (x : ℂ) - (11281 / 10000 : ℂ) := by
    simpa [pinned_xi_eq_center, Complex.ofReal_sub] using hs
  have hp' : (contourScale : ℂ) *
      pinnedRootPlus x * pinnedRootMinus x =
        ((contourScale * contourRatio : ℝ) : ℂ) := by
    simpa [pinned_beta_eq_scale_mul_ratio] using hp
  linear_combination (10000 * ConfigContourKernel.phase v) * hs' -
    10000 * hp'

theorem log_norm_inverse_phase_complex (a : ℂ) (v : ℝ) :
    Real.log ‖1 - a / ConfigContourKernel.phase v‖ =
      Real.log ‖1 - (starRingEnd ℂ) a * ConfigContourKernel.phase v‖ := by
  rw [div_eq_mul_inv,
    Complex.inv_eq_conj (ConfigContourKernel.norm_phase v)]
  have h : 1 - a * (starRingEnd ℂ) (ConfigContourKernel.phase v) =
      (starRingEnd ℂ) (1 - (starRingEnd ℂ) a * ConfigContourKernel.phase v) := by
    simp
  rw [h, Complex.norm_conj]

theorem log_factor_ne_zero_of_norm_lt_one {a : ℂ} (ha : ‖a‖ < 1) (v : ℝ) :
    1 - a * ConfigContourKernel.phase v ≠ 0 := by
  intro h
  have hn := congrArg norm (sub_eq_zero.mp h)
  rw [norm_one, norm_mul, ConfigContourKernel.norm_phase, mul_one] at hn
  linarith

/-- The true contour potential for every pinned real point is evaluated from
the two interior roots and the literal degree-48 Fejer moments.  In contrast
to the contour-boundary self-potential, no collision or Abel-limit premise is
needed on this interval. -/
theorem contourReferencePotential_inside (x : ℝ)
    (hx0 : 0 ≤ x) (hx2 : x ≤ 2) :
    ConfigContourReference.contourReferencePotential (x : ℂ) =
      (267885951940 / 1000000000000 : ℝ) *
        Real.log ConfigContourKernel.contourScale -
        ConfigFejerLog.contourLogPolynomial
          ((starRingEnd ℂ) (pinnedRootPlus x)) -
      ConfigFejerLog.contourLogPolynomial
          ((starRingEnd ℂ) (pinnedRootMinus x)) := by
  have hr1 := pinnedRootPlus_norm_lt_one hx0 hx2
  have hr2 := pinnedRootMinus_norm_lt_one hx0 hx2
  have h1 : ‖(starRingEnd ℂ) (pinnedRootPlus x)‖ < 1 := by
    simpa only [Complex.norm_conj] using hr1
  have h2 : ‖(starRingEnd ℂ) (pinnedRootMinus x)‖ < 1 := by
    simpa only [Complex.norm_conj] using hr2
  have hconst : IntervalIntegrable
      (fun v : ℝ => ConfigContourReference.contourDensity v *
        Real.log ConfigContourKernel.contourScale) volume 0 (2 * Real.pi) := by
    exact (ConfigContourFormula.continuous_contourDensity.mul continuous_const).intervalIntegrable _ _
  have hterm1 : IntervalIntegrable
      (fun v : ℝ => ConfigContourReference.contourDensity v *
        Real.log ‖1 - (starRingEnd ℂ) (pinnedRootPlus x) *
          ConfigContourKernel.phase v‖) volume 0 (2 * Real.pi) := by
    exact (ConfigContourFormula.continuous_contourDensity.mul
      (ConfigFejerLog.continuous_log_norm h1)).intervalIntegrable _ _
  have hterm2 : IntervalIntegrable
      (fun v : ℝ => ConfigContourReference.contourDensity v *
        Real.log ‖1 - (starRingEnd ℂ) (pinnedRootMinus x) *
          ConfigContourKernel.phase v‖) volume 0 (2 * Real.pi) := by
    exact (ConfigContourFormula.continuous_contourDensity.mul
      (ConfigFejerLog.continuous_log_norm h2)).intervalIntegrable _ _
  have hdist (v : ℝ) :
      Real.log ‖(x : ℂ) - Li2Lean.p0EllipsePoint 1 v‖ =
        Real.log ConfigContourKernel.contourScale +
          Real.log ‖1 - (starRingEnd ℂ) (pinnedRootPlus x) *
            ConfigContourKernel.phase v‖ +
          Real.log ‖1 - (starRingEnd ℂ) (pinnedRootMinus x) *
            ConfigContourKernel.phase v‖ := by
    have hfact := ellipse_difference_pinned_roots x v
    have hnorm :
        ‖(x : ℂ) - Li2Lean.p0EllipsePoint 1 v‖ =
          ConfigContourKernel.contourScale *
            ‖1 - pinnedRootPlus x / ConfigContourKernel.phase v‖ *
            ‖1 - pinnedRootMinus x / ConfigContourKernel.phase v‖ := by
      rw [show (x : ℂ) - Li2Lean.p0EllipsePoint 1 v =
        -(Li2Lean.p0EllipsePoint 1 v - (x : ℂ)) by ring,
        norm_neg, hfact, norm_mul, norm_mul, norm_mul,
        pinned_alpha_eq_contourScale,
        Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (by norm_num [ConfigContourKernel.contourScale]),
        ConfigContourKernel.norm_phase]
      ring
    have ha1 : ‖(starRingEnd ℂ) (pinnedRootPlus x)‖ < 1 := h1
    have ha2 : ‖(starRingEnd ℂ) (pinnedRootMinus x)‖ < 1 := h2
    have hn1 : ‖1 - pinnedRootPlus x / ConfigContourKernel.phase v‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro hzero
      have h' : ConfigContourKernel.phase v = pinnedRootPlus x := by
        have hdiv : pinnedRootPlus x / ConfigContourKernel.phase v = 1 :=
          (sub_eq_zero.mp hzero).symm
        have := (div_eq_iff (ConfigContourKernel.phase_ne_zero v)).mp hdiv
        simpa using this.symm
      have := congrArg norm h'
      rw [ConfigContourKernel.norm_phase] at this
      linarith [hr1]
    have hn2 : ‖1 - pinnedRootMinus x / ConfigContourKernel.phase v‖ ≠ 0 := by
      apply norm_ne_zero_iff.mpr
      intro hzero
      have h' : ConfigContourKernel.phase v = pinnedRootMinus x := by
        have hdiv : pinnedRootMinus x / ConfigContourKernel.phase v = 1 :=
          (sub_eq_zero.mp hzero).symm
        have := (div_eq_iff (ConfigContourKernel.phase_ne_zero v)).mp hdiv
        simpa using this.symm
      have := congrArg norm h'
      rw [ConfigContourKernel.norm_phase] at this
      linarith [hr2]
    rw [hnorm, Real.log_mul
      (mul_ne_zero (ne_of_gt (by norm_num [ConfigContourKernel.contourScale])) hn1)
      hn2,
      Real.log_mul (ne_of_gt (by norm_num [ConfigContourKernel.contourScale])) hn1,
      log_norm_inverse_phase_complex, log_norm_inverse_phase_complex]
  unfold ConfigContourReference.contourReferencePotential
    ConfigContourReference.contourReferenceIntegral
  simp_rw [hdist, mul_add]
  rw [intervalIntegral.integral_add (hconst.add hterm1) hterm2,
    intervalIntegral.integral_add hconst hterm1,
    intervalIntegral.integral_mul_const,
    ConfigFejerMass.integral_contourDensity,
    ConfigFejerLog.integral_contourDensity_log_norm h1,
    ConfigFejerLog.integral_contourDensity_log_norm h2]
  have hp : 2 * Real.pi ≠ 0 := by positivity
  have hmass := ConfigFejerMass.contourWeight_sum
  rw [hmass]
  field_simp
  unfold ConfigFejerLog.contourLogPolynomial
  ring

theorem contourReferencePotential_pinned_interval (x : ℝ)
    (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 5 / 4) :
    ConfigContourReference.contourReferencePotential (x : ℂ) =
      (267885951940 / 1000000000000 : ℝ) *
        Real.log ConfigContourKernel.contourScale -
        ConfigFejerLog.contourLogPolynomial
          ((starRingEnd ℂ) (pinnedRootPlus x)) -
      ConfigFejerLog.contourLogPolynomial
          ((starRingEnd ℂ) (pinnedRootMinus x)) := by
  apply contourReferencePotential_inside
  · linarith
  · linarith

end

end Li2Lean.P0.ConfigInteriorContourPotential
