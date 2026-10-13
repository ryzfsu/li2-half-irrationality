/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigContourFormula
import Li2Lean.P0.ConfigSegment

/-!
# Exact exterior contour primitives

These are elementary endpoint primitives for the actual contour potential on
the negative frequency axis. They preserve the finite Fejer formula and its
literal scale and ratio. No numerical enclosure is assumed.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.ActualReferenceQLogOutside

noncomputable section

open ConfigContourReference ConfigContourKernel ConfigFejerLog ConfigContourFormula ConfigSegment

/-- The product in the exterior Joukowski quadratic. -/
def outsideProduct : ℝ := contourScale ^ 2 * contourRatio

/-- The derivative of the exterior inverse Joukowski radius. -/
def outsideRadiusDerivative (t : ℝ) : ℝ :=
  outsideRadius t /
    Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct)

theorem outside_discriminant_pos {t : ℝ} (ht : 1 / 2 ≤ t) :
    0 < (t + 11281 / 10000) ^ 2 - 4 * outsideProduct := by
  norm_num [outsideProduct, contourScale, contourRatio]
  nlinarith [sq_nonneg (t - 1 / 2)]

theorem hasDerivAt_outsideRadius {t : ℝ} (ht : 1 / 2 ≤ t) :
    HasDerivAt outsideRadius (outsideRadiusDerivative t) t := by
  have hs := outside_discriminant_pos ht
  have hr : Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) ≠ 0 :=
    (Real.sqrt_pos.2 hs).ne'
  have hd := ((((hasDerivAt_id t).add_const (11281 / 10000 : ℝ)).pow 2).sub_const
    (4 * outsideProduct)).sqrt hs.ne'
  have h := (((hasDerivAt_id t).add_const (11281 / 10000 : ℝ)).add hd).div_const 2
  have heq : outsideRadius = fun s : ℝ =>
      (s + 11281 / 10000 +
        Real.sqrt ((s + 11281 / 10000) ^ 2 - 4 * outsideProduct)) / 2 := by
    funext s
    simp only [outsideRadius, outsideProduct, mul_assoc]
  convert h using 1
  · exact heq
  · unfold outsideRadiusDerivative
    rw [heq]
    norm_num only [Nat.cast_ofNat, id_eq, Pi.pow_apply, pow_one, mul_one]
    generalize hS : Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) = S at *
    field_simp [hr]
    ring

theorem outsideRadius_jacobian {t : ℝ} (ht : 1 / 2 ≤ t) :
    (1 - outsideProduct / outsideRadius t ^ 2) * outsideRadiusDerivative t = 1 := by
  have hR : outsideRadius t ≠ 0 := (outsideRadius_pos ht).ne'
  have hs := outside_discriminant_pos ht
  have hS : Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) ≠ 0 :=
    (Real.sqrt_pos.2 hs).ne'
  have hquad := outsideRadius_quadratic ht
  change outsideRadius t ^ 2 - (t + 11281 / 10000) * outsideRadius t +
    outsideProduct = 0 at hquad
  have hlinear : 2 * outsideRadius t =
      t + 11281 / 10000 +
        Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) := by
    unfold outsideRadius outsideProduct
    ring
  unfold outsideRadiusDerivative
  generalize hS' : Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) = S at *
  generalize hR' : outsideRadius t = R at *
  field_simp [hR, hS]
  linear_combination R * hlinear - hquad

theorem outsideRadius_joukowski {t : ℝ} (ht : 1 / 2 ≤ t) :
    outsideRadius t + outsideProduct / outsideRadius t = t + 11281 / 10000 := by
  have hR : outsideRadius t ≠ 0 := (outsideRadius_pos ht).ne'
  have hquad := outsideRadius_quadratic ht
  change outsideRadius t ^ 2 - (t + 11281 / 10000) * outsideRadius t +
    outsideProduct = 0 at hquad
  field_simp [hR]
  linear_combination 10000 * hquad

theorem outsideRadius_sqrt {t : ℝ} (ht : 1 / 2 ≤ t) :
    outsideRadius t - outsideProduct / outsideRadius t =
      Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) := by
  have hlinear : 2 * outsideRadius t =
      t + 11281 / 10000 +
        Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) := by
    unfold outsideRadius outsideProduct
    ring
  nth_rw 1 [← outsideRadius_joukowski ht] at hlinear
  linarith

/-- A natural reciprocal-power primitive, used for all orders at least two. -/
def reciprocalPowerPrimitive (k : ℕ) (R : ℝ) : ℝ :=
  -(R⁻¹) ^ (k + 1) / (k + 1 : ℝ)

theorem hasDerivAt_reciprocalPowerPrimitive (k : ℕ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (reciprocalPowerPrimitive k) ((R⁻¹) ^ (k + 2)) R := by
  have hI : HasDerivAt (fun x : ℝ => x⁻¹) (-(R⁻¹) ^ 2) R := by
    have h := (hasDerivAt_id R).inv hR
    refine h.congr_deriv ?_
    simp only [id_eq, div_eq_mul_inv, inv_pow]
    ring
  have h := ((hI.pow (k + 1)).neg).div_const (k + 1 : ℝ)
  have hk : (k + 1 : ℝ) ≠ 0 := by positivity
  refine h.congr_deriv ?_
  simp only [Nat.add_sub_cancel, Nat.cast_add, Nat.cast_one]
  rw [pow_add]
  field_simp [hk]

/-- Primitive in the radius variable of the logarithmic mass term. -/
def outsideLogPrimitive (R : ℝ) : ℝ :=
  R * Real.log R - R + outsideProduct * (Real.log R + 1) * R⁻¹

theorem hasDerivAt_outsideLogPrimitive {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt outsideLogPrimitive
      (Real.log R * (1 - outsideProduct / R ^ 2)) R := by
  have hid := hasDerivAt_id R
  have hlog := hid.log hR
  have hI := hid.inv hR
  have h := ((hid.mul hlog).sub hid).add
    (((hlog.add_const 1).const_mul outsideProduct).mul hI)
  refine h.congr_deriv ?_
  simp only [id_eq, Pi.inv_apply]
  field_simp [hR]
  ring

/-- The stable logarithmic endpoint form used by rational enclosures. -/
theorem outsideLogPrimitive_eq {t : ℝ} (ht : 1 / 2 ≤ t) :
    outsideLogPrimitive (outsideRadius t) =
      (t + 11281 / 10000) * Real.log (outsideRadius t) -
        Real.sqrt ((t + 11281 / 10000) ^ 2 - 4 * outsideProduct) := by
  calc
    outsideLogPrimitive (outsideRadius t) =
        (outsideRadius t + outsideProduct / outsideRadius t) * Real.log (outsideRadius t) -
          (outsideRadius t - outsideProduct / outsideRadius t) := by
      unfold outsideLogPrimitive
      simp only [div_eq_mul_inv]
      ring
    _ = _ := by rw [outsideRadius_joukowski ht, outsideRadius_sqrt ht]

/-- Primitive in the radius variable of `(-contourScale / R)^n`.

The exceptional logarithmic order is `n=1`. All higher orders use only
natural reciprocal powers, which are convenient for rational enclosures.
-/
def outsidePowerPrimitive (n : ℕ) (R : ℝ) : ℝ :=
  match n with
  | 0 => R + outsideProduct * R⁻¹
  | 1 => -contourScale * (Real.log R + outsideProduct / 2 * (R⁻¹) ^ 2)
  | k + 2 => (-contourScale) ^ (k + 2) *
      (reciprocalPowerPrimitive k R -
        outsideProduct * reciprocalPowerPrimitive (k + 2) R)

theorem hasDerivAt_outsidePowerPrimitive (n : ℕ) {R : ℝ} (hR : R ≠ 0) :
    HasDerivAt (outsidePowerPrimitive n)
      ((-contourScale / R) ^ n * (1 - outsideProduct / R ^ 2)) R := by
  have hid := hasDerivAt_id R
  have hI := hid.inv hR
  cases n with
  | zero =>
      have h := hid.add (hI.const_mul outsideProduct)
      refine h.congr_deriv ?_
      simp only [id_eq, pow_zero, one_mul]
      ring
  | succ n =>
      cases n with
      | zero =>
          have h := ((hid.log hR).add ((hI.pow 2).const_mul (outsideProduct / 2))).const_mul
            (-contourScale)
          refine h.congr_deriv ?_
          norm_num
          simp only [div_eq_mul_inv]
          field_simp
          ring
      | succ k =>
          have h := ((hasDerivAt_reciprocalPowerPrimitive k hR).sub
            ((hasDerivAt_reciprocalPowerPrimitive (k + 2) hR).const_mul outsideProduct)).const_mul
              ((-contourScale) ^ (k + 2))
          change HasDerivAt (outsidePowerPrimitive (k + 2))
            ((-contourScale / R) ^ (k + 2) * (1 - outsideProduct / R ^ 2)) R
          refine h.congr_deriv ?_
          simp only [div_eq_mul_inv, mul_pow, inv_pow, pow_add]
          ring

theorem outsidePowerPrimitive_one_eq (R : ℝ) :
    outsidePowerPrimitive 1 R =
      -contourScale * (Real.log R + contourRatio * (-contourScale / R) ^ 2 / 2) := by
  dsimp [outsidePowerPrimitive, outsideProduct]
  simp only [div_eq_mul_inv, mul_pow]
  ring

/-- The higher endpoint powers use only the small exterior parameter. -/
theorem outsidePowerPrimitive_add_two_eq (k : ℕ) (R : ℝ) :
    outsidePowerPrimitive (k + 2) R =
      contourScale * ((-contourScale / R) ^ (k + 1) / (k + 1 : ℝ) -
        contourRatio * (-contourScale / R) ^ (k + 3) / (k + 3 : ℝ)) := by
  dsimp [outsidePowerPrimitive, reciprocalPowerPrimitive, outsideProduct]
  simp only [div_eq_mul_inv, mul_pow, pow_add, Nat.cast_add, Nat.cast_ofNat]
  ring

/-- The actual finite Fourier coefficient, including the zero order. -/
def outsideCoefficient (n : ℕ) : ℝ :=
  (1 + contourRatio ^ n) * contourMoment n / (n : ℝ)

theorem outsideCoefficient_zero : outsideCoefficient 0 = 0 := by
  simp [outsideCoefficient]

/-- Exact elementary primitive of the actual negative-axis contour potential. -/
def outsideContourPrimitive (t : ℝ) : ℝ :=
  (267885951940 / 1000000000000 : ℝ) * outsideLogPrimitive (outsideRadius t) -
    ∑ n ∈ Finset.range 49, outsideCoefficient n *
      outsidePowerPrimitive n (outsideRadius t)

theorem outsideContourPrimitive_eq_sum48 (t : ℝ) :
    outsideContourPrimitive t =
      (267885951940 / 1000000000000 : ℝ) * outsideLogPrimitive (outsideRadius t) -
        ∑ n ∈ Finset.range 48, outsideCoefficient (n + 1) *
          outsidePowerPrimitive (n + 1) (outsideRadius t) := by
  unfold outsideContourPrimitive
  have h := Finset.sum_range_succ'
    (fun n => outsideCoefficient n * outsidePowerPrimitive n (outsideRadius t)) 48
  rw [outsideCoefficient_zero, zero_mul, add_zero] at h
  rw [h]

theorem hasDerivAt_outsideContourPrimitive {t : ℝ} (ht : 1 / 2 ≤ t) :
    HasDerivAt outsideContourPrimitive (contourReferencePotential (-(t : ℂ))) t := by
  have hR := hasDerivAt_outsideRadius ht
  have hR0 : outsideRadius t ≠ 0 := (outsideRadius_pos ht).ne'
  have hJ := outsideRadius_jacobian ht
  have hlog : HasDerivAt (fun s => outsideLogPrimitive (outsideRadius s))
      (Real.log (outsideRadius t)) t := by
    have h := (hasDerivAt_outsideLogPrimitive hR0).comp t hR
    refine h.congr_deriv ?_
    rw [mul_assoc, hJ, mul_one]
  have hpow : ∀ n, HasDerivAt (fun s => outsidePowerPrimitive n (outsideRadius s))
      (outsideParameter t ^ n) t := by
    intro n
    have h := (hasDerivAt_outsidePowerPrimitive n hR0).comp t hR
    refine h.congr_deriv ?_
    rw [mul_assoc, hJ, mul_one]
    rfl
  have hsum := HasDerivAt.fun_sum (u := Finset.range 49)
    (fun n _ => (hpow n).const_mul (outsideCoefficient n))
  have h := (hlog.const_mul (267885951940 / 1000000000000 : ℝ)).sub hsum
  refine h.congr_deriv ?_
  rw [contourReferencePotential_neg t ht]
  rfl

/-- Local continuity of the finite exterior formula at every allowed endpoint. -/
theorem continuousAt_outsideFormula {t : ℝ} (ht : 1 / 2 ≤ t) :
    ContinuousAt (fun s =>
      (267885951940 / 1000000000000 : ℝ) * Real.log (outsideRadius s) -
        ∑ n ∈ Finset.range 49, outsideCoefficient n * outsideParameter s ^ n) t := by
  have hR := (hasDerivAt_outsideRadius ht).continuousAt
  have hR0 : outsideRadius t ≠ 0 := (outsideRadius_pos ht).ne'
  have hparam : DifferentiableAt ℝ outsideParameter t :=
    ((hasDerivAt_const t (-contourScale)).div (hasDerivAt_outsideRadius ht) hR0).differentiableAt
  have hsum : ContinuousAt (fun s =>
      ∑ n ∈ Finset.range 49, outsideCoefficient n * outsideParameter s ^ n) t :=
    (HasDerivAt.fun_sum (fun n _ => (hparam.hasDerivAt.pow n).const_mul
      (outsideCoefficient n))).continuousAt
  exact (continuousAt_const.mul (hR.log hR0)).sub
    hsum

theorem continuousOn_contourReferencePotential_neg :
    ContinuousOn (fun t : ℝ => contourReferencePotential (-(t : ℂ))) (Set.Ici (1 / 2)) := by
  have hform : ContinuousOn (fun s =>
      (267885951940 / 1000000000000 : ℝ) * Real.log (outsideRadius s) -
        ∑ n ∈ Finset.range 49, outsideCoefficient n * outsideParameter s ^ n)
      (Set.Ici (1 / 2)) := fun t ht =>
    (continuousAt_outsideFormula ht).continuousWithinAt
  apply hform.congr
  intro t ht
  exact contourReferencePotential_neg t ht

theorem integrableOn_contourReferencePotential_neg_Icc {a b : ℝ} (ha : 1 / 2 ≤ a) :
    IntegrableOn (fun t : ℝ => contourReferencePotential (-(t : ℂ))) (Set.Icc a b) volume := by
  have hcont := continuousOn_contourReferencePotential_neg.mono
    (show Set.Icc a b ⊆ Set.Ici (1 / 2) from fun _ ht => ha.trans ht.1)
  exact hcont.integrableOn_Icc

theorem integrableOn_contourReferencePotential_neg_Ico {a b : ℝ} (ha : 1 / 2 ≤ a) :
    IntegrableOn (fun t : ℝ => contourReferencePotential (-(t : ℂ))) (Set.Ico a b) volume :=
  (integrableOn_contourReferencePotential_neg_Icc ha).mono_set Set.Ico_subset_Icc_self

theorem integral_contourReferencePotential_neg {a b : ℝ}
    (ha : 1 / 2 ≤ a) (hab : a ≤ b) :
    (∫ t in a..b, contourReferencePotential (-(t : ℂ))) =
      outsideContourPrimitive b - outsideContourPrimitive a := by
  have ht : ∀ t ∈ Set.uIcc a b, 1 / 2 ≤ t := by
    intro t ht
    rw [Set.uIcc_of_le hab] at ht
    exact ha.trans ht.1
  have hcont : ContinuousOn (fun t : ℝ => contourReferencePotential (-(t : ℂ)))
      (Set.uIcc a b) := by
    have hform : ContinuousOn (fun s =>
        (267885951940 / 1000000000000 : ℝ) * Real.log (outsideRadius s) -
          ∑ n ∈ Finset.range 49, outsideCoefficient n * outsideParameter s ^ n)
        (Set.uIcc a b) := fun t ht' =>
      (continuousAt_outsideFormula (ht t ht')).continuousWithinAt
    apply hform.congr
    intro t ht'
    exact contourReferencePotential_neg t (ht t ht')
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t ht' => hasDerivAt_outsideContourPrimitive (ht t ht')) hcont.intervalIntegrable

theorem frequencyCell_left_ge_half (j : ℕ) :
    1 / 2 ≤ referenceCellLeft (1 / 2) j := by
  unfold referenceCellLeft
  exact le_add_of_nonneg_right (by positivity)

theorem integrable_contourReferencePotential_neg_frequency :
    Integrable (fun t : ℝ => contourReferencePotential (-(t : ℂ))) frequencyReferenceMeasure := by
  unfold frequencyReferenceMeasure referenceMeasure
  apply integrable_finsetSum_measure.mpr
  intro j hj
  exact (integrableOn_contourReferencePotential_neg_Ico (frequencyCell_left_ge_half j)).smul_measure
    ENNReal.ofReal_ne_top

/-- Exact reduction of the actual 160-cell frequency/contour interaction to
the elementary endpoint values, with the literal Appendix A densities. -/
theorem integral_contourReferencePotential_neg_frequency :
    (∫ t, contourReferencePotential (-(t : ℂ)) ∂frequencyReferenceMeasure) =
      ∑ j ∈ Finset.range 160, referenceDensity ConfigData.frequencyMassUnits j *
        (outsideContourPrimitive (referenceCellRight (1 / 2) j) -
          outsideContourPrimitive (referenceCellLeft (1 / 2) j)) := by
  unfold frequencyReferenceMeasure referenceMeasure
  rw [integral_finsetSum_measure]
  · apply Finset.sum_congr rfl
    intro j hj
    rw [integral_smul_measure,
      ENNReal.toReal_ofReal (referenceDensity_nonneg ConfigData.frequencyMassUnits j),
      integral_Ico_eq_integral_Ioc,
      ← intervalIntegral.integral_of_le (referenceCellLeft_le_right (1 / 2) j),
      integral_contourReferencePotential_neg (frequencyCell_left_ge_half j)
        (referenceCellLeft_le_right (1 / 2) j)]
    rfl
  · intro j hj
    exact (integrableOn_contourReferencePotential_neg_Ico (frequencyCell_left_ge_half j)).smul_measure
      ENNReal.ofReal_ne_top

end

end Li2Lean.P0.ActualReferenceQLogOutside
