/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.ClosedForm

/-!
# First and second derivatives of the contour closed form

For `sin θ ≠ 0` the closed form `Wform` is twice differentiable with the
explicit derivatives `W1`, `W2` below.  Everything is elementary calculus on
the formula of `ClosedForm.lean`.
-/

namespace Li2Lean.P0.CA.Contour

noncomputable section

open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourKernel

def ρp (j : ℕ) : ℝ := referenceDensity ConfigData.pinnedMassUnits j
def ρf (j : ℕ) : ℝ := referenceDensity ConfigData.frequencyMassUnits j
def pL (j : ℕ) : ℝ := referenceCellLeft (1 / 4) j
def pR (j : ℕ) : ℝ := referenceCellRight (1 / 4) j
def fL (j : ℕ) : ℝ := referenceCellLeft (1 / 2) j
def fR (j : ℕ) : ℝ := referenceCellRight (1 / 2) j

/-- The linear combination of shifted primitives appearing in `segForm`;
`g κ` stands for the primitive at `X + κ`. -/
def segComb (g : ℝ → ℝ) (lin c : ℝ) : ℝ :=
  (g (-(1 / 4)) - g (-(5 / 4)) + (g 0 - g (-2))) - (lin + (g (1 / 2) - g 0) + c) -
    2 * (∑ j ∈ Finset.range 32, ρp j * (g (-pL j) - g (-pR j))) -
    (∑ j ∈ Finset.range 160, ρf j * (g (fR j) - g (fL j)))

theorem segForm_eq_comb (X Y : ℝ) :
    segForm X Y = segComb (fun κ => Gr (X + κ) Y) (X * Real.log 2)
      (1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) := by
  simp only [segForm, segComb, ρp, ρf, pL, pR, fL, fR, ← sub_eq_add_neg, add_zero,
    sub_zero]
  ring

theorem hasDerivAt_segComb {G G' : ℝ → ℝ → ℝ} {lin : ℝ → ℝ} {lin' c θ : ℝ}
    (hG : ∀ κ, HasDerivAt (fun t => G t κ) (G' θ κ) θ)
    (hl : HasDerivAt lin lin' θ) :
    HasDerivAt (fun t => segComb (G t) (lin t) c) (segComb (G' θ) lin' 0) θ := by
  have hs1 : HasDerivAt
      (fun t => ∑ j ∈ Finset.range 32, ρp j * (G t (-pL j) - G t (-pR j)))
      (∑ j ∈ Finset.range 32, ρp j * (G' θ (-pL j) - G' θ (-pR j))) θ :=
    HasDerivAt.fun_sum (fun j _ => ((hG _).sub (hG _)).const_mul _)
  have hs2 : HasDerivAt
      (fun t => ∑ j ∈ Finset.range 160, ρf j * (G t (fR j) - G t (fL j)))
      (∑ j ∈ Finset.range 160, ρf j * (G' θ (fR j) - G' θ (fL j))) θ :=
    HasDerivAt.fun_sum (fun j _ => ((hG _).sub (hG _)).const_mul _)
  have h := ((((hG (-(1 / 4))).sub (hG (-(5 / 4)))).add ((hG 0).sub (hG (-2)))).sub
    ((hl.add ((hG (1 / 2)).sub (hG 0))).add_const c)).sub (hs1.const_mul 2) |>.sub hs2
  unfold segComb
  convert h using 1
  ring

/-! ## Derivatives of the primitive along a curve -/

def dGr (u v u' v' : ℝ) : ℝ :=
  Real.log (u ^ 2 + v ^ 2) / 2 * u' + Real.arctan (u / v) * v'

def d2Gr (u v u' v' u'' v'' : ℝ) : ℝ :=
  (u * u' + v * v') / (u ^ 2 + v ^ 2) * u' + Real.log (u ^ 2 + v ^ 2) / 2 * u'' +
    (u' * v - u * v') / (u ^ 2 + v ^ 2) * v' + Real.arctan (u / v) * v''

theorem hasDerivAt_Gr_comp {u v : ℝ → ℝ} {u' v' θ : ℝ}
    (hu : HasDerivAt u u' θ) (hv : HasDerivAt v v' θ) (hv0 : v θ ≠ 0) :
    HasDerivAt (fun t => Gr (u t) (v t)) (dGr (u θ) (v θ) u' v') θ := by
  have hvsq : 0 < v θ ^ 2 := by positivity
  have hpos : 0 < u θ ^ 2 + v θ ^ 2 := by nlinarith [sq_nonneg (u θ)]
  have h1 : HasDerivAt (fun t => u t ^ 2 + v t ^ 2)
      (2 * u θ * u' + 2 * v θ * v') θ := by
    have := (hu.pow 2).add (hv.pow 2)
    convert this using 1
    push_cast
    ring
  have hlog := h1.log hpos.ne'
  have hA := hu.mul ((hlog.div_const 2).sub_const 1)
  have hB := hv.mul (hu.div hv hv0).arctan
  have h := hA.add hB
  have h3 : 1 + (u θ / v θ) ^ 2 ≠ 0 := by positivity
  refine h.congr_deriv ?_
  unfold dGr
  simp only [Pi.div_apply]
  field_simp
  ring

theorem hasDerivAt_dGr_comp {u v du dv : ℝ → ℝ} {d2u d2v θ : ℝ}
    (hu : HasDerivAt u (du θ) θ) (hv : HasDerivAt v (dv θ) θ)
    (hdu : HasDerivAt du d2u θ) (hdv : HasDerivAt dv d2v θ) (hv0 : v θ ≠ 0) :
    HasDerivAt (fun t => dGr (u t) (v t) (du t) (dv t))
      (d2Gr (u θ) (v θ) (du θ) (dv θ) d2u d2v) θ := by
  have hvsq : 0 < v θ ^ 2 := by positivity
  have hpos : 0 < u θ ^ 2 + v θ ^ 2 := by nlinarith [sq_nonneg (u θ)]
  have h1 : HasDerivAt (fun t => u t ^ 2 + v t ^ 2)
      (2 * u θ * du θ + 2 * v θ * dv θ) θ := by
    have := (hu.pow 2).add (hv.pow 2)
    convert this using 1
    push_cast
    ring
  have hlog := h1.log hpos.ne'
  have hA := (hlog.div_const 2).mul hdu
  have hB := (hu.div hv hv0).arctan.mul hdv
  have h := hA.add hB
  have h3 : 1 + (u θ / v θ) ^ 2 ≠ 0 := by positivity
  refine h.congr_deriv ?_
  unfold d2Gr
  simp only [Pi.div_apply]
  field_simp
  ring

/-! ## The ellipse coordinates -/

def ellX1 (θ : ℝ) : ℝ := -(12783 / 10000) * Real.sin θ
def ellY1 (θ : ℝ) : ℝ := 229 / 200 * Real.cos θ
def ellX2 (θ : ℝ) : ℝ := -(12783 / 10000) * Real.cos θ
def ellY2 (θ : ℝ) : ℝ := -(229 / 200) * Real.sin θ

theorem hasDerivAt_ellX (θ : ℝ) : HasDerivAt ellX (ellX1 θ) θ := by
  have := ((Real.hasDerivAt_cos θ).const_mul (12783 / 10000 : ℝ)).const_add
    (11281 / 10000 : ℝ)
  refine this.congr_deriv ?_
  unfold ellX1; ring

theorem hasDerivAt_ellY (θ : ℝ) : HasDerivAt ellY (ellY1 θ) θ :=
  (Real.hasDerivAt_sin θ).const_mul (229 / 200 : ℝ)

theorem hasDerivAt_ellX1 (θ : ℝ) : HasDerivAt ellX1 (ellX2 θ) θ := by
  have := (Real.hasDerivAt_sin θ).const_mul (-(12783 / 10000) : ℝ)
  exact this

theorem hasDerivAt_ellY1 (θ : ℝ) : HasDerivAt ellY1 (ellY2 θ) θ := by
  have := (Real.hasDerivAt_cos θ).const_mul (229 / 200 : ℝ)
  refine this.congr_deriv ?_
  unfold ellY2; ring

/-! ## The Fourier part -/

def bR (n : ℕ) : ℝ :=
  (1 + contourRatio ^ (n + 1)) * contourFourierMoment (n + 1) / (n + 1 : ℝ)

def F1 (θ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 48, bR n * ((n + 1 : ℝ) * Real.sin ((n + 1 : ℝ) * θ))

def F2 (θ : ℝ) : ℝ :=
  ∑ n ∈ Finset.range 48, bR n * ((n + 1 : ℝ) ^ 2 * Real.cos ((n + 1 : ℝ) * θ))

theorem fourier_eq (θ : ℝ) :
    contourSelfPotentialFourier θ =
      contourMass * Real.log contourScale -
        ∑ n ∈ Finset.range 48, bR n * Real.cos ((n + 1 : ℝ) * θ) := rfl

theorem hasDerivAt_fourier (θ : ℝ) :
    HasDerivAt contourSelfPotentialFourier (F1 θ) θ := by
  have hsum : HasDerivAt
      (fun x : ℝ => ∑ n ∈ Finset.range 48, bR n * Real.cos ((n + 1 : ℝ) * x))
      (∑ n ∈ Finset.range 48,
        bR n * (-(Real.sin ((n + 1 : ℝ) * θ)) * ((n + 1 : ℝ) * 1))) θ := by
    apply HasDerivAt.fun_sum
    intro n _
    exact ((Real.hasDerivAt_cos _).comp θ
      ((hasDerivAt_id θ).const_mul (n + 1 : ℝ))).const_mul (bR n)
  have h := (hasDerivAt_const θ (contourMass * Real.log contourScale)).sub hsum
  rw [show contourSelfPotentialFourier = fun x => contourMass * Real.log contourScale -
      ∑ n ∈ Finset.range 48, bR n * Real.cos ((n + 1 : ℝ) * x) from funext fourier_eq]
  convert h using 1
  unfold F1
  rw [zero_sub, ← Finset.sum_neg_distrib]
  apply Finset.sum_congr rfl
  intro n _
  ring

theorem hasDerivAt_F1 (θ : ℝ) : HasDerivAt F1 (F2 θ) θ := by
  unfold F1 F2
  apply HasDerivAt.fun_sum
  intro n _
  have h := (((Real.hasDerivAt_sin _).comp θ
      ((hasDerivAt_id θ).const_mul (n + 1 : ℝ))).const_mul
      ((n + 1 : ℝ))).const_mul (bR n)
  refine h.congr_deriv ?_
  simp only [id]
  ring

/-! ## The derivatives of `Wform` -/

def W1 (θ : ℝ) : ℝ :=
  segComb (fun κ => dGr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ))
      (ellX1 θ * Real.log 2) 0 - 2 * F1 θ

def W2 (θ : ℝ) : ℝ :=
  segComb (fun κ => d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ))
      (ellX2 θ * Real.log 2) 0 - 2 * F2 θ

theorem Wform_eq_comb (θ : ℝ) :
    Wform θ = segComb (fun κ => Gr (ellX θ + κ) (ellY θ)) (ellX θ * Real.log 2)
      (1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
      2 * contourSelfPotentialFourier θ := by
  rw [Wform, segForm_eq_comb]

theorem hasDerivAt_Wform {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasDerivAt Wform (W1 θ) θ := by
  have hY : ellY θ ≠ 0 := by unfold ellY; exact mul_ne_zero (by norm_num) hs
  have hseg := hasDerivAt_segComb (c := 1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ))
    (G := fun t κ => Gr (ellX t + κ) (ellY t))
    (G' := fun t κ => dGr (ellX t + κ) (ellY t) (ellX1 t) (ellY1 t))
    (lin := fun t => ellX t * Real.log 2)
    (fun κ => hasDerivAt_Gr_comp ((hasDerivAt_ellX θ).add_const κ)
      (hasDerivAt_ellY θ) hY)
    ((hasDerivAt_ellX θ).mul_const (Real.log 2))
  have h := hseg.sub ((hasDerivAt_fourier θ).const_mul 2)
  rw [show Wform = fun t => segComb (fun κ => Gr (ellX t + κ) (ellY t))
      (ellX t * Real.log 2) (1 / 2 - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)) -
      2 * contourSelfPotentialFourier t from funext Wform_eq_comb]
  exact h

theorem hasDerivAt_W1 {θ : ℝ} (hs : Real.sin θ ≠ 0) :
    HasDerivAt W1 (W2 θ) θ := by
  have hY : ellY θ ≠ 0 := by unfold ellY; exact mul_ne_zero (by norm_num) hs
  have hseg := hasDerivAt_segComb (c := 0)
    (G := fun t κ => dGr (ellX t + κ) (ellY t) (ellX1 t) (ellY1 t))
    (G' := fun t κ => d2Gr (ellX t + κ) (ellY t) (ellX1 t) (ellY1 t) (ellX2 t) (ellY2 t))
    (lin := fun t => ellX1 t * Real.log 2)
    (fun κ => hasDerivAt_dGr_comp (u := fun t => ellX t + κ)
      ((hasDerivAt_ellX θ).add_const κ) (hasDerivAt_ellY θ)
      (hasDerivAt_ellX1 θ) (hasDerivAt_ellY1 θ) hY)
    ((hasDerivAt_ellX1 θ).mul_const (Real.log 2))
  exact hseg.sub ((hasDerivAt_F1 θ).const_mul 2)

end

end Li2Lean.P0.CA.Contour
