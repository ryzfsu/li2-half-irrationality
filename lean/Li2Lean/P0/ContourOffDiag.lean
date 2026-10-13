/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.TwoPreimageResidue
import Li2Lean.P0.ResidueLeaf

open MeasureTheory
open Filter
open Topology

namespace Li2Lean
namespace P0

noncomputable section

/-! Pullback and primitive-free auxiliary lemmas for the off-diagonal contour entry. -/

private def contourJoukowski (m : ℕ) (zeta : ℂ) : ℂ := scaledJoukowski m zeta

private theorem ellipsePoint_eq_joukowski (m : ℕ) (u : ℝ) :
    ellipsePoint m u = contourJoukowski m (Complex.exp (Complex.I * (u : ℂ))) := by
  simpa [contourJoukowski] using ellipsePoint_eq_scaledJoukowski m u

private theorem p0_contour_pole_preimage_condition (m i : ℕ)
    (hm : 0 < m) (hi : i < 2 * m) : P0PolePreimageCondition m i := by
  rcases P0ContourLeaf.p0_pole_preimage_condition m i hm hi with
    ⟨z₁, z₂, hsum, hprod, h₁, h₂⟩
  have hxi : (xiScaled m : ℂ) = (P0ContourLeaf.xiScaled m : ℂ) := by
    simp [xiScaled, P0ContourLeaf.xiScaled, xi, P0ContourLeaf.xi]
  have hAlpha : (alphaScaled m : ℂ) = (P0ContourLeaf.alphaScaled m : ℂ) := by
    simp [alphaScaled, axisAScaled, axisBScaled, axisA, axisB,
      P0ContourLeaf.alphaScaled, P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]
    ring
  have hBeta : (betaScaled m : ℂ) = (P0ContourLeaf.betaScaled m : ℂ) := by
    simp [betaScaled, axisAScaled, axisBScaled, axisA, axisB,
      P0ContourLeaf.betaScaled, P0ContourLeaf.beta,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]
    ring
  refine ⟨z₁, z₂, ?_, ?_, h₁, h₂⟩
  · simpa [hxi, hAlpha] using hsum
  · simpa [hBeta, hAlpha] using hprod

theorem p0EllipseIntegral_eq_circleIntegral_pullback (m : ℕ) (f : ℂ → ℂ) :
    p0EllipseIntegral m f =
      (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ *
        (∮ z in C(0, 1),
          f (contourJoukowski m z) *
            ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) := by
  change (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ *
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        f (ellipsePoint m u) * ellipseTangent m u) = _
  rw [circleIntegral]
  apply congrArg (fun x : ℂ => (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ * x)
  apply intervalIntegral.integral_congr
  intro u hu
  change f (ellipsePoint m u) * ellipseTangent m u = _
  have hp : ellipsePoint m u = contourJoukowski m (circleMap 0 1 u) := by
    rw [ellipsePoint_eq_joukowski]
    simp [circleMap]
    congr 1
    ring
  rw [hp, ellipseTangent_eq_joukowskiDeriv]
  simp only [deriv_circleMap, smul_eq_mul]
  ring

theorem p0EllipseIntegral_simplePole (m i : ℕ) (hm : 0 < m)
    (hi : i < 2 * m) :
    p0EllipseIntegral m (fun z => (z - (i : ℂ))⁻¹) = 1 := by
  rw [p0EllipseIntegral_eq_circleIntegral_pullback]
  have hpre := p0_contour_pole_preimage_condition m i hm hi
  have hcircle :
      (∮ z in C(0, 1),
        (contourJoukowski m z - (i : ℂ))⁻¹ *
          ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) =
      2 * (Real.pi : ℂ) * Complex.I := by
    calc
      _ = ∮ z in C(0, 1),
          ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z /
            (contourJoukowski m z - (i : ℂ)) := by
              apply circleIntegral.integral_congr (by norm_num)
              intro z hz
              simp [div_eq_mul_inv, mul_comm]
      _ = _ := p0_pole_pullback_log_derivative m i hm hpre
  have hscale :
      Complex.ofReal (2 * Real.pi) * Complex.I =
        2 * (Real.pi : ℂ) * Complex.I := by
    push_cast
    ring
  rw [hscale, hcircle]
  field_simp [Real.pi_ne_zero, Complex.I_ne_zero]

theorem p0EllipseIntegral_const_mul (m : ℕ) (c : ℂ) (f : ℂ → ℂ) :
    p0EllipseIntegral m (fun z => c * f z) = c * p0EllipseIntegral m f := by
  unfold p0EllipseIntegral
  rw [show (∫ u in (0 : ℝ)..(2 * Real.pi),
      (c * f (p0EllipsePoint m u)) * p0EllipseTangent m u) =
      c * ∫ u in (0 : ℝ)..(2 * Real.pi),
        f (p0EllipsePoint m u) * p0EllipseTangent m u by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro u hu
    ring]
  ring

theorem p0EllipseIntegral_dslope_eq_zero (m : ℕ) (f : ℂ → ℂ) (w : ℂ)
    (hf : Differentiable ℂ f) :
    p0EllipseIntegral m (dslope f w) = 0 := by
  have hslope : Differentiable ℂ (dslope f w) := by
    have hUniv : (Set.univ : Set ℂ) ∈ 𝓝 w := by simp
    exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope hUniv).2 hf.differentiableOn)
  obtain ⟨G, hG⟩ := Differentiable.isExactOn_univ hslope
  rw [p0EllipseIntegral_eq_circleIntegral_pullback]
  have hcir :
      (∮ z in C(0, 1),
        dslope f w (contourJoukowski m z) *
          ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt (by norm_num)
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      rw [mem_sphere_zero_iff_norm] at hz
      norm_num at hz
    have hJ : HasDerivAt (contourJoukowski m)
        (ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) z := by
      change HasDerivAt
        (ContourKit.joukowski (xiScaled m : ℂ) (alphaScaled m : ℂ) (betaScaled m : ℂ))
        (ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) z
      exact ContourKit.hasDerivAt_joukowski hz0
    have hcomp := (hG (contourJoukowski m z) (by simp)).comp z hJ
    simpa only [Function.comp_def] using hcomp.hasDerivWithinAt
  simp [hcir]

theorem p0_contourJoukowski_ne_nat {m i : ℕ} (hm : 0 < m)
    (hi : i < 2 * m) {z : ℂ} (hz : z ∈ Metric.sphere 0 1) :
    contourJoukowski m z ≠ (i : ℂ) := by
  have hnorm : ‖z‖ = 1 := by
    rw [mem_sphere_zero_iff_norm] at hz
    exact hz
  intro hmap
  have hpre := p0_contour_pole_preimage_condition m i hm hi
  rcases hpre with ⟨z₁, z₂, hsum, hprod, h₁, h₂⟩
  have hxi : (xiScaled m : ℂ) = (P0ContourLeaf.xiScaled m : ℂ) := by
    simp [xiScaled, P0ContourLeaf.xiScaled, xi, P0ContourLeaf.xi]
  have hAlpha : (alphaScaled m : ℂ) = (P0ContourLeaf.alphaScaled m : ℂ) := by
    simp [alphaScaled, axisAScaled, axisBScaled, axisA, axisB,
      P0ContourLeaf.alphaScaled, P0ContourLeaf.alpha,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]
    ring
  have hBeta : (betaScaled m : ℂ) = (P0ContourLeaf.betaScaled m : ℂ) := by
    simp [betaScaled, axisAScaled, axisBScaled, axisA, axisB,
      P0ContourLeaf.betaScaled, P0ContourLeaf.beta,
      P0ContourLeaf.axisA, P0ContourLeaf.axisB]
    ring
  have hz0 : z ≠ 0 := by
    intro hzero
    subst z
    norm_num at hnorm
  have hmap' : P0ContourLeaf.affineJoukowski
      (P0ContourLeaf.xiScaled m : ℂ) (P0ContourLeaf.alphaScaled m : ℂ)
      (P0ContourLeaf.betaScaled m : ℂ) z = (i : ℂ) := by
    have hmap0 : contourJoukowski m z =
        P0ContourLeaf.affineJoukowski
          (P0ContourLeaf.xiScaled m : ℂ) (P0ContourLeaf.alphaScaled m : ℂ)
          (P0ContourLeaf.betaScaled m : ℂ) z := by
      calc
        contourJoukowski m z =
            (xiScaled m : ℂ) + (alphaScaled m : ℂ) * z +
              (betaScaled m : ℂ) / z := by
          simp [contourJoukowski, scaledJoukowski,
            ContourKit.ellipseJoukowski, ContourKit.joukowski,
            alphaScaled, betaScaled, axisAScaled, axisBScaled]
        _ = P0ContourLeaf.affineJoukowski
            (P0ContourLeaf.xiScaled m : ℂ) (P0ContourLeaf.alphaScaled m : ℂ)
            (P0ContourLeaf.betaScaled m : ℂ) z := by
          simp [P0ContourLeaf.affineJoukowski, hxi, hAlpha, hBeta]
    rw [← hmap0]
    exact hmap
  have hAlphaNe : (P0ContourLeaf.alphaScaled m : ℂ) ≠ 0 := by
    have hpos : 0 < P0ContourLeaf.alphaScaled m := by
      rw [P0ContourLeaf.alphaScaled, P0ContourLeaf.alpha]
      exact mul_pos (by exact_mod_cast hm)
        (by norm_num [P0ContourLeaf.axisA, P0ContourLeaf.axisB])
    exact_mod_cast (ne_of_gt hpos)
  have hsum' : z₁ + z₂ =
      ((i : ℂ) - (P0ContourLeaf.xiScaled m : ℂ)) /
        (P0ContourLeaf.alphaScaled m : ℂ) := by
    simpa [hxi, hAlpha] using hsum
  have hprod' : z₁ * z₂ =
      (P0ContourLeaf.betaScaled m : ℂ) /
        (P0ContourLeaf.alphaScaled m : ℂ) := by
    simpa [hBeta, hAlpha] using hprod
  have hfac := P0ContourLeaf.affineJoukowski_factorization
    hAlphaNe hsum' hprod' hz0
  have hz₁ne : z ≠ z₁ := by
    intro heq
    subst z
    rw [hnorm] at h₁
    norm_num at h₁
  have hz₂ne : z ≠ z₂ := by
    intro heq
    subst z
    rw [hnorm] at h₂
    norm_num at h₂
  have hzero : P0ContourLeaf.affineJoukowski
      (P0ContourLeaf.xiScaled m : ℂ) (P0ContourLeaf.alphaScaled m : ℂ)
      (P0ContourLeaf.betaScaled m : ℂ) z - (i : ℂ) = 0 := by
    rw [hmap']
    ring
  rw [hfac] at hzero
  exact (mul_ne_zero (mul_ne_zero (div_ne_zero hAlphaNe hz0)
    (sub_ne_zero.mpr hz₁ne)) (sub_ne_zero.mpr hz₂ne)) hzero

theorem p0EllipsePoint_ne_nat {m i : ℕ} (hm : 0 < m)
    (hi : i < 2 * m) (u : ℝ) :
    ellipsePoint m u ≠ (i : ℂ) := by
  have hsphere : circleMap 0 1 u ∈ Metric.sphere (0 : ℂ) 1 := by
    simp
  have hne := p0_contourJoukowski_ne_nat hm hi hsphere
  intro hpoint
  apply hne
  rw [ellipsePoint_eq_joukowski] at hpoint
  have hexp : Complex.exp (Complex.I * (u : ℂ)) =
      Complex.exp ((u : ℂ) * Complex.I) := by congr 1 <;> ring
  rw [hexp] at hpoint
  simpa [circleMap] using hpoint

theorem p0EllipseIntegral_add (m : ℕ) (f g : ℂ → ℂ)
    (hf : IntervalIntegrable
      (fun u => f (ellipsePoint m u) * ellipseTangent m u) volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable
      (fun u => g (ellipsePoint m u) * ellipseTangent m u) volume 0 (2 * Real.pi)) :
    p0EllipseIntegral m (fun z => f z + g z) =
      p0EllipseIntegral m f + p0EllipseIntegral m g := by
  unfold p0EllipseIntegral
  have hf' : IntervalIntegrable
      (fun u => f (p0EllipsePoint m u) * p0EllipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [ellipsePoint, ellipseTangent] using hf
  have hg' : IntervalIntegrable
      (fun u => g (p0EllipsePoint m u) * p0EllipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [ellipsePoint, ellipseTangent] using hg
  have hpoint (u : ℝ) :
      (f (p0EllipsePoint m u) + g (p0EllipsePoint m u)) * p0EllipseTangent m u =
        f (p0EllipsePoint m u) * p0EllipseTangent m u +
          g (p0EllipsePoint m u) * p0EllipseTangent m u := by ring
  have hint :
      (∫ u in (0 : ℝ)..(2 * Real.pi),
        (f (p0EllipsePoint m u) + g (p0EllipsePoint m u)) * p0EllipseTangent m u) =
      (∫ u in (0 : ℝ)..(2 * Real.pi), f (p0EllipsePoint m u) * p0EllipseTangent m u) +
      (∫ u in (0 : ℝ)..(2 * Real.pi), g (p0EllipsePoint m u) * p0EllipseTangent m u) := by
    rw [intervalIntegral.integral_congr (fun u _ => hpoint u),
      intervalIntegral.integral_add hf' hg']
  rw [hint]
  ring

theorem p0EllipseIntegral_neg (m : ℕ) (f : ℂ → ℂ) :
    p0EllipseIntegral m (fun z => -f z) = -p0EllipseIntegral m f := by
  unfold p0EllipseIntegral
  rw [show (∫ u in (0 : ℝ)..(2 * Real.pi),
      (-f (p0EllipsePoint m u)) * p0EllipseTangent m u) =
      -(∫ u in (0 : ℝ)..(2 * Real.pi),
        f (p0EllipsePoint m u) * p0EllipseTangent m u) by
    calc
      _ = ∫ u in (0 : ℝ)..(2 * Real.pi),
          -(f (p0EllipsePoint m u) * p0EllipseTangent m u) := by
            apply intervalIntegral.integral_congr
            intro u hu
            ring
      _ = _ := by rw [intervalIntegral.integral_neg]]
  ring

theorem p0EllipseIntegral_sub (m : ℕ) (f g : ℂ → ℂ)
    (hf : IntervalIntegrable
      (fun u => f (ellipsePoint m u) * ellipseTangent m u) volume 0 (2 * Real.pi))
    (hg : IntervalIntegrable
      (fun u => g (ellipsePoint m u) * ellipseTangent m u) volume 0 (2 * Real.pi)) :
    p0EllipseIntegral m (fun z => f z - g z) =
      p0EllipseIntegral m f - p0EllipseIntegral m g := by
  have hfun : (fun z => f z - g z) = (fun z => f z + -g z) := by
    funext z
    exact sub_eq_add_neg _ _
  have hgn : IntervalIntegrable
      (fun u => (-g (ellipsePoint m u)) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have hbase := hg.neg
    exact hbase.congr (by
      intro u hu
      dsimp
      ring)
  rw [hfun, p0EllipseIntegral_add m f (fun z => -g z) hf hgn,
    p0EllipseIntegral_neg]
  ring

theorem p0EllipseIntegral_dslope_path_integrable (m : ℕ) (f : ℂ → ℂ) (w : ℂ)
    (hf : Differentiable ℂ f) :
    IntervalIntegrable
      (fun u => dslope f w (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
  have hUniv : (Set.univ : Set ℂ) ∈ 𝓝 w := by simp
  have hslope : Differentiable ℂ (dslope f w) := by
    exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope hUniv).2 hf.differentiableOn)
  have hp : Continuous (ellipsePoint m) := by fun_prop [ellipsePoint, p0EllipsePoint]
  have ht : Continuous (ellipseTangent m) := by fun_prop [ellipseTangent, p0EllipseTangent]
  exact ((hslope.continuous.comp hp).mul ht).intervalIntegrable 0 (2 * Real.pi)

theorem p0EllipseIntegral_simplePole_path_integrable (m i : ℕ)
    (hm : 0 < m) (hi : i < 2 * m) :
    IntervalIntegrable
      (fun u => (ellipsePoint m u - (i : ℂ))⁻¹ * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
  have hp : Continuous (ellipsePoint m) := by fun_prop [ellipsePoint, p0EllipsePoint]
  have ht : Continuous (ellipseTangent m) := by fun_prop [ellipseTangent, p0EllipseTangent]
  have hden : ∀ u ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      ellipsePoint m u - (i : ℂ) ≠ 0 := by
    intro u hu
    exact sub_ne_zero.mpr (p0EllipsePoint_ne_nat hm hi u)
  have hInv : ContinuousOn
      (fun u => (ellipsePoint m u - (i : ℂ))⁻¹) (Set.uIcc 0 (2 * Real.pi)) := by
    exact (hp.continuousOn.sub continuousOn_const).inv₀ hden
  exact (hInv.mul ht.continuousOn).intervalIntegrable

theorem p0EllipseIntegral_doublePole_path_integrable (m i : ℕ)
    (hm : 0 < m) (hi : i < 2 * m) :
    IntervalIntegrable
      (fun u => ((ellipsePoint m u - (i : ℂ))⁻¹ *
        (ellipsePoint m u - (i : ℂ))⁻¹) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
  have hp : Continuous (ellipsePoint m) := by fun_prop [ellipsePoint, p0EllipsePoint]
  have ht : Continuous (ellipseTangent m) := by fun_prop [ellipseTangent, p0EllipseTangent]
  have hden : ∀ u ∈ Set.uIcc (0 : ℝ) (2 * Real.pi),
      ellipsePoint m u - (i : ℂ) ≠ 0 := by
    intro u hu
    exact sub_ne_zero.mpr (p0EllipsePoint_ne_nat hm hi u)
  have hInv : ContinuousOn
      (fun u => (ellipsePoint m u - (i : ℂ))⁻¹) (Set.uIcc 0 (2 * Real.pi)) := by
    exact (hp.continuousOn.sub continuousOn_const).inv₀ hden
  exact ((hInv.mul hInv).mul ht.continuousOn).intervalIntegrable

theorem p0EllipseIntegral_doublePole_eq_zero (m i : ℕ)
    (hm : 0 < m) (hi : i < 2 * m) :
    p0EllipseIntegral m (fun z =>
      (z - (i : ℂ))⁻¹ * (z - (i : ℂ))⁻¹) = 0 := by
  rw [p0EllipseIntegral_eq_circleIntegral_pullback]
  have hcir :
      (∮ z in C(0, 1),
        ((contourJoukowski m z - (i : ℂ))⁻¹ *
          (contourJoukowski m z - (i : ℂ))⁻¹) *
          ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) = 0 := by
    apply circleIntegral.integral_eq_zero_of_hasDerivWithinAt (by norm_num)
    intro z hz
    have hz0 : z ≠ 0 := by
      intro hzero
      subst z
      rw [mem_sphere_zero_iff_norm] at hz
      norm_num at hz
    have hne : contourJoukowski m z ≠ (i : ℂ) :=
      p0_contourJoukowski_ne_nat hm hi hz
    have hJ : HasDerivAt (contourJoukowski m)
        (ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) z := by
      change HasDerivAt
        (ContourKit.joukowski (xiScaled m : ℂ) (alphaScaled m : ℂ) (betaScaled m : ℂ))
        (ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z) z
      exact ContourKit.hasDerivAt_joukowski hz0
    have hInv := ((hasDerivAt_id (contourJoukowski m z)).sub_const (i : ℂ)).inv
      (sub_ne_zero.mpr hne)
    have hphi : HasDerivAt (fun w : ℂ => -((w - (i : ℂ))⁻¹))
        ((contourJoukowski m z - (i : ℂ))⁻¹ *
          (contourJoukowski m z - (i : ℂ))⁻¹) (contourJoukowski m z) := by
      convert hInv.neg using 1
      · ext w
        rfl
      · rw [← mul_inv_rev, pow_two]
        simp [div_eq_mul_inv]
    have hcomp := hphi.comp z hJ
    simpa only [Function.comp_def] using hcomp.hasDerivWithinAt
  simp [hcir]

theorem p0EllipseIntegral_doublePole (m i : ℕ) (F : ℂ → ℂ)
    (hm : 0 < m) (hi : i < 2 * m) (hF : Differentiable ℂ F) :
    p0EllipseIntegral m (fun z =>
      F z / ((z - (i : ℂ)) * (z - (i : ℂ)))) = deriv F (i : ℂ) := by
  let a : ℂ := (i : ℂ)
  let G : ℂ → ℂ := dslope F a
  let H : ℂ → ℂ := dslope G a
  have hG : Differentiable ℂ G := by
    dsimp [G]
    have hUniv : (Set.univ : Set ℂ) ∈ 𝓝 a := by simp
    exact differentiableOn_univ.mp
      ((Complex.differentiableOn_dslope hUniv).2 hF.differentiableOn)
  have hHzero : p0EllipseIntegral m H = 0 := by
    dsimp [H]
    exact p0EllipseIntegral_dslope_eq_zero m G a hG
  have hQ2 : IntervalIntegrable
      (fun u => (F a * ((ellipsePoint m u - a)⁻¹ *
        (ellipsePoint m u - a)⁻¹)) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have hbase : IntervalIntegrable
        (fun u => ((ellipsePoint m u - a)⁻¹ *
          (ellipsePoint m u - a)⁻¹) * ellipseTangent m u)
        volume 0 (2 * Real.pi) := by
      simpa [a] using p0EllipseIntegral_doublePole_path_integrable m i hm hi
    have h := hbase.const_mul (F a)
    exact h.congr (by
      intro u hu
      ring)
  have hQ1 : IntervalIntegrable
      (fun u => (G a * (ellipsePoint m u - a)⁻¹) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have hbase : IntervalIntegrable
        (fun u => (ellipsePoint m u - a)⁻¹ * ellipseTangent m u)
        volume 0 (2 * Real.pi) := by
      simpa [a] using p0EllipseIntegral_simplePole_path_integrable m i hm hi
    have h := hbase.const_mul (G a)
    exact h.congr (by
      intro u hu
      ring)
  have hHpath : IntervalIntegrable
      (fun u => H (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [H] using p0EllipseIntegral_dslope_path_integrable m G a hG
  have hQsum : IntervalIntegrable
      (fun u => (G a * (ellipsePoint m u - a)⁻¹ +
        H (ellipsePoint m u)) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have h := hQ1.add hHpath
    exact h.congr (by
      intro u hu
      ring)
  have hdecomp :
      p0EllipseIntegral m (fun z =>
        F z / ((z - a) * (z - a))) =
      p0EllipseIntegral m (fun z =>
        F a * ((z - a)⁻¹ * (z - a)⁻¹) +
          (G a * (z - a)⁻¹ + H z)) := by
    unfold p0EllipseIntegral
    apply congrArg (fun x : ℂ => (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ * x)
    apply intervalIntegral.integral_congr
    intro u hu
    have hne : ellipsePoint m u ≠ a := by
      dsimp [a]
      exact p0EllipsePoint_ne_nat hm hi u
    have hden : ellipsePoint m u - a ≠ 0 := sub_ne_zero.mpr hne
    have hFG : (ellipsePoint m u - a) * G (ellipsePoint m u) =
        F (ellipsePoint m u) - F a := by
      dsimp [G]
      simpa only [smul_eq_mul] using sub_smul_dslope F a (ellipsePoint m u)
    have hGH : (ellipsePoint m u - a) * H (ellipsePoint m u) =
        G (ellipsePoint m u) - G a := by
      dsimp [H]
      simpa only [smul_eq_mul] using sub_smul_dslope G a (ellipsePoint m u)
    have hpoly : F (ellipsePoint m u) =
        F a + (ellipsePoint m u - a) * G a +
          (ellipsePoint m u - a) ^ 2 * H (ellipsePoint m u) := by
      have hstep₁ : F (ellipsePoint m u) =
          F a + (ellipsePoint m u - a) * G (ellipsePoint m u) := by
        calc
          _ = F a + (F (ellipsePoint m u) - F a) := by ring
          _ = _ := by rw [← hFG]
      have hstep₂ : G (ellipsePoint m u) =
          G a + (ellipsePoint m u - a) * H (ellipsePoint m u) := by
        calc
          _ = G a + (G (ellipsePoint m u) - G a) := by ring
          _ = _ := by rw [← hGH]
      calc
        _ = F a + (ellipsePoint m u - a) * G (ellipsePoint m u) := hstep₁
        _ = F a + (ellipsePoint m u - a) *
              (G a + (ellipsePoint m u - a) * H (ellipsePoint m u)) := by rw [hstep₂]
        _ = _ := by ring
    have hden' : p0EllipsePoint m u - a ≠ 0 := by
      simpa [ellipsePoint] using hden
    have hpoly' : F (p0EllipsePoint m u) =
        F a + (p0EllipsePoint m u - a) * G a +
          (p0EllipsePoint m u - a) ^ 2 * H (p0EllipsePoint m u) := by
      simpa [ellipsePoint] using hpoly
    change
      F (p0EllipsePoint m u) /
        ((p0EllipsePoint m u - a) * (p0EllipsePoint m u - a)) * p0EllipseTangent m u =
      (F a * ((p0EllipsePoint m u - a)⁻¹ * (p0EllipsePoint m u - a)⁻¹) +
        (G a * (p0EllipsePoint m u - a)⁻¹ + H (p0EllipsePoint m u))) *
          p0EllipseTangent m u
    rw [hpoly']
    field_simp [hden']
    ring
  rw [hdecomp,
    p0EllipseIntegral_add m
      (fun z => F a * ((z - a)⁻¹ * (z - a)⁻¹))
      (fun z => G a * (z - a)⁻¹ + H z) hQ2 hQsum,
    p0EllipseIntegral_add m (fun z => G a * (z - a)⁻¹) H hQ1 hHpath,
    p0EllipseIntegral_const_mul, p0EllipseIntegral_const_mul]
  rw [p0EllipseIntegral_doublePole_eq_zero m i hm hi,
    p0EllipseIntegral_simplePole m i hm hi, hHzero]
  simp [G, a, dslope_same]

theorem p0EllipseIntegral_offdiag (g i j : ℕ) (hi : i < 4 * g)
    (hj : j < 4 * g) (hij : i ≠ j) :
    p0EllipseIntegral (2 * g) (fun z =>
      p0Entire g z / ((z - (i : ℂ)) * (z - (j : ℂ)))) =
      (p0U g i - p0U g j) / ((i : ℂ) - (j : ℂ)) := by
  have hg : 0 < g := by omega
  have hm : 0 < 2 * g := by omega
  have hi' : i < 2 * (2 * g) := by omega
  have hj' : j < 2 * (2 * g) := by omega
  let m : ℕ := 2 * g
  let a : ℂ := (i : ℂ)
  let b : ℂ := (j : ℂ)
  let F : ℂ → ℂ := p0Entire g
  have hF : Differentiable ℂ F := by
    dsimp [F]
    unfold p0Entire
    fun_prop
  have hab : a ≠ b := by
    dsimp [a, b]
    exact_mod_cast hij
  have hia : a = (i : ℂ) := rfl
  have hja : b = (j : ℂ) := rfl
  have hpi : IntervalIntegrable
      (fun u => (ellipsePoint m u - a)⁻¹ * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [a, m] using p0EllipseIntegral_simplePole_path_integrable
      (2 * g) i hm hi'
  have hpj : IntervalIntegrable
      (fun u => (ellipsePoint m u - b)⁻¹ * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [b, m] using p0EllipseIntegral_simplePole_path_integrable
      (2 * g) j hm hj'
  have hdi : IntervalIntegrable
      (fun u => dslope F a (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [F, a, m] using p0EllipseIntegral_dslope_path_integrable
      (2 * g) (p0Entire g) i hF
  have hdj : IntervalIntegrable
      (fun u => dslope F b (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    simpa [F, b, m] using p0EllipseIntegral_dslope_path_integrable
      (2 * g) (p0Entire g) j hF
  let ci : ℂ := F a / (a - b)
  let cj : ℂ := -(F b / (a - b))
  let cd : ℂ := (a - b)⁻¹
  let H1 : ℂ → ℂ := fun z => ci * (z - a)⁻¹
  let H2 : ℂ → ℂ := fun z => cj * (z - b)⁻¹
  let H3 : ℂ → ℂ := fun z => cd * (dslope F a z - dslope F b z)
  have hH1 : IntervalIntegrable
      (fun u => H1 (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have h := hpi.const_mul ci
    exact h.congr (by
      intro u hu
      dsimp [H1]
      ring)
  have hH2 : IntervalIntegrable
      (fun u => H2 (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have h := hpj.const_mul cj
    exact h.congr (by
      intro u hu
      dsimp [H2]
      ring)
  have hdsub : IntervalIntegrable
      (fun u => (dslope F a (ellipsePoint m u) -
        dslope F b (ellipsePoint m u)) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have h := hdi.sub hdj
    exact h.congr (by
      intro u hu
      ring)
  have hH3 : IntervalIntegrable
      (fun u => H3 (ellipsePoint m u) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have h := hdsub.const_mul cd
    exact h.congr (by
      intro u hu
      dsimp [H3]
      ring)
  have hH23 : IntervalIntegrable
      (fun u => (H2 (ellipsePoint m u) + H3 (ellipsePoint m u)) * ellipseTangent m u)
      volume 0 (2 * Real.pi) := by
    have h := hH2.add hH3
    exact h.congr (by
      intro u hu
      ring)
  have hdecomp :
      p0EllipseIntegral m (fun z =>
        F z / ((z - a) * (z - b))) =
      p0EllipseIntegral m (fun z => H1 z + (H2 z + H3 z)) := by
    unfold p0EllipseIntegral
    apply congrArg (fun x : ℂ => (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ * x)
    apply intervalIntegral.integral_congr
    intro u hu
    have hia0 : ellipsePoint m u - a ≠ 0 := by
      exact sub_ne_zero.mpr (p0EllipsePoint_ne_nat hm hi' u)
    have hja0 : ellipsePoint m u - b ≠ 0 := by
      exact sub_ne_zero.mpr (p0EllipsePoint_ne_nat hm hj' u)
    have hia' : ellipsePoint m u ≠ a := sub_ne_zero.mp hia0
    have hja' : ellipsePoint m u ≠ b := sub_ne_zero.mp hja0
    have hia0p : p0EllipsePoint m u - a ≠ 0 := by simpa [ellipsePoint] using hia0
    have hja0p : p0EllipsePoint m u - b ≠ 0 := by simpa [ellipsePoint] using hja0
    have hiap : p0EllipsePoint m u ≠ a := by simpa [ellipsePoint] using hia'
    have hjap : p0EllipsePoint m u ≠ b := by simpa [ellipsePoint] using hja'
    change F (ellipsePoint m u) /
        ((ellipsePoint m u - a) * (ellipsePoint m u - b)) * ellipseTangent m u = _
    simp only [ellipsePoint, ellipseTangent]
    dsimp [H1, H2, H3, ci, cj, cd]
    rw [dslope_of_ne _ hiap, slope_def_field,
      dslope_of_ne _ hjap, slope_def_field]
    field_simp [hia0p, hja0p, hab]
    ring
  rw [hdecomp]
  rw [p0EllipseIntegral_add m H1 (fun z => H2 z + H3 z) hH1 hH23,
    p0EllipseIntegral_add m H2 H3 hH2 hH3,
    p0EllipseIntegral_const_mul, p0EllipseIntegral_const_mul,
    p0EllipseIntegral_const_mul]
  have hsub :
      p0EllipseIntegral m (fun z => dslope F a z - dslope F b z) = 0 := by
    apply p0EllipseIntegral_sub m (dslope F a) (dslope F b) hdi hdj |>.trans
    rw [p0EllipseIntegral_dslope_eq_zero m (p0Entire g) i hF,
      p0EllipseIntegral_dslope_eq_zero m (p0Entire g) j hF]
    ring
  rw [hsub, mul_zero, p0EllipseIntegral_simplePole (2 * g) i hm hi',
    p0EllipseIntegral_simplePole (2 * g) j hm hj']
  dsimp [ci, cj, F, a, b]
  rw [p0Entire_nat_eq_U, p0Entire_nat_eq_U]
  ring

theorem p0C_offdiag_eq_neg_p0EllipseIntegral (g i j : ℕ)
    (hi : i < 4 * g) (hj : j < 4 * g) (hij : i ≠ j) :
    p0C g i j =
      -p0EllipseIntegral (2 * g) (fun z =>
        p0Entire g z / ((z - (i : ℂ)) * (z - (j : ℂ)))) := by
  rw [p0C, if_neg hij, p0EllipseIntegral_offdiag g i j hi hj hij]
  have hijC : (i : ℂ) ≠ (j : ℂ) := by exact_mod_cast hij
  have hden : (i : ℂ) - (j : ℂ) ≠ 0 := sub_ne_zero.mpr hijC
  have hden' : -(i : ℂ) + (j : ℂ) ≠ 0 := by
    have heq : -(i : ℂ) + (j : ℂ) = (j : ℂ) - (i : ℂ) := by ring
    rw [heq]
    exact sub_ne_zero.mpr hijC.symm
  field_simp [hden, hden']
  ring

theorem p0C_diag_eq_neg_p0EllipseIntegral_add (g i : ℕ)
    (hi : i < 4 * g) :
    p0C g i i =
      -p0EllipseIntegral (2 * g) (fun z =>
        p0Entire g z / ((z - (i : ℂ)) * (z - (i : ℂ)))) +
        Complex.ofReal (Real.log 2) * p0U g i := by
  have hm : 0 < 2 * g := by omega
  have hi' : i < 2 * (2 * g) := by omega
  have hF : Differentiable ℂ (p0Entire g) := by
    unfold p0Entire
    fun_prop
  have hdouble := p0EllipseIntegral_doublePole (2 * g) i (p0Entire g) hm hi' hF
  rw [p0C_diag_eq_neg_derivative g i, hdouble]

theorem p0ContourIdentityStatement_proved : P0ContourIdentityStatement := by
  intro g i j hi hj
  by_cases hij : i = j
  · subst j
    rw [if_pos rfl]
    exact p0C_diag_eq_neg_p0EllipseIntegral_add g i hi
  · rw [if_neg hij]
    simpa using p0C_offdiag_eq_neg_p0EllipseIntegral g i j hi hj hij

end

end P0
end Li2Lean
