/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeExterior
import Mathlib.Analysis.Complex.Poisson

/-! # Explicit Poisson means for the v10 exterior Joukowski map -/

open MeasureTheory Complex
open scoped ComplexConjugate

namespace Li2Lean.P0

noncomputable section

/-- The disk parameter for exterior harmonic measure under Joukowski. -/
def exteriorPoissonParameter (w : ℂ) : ℂ := (conj w)⁻¹

/-- Strict exterior points map into the open unit disk. -/
theorem exteriorPoissonParameter_mem_ball {w : ℂ} (hw : 1 < ‖w‖) :
    exteriorPoissonParameter w ∈ Metric.ball 0 1 := by
  simp only [Metric.mem_ball, dist_zero_right, exteriorPoissonParameter, norm_inv, norm_conj]
  exact inv_lt_one_of_one_lt₀ hw

/-- Poisson density on the unit circle is nonnegative for disk parameters. -/
theorem poissonKernel_unit_nonneg {p ζ : ℂ} (hp : ‖p‖ < 1) (hζ : ‖ζ‖ = 1) :
    0 ≤ poissonKernel 0 p ζ := by
  simp only [poissonKernel, sub_zero, hζ, one_pow]
  apply div_nonneg _ (sq_nonneg _)
  nlinarith [norm_nonneg p]

/-- Unit-circle reciprocal values are conjugate values. -/
theorem joukowski_unit_eq_affine_conj {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    joukowski ζ = (center : ℂ) + ellipseC * ζ + ellipseD * conj ζ := by
  have hs : Complex.normSq ζ = 1 := by rw [Complex.normSq_eq_norm_sq, hζ]; norm_num
  simp [joukowski, Complex.inv_def, hs]

/-- Continuity of the disk Poisson density on the unit circle. -/
theorem poissonKernel_unit_continuous {p : ℂ} (hp : ‖p‖ < 1) :
    ContinuousOn (poissonKernel 0 p) (Metric.sphere 0 1) := by
  have hnot : p ∉ Metric.sphere (0 : ℂ) |(1 : ℝ)| := by
    simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using ne_of_lt hp
  rw [poissonKernel_eq_re_herglotzRieszKernel]
  simpa only [abs_one] using
    Complex.continuous_re.comp_continuousOn (continuousOn_herglotzRieszKernel_sphere hnot)

/-- Explicit unit-circle Poisson mean of the literal Joukowski map. -/
theorem poisson_mean_joukowski {p : ℂ} (hp : ‖p‖ < 1) :
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ • joukowski ζ) 0 1 =
      (center : ℂ) + ellipseC * p + ellipseD * conj p := by
  let L : ℂ →L[ℝ] ℂ :=
    ellipseC • (ContinuousLinearMap.id ℝ ℂ) +
      ellipseD • Complex.conjLIE.toContinuousLinearMap
  have hL (ζ : ℂ) : L ζ = ellipseC * ζ + ellipseD * conj ζ := rfl
  have hpball : p ∈ Metric.ball (0 : ℂ) 1 := by simpa using hp
  have hpc := poissonKernel_unit_continuous hp
  have hpid : CircleIntegrable (fun ζ : ℂ => poissonKernel 0 p ζ • ζ) 0 1 :=
    (hpc.smul continuousOn_id).circleIntegrable (by norm_num)
  have hpl : CircleIntegrable (fun ζ : ℂ => poissonKernel 0 p ζ • L ζ) 0 1 :=
    (hpc.smul L.continuous.continuousOn).circleIntegrable (by norm_num)
  have hpk : CircleIntegrable (fun ζ : ℂ => poissonKernel 0 p ζ • (center : ℂ)) 0 1 :=
    (hpc.smul continuousOn_const).circleIntegrable (by norm_num)
  have hid : Real.circleAverage (fun ζ : ℂ => poissonKernel 0 p ζ • ζ) 0 1 = p := by
    exact (differentiable_id.diffContOnCl : DiffContOnCl ℂ (fun ζ : ℂ => ζ)
      (Metric.ball 0 1)).circleAverage_poissonKernel_smul hpball
  have hc : Real.circleAverage (fun ζ : ℂ => poissonKernel 0 p ζ • (center : ℂ)) 0 1 =
      (center : ℂ) := by
    exact ((differentiable_const (center : ℂ)).diffContOnCl :
      DiffContOnCl ℂ (fun _ : ℂ => (center : ℂ)) (Metric.ball 0 1)).circleAverage_poissonKernel_smul hpball
  have hl : Real.circleAverage (fun ζ : ℂ => poissonKernel 0 p ζ • L ζ) 0 1 = L p := by
    simpa only [Function.comp_def, map_smul, hid] using L.circleAverage_comp_comm hpid
  calc
    Real.circleAverage (fun ζ => poissonKernel 0 p ζ • joukowski ζ) 0 1 =
        Real.circleAverage (fun ζ => poissonKernel 0 p ζ • (center : ℂ) +
          poissonKernel 0 p ζ • L ζ) 0 1 := by
      apply Real.circleAverage_congr_sphere
      intro ζ hζ
      have hζ' : ‖ζ‖ = 1 := by simpa only [abs_one, Metric.mem_sphere, dist_zero_right] using hζ
      dsimp only
      rw [joukowski_unit_eq_affine_conj hζ', hL, ← smul_add]
      congr 1
      ring
    _ = (center : ℂ) + L p := by rw [Real.circleAverage_fun_add hpk hpl, hc, hl]
    _ = _ := by rw [hL]; ring

/-- The mean coordinate in `sec-tube.tex` is the actual Poisson boundary integral. -/
theorem exterior_poisson_mean_coordinate {w : ℂ} (hw : 1 < ‖w‖) :
    Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ • joukowski ζ) 0 1 =
      exteriorMeanCoordinate w := by
  have hp : ‖exteriorPoissonParameter w‖ < 1 := by
    simpa using exteriorPoissonParameter_mem_ball hw
  simpa [exteriorPoissonParameter, exteriorMeanCoordinate] using poisson_mean_joukowski hp

/-- Quantitative displacement of the genuine exterior Poisson mean. -/
theorem exterior_poisson_mean_distance {w : ℂ} (hw : 1 < ‖w‖) :
    ‖joukowski w - Real.circleAverage
      (fun ζ => poissonKernel 0 (exteriorPoissonParameter w) ζ • joukowski ζ) 0 1‖ ≤
      (semiMajor + semiMinor) * (‖w‖ - 1) := by
  rw [exterior_poisson_mean_coordinate hw]
  exact exteriorMeanCoordinate_distance hw.le

/-- Normalization of the scalar Poisson density used for the exterior sweep. -/
theorem poissonKernel_unit_mass {p : ℂ} (hp : ‖p‖ < 1) :
    Real.circleAverage (poissonKernel 0 p) 0 1 = 1 := by
  have hpball : p ∈ Metric.ball (0 : ℂ) 1 := by simpa using hp
  have hi := (poissonKernel_unit_continuous hp).circleIntegrable (by norm_num : (0 : ℝ) ≤ 1)
  have h := ((differentiable_const (1 : ℂ)).diffContOnCl :
    DiffContOnCl ℂ (fun _ : ℂ => (1 : ℂ)) (Metric.ball 0 1)).circleAverage_poissonKernel_smul hpball
  change Real.circleAverage (fun ζ => poissonKernel 0 p ζ • (1 : ℂ)) 0 1 = 1 at h
  have hc := Complex.ofRealCLM.circleAverage_comp_comm hi
  apply Complex.ofReal_injective
  calc
    ((Real.circleAverage (poissonKernel 0 p) 0 1 : ℝ) : ℂ) =
        Real.circleAverage (fun ζ => (poissonKernel 0 p ζ : ℂ)) 0 1 := hc.symm
    _ = 1 := by simpa only [Pi.smul_apply, Complex.real_smul, mul_one] using h
    _ = ((1 : ℝ) : ℂ) := by norm_num

end
end Li2Lean.P0
