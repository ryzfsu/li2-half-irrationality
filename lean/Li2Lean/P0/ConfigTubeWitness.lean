/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CoefficientStepMain
import Li2Lean.P0.TubeCircleMeasure

/-!
# The paper's tube competitor for one finite configuration

Paper v13 `p0-analytic.tex` ll. 259-273: for a configuration `(S, R, Z)` at
scale `m`, the competitor is

* `κ_S = ∑_{i∈S} 1_{[i/m,(i+1)/m)} dx` (`Config.pinnedMeasure`),
* `ν_δ = m⁻¹ ∑_a σ_{ζ_a, δ}` with `δ = m^{-2}` (`circleEmpiricalMeasure`),
* `μ_R = ∑_{r∈R} 1_{[(r-1)/m, r/m)} dt` (`Config.frequencyMeasure`).

This file proves that it is a `P0TubeAdmissibleMeasures (m^{-2})` (density
caps, support in the tube, unit masses) and states the remaining cell
comparison with this fixed witness.
-/

open MeasureTheory

namespace Li2Lean.P0.CoefficientAssembly

open Li2Lean.P0
open Li2Lean.P0.Config

noncomputable section

/-! ## Unit-density cell sums -/

/-- A finite sum of Lebesgue restrictions to pairwise disjoint measurable
cells inside `T` is below the restriction to `T`. -/
theorem sum_restrict_le_restrict {ι : Type*} (s : Finset ι) (c : ι → Set ℝ)
    (T : Set ℝ) (hmeas : ∀ i, MeasurableSet (c i))
    (hdisj : (s : Set ι).PairwiseDisjoint c) (hsub : ∀ i ∈ s, c i ⊆ T) :
    (∑ i ∈ s, volume.restrict (c i)) ≤ volume.restrict T := by
  rw [Measure.le_iff]
  intro A hA
  rw [Measure.coe_finsetSum, Finset.sum_apply, Measure.restrict_apply hA]
  simp_rw [Measure.restrict_apply hA]
  rw [← measure_biUnion_finset (f := fun i => A ∩ c i)]
  · apply measure_mono
    intro x hx
    simp only [Set.mem_iUnion] at hx
    obtain ⟨i, hi, hxA, hxc⟩ := hx
    exact ⟨hxA, hsub i hi hxc⟩
  · intro i hi j hj hij
    exact Disjoint.mono Set.inter_subset_right Set.inter_subset_right (hdisj hi hj hij)
  · intro i _
    exact hA.inter (hmeas i)

theorem Ico_cells_pairwiseDisjoint (m : ℕ) (s : Finset ℕ) (a : ℕ → ℝ)
    (ha : ∀ i, a i = (i : ℝ) / (m : ℝ)) :
    (s : Set ℕ).PairwiseDisjoint
      (fun i => Set.Ico (a i) (((i + 1 : ℕ) : ℝ) / (m : ℝ))) := by
  intro i _ j _ hij
  rw [Function.onFun, Set.disjoint_left]
  intro x hxi hxj
  rw [Set.mem_Ico, ha] at hxi hxj
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have hle : ((i + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by exact_mod_cast h
    by_cases hm : (m : ℝ) = 0
    · rw [hm, div_zero, div_zero] at hxi
      linarith [hxi.1, hxi.2]
    · have hmpos : 0 < (m : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg m) (Ne.symm hm)
      have : ((i + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (j : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_right hle hmpos.le
      linarith [hxi.2, hxj.1]
  · have hle : ((j + 1 : ℕ) : ℝ) ≤ (i : ℝ) := by exact_mod_cast h
    by_cases hm : (m : ℝ) = 0
    · rw [hm, div_zero, div_zero] at hxi
      linarith [hxi.1, hxi.2]
    · have hmpos : 0 < (m : ℝ) := lt_of_le_of_ne (Nat.cast_nonneg m) (Ne.symm hm)
      have : ((j + 1 : ℕ) : ℝ) / (m : ℝ) ≤ (i : ℝ) / (m : ℝ) :=
        div_le_div_of_nonneg_right hle hmpos.le
      linarith [hxj.2, hxi.1]

theorem volume_cell {m : ℕ} (hm : 0 < m) (i : ℕ) :
    volume (Set.Ico ((i : ℝ) / (m : ℝ)) (((i + 1 : ℕ) : ℝ) / (m : ℝ))) =
      ENNReal.ofReal ((m : ℝ)⁻¹) := by
  rw [Real.volume_Ico]
  congr 1
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  push_cast
  field_simp
  ring

/-! ## The pinned cells -/

theorem pinnedMeasure_le (C : FiniteConfiguration) :
    pinnedMeasure C.m C.pinned ≤
      volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ)) := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  unfold pinnedMeasure pinnedCell
  apply sum_restrict_le_restrict C.pinned _ _ (fun i => measurableSet_Ico)
    (Ico_cells_pairwiseDisjoint C.m C.pinned (fun i => (i : ℝ) / (C.m : ℝ))
      (fun i => rfl))
  intro i hi
  have hiS := C.pinned_subset hi
  simp only [pinnedUniverse, Finset.mem_Ico] at hiS
  have hlo : C.m / 4 ≤ i := hiS.1
  have hhi : i + 1 ≤ 5 * C.m / 4 := hiS.2
  have hk4 : C.m / 4 = k := by omega
  have hk5 : 5 * C.m / 4 = 5 * k := by omega
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  have hlo' : (k : ℝ) ≤ i := by exact_mod_cast (hk4 ▸ hlo)
  have hhi' : ((i + 1 : ℕ) : ℝ) ≤ 5 * k := by exact_mod_cast (hk5 ▸ hhi)
  intro x hx
  rw [Set.mem_Ico] at hx
  constructor
  · have : (1 / 4 : ℝ) ≤ (i : ℝ) / (C.m : ℝ) := by
      rw [le_div_iff₀ hmR, hmk]
      linarith
    linarith [hx.1]
  · have : ((i + 1 : ℕ) : ℝ) / (C.m : ℝ) ≤ 5 / 4 := by
      rw [div_le_iff₀ hmR, hmk]
      linarith
    linarith [hx.2]

theorem pinnedMeasure_univ (C : FiniteConfiguration) :
    pinnedMeasure C.m C.pinned Set.univ =
      (C.pinned.card : ENNReal) * ENNReal.ofReal ((C.m : ℝ)⁻¹) := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  unfold pinnedMeasure pinnedCell
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  simp_rw [Measure.restrict_apply_univ, volume_cell hm]
  rw [Finset.sum_const, nsmul_eq_mul]

/-! ## The frequency cells -/

theorem frequencyMeasure_le (C : FiniteConfiguration) :
    frequencyMeasure C.m C.frequency ≤ volume.restrict (Set.Ici (1 / 2 : ℝ)) := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hmk : (C.m : ℝ) = 4 * k := by exact_mod_cast hk
  unfold frequencyMeasure frequencyCell
  -- reindex the cells by `r - 1`
  have hcell : ∀ r ∈ C.frequency,
      Set.Ico (((r - 1 : ℕ) : ℝ) / (C.m : ℝ)) ((r : ℝ) / (C.m : ℝ)) =
        Set.Ico (((r - 1 : ℕ) : ℝ) / (C.m : ℝ)) ((((r - 1) + 1 : ℕ) : ℝ) / (C.m : ℝ)) := by
    intro r hr
    have h1 := C.frequency_lower r hr
    have : r - 1 + 1 = r := by omega
    rw [this]
  rw [Finset.sum_congr rfl (fun r hr => by rw [hcell r hr])]
  apply sum_restrict_le_restrict C.frequency _ _ (fun i => measurableSet_Ico)
  · intro r hr s hs hrs
    have hr1 := C.frequency_lower r hr
    have hs1 := C.frequency_lower s hs
    have hne : r - 1 ≠ s - 1 := by omega
    have hd := Ico_cells_pairwiseDisjoint C.m {r - 1, s - 1}
      (fun i => (i : ℝ) / (C.m : ℝ)) (fun i => rfl)
      (by simp) (by simp) hne
    exact hd
  · intro r hr
    have h1 := C.frequency_lower r hr
    have hhalf : C.m / 2 = 2 * k := by omega
    have hr' : (2 * k : ℝ) ≤ ((r - 1 : ℕ) : ℝ) := by
      have : 2 * k ≤ r - 1 := by omega
      exact_mod_cast this
    intro x hx
    rw [Set.mem_Ico] at hx
    rw [Set.mem_Ici]
    have : (1 / 2 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) := by
      rw [le_div_iff₀ hmR, hmk]
      linarith
    linarith [hx.1]

theorem frequencyMeasure_univ (C : FiniteConfiguration) :
    frequencyMeasure C.m C.frequency Set.univ = 1 := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (C.m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold frequencyMeasure frequencyCell
  rw [Measure.coe_finsetSum, Finset.sum_apply]
  have hvol : ∀ r ∈ C.frequency,
      volume.restrict (Set.Ico (((r - 1 : ℕ) : ℝ) / (C.m : ℝ)) ((r : ℝ) / (C.m : ℝ)))
        Set.univ = ENNReal.ofReal ((C.m : ℝ)⁻¹) := by
    intro r hr
    have h1 := C.frequency_lower r hr
    rw [Measure.restrict_apply_univ, Real.volume_Ico]
    congr 1
    have : ((r - 1 : ℕ) : ℝ) = (r : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]
      simp
    rw [this]
    field_simp
    ring
  rw [Finset.sum_congr rfl hvol, Finset.sum_const, nsmul_eq_mul, C.frequency_card]
  rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _),
    mul_inv_cancel₀ hmR, ENNReal.ofReal_one]

/-! ## The contour circles -/

/-- Tube radius `δ = m^{-2}` used for configuration `C`. -/
def configTubeRadius (C : FiniteConfiguration) : ℝ := 1 / (C.m : ℝ) ^ 2

theorem configTubeRadius_pos (C : FiniteConfiguration) : 0 < configTubeRadius C := by
  have hm : (0 : ℝ) < C.m := by exact_mod_cast (show 0 < C.m by have := C.m_ge_eight; omega)
  unfold configTubeRadius
  positivity

theorem contour_mem_Gamma (C : FiniteConfiguration) (a : Fin C.contourCount) :
    C.contour a ∈ Gamma := by
  obtain ⟨u, hu⟩ := C.contour_mem a
  refine ⟨u, ?_⟩
  rw [← hu, baseEllipse]
  exact (ellipsePoint_one_eq_gammaPoint u).symm

/-- `ν_δ = m⁻¹ ∑_a σ_{ζ_a, δ}`. -/
def configContourMeasure (C : FiniteConfiguration) : Measure ℂ :=
  circleEmpiricalMeasure C.contour (configTubeRadius C) C.m

theorem configContourMeasure_supported (C : FiniteConfiguration) :
    Measure.support (configContourMeasure C) ⊆ tube (configTubeRadius C) := by
  apply Measure.support_subset_of_isClosed
    (isClosed_le (Metric.continuous_infDist_pt Gamma) continuous_const)
  rw [mem_ae_iff]
  exact circleEmpiricalMeasure_outside_tube C.contour (contour_mem_Gamma C)
    (configTubeRadius_pos C) C.m

theorem configContourMeasure_univ (C : FiniteConfiguration) :
    configContourMeasure C Set.univ =
      ENNReal.ofReal ((C.m : ℝ)⁻¹) * (C.contourCount : ENNReal) := by
  unfold configContourMeasure circleEmpiricalMeasure
  rw [Measure.smul_apply, Measure.sum_apply _ MeasurableSet.univ]
  simp [smul_eq_mul]

/-! ## The witness -/

theorem configCompanion_mass (C : FiniteConfiguration) :
    p0CompanionMeasure (pinnedMeasure C.m C.pinned) (configContourMeasure C)
      Set.univ = 1 := by
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (C.m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  rw [p0CompanionMeasure, Measure.add_apply,
    Measure.map_apply (by fun_prop) MeasurableSet.univ, Set.preimage_univ,
    pinnedMeasure_univ, configContourMeasure_univ]
  rw [← ENNReal.ofReal_natCast C.pinned.card, ← ENNReal.ofReal_natCast C.contourCount,
    ← ENNReal.ofReal_mul (Nat.cast_nonneg _), ← ENNReal.ofReal_mul (inv_nonneg.mpr
      (Nat.cast_nonneg _)),
    ← ENNReal.ofReal_add (by positivity) (by positivity)]
  have hbal : ((C.contourCount : ℝ) + C.pinned.card) = C.m := by
    exact_mod_cast C.mass_balance
  rw [show (C.pinned.card : ℝ) * (C.m : ℝ)⁻¹ + (C.m : ℝ)⁻¹ * C.contourCount =
      ((C.contourCount : ℝ) + C.pinned.card) * (C.m : ℝ)⁻¹ by ring, hbal,
    mul_inv_cancel₀ hmR, ENNReal.ofReal_one]

/-- The paper's competitor `(κ_S + ν_δ, μ_R)` in the tube class at `δ = m^{-2}`. -/
def configTubeWitness (C : FiniteConfiguration) :
    P0TubeAdmissibleMeasures (1 / (C.m : ℝ) ^ 2) where
  kappa := pinnedMeasure C.m C.pinned
  nu := configContourMeasure C
  mu := frequencyMeasure C.m C.frequency
  kappa_le_density := pinnedMeasure_le C
  nu_supported := configContourMeasure_supported C
  companion_mass := configCompanion_mass C
  mu_le_density := frequencyMeasure_le C
  frequency_mass := frequencyMeasure_univ C

/-! ## The cell comparison with the fixed witness -/

/-- Finite energy of the witness (the seven integrability/atomless clauses of
`p0TubeFiniteEnergyCondition`; v13 l. 203: bounded densities, compact
support). -/
def ConfigWitnessFiniteEnergy : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    p0TubeFiniteEnergyCondition (configTubeWitness C)

/-- The cell inequality of v13 ll. 257-431 for the fixed witness. -/
def ConfigWitnessCellBound : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    0 < literalConfigQWeight C →
    Real.log (literalConfigQWeight C) ≤
      -(C.m : ℝ) ^ 2 * p0TubeRegularizedEnergyValue (configTubeWitness C) +
        10 * (C.m : ℝ) * Real.log (C.m : ℝ) + cStar * (C.m : ℝ) + 1 / 3

theorem configEnergyComparisonHead_of_witness
    (hfin : ConfigWitnessFiniteEnergy) (hcell : ConfigWitnessCellBound) :
    ConfigEnergyComparisonHead :=
  fun C hhead hpos => ⟨configTubeWitness C, hfin C hhead, hcell C hhead hpos⟩

end

end Li2Lean.P0.CoefficientAssembly
