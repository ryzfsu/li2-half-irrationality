/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Defs

/-!
# Cell inequality for the configuration witness: assembly

Paper v13 `p0-analytic.tex` ll. 425-431: combining the exact expansion of
`log Q`, the decomposition of the witness energy and the term-by-term cell
estimates gives

`log Q ≤ -m^2 E(κ_S + ν_δ, μ_R) + 10 m log m + c_* m + 1/3`.

The linear constant is exactly `c_*`; the pinned-frequency displacement is
bounded crudely by `4m/3` and absorbed, together with the unused
`m log m` budget, by `10 m log m` (`log m ≥ log 8 > 2`).
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

theorem log_eight_gt_two : (2 : ℝ) < Real.log 8 := by
  have h := Real.exp_one_lt_d9
  have he2 : Real.exp 2 < 8 := by
    have : Real.exp 2 = Real.exp 1 * Real.exp 1 := by
      rw [← Real.exp_add]; norm_num
    rw [this]
    nlinarith [Real.exp_pos 1]
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact he2

theorem log_two_pi_pos : 0 < Real.log (2 * Real.pi) := by
  apply Real.log_pos
  nlinarith [Real.pi_gt_three]

/-- `d b_m ≤ 9m + 10 m log 2 + 4 d log m` (`g + 1 ≤ m`). -/
theorem contourCount_mul_b_le (C : FiniteConfiguration) :
    (C.contourCount : ℝ) * b C.m ≤
      9 * (C.m : ℝ) + 10 * (C.m : ℝ) * Real.log 2 +
        4 * (C.contourCount : ℝ) * Real.log (C.m : ℝ) := by
  have hm8 : 8 ≤ C.m := C.m_ge_eight
  have hdm : (C.contourCount : ℝ) ≤ C.m := by
    have := C.mass_balance
    exact_mod_cast (by omega : C.contourCount ≤ C.m)
  have hd0 : (0 : ℝ) ≤ C.contourCount := Nat.cast_nonneg _
  have hg : ((C.m / 2 + 1 : ℕ) : ℝ) ≤ (C.m : ℝ) := by
    exact_mod_cast (by omega : C.m / 2 + 1 ≤ C.m)
  have hgpos : (0 : ℝ) < ((C.m / 2 + 1 : ℕ) : ℝ) := by positivity
  have hlog : Real.log ((C.m / 2 + 1 : ℕ) : ℝ) ≤ Real.log (C.m : ℝ) :=
    Real.log_le_log hgpos hg
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  unfold b
  have h1 : (C.contourCount : ℝ) * Real.log ((C.m / 2 + 1 : ℕ) : ℝ) ≤
      (C.contourCount : ℝ) * Real.log (C.m : ℝ) :=
    mul_le_mul_of_nonneg_left hlog hd0
  have h2 : (C.contourCount : ℝ) * Real.log 2 ≤ (C.m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hdm hl2
  nlinarith

/-- The assembly: the cell inequality from the component statements. -/
theorem configWitnessCellBound_of_components
    (hQ : LogQIdentity) (hpos : QPosFacts) (hE : EnergyDecomposition)
    (hPk : PinFieldPiece) (hPν : ContFieldPiece) (hFμ : FreqFieldPiece)
    (hkk : KKPiece) (hkν : KNuPiece) (hνν : NuNuPiece) (hμμ : MuMuPiece)
    (hkμ : KMuPiece) (hνμ : NuMuPiece)
    (hpf : PinFieldLower) (hcf : ContFieldLower) (hff : FreqFieldLower)
    (hV : FixedVBound) (hob : OneBodyBound) :
    ConfigWitnessCellBound := by
  intro C hhead hQpos
  obtain ⟨hdist, hF⟩ := hpos C hQpos
  have hlogQ := hQ C hQpos
  have hEC := hE C hhead
  have h1 := hPk C
  have h2 := hPν C
  have h3 := hFμ C hhead
  have h4 := hkk C
  have h5 := hkν C
  have h6 := hνν C hdist
  have h7 := hμμ C
  have h8 := hkμ C
  have h9 := hνμ C hhead
  have h10 := hpf C
  have h11 := hcf C
  have h12 := hff C
  have h13 := hV C
  have h14 := hob C hF
  have hdb := contourCount_mul_b_le C
  -- sums of differences
  have hsA : (∑ s ∈ C.pinned, p0CompanionField (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) =
      (∑ s ∈ C.pinned, P0.A0 (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) -
        ∑ s ∈ C.pinned, P0.phi (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ) := by
    rw [← Finset.sum_sub_distrib]; rfl
  have hcA : (∑ a : Fin C.contourCount, p0CompanionField (C.contour a)) =
      (∑ a : Fin C.contourCount, P0.A0 (C.contour a)) -
        ∑ a : Fin C.contourCount, P0.phi (C.contour a) := by
    rw [← Finset.sum_sub_distrib]; rfl
  have hfB : (∑ r ∈ C.frequency,
        (P0.B0 ((r : ℝ) / (C.m : ℝ)) - P0.psi ((r : ℝ) / (C.m : ℝ)))) =
      (∑ r ∈ C.frequency, P0.B0 ((r : ℝ) / (C.m : ℝ))) -
        ∑ r ∈ C.frequency, P0.psi ((r : ℝ) / (C.m : ℝ)) := by
    rw [Finset.sum_sub_distrib]
  rw [hsA] at h1
  rw [hcA] at h2
  rw [hfB] at h3
  -- numerical facts
  have hm8 : (8 : ℝ) ≤ C.m := by exact_mod_cast C.m_ge_eight
  have hm0 : (0 : ℝ) < C.m := by linarith
  have hbal : (C.contourCount : ℝ) + C.pinned.card = C.m := by
    exact_mod_cast C.mass_balance
  have hk0 : (0 : ℝ) ≤ C.pinned.card := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ C.contourCount := Nat.cast_nonneg _
  set L := Real.log (C.m : ℝ) with hL
  have hL2 : 2 < L := by
    have := Real.log_le_log (by norm_num) hm8
    linarith [log_eight_gt_two]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hpi := log_two_pi_pos
  have hdP : 0 < dPlus := by norm_num [dPlus]
  have hdM : 0 < dMinus := by norm_num [dMinus]
  have hell : ell = Real.log 2 := rfl
  have h336 : (C.m : ℝ) * Real.log 336 =
      (C.m : ℝ) * Real.log 168 + (C.m : ℝ) * Real.log 2 := by
    rw [← pinnedQuadratureCost_log336]; ring
  -- the products that occur, compared with `m`
  have hkm : (C.pinned.card : ℝ) ≤ C.m := by linarith
  have hdm : (C.contourCount : ℝ) ≤ C.m := by linarith
  have hkL : (C.pinned.card : ℝ) * L ≤ (C.m : ℝ) * L :=
    mul_le_mul_of_nonneg_right hkm (by linarith)
  have hdL : (C.contourCount : ℝ) * L ≤ (C.m : ℝ) * L :=
    mul_le_mul_of_nonneg_right hdm (by linarith)
  have hkl2 : (C.pinned.card : ℝ) * Real.log 2 ≤ (C.m : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_right hkm hl2.le
  have hkpi : (C.pinned.card : ℝ) * Real.log (2 * Real.pi) ≤
      (C.m : ℝ) * Real.log (2 * Real.pi) :=
    mul_le_mul_of_nonneg_right hkm hpi.le
  have hdP' : (C.contourCount : ℝ) * (3 / (2 * dPlus)) ≤ (C.m : ℝ) * (3 / (2 * dPlus)) := by
    apply mul_le_mul_of_nonneg_right _ (by positivity); linarith
  have hmL : 4 * (C.m : ℝ) / 3 ≤ (C.m : ℝ) * L := by
    have := mul_le_mul_of_nonneg_left hL2.le hm0.le
    linarith
  have hcs : cStar * (C.m : ℝ) =
      4 * (C.m : ℝ) * Real.log (2 * Real.pi) + 9 * (C.m : ℝ) +
        (21 / 2 : ℝ) * (C.m : ℝ) * Real.log 2 + (C.m : ℝ) * Real.log 336 +
        (C.m : ℝ) * Real.log (35 / 3 : ℝ) + (C.m : ℝ) * (5 / (2 * dPlus)) +
        (C.m : ℝ) * (1 / (2 * dMinus)) := by
    unfold cStar; ring
  have hfrac1 : (C.m : ℝ) / (2 * dPlus) * 2 + (C.m : ℝ) * (3 / (2 * dPlus)) =
      (C.m : ℝ) * (5 / (2 * dPlus)) := by field_simp; ring
  have hfrac2 : (C.m : ℝ) / (2 * dMinus) = (C.m : ℝ) * (1 / (2 * dMinus)) := by ring
  -- energy times `m^2`
  have hmE : (C.m : ℝ) ^ 2 * p0TubeRegularizedEnergyValue (configTubeWitness C) =
      (C.m : ℝ) ^ 2 * ((9 / 2 : ℝ) - 2 * ell) + (C.m : ℝ) ^ 2 * ePk C +
        (C.m : ℝ) ^ 2 * ePν C + (C.m : ℝ) ^ 2 * (eBμ C - eΨμ C) +
        (C.m : ℝ) ^ 2 * eIkk C + 2 * ((C.m : ℝ) ^ 2 * eIkν C) +
        (C.m : ℝ) ^ 2 * eIνν C - (C.m : ℝ) ^ 2 * eLLμ C -
        (C.m : ℝ) ^ 2 * eMkμ C - (C.m : ℝ) ^ 2 * eMνμ C := by
    rw [hEC]; ring
  rw [hlogQ]
  have hgoal : -(C.m : ℝ) ^ 2 * p0TubeRegularizedEnergyValue (configTubeWitness C) =
      -((C.m : ℝ) ^ 2 * p0TubeRegularizedEnergyValue (configTubeWitness C)) := by ring
  rw [hgoal, hmE, hell]
  rw [hcs]
  linarith only [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, hdb,
    hkL, hdL, hkl2, hkpi, hdP', hmL, hfrac1, hfrac2, h336, hbal, hk0, hd0, hm0]

end

end Li2Lean.P0.CellBound
