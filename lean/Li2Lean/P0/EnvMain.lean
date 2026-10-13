/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.EnvAndreief
import Li2Lean.P0.ConfigWitnessFiniteEnergy

/-!
# The signed coefficient envelope `‖G_m(β)‖ ≤ E_m(∞)` (paper v13 `p0-analytic.tex` l. 629)

Assembly:
1. `‖G_m(β)‖ ≤ sup_H ‖det truncMatrix m H‖` (`norm_GmBeta_le_of_trunc`: source bank,
   unipotent row operation, frequency truncation);
2. frequency Cauchy-Binet (`norm_det_trunc_le`);
3. row-by-row splitting of the source rows into diagonal and contour parts
   (`det_split_rows`), block reduction of the pinned rows (`norm_det_split_eq`);
4. Andreief antisymmetrization and the pointwise envelope (`norm_det_pinnedD_le`);
5. Tonelli (finite sums and integrals) to `E m H` and `E m H ≤ E_m(∞)`.

The result `p0SignedCoefficientEnvelope_proved` is premise-free.
-/

open Finset MeasureTheory

namespace Li2Lean.P0.Env

noncomputable section

/-- The integrand of `norm_det_pinnedD_le`, before the pinned and frequency factors. -/
def contourIntegrand (m : ℕ) (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) : ℝ :=
  (∏ l, ‖p0Entire (m / 2) (p0EllipsePoint m (u l))‖) *
    ‖contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l))‖ *
    ‖(contourQMinors S h4 hSI r.val r.property.1 (fun l => p0EllipsePoint m (u l))).2.2‖ *
    ∏ l, contourArcDensity m (u l)

theorem envelopeTerm_eq (m : ℕ) (h4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ Iset m)
    (r : IncreasingFrequencyTuple (m / 2) m) (u : Fin (m - S.card) → ℝ) :
    FrequencyLimit.envelopeTerm m h4 S hSI r u =
      ((∏ l, frequencyWeightReal (m / 2) (r.val l)) *
        ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
          (fun j => ((r.val j : ℕ) : ℂ))‖) *
        ((∏ a ∈ S, ell * UReal (m / 2) a) * contourIntegrand m S h4 hSI r u) := by
  simp only [FrequencyLimit.envelopeTerm, contourQValue, contourIntegrand, norm_mul]
  have h1 : (contourQMinors S h4 hSI r.val r.property.1
      (fun l => p0EllipsePoint m (u l))).1 =
      contourQLeftMinor S hSI (fun l => p0EllipsePoint m (u l)) := rfl
  have h2 : (contourQMinors S h4 hSI r.val r.property.1
      (fun l => p0EllipsePoint m (u l))).2.1 =
      cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
        (fun j => ((r.val j : ℕ) : ℂ)) := rfl
  rw [h1, h2]
  ring

theorem tOf_image_rowIndex (m : ℕ) (t : Finset (Fin m)) :
    tOf m (t.image (rowIndex m)) = t := by
  ext i
  simp only [tOf, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
  constructor
  · rintro ⟨j, hj, hji⟩
    rw [rowIndex_injective m hji] at hj
    exact hj
  · intro hi; exact ⟨i, hi, rfl⟩

/-- Contour bound for `[K_{R,J}; C]`, summed over pinned sets. -/
theorem norm_det_Ymat_le (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (r : IncreasingFrequencyTuple (m / 2) m) :
    ‖(Ymat m r.val).det‖ ≤ ∑ S ∈ (Iset m).powerset,
      if hSI : S ⊆ Iset m then
        (∏ a ∈ S, ell * UReal (m / 2) a) * (((m - S.card).factorial : ℝ)⁻¹ *
          ∫ u, contourIntegrand m S h4 hSI r u
            ∂(ContourKit.productMeasure contourParameterMeasure))
      else 0 := by
  classical
  rw [det_split_rows (Ymat m r.val) (Pp m) (Qp m) (Ymat_inr_split m h4 r.val)]
  refine (norm_sum_le _ _).trans ?_
  have hre : (∑ t : Finset (Fin m), ‖(splitMat (Ymat m r.val) (Pp m) (Qp m) t).det‖) =
      ∑ S ∈ (Iset m).powerset,
        ‖(splitMat (Ymat m r.val) (Pp m) (Qp m) (tOf m S)).det‖ := by
    symm
    apply Finset.sum_nbij' (fun S => tOf m S) (fun t => t.image (rowIndex m))
    · intro S _; exact Finset.mem_univ _
    · intro t _
      rw [Finset.mem_powerset]
      intro a ha
      obtain ⟨i, _, rfl⟩ := Finset.mem_image.mp ha
      exact Finset.mem_image_of_mem _ (Finset.mem_univ i)
    · intro S hS; exact tOf_image m S (Finset.mem_powerset.mp hS)
    · intro t _; exact tOf_image_rowIndex m t
    · intro S _; rfl
  rw [hre]
  apply Finset.sum_le_sum
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  rw [dif_pos hSI, norm_det_split_eq m hm h4 S hSI r.val, mul_comm]
  exact mul_le_mul_of_nonneg_left (norm_det_pinnedD_le m hm h4 S hSI r.val r.property.1)
    (Finset.prod_nonneg (fun a _ => mul_nonneg (Real.log_nonneg (by norm_num))
      (by unfold UReal; positivity)))

/-- The truncated determinants are bounded by the finite envelope `E m H`. -/
theorem norm_det_trunc_le_E (m H : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    ‖(truncMatrix m H).det‖ ≤ E m H h4 := by
  classical
  refine (norm_det_trunc_le m H).trans ?_
  set c : IncreasingFrequencyTuple (m / 2) m → ℝ := fun r =>
    (∏ l, frequencyWeightReal (m / 2) (r.val l)) *
      ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ)) (fun j => ((r.val j : ℕ) : ℂ))‖
  have hc0 : ∀ r, 0 ≤ c r := fun r => mul_nonneg
    (Finset.prod_nonneg (fun l _ => by unfold frequencyWeightReal; positivity)) (norm_nonneg _)
  have step1 : (∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
      (∏ l, frequencyWeightReal (m / 2) (r.val l)) *
        ‖cauchyDet (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
            (fun j => ((r.val j : ℕ) : ℂ))‖ * ‖(Ymat m r.val).det‖) ≤
      ∑ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H, c r *
        ∑ S ∈ (Iset m).powerset,
          if hSI : S ⊆ Iset m then
            (∏ a ∈ S, ell * UReal (m / 2) a) * (((m - S.card).factorial : ℝ)⁻¹ *
              ∫ u, contourIntegrand m S h4 hSI r u
                ∂(ContourKit.productMeasure contourParameterMeasure))
          else 0 := by
    apply Finset.sum_le_sum
    intro r _
    exact mul_le_mul_of_nonneg_left (norm_det_Ymat_le m hm h4 r) (hc0 r)
  refine step1.trans (le_of_eq ?_)
  unfold E
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro S hS
  have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
  simp only [dif_pos hSI]
  rw [FrequencyLimit.contourEContribution_eq_cutoff]
  have hint : ∀ r ∈ FrequencyCutoff.cutoffTuples (m / 2) m H,
      Integrable (fun u => FrequencyLimit.envelopeTerm m h4 S hSI r u)
        (ContourKit.productMeasure contourParameterMeasure) := fun r _ =>
    FrequencyRegularity.integrable_parameter
      (FrequencyLimit.continuous_envelopeTerm m hm h4 S hSI r)
  rw [integral_finsetSum _ hint, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp_rw [envelopeTerm_eq m h4 S hSI r]
  rw [integral_const_mul, integral_const_mul]
  ring

end

end Li2Lean.P0.Env

namespace Li2Lean.P0.CoefficientAssembly

/-- **The signed coefficient envelope** (paper v13 l. 629), premise-free:
`‖G_m(β)‖ ≤ E_m(∞)` for every `m ≥ 8` with `4 ∣ m`. -/
theorem p0SignedCoefficientEnvelope_proved : P0SignedCoefficientEnvelope := by
  intro m hm8 h4
  have hm : 0 < m := by omega
  have hfin : FrequencyLimit.fullEnvelope m h4 ≠ ⊤ := by
    rw [← FrequencyLimit.EInfinityENN_eq_fullEnvelope m hm h4]
    exact (FrequencyLimit.full_cutoffENN_actual_tail_factor m hm h4).1
  apply Env.norm_GmBeta_le_of_trunc m hm h4
  intro H
  exact (Env.norm_det_trunc_le_E m H hm h4).trans (E_le_EInfinity hm h4 H hfin)

end Li2Lean.P0.CoefficientAssembly

namespace Li2Lean

open Li2Lean.P0.CoefficientAssembly

/-- Main consumer with the signed envelope discharged: irrationality of `Li2(1/2)` from the
witness cell inequality and the integerizer bound alone. -/
theorem li2_half_irrational_of_cellBound (hcell : ConfigWitnessCellBound)
    (hIntegerizer : P0IntegerizerBound p0A2CanonicalFamily) :
    Irrational (li2InvValue (2 : ℤ)) :=
  li2_half_irrational_of_envelope_cellBound p0SignedCoefficientEnvelope_proved hcell
    hIntegerizer

end Li2Lean
