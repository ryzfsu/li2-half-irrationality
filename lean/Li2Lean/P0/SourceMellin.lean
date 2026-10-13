/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Source
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.MeasureTheory.Integral.DominatedConvergence

open MeasureTheory
open Set Filter
open scoped Topology Interval

namespace Li2Lean

noncomputable section

private def sourceUnitInterval : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)

private theorem sourcePowerIntegral (n : ℕ) :
    (∫ x : ℝ, x ^ n ∂sourceUnitInterval) = 1 / ((n + 1 : ℕ) : ℝ) := by
  rw [sourceUnitInterval]
  rw [← integral_Ioc_eq_integral_Ioo]
  rw [← intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1)]
  rw [integral_pow]
  norm_num

private theorem sourceLogTail (a : ℝ) (ha : 1 < a) (i : ℕ) :
    sourceT0 a i + a ^ i * sourceLog a =
      - ∑' r : ℕ, (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) := by
  let q : ℝ := a⁻¹
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < q := by simp [q, ha0]
  have hqmul : a * q = 1 := by simp [q, ha0.ne']
  have hq_lt : q < 1 := by nlinarith [ha, hqpos, hqmul]
  have hqabs : |q| < 1 := by simpa [abs_of_pos hqpos] using hq_lt
  have hlog := Real.hasSum_pow_div_log_of_abs_lt_one hqabs
  have hsum : Summable (fun r : ℕ => q ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog.summable
  have hlogtsum :
      (∑' r : ℕ, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) = -Real.log (1 - q) := by
    simpa only [Nat.cast_add, Nat.cast_one] using hlog.tsum_eq
  have hsplit := hsum.sum_add_tsum_nat_add i
  have hprefix :
      (∑ r ∈ Finset.range i, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ)) =
        q ^ i * sourceT0 a i := by
    simp only [sourceT0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    have hr' : r + 1 ≤ i := by omega
    have hpow : q ^ i * a ^ (i - (r + 1)) = q ^ (r + 1) := by
      rw [show q = a⁻¹ by rfl]
      rw [pow_sub₀ a ha0.ne' hr']
      rw [inv_pow]
      field_simp [ha0.ne']
      simp [ha0.ne']
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [← hpow]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have htail :
      (∑' r : ℕ, q ^ (r + i + 1) / ((r + i + 1 : ℕ) : ℝ)) =
        q ^ i * ∑' r : ℕ, q ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    have hpow : q ^ i * q ^ (r + 1) = q ^ (r + i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hpow]
    norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
    ring
  have hlogval : sourceLog a = -∑' r : ℕ, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) := by
    rw [show sourceLog a = Real.log (1 - q) by rfl]
    linarith [hlogtsum]
  rw [hlogval]
  rw [hprefix, htail] at hsplit
  have hpowi : a ^ i * q ^ i = 1 := by
    rw [show q = a⁻¹ by rfl, ← mul_pow, mul_inv_cancel₀ ha0.ne', one_pow]
  have hmul := congrArg (fun z : ℝ => a ^ i * z) hsplit
  simp only [mul_add, ← mul_assoc, hpowi] at hmul
  dsimp [q] at hmul ⊢
  linarith [hmul]

private theorem sourceBetaTail (a : ℝ) (ha : 1 < a) (i : ℕ) :
    sourceB0 a i - a ^ i * sourceBeta a =
      - ∑' r : ℕ,
          (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) ^ 2 := by
  let q : ℝ := a⁻¹
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < q := by simp [q, ha0]
  have hqmul : a * q = 1 := by simp [q, ha0.ne']
  have hq_lt : q < 1 := by nlinarith [ha, hqpos, hqmul]
  have hqabs : |q| < 1 := by simpa [abs_of_pos hqpos] using hq_lt
  have hgeom : Summable (fun r : ℕ => q ^ (r + 1)) := by
    have hg := (hasSum_geometric_of_abs_lt_one hqabs).summable
    have hm := hg.mul_left q
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hsum : Summable (fun r : ℕ => q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2) := by
    apply hgeom.of_norm_bounded
    intro r
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg hqpos.le _) (sq_nonneg _))]
    rw [div_le_iff₀ (by positivity)]
    have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ r + 1 by omega)
    have hr2 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    nlinarith [mul_nonneg (pow_nonneg hqpos.le (r + 1)) (sub_nonneg.mpr hr2)]
  have hsplit := hsum.sum_add_tsum_nat_add i
  have hprefix :
      (∑ r ∈ Finset.range i, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2) =
        q ^ i * sourceB0 a i := by
    simp only [sourceB0]
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    rw [Finset.mem_range] at hr
    have hr' : r + 1 ≤ i := by omega
    have hpow : q ^ i * a ^ (i - (r + 1)) = q ^ (r + 1) := by
      rw [show q = a⁻¹ by rfl]
      rw [pow_sub₀ a ha0.ne' hr']
      rw [inv_pow]
      field_simp [ha0.ne']
      simp [ha0.ne']
    rw [div_eq_mul_inv, div_eq_mul_inv]
    rw [← hpow]
    rw [Nat.cast_add, Nat.cast_one]
    ring
  have htail :
      (∑' r : ℕ, q ^ (r + i + 1) / ((r + i + 1 : ℕ) : ℝ) ^ 2) =
        q ^ i * ∑' r : ℕ, q ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) ^ 2 := by
    rw [← tsum_mul_left]
    apply tsum_congr
    intro r
    have hpow : q ^ i * q ^ (r + 1) = q ^ (r + i + 1) := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_eq_mul_inv, div_eq_mul_inv, ← hpow]
    norm_num [Nat.cast_add, Nat.cast_one, add_comm, add_left_comm, add_assoc]
    ring
  have hbetaval : sourceBeta a =
      ∑' r : ℕ, q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2 := by
    simp [sourceBeta, q, Nat.cast_add, Nat.cast_one]
  rw [hbetaval]
  rw [hprefix, htail] at hsplit
  have hpowi : a ^ i * q ^ i = 1 := by
    rw [show q = a⁻¹ by rfl, ← mul_pow, mul_inv_cancel₀ ha0.ne', one_pow]
  have hmul := congrArg (fun z : ℝ => a ^ i * z) hsplit
  simp only [mul_add, ← mul_assoc, hpowi] at hmul
  dsimp [q] at hmul ⊢
  linarith [hmul]

private theorem sourceMellinSeries (a : ℝ) (ha : 1 < a) (i j : ℕ) :
    sourceM a i j = sourceMSeries a i j := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < a⁻¹ := by positivity
  have hq_lt : a⁻¹ < 1 := by
    exact (inv_lt_one₀ ha0).2 ha
  have hqabs : |a⁻¹| < 1 := by simpa [abs_of_pos hqpos] using hq_lt
  have hgeom : Summable (fun r : ℕ => (a⁻¹) ^ (r + 1)) := by
    have hg := (hasSum_geometric_of_abs_lt_one hqabs).summable
    have hm := hg.mul_left (a⁻¹)
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hsum (k : ℕ) :
      Summable (fun r : ℕ => (a⁻¹) ^ (r + 1) /
        ((k + r + 1 : ℕ) : ℝ)) := by
    apply hgeom.of_norm_bounded
    intro r
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg (inv_nonneg.mpr ha0.le) _)
      (by positivity))]
    rw [div_le_iff₀ (by positivity)]
    have hk : (1 : ℝ) ≤ ((k + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ k + r + 1 by omega)
    nlinarith [mul_nonneg (pow_nonneg (inv_nonneg.mpr ha0.le) (r + 1))
      (sub_nonneg.mpr hk)]
  by_cases hij : i = j
  · subst j
    simp [sourceM, sourceB0ij, sourceC0, sourceA0, sourceMSeries]
    rw [mul_comm (sourceBeta a) (a ^ i), sourceBetaTail a ha i]
    apply congrArg Neg.neg
    apply tsum_congr
    intro r
    have hd : ((i + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    field_simp [hd]
    rw [one_div]
    have hpow : (a⁻¹) ^ (r + 1) * a ^ (r + 1) = 1 := by
      rw [← mul_pow, inv_mul_cancel₀ ha0.ne', one_pow]
    rw [hpow]
    norm_num [Nat.cast_add, Nat.cast_one]
  · have hdi : (j : ℝ) - (i : ℝ) ≠ 0 := by
      have hji : j ≠ i := by
        intro h
        exact hij h.symm
      have hcast : (j : ℝ) ≠ (i : ℝ) := by exact_mod_cast hji
      exact sub_ne_zero.mpr hcast
    have hi := sourceLogTail a ha i
    have hj := sourceLogTail a ha j
    rw [sourceM]
    simp only [sourceB0ij, sourceC0, sourceA0, if_neg hij, mul_zero, sub_zero]
    have hfrac :
        (sourceT0 a i - sourceT0 a j) / ((j : ℝ) - (i : ℝ)) +
            sourceLog a * ((a ^ i - a ^ j) / ((j : ℝ) - (i : ℝ))) =
          (sourceT0 a i + a ^ i * sourceLog a -
            (sourceT0 a j + a ^ j * sourceLog a)) /
              ((j : ℝ) - (i : ℝ)) := by
      field_simp [hdi]
      ring
    rw [hfrac]
    rw [hi, hj]
    let fi : ℕ → ℝ := fun r =>
      (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ)
    let fj : ℕ → ℝ := fun r =>
      (a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)
    have hfi : Summable fi := by simpa [fi] using hsum i
    have hfj : Summable fj := by simpa [fj] using hsum j
    have hdiffsum := hfi.tsum_sub hfj
    have hpoint (r : ℕ) :
        (fi r - fj r) / ((j : ℝ) - (i : ℝ)) =
          (a⁻¹) ^ (r + 1) /
            ((i + r + 1 : ℕ) : ℝ) /
            ((j + r + 1 : ℕ) : ℝ) := by
      dsimp [fi, fj]
      have h1 : ((i + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have h2 : ((j + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      have hd : ((j + r + 1 : ℕ) : ℝ) - ((i + r + 1 : ℕ) : ℝ) =
          (j : ℝ) - (i : ℝ) := by
        norm_num [Nat.cast_add, Nat.cast_one]
      field_simp [hdi, h1, h2]
      rw [hd]
    calc
      (-∑' r : ℕ, fi r - -∑' r : ℕ, fj r) /
          ((j : ℝ) - (i : ℝ)) =
          -((∑' r : ℕ, fi r - ∑' r : ℕ, fj r) /
            ((j : ℝ) - (i : ℝ))) := by ring
      _ = -∑' r : ℕ, (fi r - fj r) /
          ((j : ℝ) - (i : ℝ)) := by
        rw [← hdiffsum, div_eq_mul_inv, ← tsum_mul_right]
        congr 1
      _ = -∑' r : ℕ, (a⁻¹) ^ (r + 1) /
          ((i + r + 1 : ℕ) : ℝ) /
          ((j + r + 1 : ℕ) : ℝ) := by
        congr 1
        apply tsum_congr
        intro r
        simpa [Nat.cast_add, Nat.cast_one, inv_pow] using hpoint r
private def sourceMellinTerm (q : ℝ) (i j r : ℕ) (x y : ℝ) : ℝ :=
  q ^ (r + 1) * (x ^ (i + r) * y ^ (j + r))

private def sourceMellinXTerm (q : ℝ) (i j r : ℕ) (x : ℝ) : ℝ :=
  q ^ (r + 1) * x ^ (i + r) / ((j + r + 1 : ℕ) : ℝ)

private theorem sourceIntegrablePow (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) sourceUnitInterval := by
  have hbase : IntegrableOn (fun x : ℝ => x ^ n) (Set.Ioo (0 : ℝ) 1) :=
    (intervalIntegrable_iff_integrableOn_Ioo_of_le
      (by norm_num : (0 : ℝ) ≤ 1)).mp (intervalIntegral.intervalIntegrable_pow n)
  simpa only [IntegrableOn, sourceUnitInterval] using hbase

private theorem sourceMellinKernelHasSum (a : ℝ) (ha : 1 < a) (i j : ℕ)
    (x y : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) (hy : y ∈ Set.Ioo (0 : ℝ) 1) :
    HasSum (fun r : ℕ => sourceMellinTerm (a⁻¹) i j r x y)
      (x ^ i * y ^ j / (a - x * y)) := by
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < a⁻¹ := by positivity
  have hq_lt : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha
  have hxypos : 0 < x * y := mul_pos hx.1 hy.1
  have hxylt : x * y < 1 := by
    have hlt : x * y < x := by nlinarith [mul_lt_mul_of_pos_left hy.2 hx.1]
    linarith [hlt, hx.2]
  have hqxy : |a⁻¹ * x * y| < 1 := by
    rw [abs_of_pos (mul_pos (mul_pos hqpos hx.1) hy.1)]
    have hlt : a⁻¹ * (x * y) < 1 * 1 :=
      mul_lt_mul hq_lt hxylt.le hxypos (by norm_num)
    simpa [mul_assoc] using hlt
  have hgeo := (hasSum_geometric_of_abs_lt_one hqxy)
  have hmul := hgeo.mul_left (a⁻¹ * x ^ i * y ^ j)
  have hterm (r : ℕ) :
      a⁻¹ * x ^ i * y ^ j * (a⁻¹ * x * y) ^ r =
        sourceMellinTerm (a⁻¹) i j r x y := by
    dsimp [sourceMellinTerm]
    rw [mul_pow, pow_succ, pow_add, pow_add]
    ring
  have hden : a - x * y ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hxylt ha))
  have hvalue : a⁻¹ * x ^ i * y ^ j * (1 - a⁻¹ * x * y)⁻¹ =
      x ^ i * y ^ j / (a - x * y) := by
    field_simp [ha0.ne', hden]
  convert hmul using 1 <;> simp only [hterm, hvalue]

private theorem sourceInnerMellinIntegral (a : ℝ) (ha : 1 < a) (i j : ℕ)
    (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
    (∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂sourceUnitInterval) =
      ∑' r : ℕ, sourceMellinXTerm (a⁻¹) i j r x := by
  let μ := sourceUnitInterval
  let F : ℕ → ℝ → ℝ := fun r y => sourceMellinTerm (a⁻¹) i j r x y
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < a⁻¹ := by positivity
  have hq_lt : a⁻¹ < 1 := (inv_lt_one₀ ha0).2 ha
  have hqabs : |a⁻¹| < 1 := by rw [abs_of_pos hqpos]; exact hq_lt
  have hgeom : Summable (fun r : ℕ => (a⁻¹) ^ (r + 1)) := by
    have hg := (hasSum_geometric_of_abs_lt_one hqabs).summable
    have hm := hg.mul_left (a⁻¹)
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hF (r : ℕ) : Integrable (F r) μ := by
    have hp := sourceIntegrablePow (j + r)
    simpa only [μ, F, sourceMellinTerm, mul_assoc] using
      hp.const_mul ((a⁻¹) ^ (r + 1) * x ^ (i + r))
  have hpowint (k : ℕ) :
      (∫ y : ℝ, y ^ k ∂μ) = 1 / ((k + 1 : ℕ) : ℝ) := by
    simpa [μ] using sourcePowerIntegral k
  have hnorm (r : ℕ) :
      (∫ y : ℝ, ‖F r y‖ ∂μ) =
        (a⁻¹) ^ (r + 1) * x ^ (i + r) /
          ((j + r + 1 : ℕ) : ℝ) := by
    calc
      (∫ y : ℝ, ‖F r y‖ ∂μ) =
          ∫ y : ℝ, ((a⁻¹) ^ (r + 1) * x ^ (i + r)) * y ^ (j + r) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
        have hnonneg : 0 ≤ F r y := by
          dsimp [F, sourceMellinTerm]
          exact mul_nonneg (pow_nonneg (by positivity) _)
            (mul_nonneg (pow_nonneg hx.1.le _) (pow_nonneg hy.1.le _))
        rw [Real.norm_of_nonneg hnonneg]
        dsimp [F, sourceMellinTerm]
        ring
      _ = ((a⁻¹) ^ (r + 1) * x ^ (i + r)) *
          ∫ y : ℝ, y ^ (j + r) ∂μ := integral_const_mul _ _
      _ = _ := by rw [hpowint]; ring
  have hsum : Summable (fun r : ℕ => ∫ y : ℝ, ‖F r y‖ ∂μ) := by
    apply hgeom.of_norm_bounded
    intro r
    rw [hnorm r, Real.norm_of_nonneg
      (div_nonneg (mul_nonneg (pow_nonneg (inv_nonneg.mpr ha0.le) _) (pow_nonneg hx.1.le _))
        (by positivity))]
    have hxpow : x ^ (i + r) ≤ 1 := pow_le_one₀ hx.1.le hx.2.le
    have hden : (1 : ℝ) ≤ ((j + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ j + r + 1 by omega)
    have hqpow : 0 ≤ (a⁻¹) ^ (r + 1) := pow_nonneg (inv_nonneg.mpr ha0.le) _
    apply (div_le_iff₀ (by positivity)).2
    calc
      (a⁻¹) ^ (r + 1) * x ^ (i + r) ≤ (a⁻¹) ^ (r + 1) * 1 :=
        mul_le_mul_of_nonneg_left hxpow hqpow
      _ ≤ (a⁻¹) ^ (r + 1) * ((j + r + 1 : ℕ) : ℝ) :=
        mul_le_mul_of_nonneg_left hden hqpow
  have hpoint :
      (fun y : ℝ => ∑' r : ℕ, F r y) =ᵐ[μ]
        (fun y => x ^ i * y ^ j / (a - x * y)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with y hy
    exact (sourceMellinKernelHasSum a ha i j x y hx hy).tsum_eq
  calc
    (∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂μ) =
        ∫ y : ℝ, ∑' r : ℕ, F r y ∂μ := integral_congr_ae hpoint.symm
    _ = ∑' r : ℕ, ∫ y : ℝ, F r y ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = ∑' r : ℕ, sourceMellinXTerm (a⁻¹) i j r x := by
      apply tsum_congr
      intro r
      have hterm (y : ℝ) : F r y =
          ((a⁻¹) ^ (r + 1) * x ^ (i + r)) * y ^ (j + r) := by
        dsimp [F, sourceMellinTerm]
        ring
      rw [show (∫ y : ℝ, F r y ∂μ) =
          ∫ y : ℝ, ((a⁻¹) ^ (r + 1) * x ^ (i + r)) * y ^ (j + r) ∂μ by
        apply integral_congr_ae
        filter_upwards with y
        exact hterm y]
      rw [integral_const_mul, hpowint]
      dsimp [sourceMellinXTerm]
      ring

private theorem sourceMellinMeasureIntegral (a : ℝ) (ha : 1 < a) (i j : ℕ) :
    (∫ x : ℝ, ∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂sourceUnitInterval
      ∂sourceUnitInterval) =
      ∑' r : ℕ,
        (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) /
          ((j + r + 1 : ℕ) : ℝ) := by
  let μ := sourceUnitInterval
  let F : ℕ → ℝ → ℝ := fun r x => sourceMellinXTerm (a⁻¹) i j r x
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < a⁻¹ := by positivity
  have hqabs : |a⁻¹| < 1 := by
    rw [abs_of_pos hqpos]
    exact (inv_lt_one₀ ha0).2 ha
  have hgeom : Summable (fun r : ℕ => (a⁻¹) ^ (r + 1)) := by
    have hg := (hasSum_geometric_of_abs_lt_one hqabs).summable
    have hm := hg.mul_left (a⁻¹)
    convert hm using 1
    ext r
    rw [pow_succ]
    ring
  have hinner :
      (fun x : ℝ => ∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂μ) =ᵐ[μ]
        (fun x => ∑' r : ℕ, F r x) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    simpa [μ, F, sourceMellinXTerm] using sourceInnerMellinIntegral a ha i j x hx
  have hF (r : ℕ) : Integrable (F r) μ := by
    have hp := sourceIntegrablePow (i + r)
    have hc : (a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ) ≠ 0 := by positivity
    have hrepr : F r = fun x =>
        ((a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) * x ^ (i + r) := by
      funext x
      dsimp [F, sourceMellinXTerm]
      ring
    rw [hrepr]
    exact hp.const_mul _
  have hnorm (r : ℕ) :
      (∫ x : ℝ, ‖F r x‖ ∂μ) =
        ((a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) /
          ((i + r + 1 : ℕ) : ℝ) := by
    have hc : 0 ≤ (a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ) := by positivity
    calc
      (∫ x : ℝ, ‖F r x‖ ∂μ) =
          ∫ x : ℝ,
            ((a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) * x ^ (i + r) ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        have hn : 0 ≤ F r x := by
          dsimp [F, sourceMellinXTerm]
          apply div_nonneg
          · exact mul_nonneg (pow_nonneg (by positivity) _)
              (pow_nonneg hx.1.le _)
          · positivity
        rw [Real.norm_of_nonneg hn]
        dsimp [F, sourceMellinXTerm]
        ring
      _ = ((a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) *
          ∫ x : ℝ, x ^ (i + r) ∂μ := integral_const_mul _ _
      _ = _ := by
        have hpowint :
            (∫ x : ℝ, x ^ (i + r) ∂μ) = 1 / ((i + r + 1 : ℕ) : ℝ) := by
          simpa [μ] using sourcePowerIntegral (i + r)
        rw [hpowint]
        ring
  have hsum : Summable (fun r : ℕ => ∫ x : ℝ, ‖F r x‖ ∂μ) := by
    apply hgeom.of_norm_bounded
    intro r
    rw [hnorm r, Real.norm_of_nonneg (div_nonneg (div_nonneg
      (pow_nonneg (inv_nonneg.mpr ha0.le) _) (by positivity)) (by positivity))]
    have hqpow : 0 ≤ (a⁻¹) ^ (r + 1) := pow_nonneg (inv_nonneg.mpr ha0.le) _
    have hdeni : (1 : ℝ) ≤ ((i + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ i + r + 1 by omega)
    have hdenj : (1 : ℝ) ≤ ((j + r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ j + r + 1 by omega)
    have hdeni0 : 0 < ((i + r + 1 : ℕ) : ℝ) := by positivity
    have hdenj0 : 0 < ((j + r + 1 : ℕ) : ℝ) := by positivity
    apply (div_le_iff₀ hdeni0).2
    apply (div_le_iff₀ hdenj0).2
    calc
      (a⁻¹) ^ (r + 1) ≤ (a⁻¹) ^ (r + 1) * ((i + r + 1 : ℕ) : ℝ) :=
        le_mul_of_one_le_right hqpow hdeni
      _ ≤ (a⁻¹) ^ (r + 1) * ((i + r + 1 : ℕ) : ℝ) *
          ((j + r + 1 : ℕ) : ℝ) := by
        apply le_mul_of_one_le_right
        · positivity
        · exact hdenj
  calc
    (∫ x : ℝ, ∫ y : ℝ, x ^ i * y ^ j / (a - x * y) ∂μ ∂μ) =
        ∫ x : ℝ, ∑' r : ℕ, F r x ∂μ := integral_congr_ae hinner
    _ = ∑' r : ℕ, ∫ x : ℝ, F r x ∂μ :=
      (integral_tsum_of_summable_integral_norm hF hsum).symm
    _ = ∑' r : ℕ,
        (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) /
          ((j + r + 1 : ℕ) : ℝ) := by
      apply tsum_congr
      intro r
      have hrepr : F r = fun x =>
          ((a⁻¹) ^ (r + 1) / ((j + r + 1 : ℕ) : ℝ)) * x ^ (i + r) := by
        funext x
        dsimp [F, sourceMellinXTerm]
        ring
      rw [hrepr, integral_const_mul]
      have hpowint :
          (∫ x : ℝ, x ^ (i + r) ∂μ) = 1 / ((i + r + 1 : ℕ) : ℝ) := by
        simpa [μ] using sourcePowerIntegral (i + r)
      rw [hpowint]
      ring

private theorem sourceMellinIntegralSeries (a : ℝ) (ha : 1 < a) (i j : ℕ) :
    (∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
      x ^ i * y ^ j / (a - x * y)) =
      ∑' r : ℕ,
        (a⁻¹) ^ (r + 1) / ((i + r + 1 : ℕ) : ℝ) /
          ((j + r + 1 : ℕ) : ℝ) := by
  have hmeasure := sourceMellinMeasureIntegral a ha i j
  simpa only [sourceUnitInterval, intervalIntegral.integral_of_le
      (by norm_num : (0 : ℝ) ≤ 1), integral_Ioc_eq_integral_Ioo] using hmeasure

/-- The exact paper-facing Mellin/source identities of v10 `eq:source-mellin`. -/
theorem sourceMellinStatement_proved : sourceMellinStatement := by
  intro a ha i j
  constructor
  · exact sourceMellinSeries a ha i j
  · rw [sourceMellinSeries a ha i j]
    dsimp [sourceMIntegral, sourceMSeries]
    rw [sourceMellinIntegralSeries a ha i j]

#print axioms sourceMellinStatement_proved

end

end Li2Lean
