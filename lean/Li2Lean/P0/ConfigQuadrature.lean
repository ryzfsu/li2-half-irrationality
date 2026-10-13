/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigMixedCell
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

open MeasureTheory
open scoped BigOperators Nat

namespace Li2Lean.P0.Config

noncomputable section

/-!
# Finite-configuration quadrature estimates

Kernel proofs of the three quadrature assertions stated in `Config`:

* `bzeroQuadratureBound : BzeroQuadratureBound` (`eq:config-Bzero`):
  monotone left-endpoint quadrature for the fixed-grid field `B0`, with the
  exact two-sided bound `0 ≤ m B0(t) - Σ log(t + i/m) ≤ log (35/3)`.
* `pinnedQuadratureBound : PinnedQuadratureBound` (`eq:config-pinned`):
  the omitted-site factorials against the cell integral of `log |i/m - y|`.
* `psiQuadratureBound C : PsiQuadratureBound C` (`eq:config-psi`), for every
  literal finite configuration `C`, including the cell normalization
  `∫ psi ∂ C.mu = Σ_r ∫_{(r-1)/m}^{r/m} psi`.

All three are proved from Mathlib only; no hypothesis restates a conclusion.
-/

/-! ## A scaled monotone block comparison -/

/-- Left- and right-endpoint quadrature for `u ↦ log (t + u)` on a block of
`n` consecutive lattice cells of width `1/m` starting at `s/m`. -/
theorem quad_scaled_log_block {m n s : ℕ} (hm : 0 < m) {t : ℝ} (ht : 0 < t) :
    (∑ k ∈ Finset.range n, Real.log (t + ((s + k : ℕ) : ℝ) / m)) ≤
        (m : ℝ) * (∫ x in (s : ℝ) / m..((s + n : ℕ) : ℝ) / m, Real.log (t + x)) ∧
      (m : ℝ) * (∫ x in (s : ℝ) / m..((s + n : ℕ) : ℝ) / m, Real.log (t + x)) -
          ∑ k ∈ Finset.range n, Real.log (t + ((s + k : ℕ) : ℝ) / m) ≤
        Real.log (t + ((s + n : ℕ) : ℝ) / m) - Real.log (t + (s : ℝ) / m) := by
  set f : ℝ → ℝ := fun u => Real.log (t + u / m) with hf
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hmono : MonotoneOn f (Set.Icc (s : ℝ) ((s : ℝ) + (n : ℕ))) := by
    intro x hx y hy hxy
    have hx0 : 0 ≤ x := le_trans (Nat.cast_nonneg _) hx.1
    have hxm : 0 ≤ x / m := div_nonneg hx0 hmR.le
    apply Real.log_le_log
    · linarith
    · have := div_le_div_of_nonneg_right hxy hmR.le
      linarith
  have hchange : (∫ u in (s : ℝ)..(s : ℝ) + (n : ℕ), f u) =
      (m : ℝ) * ∫ x in (s : ℝ) / m..((s + n : ℕ) : ℝ) / m, Real.log (t + x) := by
    have h := intervalIntegral.integral_comp_div (fun x => Real.log (t + x))
      (a := (s : ℝ)) (b := (s : ℝ) + (n : ℕ)) (ne_of_gt hmR)
    rw [hf, h, smul_eq_mul, Nat.cast_add]
  have h1 := hmono.sum_le_integral
  have h2 := hmono.integral_le_sum
  rw [hchange] at h1 h2
  have hl : ∀ k : ℕ, f ((s : ℝ) + (k : ℕ)) =
      Real.log (t + ((s + k : ℕ) : ℝ) / m) := by
    intro k
    simp only [hf, Nat.cast_add]
  have htel : ∑ i ∈ Finset.range n, f ((s : ℝ) + ((i + 1 : ℕ) : ℝ)) -
      ∑ i ∈ Finset.range n, f ((s : ℝ) + (i : ℕ)) =
        f ((s : ℝ) + (n : ℕ)) - f ((s : ℝ) + ((0 : ℕ) : ℝ)) := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_range_sub (fun i : ℕ => f ((s : ℝ) + (i : ℕ))) n
  simp only [hl] at h1 h2 htel
  refine ⟨h1, ?_⟩
  have h0 : Real.log (t + ((s + 0 : ℕ) : ℝ) / m) = Real.log (t + (s : ℝ) / m) := by
    simp
  rw [h0] at htel
  linarith

/-! ## `eq:config-Bzero` -/

private theorem quad_bzero_endpoint_bound {t : ℝ} (ht : (1 / 2 : ℝ) ≤ t) :
    (Real.log (t + 5 / 4) - Real.log (t + 1 / 4)) +
        (Real.log (t + 2) - Real.log (t + 0)) ≤ Real.log (35 / 3 : ℝ) := by
  have ht0 : 0 < t := by linarith
  have h1 : Real.log (t + 5 / 4) - Real.log (t + 1 / 4) ≤ Real.log (7 / 3 : ℝ) := by
    rw [← Real.log_div (by linarith) (by linarith)]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ (by linarith)]
    linarith
  have h2 : Real.log (t + 2) - Real.log (t + 0) ≤ Real.log (5 : ℝ) := by
    rw [add_zero, ← Real.log_div (by linarith) (by linarith)]
    apply Real.log_le_log (by positivity)
    rw [div_le_iff₀ ht0]
    linarith
  have h3 : Real.log (35 / 3 : ℝ) = Real.log (7 / 3 : ℝ) + Real.log 5 := by
    rw [← Real.log_mul (by norm_num) (by norm_num)]
    norm_num
  linarith

/-- `eq:config-Bzero`: monotone quadrature for the fixed-grid field. -/
theorem bzeroQuadratureBound : BzeroQuadratureBound := by
  intro m hm8 h4 t ht
  obtain ⟨k, rfl⟩ := h4
  have hk : 0 < k := by omega
  have hm : 0 < 4 * k := by omega
  have hmR : (0 : ℝ) < ((4 * k : ℕ) : ℝ) := by exact_mod_cast hm
  have ht0 : 0 < t := by linarith
  -- pinned block: sites `k, …, 5k - 1`
  have hP := quad_scaled_log_block (m := 4 * k) (n := 4 * k) (s := k) hm ht0
  -- frequency block: sites `0, …, 8k - 1`
  have hF := quad_scaled_log_block (m := 4 * k) (n := 2 * (4 * k)) (s := 0) hm ht0
  have hdiv1 : (4 * k) / 4 = k := by omega
  have hdiv2 : 5 * (4 * k) / 4 = k + 4 * k := by omega
  have hsumP : (∑ i ∈ pinnedUniverse (4 * k),
        Real.log (t + (i : ℝ) / ((4 * k : ℕ) : ℝ))) =
      ∑ j ∈ Finset.range (4 * k),
        Real.log (t + ((k + j : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ)) := by
    rw [pinnedUniverse, hdiv1, hdiv2, Finset.sum_Ico_eq_sum_range,
      show k + 4 * k - k = 4 * k by omega]
  have hsumF : (∑ j ∈ frequencyUniverse (4 * k),
        Real.log (t + (j : ℝ) / ((4 * k : ℕ) : ℝ))) =
      ∑ j ∈ Finset.range (2 * (4 * k)),
        Real.log (t + ((0 + j : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ)) := by
    rw [frequencyUniverse]
    simp
  have hkR : (0 : ℝ) < k := by exact_mod_cast hk
  have e1 : (k : ℝ) / ((4 * k : ℕ) : ℝ) = 1 / 4 := by
    push_cast; field_simp
  have e2 : ((k + 4 * k : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ) = 5 / 4 := by
    push_cast; field_simp; ring
  have e3 : ((0 : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ) = 0 := by simp
  have e4 : ((0 + 2 * (4 * k) : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ) = 2 := by
    push_cast; field_simp; ring
  rw [e1, e2] at hP
  rw [e3, e4] at hF
  have hB : ((4 * k : ℕ) : ℝ) * B0 t - fixedLatticeLogSum (4 * k) t =
      (((4 * k : ℕ) : ℝ) * (∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ), Real.log (t + x)) -
          ∑ j ∈ Finset.range (4 * k),
            Real.log (t + ((k + j : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ))) +
        (((4 * k : ℕ) : ℝ) * (∫ x in (0 : ℝ)..2, Real.log (t + x)) -
          ∑ j ∈ Finset.range (2 * (4 * k)),
            Real.log (t + ((0 + j : ℕ) : ℝ) / ((4 * k : ℕ) : ℝ))) := by
    rw [B0, fixedLatticeLogSum, hsumP, hsumF]
    ring
  have hend := quad_bzero_endpoint_bound ht
  rw [hB]
  constructor
  · linarith [hP.1, hF.1]
  · linarith [hP.2, hF.2]

/-! ## `eq:config-pinned` -/

/-- `n log n - n ≤ log n!`, from `n^n / n! ≤ e^n`. -/
theorem quad_log_factorial_lower (n : ℕ) :
    (n : ℝ) * Real.log n - n ≤ Real.log (n ! : ℝ) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hfac : (0 : ℝ) < (n ! : ℝ) := by exact_mod_cast Nat.factorial_pos n
  have h := Real.pow_div_factorial_le_exp (x := (n : ℝ)) hnR.le n
  have hpos : 0 < (n : ℝ) ^ n / (n ! : ℝ) := by positivity
  have hlog := Real.log_le_log hpos h
  rw [Real.log_exp, Real.log_div (by positivity) hfac.ne', Real.log_pow] at hlog
  linarith

/-- Scaling identity `m ((n/m) log (n/m) - n/m) = n log n - n - n log m`. -/
theorem quad_scaled_xlogx {m : ℕ} (hm : 0 < m) (n : ℕ) :
    (m : ℝ) * (((n : ℝ) / m) * Real.log ((n : ℝ) / m) - (n : ℝ) / m) =
      (n : ℝ) * Real.log n - n - n * Real.log m := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [Real.log_div hnR.ne' hmR.ne']
  field_simp
  ring

/-- Exact value of the pinned cell integral, in scaled coordinates. -/
theorem quad_pinned_cell_integral {m : ℕ} (hm : 0 < m) (a nL nR : ℕ) :
    (m : ℝ) *
        (∫ y in ((a : ℝ) / (m : ℝ))..(((a + (nL + nR + 1) : ℕ) : ℝ) / (m : ℝ)),
          Real.log |((a + nL : ℕ) : ℝ) / (m : ℝ) - y|) =
      ((nL : ℝ) * Real.log nL - nL - nL * Real.log m) +
        (((nR + 1 : ℕ) : ℝ) * Real.log ((nR + 1 : ℕ) : ℝ) - ((nR + 1 : ℕ) : ℝ) -
          ((nR + 1 : ℕ) : ℝ) * Real.log m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hsub := intervalIntegral.integral_comp_sub_left (fun x : ℝ => Real.log |x|)
    (a := (a : ℝ) / m) (b := ((a + (nL + nR + 1) : ℕ) : ℝ) / m)
    (((a + nL : ℕ) : ℝ) / m)
  rw [hsub]
  have hA : ((a + nL : ℕ) : ℝ) / m - (a : ℝ) / m = (nL : ℝ) / m := by
    push_cast; ring
  have hB : ((a + nL : ℕ) : ℝ) / m - ((a + (nL + nR + 1) : ℕ) : ℝ) / m =
      -(((nR + 1 : ℕ) : ℝ) / m) := by
    push_cast; ring
  rw [hA, hB]
  simp_rw [Real.log_abs]
  rw [integral_log, Real.log_neg_eq_log]
  have h1 := quad_scaled_xlogx hm nL
  have h2 := quad_scaled_xlogx hm (nR + 1)
  linear_combination h1 + h2

/-- `eq:config-pinned`: the omitted-site factorial comparison. -/
theorem pinnedQuadratureBound : PinnedQuadratureBound := by
  intro m a N i hm hN hai hiN
  obtain ⟨nL, rfl⟩ := Nat.exists_eq_add_of_le hai
  obtain ⟨nR, hNdef⟩ : ∃ nR, N = nL + nR + 1 := ⟨N - nL - 1, by omega⟩
  subst hNdef
  have hR : rightOmittedCount a (nL + nR + 1) (a + nL) = nR := by
    unfold rightOmittedCount; omega
  have hL : a + nL - a = nL := by omega
  have hN1 : nL + nR + 1 - 1 = nL + nR := by omega
  rw [hR, hL, hN1]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hI := quad_pinned_cell_integral hm a nL nR
  have hfL := quad_log_factorial_lower nL
  have hfR := quad_log_factorial_lower (nR + 1)
  have hsucc : Real.log (((nR + 1) ! : ℕ) : ℝ) =
      Real.log ((nR + 1 : ℕ) : ℝ) + Real.log ((nR ! : ℕ) : ℝ) := by
    rw [Nat.factorial_succ, Nat.cast_mul]
    exact Real.log_mul (by positivity) (by exact_mod_cast (Nat.factorial_pos nR).ne')
  have hdiv : Real.log ((m : ℝ) / ((nR + 1 : ℕ) : ℝ)) =
      Real.log m - Real.log ((nR + 1 : ℕ) : ℝ) :=
    Real.log_div hmR.ne' (by positivity)
  rw [hdiv, ge_iff_le]
  have hcast : (((nL + nR : ℕ)) : ℝ) = (nL : ℝ) + ((nR + 1 : ℕ) : ℝ) - 1 := by
    push_cast; ring
  rw [hcast]
  linarith

/-! ## `eq:config-psi` -/

/-- Cell normalization: integrating against the union of frequency cells is
the sum of the interval integrals over the cells. -/
theorem quad_integral_frequencyMeasure (m : ℕ) (R : Finset ℕ) :
    (∫ t, psi t ∂frequencyMeasure m R) =
      ∑ r ∈ R, ∫ t in ((r - 1 : ℕ) : ℝ) / (m : ℝ)..(r : ℝ) / (m : ℝ), psi t := by
  unfold frequencyMeasure
  rw [integral_finsetSum_measure]
  · refine Finset.sum_congr rfl fun r _ => ?_
    have hle : ((r - 1 : ℕ) : ℝ) / (m : ℝ) ≤ (r : ℝ) / (m : ℝ) := by
      apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
      exact_mod_cast Nat.sub_le r 1
    rw [intervalIntegral.integral_of_le hle, frequencyCell,
      integral_Ico_eq_integral_Ioo, integral_Ioc_eq_integral_Ioo]
  · intro r _
    exact (psi_continuous.integrableOn_Icc).mono_set Set.Ico_subset_Icc_self

private theorem quad_psi_telescope (m a : ℕ) (n : ℕ) :
    (∑ r ∈ Finset.Ioc a (a + n),
        (psi ((r : ℝ) / (m : ℝ)) - psi (((r - 1 : ℕ) : ℝ) / (m : ℝ)))) =
      psi (((a + n : ℕ) : ℝ) / (m : ℝ)) - psi ((a : ℝ) / (m : ℝ)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [← add_assoc, Finset.sum_Ioc_succ_top (by omega), ih]
    have : (a + n + 1 - 1 : ℕ) = a + n := by omega
    rw [this]
    ring

/-- `eq:config-psi` for every literal finite configuration. -/
theorem psiQuadratureBound (C : FiniteConfiguration) : PsiQuadratureBound C := by
  unfold PsiQuadratureBound
  have hm : 0 < C.m := by have := C.m_ge_eight; omega
  have hmR : (0 : ℝ) < (C.m : ℝ) := by exact_mod_cast hm
  rw [FiniteConfiguration.mu, quad_integral_frequencyMeasure, Finset.mul_sum,
    Finset.mul_sum, ← Finset.sum_sub_distrib]
  have hterm : ∀ r ∈ C.frequency,
      (C.m : ℝ) * psi ((r : ℝ) / (C.m : ℝ)) -
          (C.m : ℝ) ^ 2 *
            (∫ t in ((r - 1 : ℕ) : ℝ) / (C.m : ℝ)..(r : ℝ) / (C.m : ℝ), psi t) =
        frequencyEndpointError C.m r := fun r _ => rfl
  rw [Finset.sum_congr rfl hterm]
  rw [← Finset.sum_filter_add_sum_filter_not C.frequency (fun r => r ≤ C.m)]
  -- decreasing part: every cell error is nonpositive
  have hdec : ∑ r ∈ C.frequency.filter (fun r => ¬ r ≤ C.m),
      frequencyEndpointError C.m r ≤ 0 := by
    apply Finset.sum_nonpos
    intro r hr
    have hr' := (Finset.mem_filter.mp hr).2
    exact frequencyEndpointError_nonpos_of_antitone hm (by omega)
  -- increasing part: bounded by the cell variation
  set g : ℕ → ℝ := fun r =>
    (C.m : ℝ) * (psi ((r : ℝ) / (C.m : ℝ)) - psi (((r - 1 : ℕ) : ℝ) / (C.m : ℝ)))
    with hg
  have hinc1 : ∑ r ∈ C.frequency.filter (fun r => r ≤ C.m),
      frequencyEndpointError C.m r ≤
        ∑ r ∈ C.frequency.filter (fun r => r ≤ C.m), g r := by
    apply Finset.sum_le_sum
    intro r hr
    obtain ⟨hrF, hrm⟩ := Finset.mem_filter.mp hr
    exact frequencyEndpointError_le_variation hm C.four_dvd_m
      (C.frequency_lower r hrF) hrm
  have hsub : C.frequency.filter (fun r => r ≤ C.m) ⊆
      Finset.Ioc (C.m / 2) (C.m / 2 + (C.m - C.m / 2)) := by
    intro r hr
    obtain ⟨hrF, hrm⟩ := Finset.mem_filter.mp hr
    have := C.frequency_lower r hrF
    rw [Finset.mem_Ioc]
    omega
  have hgnonneg : ∀ r ∈ Finset.Ioc (C.m / 2) (C.m / 2 + (C.m - C.m / 2)),
      r ∉ C.frequency.filter (fun r => r ≤ C.m) → 0 ≤ g r := by
    intro r hr _
    rw [Finset.mem_Ioc] at hr
    have h2 : 2 ∣ C.m := dvd_trans (by norm_num) C.four_dvd_m
    have hlo : (1 / 2 : ℝ) ≤ ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) := by
      rw [le_div_iff₀ hmR]
      have : C.m ≤ 2 * (r - 1) := by omega
      have : (C.m : ℝ) ≤ 2 * ((r - 1 : ℕ) : ℝ) := by exact_mod_cast this
      linarith
    have hhi : (r : ℝ) / (C.m : ℝ) ≤ 1 := by
      rw [div_le_one hmR]
      exact_mod_cast (show r ≤ C.m by omega)
    have hab : ((r - 1 : ℕ) : ℝ) / (C.m : ℝ) ≤ (r : ℝ) / (C.m : ℝ) := by
      apply div_le_div_of_nonneg_right _ hmR.le
      exact_mod_cast Nat.sub_le r 1
    have hmono := psi_monotoneOn_half_one
      ⟨hlo, le_trans hab hhi⟩ ⟨le_trans hlo hab, hhi⟩ hab
    simp only [hg]
    exact mul_nonneg hmR.le (by linarith)
  have hinc2 := Finset.sum_le_sum_of_subset_of_nonneg hsub hgnonneg
  have htel : ∑ r ∈ Finset.Ioc (C.m / 2) (C.m / 2 + (C.m - C.m / 2)), g r =
      (C.m : ℝ) * (Real.log 2 / 2) := by
    simp only [hg]
    rw [← Finset.mul_sum, quad_psi_telescope]
    have h2 : 2 ∣ C.m := dvd_trans (by norm_num) C.four_dvd_m
    have e1 : C.m / 2 + (C.m - C.m / 2) = C.m := by omega
    have e2 : ((C.m / 2 : ℕ) : ℝ) / (C.m : ℝ) = 1 / 2 := by
      obtain ⟨k, hk⟩ := h2
      rw [hk, Nat.mul_div_cancel_left k (by norm_num)]
      have hk0 : (0 : ℝ) < k := by
        have : 0 < k := by omega
        exact_mod_cast this
      push_cast
      field_simp
    rw [e1, e2, div_self hmR.ne', psi_positive_variation_half_one]
  have hfinal : (C.m : ℝ) * (Real.log 2 / 2) = (C.m : ℝ) / 2 * Real.log 2 := by ring
  linarith

/-- The three `Config` quadrature assertions, packaged for the
per-configuration assembly. -/
theorem configQuadratureBounds (C : FiniteConfiguration) :
    PsiQuadratureBound C ∧ BzeroQuadratureBound ∧ PinnedQuadratureBound :=
  ⟨psiQuadratureBound C, bzeroQuadratureBound, pinnedQuadratureBound⟩

end

end Li2Lean.P0.Config
