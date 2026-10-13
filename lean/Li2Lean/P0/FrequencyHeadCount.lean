/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
General head-counting and scale bookkeeping for the frequency part of the
v10 construction (paper `sec-frequency-tail.tex`, especially (7.8)--(7.9)).

This file contains only the discrete counting and factorial-volume estimates.
It does not define, or assume a theorem about, the analytic quantity `G_m` or
the literal `Q_m`; those remain supplied by the Contour/Config layers.
In particular, no field below is an alias for the final analytic conclusion.
-/

namespace Li2Lean.P0.FrequencyHeadCount

open scoped BigOperators

noncomputable section

/-! ### The two finite head universes -/

def pinnedHeadUniverse (m : ℕ) : Finset ℕ := Finset.Ico (m / 4) (5 * m / 4)

def frequencyHeadUniverse (m : ℕ) : Finset ℕ := Finset.Ioc (m / 2) (20 * m)

theorem pinnedHeadUniverse_card {m : ℕ} (hm4 : 4 ∣ m) :
    (pinnedHeadUniverse m).card = m := by
  obtain ⟨h, rfl⟩ := hm4
  simp only [pinnedHeadUniverse, Nat.card_Ico]
  omega

theorem frequencyHeadUniverse_card {m : ℕ} (hm4 : 4 ∣ m) :
    (frequencyHeadUniverse m).card = 39 * m / 2 := by
  obtain ⟨h, rfl⟩ := hm4
  simp only [frequencyHeadUniverse, Nat.card_Ioc]
  omega

theorem frequencyHeadUniverse_card_eq {m : ℕ} (hm4 : 4 ∣ m) :
    (frequencyHeadUniverse m).card = 39 * (m / 2) := by
  rw [frequencyHeadUniverse_card hm4]
  omega

/-! ### Binomial head count -/

/-- A general logarithmic binomial estimate.  This is the only entropy
    estimate needed below; it is the elementary `choose ≤ n^k` bound, so it
    does not hide an asymptotic or an analytic premise. -/
theorem log_choose_le_mul_log {N k : ℕ} (hk : 0 < k) (hkN : k ≤ N) :
    Real.log (Nat.choose N k : ℝ) ≤
      (k : ℝ) * Real.log (N : ℝ) := by
  have hchoose : 0 < Nat.choose N k := Nat.choose_pos hkN
  have hN : 0 < N := lt_of_lt_of_le hk hkN
  have hpow : (Nat.choose N k : ℝ) ≤ (N : ℝ) ^ k := by
    exact_mod_cast Nat.choose_le_pow N k
  calc
    Real.log (Nat.choose N k : ℝ) ≤ Real.log ((N : ℝ) ^ k) :=
      Real.log_le_log (by exact_mod_cast hchoose) hpow
    _ = (k : ℝ) * Real.log (N : ℝ) := Real.log_pow _ _

theorem frequencyHead_count_positive {m : ℕ} (hm8 : 8 ≤ m) (hm4 : 4 ∣ m) :
    0 < Nat.choose (frequencyHeadUniverse m).card m := by
  apply Nat.choose_pos
  rw [frequencyHeadUniverse_card hm4]
  omega

/-- The exact general-`m` frequency head-count bound.  The right hand side
    is deliberately left as `log (39m/2)` here: this is the sharp finite
    counting statement, before the harmless paper relaxation to
    `log m + log 39 + 1`. -/
theorem log_frequencyHead_count_le {m : ℕ} (hm8 : 8 ≤ m) (hm4 : 4 ∣ m) :
    Real.log (Nat.choose (frequencyHeadUniverse m).card m : ℝ) ≤
      (m : ℝ) * Real.log ((39 * m / 2 : ℕ) : ℝ) := by
  rw [frequencyHeadUniverse_card hm4]
  apply log_choose_le_mul_log (k := m)
  · omega
  · omega

/-- The same estimate in the paper's `m log m + m(log 39 + 1)` format.
    We use only monotonicity of `log`, so this is stronger than the usual
    `(39e/2)^m` entropy certificate and is uniform for every `m ≥ 8`, `4 ∣ m`.
-/ 
theorem log_frequencyHead_count_le_paper {m : ℕ} (hm8 : 8 ≤ m) (hm4 : 4 ∣ m) :
    Real.log (Nat.choose (frequencyHeadUniverse m).card m : ℝ) ≤
      (m : ℝ) * Real.log (m : ℝ) +
        (m : ℝ) * (Real.log 39 + 1) := by
  have hmain := log_frequencyHead_count_le hm8 hm4
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hNpos : 0 < ((39 * m / 2 : ℕ) : ℝ) := by
    have hN : 0 < 39 * m / 2 := by
      rw [show m = 4 * (m / 4) by omega]
      omega
    exact_mod_cast hN
  have hNle : ((39 * m / 2 : ℕ) : ℝ) ≤ (39 : ℝ) * (m : ℝ) := by
    have hN : 39 * m / 2 ≤ 39 * m := by omega
    exact_mod_cast hN
  have hlogN : Real.log ((39 * m / 2 : ℕ) : ℝ) ≤
      Real.log 39 + Real.log (m : ℝ) := by
    calc
      Real.log ((39 * m / 2 : ℕ) : ℝ) ≤ Real.log ((39 : ℝ) * (m : ℝ)) :=
        Real.log_le_log hNpos hNle
      _ = Real.log 39 + Real.log (m : ℝ) := by
        rw [Real.log_mul (by norm_num) (ne_of_gt hmpos)]
  have hmul := mul_le_mul_of_nonneg_left hlogN (le_of_lt hmpos)
  have hlog2_nonneg : 0 ≤ Real.log (2 : ℝ) := Real.log_nonneg (by norm_num)
  have hrel : Real.log (39 : ℝ) ≤ Real.log 39 + 1 := by linarith
  calc
    Real.log (Nat.choose (frequencyHeadUniverse m).card m : ℝ) ≤
        (m : ℝ) * Real.log ((39 * m / 2 : ℕ) : ℝ) := hmain
    _ ≤ (m : ℝ) * (Real.log 39 + Real.log (m : ℝ)) := hmul
    _ ≤ (m : ℝ) * Real.log (m : ℝ) + (m : ℝ) * (Real.log 39 + 1) := by
      nlinarith

/-! ### Rational logarithm certificates used by the paper's linear budget -/

theorem log_two_lt_694_thousandths : Real.log (2 : ℝ) < 694 / 1000 := by
  have hseries := Real.log_div_le_sum_range_add
      (x := (1 / 3 : ℝ)) (by norm_num) (by norm_num) 8
  have hratio : ((1 + (1 / 3 : ℝ)) / (1 - (1 / 3 : ℝ))) = 2 := by norm_num
  rw [hratio] at hseries
  have hfinite :
      2 * ((∑ k ∈ Finset.range 8,
          (1 / 3 : ℝ) ^ (2 * k + 1) / (2 * k + 1)) +
          (1 / 3 : ℝ) ^ (2 * 8 + 1) / (1 - (1 / 3 : ℝ) ^ 2)) <
        (694 / 1000 : ℝ) := by
    norm_num [Finset.sum_range_succ]
  nlinarith

/-- A short range-reduced atanh certificate for the only logarithm not
    already present in the C-A numerical tables.  It is intentionally a
    standalone rational check, so the head-count theorem does not depend on
    a free numerical premise. -/
theorem log_thirty_nine_lt : Real.log (39 : ℝ) < 367 / 100 := by
  have h2 := log_two_lt_694_thousandths
  have hratio : (39 : ℝ) = 32 * (39 / 32 : ℝ) := by norm_num
  rw [hratio, Real.log_mul (by norm_num) (by norm_num)]
  have hlogratio : Real.log (39 / 32 : ℝ) < 1 / 5 := by
    have hseries := Real.log_div_le_sum_range_add
        (x := (7 / 71 : ℝ)) (by norm_num) (by norm_num) 2
    have hq : ((1 + (7 / 71 : ℝ)) / (1 - (7 / 71 : ℝ))) = 39 / 32 := by
      norm_num
    rw [hq] at hseries
    have hfinite :
        2 * ((∑ k ∈ Finset.range 2,
            (7 / 71 : ℝ) ^ (2 * k + 1) / (2 * k + 1)) +
            (7 / 71 : ℝ) ^ (2 * 2 + 1) / (1 - (7 / 71 : ℝ) ^ 2)) <
          (1 / 5 : ℝ) := by
      norm_num [Finset.sum_range_succ]
    nlinarith
  rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
  have hlogratio' : Real.log (39 / (2 : ℝ) ^ 5) < 1 / 5 := by
    convert hlogratio using 1 <;> norm_num
  nlinarith

/-- The exact rounded linear-budget check in `sec-frequency-tail.tex`:
    `c_* < 49.979`, `A = 12783/10000`, and the frequency entropy term
    together are below `56`. -/
theorem paper_linear_budget_lt_56 {cStar : ℝ}
    (hc : cStar < (49979 / 1000 : ℝ)) :
    cStar + Real.log 39 + 1 + (12783 / 10000 : ℝ) < 56 := by
  have hlog := log_thirty_nine_lt
  nlinarith

/-! ### Pinned choices and the combined discrete head count -/

theorem log_pinned_choice_eq (m : ℕ) :
    Real.log ((2 : ℝ) ^ m) = (m : ℝ) * Real.log 2 := by
  rw [Real.log_pow]

def discreteHeadCount (m : ℕ) : ℕ :=
  2 ^ m * Nat.choose (frequencyHeadUniverse m).card m

theorem discreteHeadCount_positive {m : ℕ} (hm8 : 8 ≤ m) (hm4 : 4 ∣ m) :
    0 < discreteHeadCount m := by
  unfold discreteHeadCount
  exact Nat.mul_pos (pow_pos (by norm_num) _) (frequencyHead_count_positive hm8 hm4)

theorem log_discreteHeadCount_le {m : ℕ} (hm8 : 8 ≤ m) (hm4 : 4 ∣ m) :
    Real.log (discreteHeadCount m : ℝ) ≤
      (m : ℝ) * Real.log (m : ℝ) +
        (m : ℝ) * (Real.log 39 + Real.log 2 + 1) := by
  have hchoose := log_frequencyHead_count_le_paper hm8 hm4
  have hmpos : 0 < (m : ℝ) := by exact_mod_cast (show 0 < m by omega)
  have hpow : (2 : ℝ) ^ m > 0 := by positivity
  have hchoosepos : 0 < (Nat.choose (frequencyHeadUniverse m).card m : ℝ) := by
    exact_mod_cast frequencyHead_count_positive hm8 hm4
  have hprod : (discreteHeadCount m : ℝ) =
      (2 : ℝ) ^ m * (Nat.choose (frequencyHeadUniverse m).card m : ℝ) := by
    simp [discreteHeadCount]
  rw [hprod, Real.log_mul (ne_of_gt hpow) (ne_of_gt hchoosepos), log_pinned_choice_eq]
  nlinarith

/-! ### Contour-volume and exact diagonal bookkeeping -/

/-- The factorial-normalized `d`-dimensional contour volume estimate from
    `sec-frequency-tail.tex`: it is the exponential-series term bound and
    does not depend on a selected frequency set. -/
theorem factorial_normalized_volume_le_exp {m d : ℕ} {A : ℝ} (hA : 0 ≤ A) :
    ((m : ℝ) * A) ^ d / (d.factorial : ℝ) ≤ Real.exp ((m : ℝ) * A) := by
  simpa only [Nat.cast_ofNat] using
    (Real.pow_div_factorial_le_exp ((m : ℝ) * A)
      (mul_nonneg (by positivity) hA) d)

/-- The diagonal determinant contribution is exactly `2 d log m`.  Keeping it
    in one named factor prevents the common double-counting bug in the final
    `10 m log m` coefficient. -/
theorem diagonal_two_d_log_m {m d : ℕ} (hm : 0 < m) :
    Real.log ((m : ℝ) ^ (2 * d)) = (2 * (d : ℝ)) * Real.log (m : ℝ) := by
  rw [Real.log_pow]
  congr 1
  norm_num

theorem diagonal_and_linear_log_m {m d k : ℕ} (hm : 0 < m) :
    Real.log ((m : ℝ) ^ (2 * d) * (m : ℝ) ^ k) =
      (2 * (d : ℝ) + (k : ℝ)) * Real.log (m : ℝ) := by
  rw [Real.log_mul (by positivity) (by positivity), diagonal_two_d_log_m hm,
    Real.log_pow]
  ring

end

end Li2Lean.P0.FrequencyHeadCount
