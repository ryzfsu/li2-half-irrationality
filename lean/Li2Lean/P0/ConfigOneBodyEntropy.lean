/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigPinnedVariation
import Li2Lean.P0.Contour

/-!
# Binomial-entropy one-body bounds

Paper v13 `p0-analytic.tex` ll. 320-323: "Binomial entropy gives
`log U_i(q) ≤ m φ_q(i/m)` and `log w_{r,q} ≤ m ψ_q(r/m)`", here at `q = 2`
against the canonical `UReal`, `frequencyWeightReal`, `Config.phi`,
`Config.psi`.  The only input is `binom(n,k) k^k (n-k)^(n-k) ≤ n^n`, the
`j = k` term of the binomial expansion of `(k + (n-k))^n`.
-/

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

/-- One term of `(k + (n-k))^n`. -/
theorem choose_mul_pow_mul_pow_le (n k : ℕ) (hk : k ≤ n) :
    Nat.choose n k * k ^ k * (n - k) ^ (n - k) ≤ n ^ n := by
  have hsum : n ^ n = ∑ j ∈ Finset.range (n + 1), k ^ j * (n - k) ^ (n - j) * Nat.choose n j := by
    have h := add_pow k (n - k) n
    simp only [Nat.cast_id] at h
    rw [← h]
    congr 1
    omega
  rw [hsum]
  have hmem : k ∈ Finset.range (n + 1) := Finset.mem_range.mpr (by omega)
  have := Finset.single_le_sum (f := fun j => k ^ j * (n - k) ^ (n - j) * Nat.choose n j)
    (fun j _ => Nat.zero_le _) hmem
  calc Nat.choose n k * k ^ k * (n - k) ^ (n - k) =
      k ^ k * (n - k) ^ (n - k) * Nat.choose n k := by ring
    _ ≤ _ := this

/-- Real-logarithm form: `log binom(n,k) ≤ n log n - k log k - (n-k) log (n-k)`. -/
theorem log_choose_le_entropy (n k : ℕ) (hk : k ≤ n) :
    Real.log (Nat.choose n k : ℝ) ≤
      (n : ℝ) * Real.log n - (k : ℝ) * Real.log k -
        ((n - k : ℕ) : ℝ) * Real.log ((n - k : ℕ) : ℝ) := by
  have hnat := choose_mul_pow_mul_pow_le n k hk
  have hreal : (Nat.choose n k : ℝ) * (k : ℝ) ^ k * ((n - k : ℕ) : ℝ) ^ (n - k) ≤
      (n : ℝ) ^ n := by exact_mod_cast hnat
  have hc : (0 : ℝ) < Nat.choose n k := by exact_mod_cast Nat.choose_pos hk
  have hkk : (0 : ℝ) < (k : ℝ) ^ k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; simp
    · exact pow_pos (by exact_mod_cast h) _
  have hnk : (0 : ℝ) < ((n - k : ℕ) : ℝ) ^ (n - k) := by
    rcases Nat.eq_zero_or_pos (n - k) with h | h
    · rw [h]; simp
    · exact pow_pos (by exact_mod_cast h) _
  have hlog := Real.log_le_log (by positivity) hreal
  rw [Real.log_mul (by positivity) hnk.ne', Real.log_mul hc.ne' hkk.ne',
    Real.log_pow, Real.log_pow, Real.log_pow] at hlog
  linarith

/-- `∫_0^{1/2} log |x + s| ds = X(x + 1/2) - X(x)` with `X(t) = t log t - t`. -/
theorem phi_real_eq (x : ℝ) :
    phi (x : ℂ) = x * Real.log 2 + (pvXlx (x + 1 / 2) - pvXlx x) + 1 / 2 -
      (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) := by
  unfold phi
  have hint : (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖(x : ℂ) + Complex.ofReal s‖) =
      pvXlx (x + 1 / 2) - pvXlx x := by
    have h1 : (fun s : ℝ => Real.log ‖(x : ℂ) + Complex.ofReal s‖) =
        fun s => Real.log |x + s| := by
      funext s
      rw [← Complex.ofReal_add, Complex.norm_real, Real.norm_eq_abs]
    rw [h1, pv_integral_log_add]
    simp
  rw [hint]
  simp

theorem mul_pvXlx_div (m a : ℕ) (hm : 0 < m) :
    (m : ℝ) * pvXlx ((a : ℝ) / (m : ℝ)) =
      (a : ℝ) * Real.log a - (a : ℝ) * Real.log m - a := by
  have hmR : (m : ℝ) ≠ 0 := by exact_mod_cast hm.ne'
  unfold pvXlx
  rcases Nat.eq_zero_or_pos a with h | h
  · subst h; simp
  · have haR : (a : ℝ) ≠ 0 := by exact_mod_cast h.ne'
    rw [Real.log_div haR hmR]
    field_simp

/-- Pinned one-body bound, v13 l. 322: `log U_i ≤ m φ(i/m)` at base `2`. -/
theorem log_UReal_le_phi (m i : ℕ) (hm : 0 < m) (h2 : 2 ∣ m) :
    Real.log (UReal (m / 2) i) ≤ (m : ℝ) * phi (((i : ℝ) / (m : ℝ) : ℝ) : ℂ) := by
  obtain ⟨g, rfl⟩ := h2
  have hg : 0 < g := by omega
  have hdiv : 2 * g / 2 = g := by omega
  rw [hdiv]
  have hmR : ((2 * g : ℕ) : ℝ) = 2 * (g : ℝ) := by push_cast; ring
  rw [phi_real_eq]
  have hx : (i : ℝ) / ((2 * g : ℕ) : ℝ) + 1 / 2 = ((i + g : ℕ) : ℝ) / ((2 * g : ℕ) : ℝ) := by
    rw [hmR]; push_cast; field_simp
  have hm2 : (0 : ℕ) < 2 * g := by omega
  have hA : ((2 * g : ℕ) : ℝ) * (pvXlx (((i + g : ℕ) : ℝ) / ((2 * g : ℕ) : ℝ)) -
      pvXlx ((i : ℝ) / ((2 * g : ℕ) : ℝ))) =
      ((i + g : ℕ) : ℝ) * Real.log ((i + g : ℕ) : ℝ) - (i : ℝ) * Real.log i -
        (g : ℝ) * Real.log ((2 * g : ℕ) : ℝ) - g := by
    rw [mul_sub, mul_pvXlx_div _ _ hm2, mul_pvXlx_div _ _ hm2]
    push_cast
    ring
  have hent := log_choose_le_entropy (i + g) g (by omega)
  have hsub : i + g - g = i := by omega
  rw [hsub] at hent
  have hU : UReal g i = (2 : ℝ) ^ i * (Nat.choose (i + g) g : ℝ) := rfl
  have hc : (0 : ℝ) < Nat.choose (i + g) g := by exact_mod_cast Nat.choose_pos (by omega)
  rw [hU, Real.log_mul (by positivity) hc.ne', Real.log_pow, hx]
  set D : ℝ := pvXlx (((i + g : ℕ) : ℝ) / ((2 * g : ℕ) : ℝ)) -
    pvXlx ((i : ℝ) / ((2 * g : ℕ) : ℝ)) with hD
  have hlogm : Real.log ((2 * g : ℕ) : ℝ) = Real.log 2 + Real.log g := by
    rw [hmR, Real.log_mul (by norm_num) (by exact_mod_cast hg.ne')]
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hexp : ((2 * g : ℕ) : ℝ) * ((i : ℝ) / ((2 * g : ℕ) : ℝ) * Real.log 2 + D + 1 / 2 -
      1 / 2 * Real.log (1 / 2)) =
      (i : ℝ) * Real.log 2 + ((2 * g : ℕ) : ℝ) * D + g + g * Real.log 2 := by
    rw [hhalf, hmR]
    field_simp
    ring
  rw [hexp, hA, hlogm]
  push_cast at hent ⊢
  nlinarith [hent]

/-- Frequency one-body bound, v13 l. 323: `log w_r ≤ m ψ(r/m)` at base `2`. -/
theorem log_frequencyWeightReal_le_psi (m r : ℕ) (hm : 0 < m) (h2 : 2 ∣ m)
    (hr : m / 2 < r) :
    Real.log (frequencyWeightReal (m / 2) r) ≤ (m : ℝ) * psi ((r : ℝ) / (m : ℝ)) := by
  obtain ⟨g, rfl⟩ := h2
  have hg : 0 < g := by omega
  have hdiv : 2 * g / 2 = g := by omega
  rw [hdiv] at hr ⊢
  have hmR : ((2 * g : ℕ) : ℝ) = 2 * (g : ℝ) := by push_cast; ring
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  -- `binom(r-1, g) ≤ binom(r, g)` and the entropy bound for `binom(r, g)`
  have hmono : (Nat.choose (r - 1) g : ℝ) ≤ Nat.choose r g := by
    exact_mod_cast Nat.choose_le_choose g (by omega : r - 1 ≤ r)
  have hc1 : (0 : ℝ) < Nat.choose (r - 1) g := by exact_mod_cast Nat.choose_pos (by omega)
  have hent := log_choose_le_entropy r g (by omega)
  have hlogc : Real.log (Nat.choose (r - 1) g : ℝ) ≤ Real.log (Nat.choose r g : ℝ) :=
    Real.log_le_log hc1 hmono
  have hw : frequencyWeightReal g r = (Nat.choose (r - 1) g : ℝ) / (2 : ℝ) ^ r := rfl
  rw [hw, Real.log_div hc1.ne' (by positivity), Real.log_pow]
  -- closed form of `m ψ(r/m)`
  have hrpos : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
  have hrg : ((r - g : ℕ) : ℝ) = (r : ℝ) - g := by
    rw [Nat.cast_sub (by omega)]
  have hrgpos : (0 : ℝ) < (r : ℝ) - g := by
    have : (g : ℝ) < r := by exact_mod_cast hr
    linarith
  have hpsi : ((2 * g : ℕ) : ℝ) * psi ((r : ℝ) / ((2 * g : ℕ) : ℝ)) =
      (r : ℝ) * Real.log r - ((r : ℝ) - g) * Real.log ((r : ℝ) - g) -
        (g : ℝ) * Real.log g - (r : ℝ) * Real.log 2 := by
    unfold psi
    rw [hmR]
    have h1 : (r : ℝ) / (2 * g) - 1 / 2 = ((r : ℝ) - g) / (2 * g) := by
      field_simp
    rw [h1, Real.log_div hrpos.ne' (by positivity), Real.log_div hrgpos.ne' (by positivity),
      Real.log_mul (by norm_num) hgR.ne']
    have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
      rw [one_div, Real.log_inv]
    rw [hhalf]
    field_simp
    ring
  rw [hpsi]
  rw [hrg] at hent
  linarith [hent, hlogc]

end

end Li2Lean.P0.Config
