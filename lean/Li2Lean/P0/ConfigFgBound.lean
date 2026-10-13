/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigQuadrature
import Li2Lean.P0.ConfigPinnedVariation

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

/-!
# The finite contour-product bound `FgBound` (`eq:config-Fg`)

Paper v13, `p0-analytic.tex` (finite contour product): with `ζ = m z`,
`f(u) = log |ζ + u|` decreases up to `r = -Re ζ` and increases afterwards.
The right-endpoint quadrature error `f(k+1) - ∫_k^{k+1} f` is nonpositive on
cells of the decreasing piece; on cells of the increasing piece it is at most
`f(k+1) - f(k)`, which telescopes.  The single turning cell is bounded by
comparing `f` with `log |u - r|` (cell integral `≥ -2`) or with the constant
`log dist(-ζ, [0, ∞))`.  This yields, for every `ζ` with no zero of the
product,
`∑_{k<g} f(k+1) - ∫_0^g f ≤ log (g + 1) + 2`,
and with `log g! ≥ g log g - g` the stated `FgBound` with the canonical
`b m = 5 (1 + 2 log 2) + 4 (1 + log (m/2 + 1))`, for every `z ∈ ℂ`
(not only on the tube).
-/

/-- `log |ζ + u|` along the real axis. -/
def cpLog (ζ : ℂ) (u : ℝ) : ℝ := Real.log ‖ζ + (u : ℂ)‖

theorem cp_sq_norm (ζ : ℂ) (u : ℝ) :
    ‖ζ + (u : ℂ)‖ ^ 2 = (u + ζ.re) ^ 2 + ζ.im ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.add_im, Complex.ofReal_im, add_zero]
  ring

theorem cp_norm_le (ζ : ℂ) {u v : ℝ} (h : (v + ζ.re) ^ 2 ≤ (u + ζ.re) ^ 2) :
    ‖ζ + (v : ℂ)‖ ≤ ‖ζ + (u : ℂ)‖ := by
  have h2 : ‖ζ + (v : ℂ)‖ ^ 2 ≤ ‖ζ + (u : ℂ)‖ ^ 2 := by
    rw [cp_sq_norm, cp_sq_norm]
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).1 h2

theorem cp_integrable (ζ : ℂ) (a b : ℝ) : IntervalIntegrable (cpLog ζ) volume a b := by
  by_cases him : ζ.im = 0
  · have heq : cpLog ζ = fun u => Real.log (u + ζ.re) := by
      funext u
      have hz : ζ + (u : ℂ) = ((u + ζ.re : ℝ) : ℂ) :=
        Complex.ext (by simp [add_comm]) (by simp [him])
      rw [cpLog, hz, Complex.norm_real, Real.norm_eq_abs, Real.log_abs]
    rw [heq]
    exact pv_log_affine_integrable ζ.re a b
  · apply Continuous.intervalIntegrable
    apply Continuous.log (by fun_prop)
    intro u hu
    rw [norm_eq_zero] at hu
    apply him
    have := congrArg Complex.im hu
    simpa using this

theorem cp_const_le_integral (ζ : ℂ) {a C : ℝ}
    (h : ∀ u ∈ Set.Icc a (a + 1), C ≤ cpLog ζ u) :
    C ≤ ∫ u in a..a + 1, cpLog ζ u := by
  have := intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
    (cp_integrable ζ a (a + 1)) h
  simpa using this

/-- Decreasing cell: the right endpoint value is below the cell integral. -/
theorem cp_cell_dec (ζ : ℂ) {a : ℝ} (ha : a + 1 + ζ.re ≤ 0)
    (hne : ζ + ((a + 1 : ℝ) : ℂ) ≠ 0) :
    cpLog ζ (a + 1) ≤ ∫ u in a..a + 1, cpLog ζ u := by
  apply cp_const_le_integral
  intro u hu
  apply Real.log_le_log (norm_pos_iff.2 hne)
  apply cp_norm_le
  nlinarith [hu.1, hu.2]

/-- Increasing cell: the left endpoint value is below the cell integral. -/
theorem cp_cell_inc (ζ : ℂ) {a : ℝ} (ha : 0 ≤ a + ζ.re) (hne : ζ + (a : ℂ) ≠ 0) :
    cpLog ζ a ≤ ∫ u in a..a + 1, cpLog ζ u := by
  apply cp_const_le_integral
  intro u hu
  apply Real.log_le_log (norm_pos_iff.2 hne)
  apply cp_norm_le
  nlinarith [hu.1, hu.2]

theorem cp_mul_log_ge {x : ℝ} (hx : 0 ≤ x) : x - 1 ≤ x * Real.log x := by
  rcases hx.eq_or_lt with h | h
  · subst h; simp
  · have hl := Real.one_sub_inv_le_log_of_pos h
    have : x * (1 - x⁻¹) = x - 1 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left hl h.le]

/-- A unit cell of `log |u|` starting at `a ≥ -1` has integral at least `-2`. -/
theorem cp_step_ge {a : ℝ} (ha : -1 ≤ a) : -2 ≤ pvXlx (a + 1) - pvXlx a := by
  unfold pvXlx
  rcases le_or_gt 0 a with h0 | h0
  · have hl1 : 0 ≤ Real.log (a + 1) := Real.log_nonneg (by linarith)
    have hstep : a * Real.log a ≤ (a + 1) * Real.log (a + 1) := by
      rcases h0.eq_or_lt with h | h
      · subst h; simp
      · have : Real.log a ≤ Real.log (a + 1) := Real.log_le_log h (by linarith)
        nlinarith [mul_le_mul_of_nonneg_left this h.le]
    linarith
  · have h1 := cp_mul_log_ge (x := a + 1) (by linarith)
    have h2 := cp_mul_log_ge (x := -a) (by linarith)
    rw [Real.log_neg_eq_log] at h2
    nlinarith

/-- Turning cell: the cell integral is at least `-2` once `-Re ζ ≤ c + 1`. -/
theorem cp_cell_turn (ζ : ℂ) {c : ℝ} (hc : -1 ≤ c + ζ.re) :
    -2 ≤ ∫ u in c..c + 1, cpLog ζ u := by
  have hcl := pv_integral_log_add ζ.re c (c + 1)
  have hlow : -2 ≤ pvXlx (ζ.re + (c + 1)) - pvXlx (ζ.re + c) := by
    have := cp_step_ge (a := ζ.re + c) (by linarith)
    rwa [show ζ.re + c + 1 = ζ.re + (c + 1) by ring] at this
  have hint : IntervalIntegrable (fun u => Real.log |ζ.re + u|) volume c (c + 1) := by
    have h := pv_log_affine_integrable ζ.re c (c + 1)
    refine h.congr ?_
    intro u _
    simp only
    rw [Real.log_abs, add_comm]
  have hmono : (∫ u in c..c + 1, Real.log |ζ.re + u|) ≤ ∫ u in c..c + 1, cpLog ζ u := by
    apply intervalIntegral.integral_mono_ae (by linarith) hint (cp_integrable ζ c (c + 1))
    refine (Measure.ae_ne volume (-ζ.re)).mono (fun u hu => ?_)
    have hpos : 0 < |ζ.re + u| := abs_pos.2 (by intro h; apply hu; linarith)
    apply Real.log_le_log hpos
    have := Complex.abs_re_le_norm (ζ + (u : ℂ))
    simpa using this
  linarith

/-- The turning cell together with the right endpoint `g`. -/
theorem cp_turn_final (ζ : ℂ) {g c : ℕ} (hcg : c + 1 ≤ g)
    (hcr : -1 ≤ (c : ℝ) + ζ.re) (hne : ζ + ((g : ℝ) : ℂ) ≠ 0) :
    cpLog ζ g - ∫ u in (c : ℝ)..(c : ℝ) + 1, cpLog ζ u ≤
      Real.log ((g : ℝ) + 1) + 2 := by
  have hcgR : (c : ℝ) + 1 ≤ g := by exact_mod_cast hcg
  have hc0 : (0 : ℝ) ≤ c := Nat.cast_nonneg c
  set p : ℝ := max (-ζ.re) 0 with hp
  set D : ℝ := ‖ζ + (p : ℂ)‖ with hD
  have hp0 : 0 ≤ p := le_max_right _ _
  have hpg : p ≤ g := max_le (by linarith) (by linarith)
  have hDu : ∀ u : ℝ, 0 ≤ u → D ≤ ‖ζ + (u : ℂ)‖ := by
    intro u hu
    apply cp_norm_le
    rcases le_total 0 (-ζ.re) with h | h
    · rw [hp, max_eq_left h]
      nlinarith
    · rw [hp, max_eq_right h]
      nlinarith
  have hgD : ‖ζ + ((g : ℝ) : ℂ)‖ ≤ D + g := by
    have hz : ζ + ((g : ℝ) : ℂ) = (ζ + (p : ℂ)) + (((g : ℝ) - p : ℝ) : ℂ) := by
      push_cast; ring
    rw [hz]
    refine (norm_add_le _ _).trans ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  have hgpos : 0 < ‖ζ + ((g : ℝ) : ℂ)‖ := norm_pos_iff.2 hne
  have hg1 : (1 : ℝ) ≤ g := by linarith
  have hlg : 0 ≤ Real.log ((g : ℝ) + 1) := Real.log_nonneg (by linarith)
  unfold cpLog
  rcases le_or_gt 1 D with hD1 | hD1
  · have hI : Real.log D ≤ ∫ u in (c : ℝ)..(c : ℝ) + 1, cpLog ζ u := by
      apply cp_const_le_integral
      intro u hu
      exact Real.log_le_log (by linarith) (hDu u (by linarith [hu.1]))
    have hup : Real.log ‖ζ + ((g : ℝ) : ℂ)‖ ≤ Real.log D + Real.log ((g : ℝ) + 1) := by
      rw [← Real.log_mul (by linarith) (by linarith)]
      apply Real.log_le_log hgpos
      nlinarith
    unfold cpLog at hI
    linarith
  · have hI := cp_cell_turn ζ (c := (c : ℝ)) hcr
    have hup : Real.log ‖ζ + ((g : ℝ) : ℂ)‖ ≤ Real.log ((g : ℝ) + 1) := by
      apply Real.log_le_log hgpos
      linarith
    unfold cpLog at hI
    linarith

/-- Right-endpoint quadrature for `log |ζ + u|` on `[0, g]`. -/
theorem cp_sum_sub_integral (ζ : ℂ) (g : ℕ)
    (hne : ∀ k : ℕ, 1 ≤ k → k ≤ g → ζ + ((k : ℝ) : ℂ) ≠ 0) :
    (∑ k ∈ Finset.range g, cpLog ζ ((k : ℝ) + 1)) -
        (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) ≤
      Real.log ((g : ℝ) + 1) + 2 := by
  have hsplit : (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) =
      ∑ k ∈ Finset.range g, ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u := by
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := cpLog ζ)
      (μ := volume) (a := fun k : ℕ => (k : ℝ)) (n := g)
      (fun k _ => cp_integrable ζ _ _)
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_zero] at h
    exact h.symm
  rw [hsplit, ← Finset.sum_sub_distrib]
  have key : ∀ n : ℕ, n ≤ g →
      (∑ k ∈ Finset.range n,
          (cpLog ζ ((k : ℝ) + 1) - ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u)) ≤ 0 ∨
      ∃ c : ℕ, c < n ∧ -1 ≤ (c : ℝ) + ζ.re ∧
        (∑ k ∈ Finset.range n,
            (cpLog ζ ((k : ℝ) + 1) - ∫ u in (k : ℝ)..(k : ℝ) + 1, cpLog ζ u)) ≤
          cpLog ζ (n : ℝ) - ∫ u in (c : ℝ)..(c : ℝ) + 1, cpLog ζ u := by
    intro n
    induction n with
    | zero => intro _; left; simp
    | succ n ih =>
      intro hn
      rw [Finset.sum_range_succ]
      rcases ih (by omega) with h | ⟨c, hc, hcr, h⟩
      · by_cases hdec : (n : ℝ) + 1 + ζ.re ≤ 0
        · left
          have hne' : ζ + (((n : ℝ) + 1 : ℝ) : ℂ) ≠ 0 := by
            have := hne (n + 1) (by omega) hn
            push_cast at this ⊢
            exact this
          have := cp_cell_dec ζ (a := (n : ℝ)) hdec hne'
          linarith
        · right
          refine ⟨n, by omega, by linarith [not_le.1 hdec], ?_⟩
          push_cast
          linarith
      · right
        refine ⟨c, by omega, hcr, ?_⟩
        have hcn : (c : ℝ) + 1 ≤ n := by exact_mod_cast hc
        have := cp_cell_inc ζ (a := (n : ℝ)) (by linarith)
          (hne n (by omega) (by omega))
        push_cast
        linarith
  have hlg : 0 ≤ Real.log ((g : ℝ) + 1) := Real.log_nonneg (by linarith [g.cast_nonneg (α := ℝ)])
  rcases key g le_rfl with h | ⟨c, hc, hcr, h⟩
  · linarith
  · have hg1 : 1 ≤ g := by omega
    have := cp_turn_final ζ (g := g) (c := c) (by omega) hcr (hne g hg1 le_rfl)
    linarith

/-- `eq:config-Fg`: the finite contour-product bound, for every `z ∈ ℂ`. -/
theorem fgBound : FgBound := by
  intro m hm8 hm4 z
  simp only
  set g : ℕ := m / 2 with hg
  have hmg : m = 2 * g := by omega
  have hm2 : (m : ℝ) = 2 * g := by exact_mod_cast hmg
  have hg4 : 4 ≤ g := by omega
  have hgR : (0 : ℝ) < g := by exact_mod_cast (show 0 < g by omega)
  have hmR : (0 : ℝ) < m := by rw [hm2]; positivity
  set ζ : ℂ := Complex.ofReal (m : ℝ) * z with hζ
  by_cases hv : p0Entire g ζ = 0
  · left; exact hv
  right
  have hfac : (0 : ℝ) < (g.factorial : ℝ) := by exact_mod_cast Nat.factorial_pos g
  have hprod : ∀ k ∈ Finset.range g, ζ + ((k + 1 : ℕ) : ℂ) ≠ 0 := by
    have hv' := hv
    unfold p0Entire at hv'
    intro k hk hz
    apply hv'
    rw [Finset.prod_eq_zero hk hz]
    simp
  have hne : ∀ k : ℕ, 1 ≤ k → k ≤ g → ζ + ((k : ℝ) : ℂ) ≠ 0 := by
    intro k hk1 hkg
    have := hprod (k - 1) (Finset.mem_range.2 (by omega))
    rwa [show k - 1 + 1 = k by omega, ← Complex.ofReal_natCast] at this
  -- the logarithm of the product
  have hlogv : Real.log ‖p0Entire g ζ‖ =
      ζ.re * Real.log 2 + (∑ k ∈ Finset.range g, cpLog ζ ((k : ℝ) + 1)) -
        Real.log (g.factorial : ℝ) := by
    unfold p0Entire
    rw [norm_div, norm_mul, Complex.norm_exp, norm_prod, Complex.norm_natCast,
      Real.log_div (by
        apply mul_ne_zero (Real.exp_pos _).ne'
        rw [Finset.prod_ne_zero_iff]
        intro k hk
        exact norm_ne_zero_iff.2 (hprod k hk)) hfac.ne',
      Real.log_mul (Real.exp_pos _).ne' (by
        rw [Finset.prod_ne_zero_iff]
        intro k hk
        exact norm_ne_zero_iff.2 (hprod k hk)),
      Real.log_exp, Real.log_prod (fun k hk => norm_ne_zero_iff.2 (hprod k hk))]
    have hre : (ζ * Complex.ofReal (Real.log 2)).re = ζ.re * Real.log 2 := by
      rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
      ring
    rw [hre]
    congr 2
    apply Finset.sum_congr rfl
    intro k _
    unfold cpLog
    push_cast
    rfl
  have hζre : ζ.re = (m : ℝ) * z.re := by
    rw [hζ, Complex.re_ofReal_mul]
  -- the cell integral after the scaling `u = m s`
  set J : ℝ := ∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + Complex.ofReal s‖ with hJ
  have hscale : (∫ u in (0 : ℝ)..(g : ℝ), cpLog ζ u) =
      (m : ℝ) * ((1 / 2) * Real.log m + J) := by
    have h1 := intervalIntegral.integral_comp_mul_left (cpLog ζ) (c := (m : ℝ))
      (a := 0) (b := 1 / 2) hmR.ne'
    have hb : (m : ℝ) * (1 / 2) = g := by rw [hm2]; ring
    rw [mul_zero, hb, smul_eq_mul] at h1
    have h2 : (∫ s in (0 : ℝ)..(1 / 2 : ℝ), cpLog ζ ((m : ℝ) * s)) =
        ∫ s in (0 : ℝ)..(1 / 2 : ℝ), (Real.log m + Real.log ‖z + Complex.ofReal s‖) := by
      apply intervalIntegral.integral_congr_ae
      refine (Measure.ae_ne volume (-z.re)).mono (fun s hs _ => ?_)
      have hzs : z + Complex.ofReal s ≠ 0 := by
        intro h0
        apply hs
        have := congrArg Complex.re h0
        simp at this
        linarith
      unfold cpLog
      rw [hζ, show Complex.ofReal (m : ℝ) * z + (((m : ℝ) * s : ℝ) : ℂ) =
          Complex.ofReal (m : ℝ) * (z + Complex.ofReal s) by push_cast; ring,
        norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hmR,
        Real.log_mul hmR.ne' (norm_ne_zero_iff.2 hzs)]
    have h3 : (∫ s in (0 : ℝ)..(1 / 2 : ℝ),
        (Real.log m + Real.log ‖z + Complex.ofReal s‖)) = (1 / 2) * Real.log m + J := by
      rw [intervalIntegral.integral_add (f := fun _ => Real.log (m : ℝ))
        (g := fun s : ℝ => Real.log ‖z + (s : ℂ)‖) intervalIntegrable_const
        (cp_integrable z 0 (1 / 2))]
      simp [hJ]
    rw [h2, h3] at h1
    rw [h1]
    field_simp
  have hmain := cp_sum_sub_integral ζ g hne
  have hstir := quad_log_factorial_lower g
  have hlogm : Real.log (m : ℝ) = Real.log 2 + Real.log g := by
    rw [hm2, Real.log_mul (by norm_num) hgR.ne']
  have hhalf : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  have hb : b m = 5 * (1 + 2 * Real.log 2) + 4 * (1 + Real.log ((g : ℝ) + 1)) := by
    unfold b
    rw [← hg]
    push_cast
    rfl
  have hl2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hlg : 0 ≤ Real.log ((g : ℝ) + 1) := Real.log_nonneg (by linarith)
  rw [hlogv, hb]
  unfold phi
  rw [hζre, hhalf]
  rw [hscale, hlogm] at hmain
  rw [hm2] at hmain ⊢
  nlinarith

end

end Li2Lean.P0.Config
