/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CellBound.Defs

/-!
# Cell inequality: one-body factors, fixed-grid fields, fixed Vandermonde

Paper v13 `p0-analytic.tex`:

* `OneBodyBound` (ll. 320-323, 386-422): binomial entropy
  `log U_i ≤ m φ(i/m)`, `log w_r ≤ m ψ(r/m)`, the finite contour product
  `log |F(mζ)| ≤ m φ(ζ) + b_m`, and `log log 2 < 0`;
* `FreqFieldLower` (ll. 334-341): `eq:config-Bzero` at every frequency;
* `PinFieldLower` (ll. 343-353): `eq:config-pinned` on `I_m` (loss `≥ 0`)
  and `J_m` (loss `≥ -log 2`);
* `ContFieldLower` (l. 380): the fixed contour denominators, left-endpoint
  quadrature of the `1/d_+`-Lipschitz function `x ↦ log |ζ - x|`, cost
  `3/(2 d_+)` per contour point;
* `FixedVBound` (ll. 142-156, 317): `eq:config-self` on `I_m` and `J_m`
  with the exact interval energies `-3/2` and `4 log 2 - 6`.
-/

open MeasureTheory

namespace Li2Lean.P0.CellBound

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.CoefficientAssembly

noncomputable section

/-! ## Agreement of the two copies of the fields -/

theorem config_phi_eq (z : ℂ) : Config.phi z = P0.phi z := rfl

theorem config_psi_eq (t : ℝ) : Config.psi t = P0.psi t := rfl

theorem config_B0_eq (t : ℝ) : Config.B0 t = P0.B0 t := rfl

theorem config_A0_eq (z : ℂ) : Config.A0 z = P0.A0 z := rfl

/-! ## One-body bound -/

theorem ell_pos : 0 < ell := Real.log_pos (by norm_num)

theorem log_ell_neg : Real.log ell < 0 := by
  apply Real.log_neg ell_pos
  have h := Real.log_two_lt_d9
  unfold ell
  linarith

theorem oneBodyBound : OneBodyBound := by
  intro C hF
  have hm8 := C.m_ge_eight
  have hm : 0 < C.m := by omega
  have h2 : 2 ∣ C.m := by
    obtain ⟨k, hk⟩ := C.four_dvd_m
    exact ⟨2 * k, by omega⟩
  have hpin : (∑ s ∈ C.pinned, Real.log (ell * UReal (C.m / 2) s)) ≤
      (C.m : ℝ) * (∑ s ∈ C.pinned, P0.phi (((s : ℝ) / (C.m : ℝ) : ℝ) : ℂ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro s _
    have hU : 0 < UReal (C.m / 2) s := by
      unfold UReal
      exact mul_pos (by positivity) (by exact_mod_cast Nat.choose_pos (by omega))
    rw [Real.log_mul ell_pos.ne' hU.ne']
    have := log_UReal_le_phi C.m s hm h2
    rw [config_phi_eq] at this
    linarith [log_ell_neg]
  have hfreq : (∑ r ∈ C.frequency, Real.log (frequencyWeightReal (C.m / 2) r)) ≤
      (C.m : ℝ) * (∑ r ∈ C.frequency, P0.psi ((r : ℝ) / (C.m : ℝ))) := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro r hr
    have hr' : C.m / 2 < r := by have := C.frequency_lower r hr; omega
    have := log_frequencyWeightReal_le_psi C.m r hm h2 hr'
    rwa [config_psi_eq] at this
  have hcont : (∑ a : Fin C.contourCount,
      Real.log ‖p0Entire (C.m / 2) (Complex.ofReal (C.m : ℝ) * C.contour a)‖) ≤
      (C.m : ℝ) * (∑ a : Fin C.contourCount, P0.phi (C.contour a)) +
        (C.contourCount : ℝ) * b C.m := by
    rw [Finset.mul_sum]
    have hcard : (C.contourCount : ℝ) * b C.m = ∑ _a : Fin C.contourCount, b C.m := by
      simp
    rw [hcard, ← Finset.sum_add_distrib]
    apply Finset.sum_le_sum
    intro a _
    have hfg := fgBound C.m hm8 C.four_dvd_m (C.contour a)
    simp only at hfg
    rcases hfg with h0 | hle
    · exact absurd h0 (hF a)
    · rw [config_phi_eq] at hle
      exact hle
  unfold oneBody
  linarith

/-! ## Frequency field (`eq:config-Bzero`) -/

theorem freqFieldLower : FreqFieldLower := by
  intro C
  have hm8 := C.m_ge_eight
  have hm : (0 : ℝ) < C.m := by exact_mod_cast (show 0 < C.m by omega)
  have hcard : (C.m : ℝ) * Real.log (35 / 3 : ℝ) =
      ∑ _r ∈ C.frequency, Real.log (35 / 3 : ℝ) := by
    rw [Finset.sum_const, C.frequency_card, nsmul_eq_mul]
  have hterm : ∀ r ∈ C.frequency,
      (C.m : ℝ) * P0.B0 ((r : ℝ) / (C.m : ℝ)) - Real.log (35 / 3 : ℝ) ≤
        fixedLatticeLogSum C.m ((r : ℝ) / (C.m : ℝ)) := by
    intro r hr
    have hr1 := C.frequency_lower r hr
    obtain ⟨k, hk⟩ := C.four_dvd_m
    have ht : (1 / 2 : ℝ) ≤ (r : ℝ) / (C.m : ℝ) := by
      rw [le_div_iff₀ hm]
      have : (C.m : ℝ) ≤ 2 * r := by exact_mod_cast (by omega : C.m ≤ 2 * r)
      linarith
    have h := (bzeroQuadratureBound C.m hm8 C.four_dvd_m _ ht).2
    rw [config_B0_eq] at h
    linarith
  unfold freqField
  rw [hcard, Finset.mul_sum, ← Finset.sum_sub_distrib]
  exact Finset.sum_le_sum hterm

/-! ## Unions of consecutive cells -/

theorem latticeCellMeasure_Ico (m : ℕ) (hm : 0 < m) (p q : ℕ) (hpq : p ≤ q) :
    latticeCellMeasure m (Finset.Ico p q) =
      volume.restrict (Set.Ico ((p : ℝ) / (m : ℝ)) ((q : ℝ) / (m : ℝ))) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  induction q, hpq using Nat.le_induction with
  | base => simp [latticeCellMeasure]
  | succ q hpq ih =>
    rw [latticeCellMeasure, Finset.sum_Ico_succ_top hpq, ← latticeCellMeasure, ih,
      pinnedCell, ← Measure.restrict_union]
    · rw [Set.Ico_union_Ico_eq_Ico]
      · apply div_le_div_of_nonneg_right _ hmR.le
        exact_mod_cast hpq
      · apply div_le_div_of_nonneg_right _ hmR.le
        exact_mod_cast Nat.le_succ q
    · rw [Set.Ico_disjoint_Ico]
      simp
    · exact measurableSet_Ico

theorem log_energy_Ico (a b : ℝ) (hab : a ≤ b) :
    (∫ p : ℝ × ℝ, Real.log |p.1 - p.2|
      ∂((volume.restrict (Set.Ico a b)).prod (volume.restrict (Set.Ico a b)))) =
      2 * LogSegment.secondPrimitive (b - a) := by
  rw [LogSegment.integral_log_abs_sub_rectangle hab hab]
  have h1 : a - b = -(b - a) := by ring
  rw [sub_self, sub_self, h1]
  unfold LogSegment.secondPrimitive
  rw [abs_neg]
  simp
  ring

theorem fixedVBound : FixedVBound := by
  intro C
  have hm8 := C.m_ge_eight
  have hm : 0 < C.m := by omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hI := selfCellBound C.m hm (pinnedUniverse C.m)
  have hJ := selfCellBound C.m hm (frequencyUniverse C.m)
  have hIcard : (pinnedUniverse C.m).card = C.m := by
    unfold pinnedUniverse; rw [Nat.card_Ico]; omega
  have hJcard : (frequencyUniverse C.m).card = 2 * C.m := by
    unfold frequencyUniverse; rw [Finset.card_range]
  have hImeas : latticeCellMeasure C.m (pinnedUniverse C.m) =
      volume.restrict (Set.Ico (1 / 4 : ℝ) (5 / 4)) := by
    unfold pinnedUniverse
    rw [latticeCellMeasure_Ico C.m hm _ _ (by omega)]
    have h1 : ((C.m / 4 : ℕ) : ℝ) / (C.m : ℝ) = 1 / 4 := by
      rw [show C.m / 4 = k by omega, div_eq_iff hmR.ne', hk]; push_cast; ring
    have h2 : ((5 * C.m / 4 : ℕ) : ℝ) / (C.m : ℝ) = 5 / 4 := by
      rw [show 5 * C.m / 4 = 5 * k by omega, div_eq_iff hmR.ne', hk]; push_cast; ring
    rw [h1, h2]
  have hJmeas : latticeCellMeasure C.m (frequencyUniverse C.m) =
      volume.restrict (Set.Ico (0 : ℝ) 2) := by
    unfold frequencyUniverse
    rw [Finset.range_eq_Ico, latticeCellMeasure_Ico C.m hm _ _ (by omega)]
    have h2 : ((2 * C.m : ℕ) : ℝ) / (C.m : ℝ) = 2 := by
      rw [div_eq_iff hmR.ne']; push_cast; ring
    rw [h2]
    simp
  rw [hImeas, log_energy_Ico _ _ (by norm_num), hIcard] at hI
  rw [hJmeas, log_energy_Ico _ _ (by norm_num), hJcard] at hJ
  have e1 : LogSegment.secondPrimitive (5 / 4 - 1 / 4 : ℝ) = -(3 / 4) := by
    unfold LogSegment.secondPrimitive; norm_num
  have e2 : LogSegment.secondPrimitive (2 - 0 : ℝ) = 2 * Real.log 2 - 3 := by
    unfold LogSegment.secondPrimitive; norm_num; ring
  rw [e1] at hI
  rw [e2] at hJ
  unfold fixedV
  push_cast at hI hJ
  nlinarith

/-! ## Pinned sites against the fixed grid (`eq:config-pinned`) -/

theorem log_factorial_eq_sum (n : ℕ) :
    Real.log (n.factorial : ℝ) = ∑ k ∈ Finset.range n, Real.log ((k + 1 : ℕ) : ℝ) := by
  rw [← Finset.prod_range_add_one_eq_factorial, Nat.cast_prod,
    Real.log_prod (fun k _ => by positivity)]

theorem sum_log_left (s a : ℕ) (has : a ≤ s) :
    (∑ i ∈ Finset.Ico a s, Real.log ((s - i : ℕ) : ℝ)) = Real.log ((s - a).factorial : ℝ) := by
  rw [log_factorial_eq_sum, Finset.sum_Ico_eq_sum_range, ← Finset.sum_range_reflect]
  apply Finset.sum_congr rfl
  intro k hk
  rw [Finset.mem_range] at hk
  congr 3
  omega

theorem sum_log_right (s b : ℕ) (hsb : s < b) :
    (∑ i ∈ Finset.Ico (s + 1) b, Real.log ((i - s : ℕ) : ℝ)) =
      Real.log ((b - 1 - s).factorial : ℝ) := by
  rw [log_factorial_eq_sum, Finset.sum_Ico_eq_sum_range]
  have : b - (s + 1) = b - 1 - s := by omega
  rw [this]
  apply Finset.sum_congr rfl
  intro k hk
  congr 3
  omega

/-- The omitted-site lattice sum in factorial form. -/
theorem sum_ne_log_eq_factorials (m a N s : ℕ) (hm : 0 < m) (has : a ≤ s)
    (hsN : s < a + N) :
    (∑ i ∈ Finset.Ico a (a + N),
        if i = s then 0 else Real.log |(s : ℝ) / (m : ℝ) - (i : ℝ) / (m : ℝ)|) =
      Real.log ((s - a).factorial : ℝ) +
        Real.log ((rightOmittedCount a N s).factorial : ℝ) -
        ((N - 1 : ℕ) : ℝ) * Real.log (m : ℝ) := by
  have hsplit : Finset.Ico a (a + N) = Finset.Ico a s ∪ ({s} ∪ Finset.Ico (s + 1) (a + N)) := by
    ext i
    simp only [Finset.mem_Ico, Finset.mem_union, Finset.mem_singleton]
    omega
  rw [hsplit, Finset.sum_union, Finset.sum_union, Finset.sum_singleton, if_pos rfl]
  · have hL : (∑ i ∈ Finset.Ico a s,
        if i = s then 0 else Real.log |(s : ℝ) / (m : ℝ) - (i : ℝ) / (m : ℝ)|) =
        ∑ i ∈ Finset.Ico a s, (Real.log ((s - i : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hne : s ≠ i := by omega
      rw [if_neg (Ne.symm hne), SelfCells.log_lattice_distance m hm s i hne]
      congr 2
      rw [Nat.dist_comm, Nat.dist_eq_sub_of_le (by omega)]
    have hR : (∑ i ∈ Finset.Ico (s + 1) (a + N),
        if i = s then 0 else Real.log |(s : ℝ) / (m : ℝ) - (i : ℝ) / (m : ℝ)|) =
        ∑ i ∈ Finset.Ico (s + 1) (a + N), (Real.log ((i - s : ℕ) : ℝ) - Real.log (m : ℝ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.mem_Ico] at hi
      have hne : s ≠ i := by omega
      rw [if_neg (Ne.symm hne), SelfCells.log_lattice_distance m hm s i hne]
      congr 2
      rw [Nat.dist_eq_sub_of_le (by omega)]
    rw [hL, hR, Finset.sum_sub_distrib, Finset.sum_sub_distrib, sum_log_left s a has,
      sum_log_right s (a + N) hsN, Finset.sum_const, Finset.sum_const, Nat.card_Ico,
      Nat.card_Ico, nsmul_eq_mul, nsmul_eq_mul]
    unfold rightOmittedCount
    have hc : ((s - a : ℕ) : ℝ) + ((a + N - (s + 1) : ℕ) : ℝ) = ((N - 1 : ℕ) : ℝ) := by
      rw [← Nat.cast_add]; congr 1; omega
    have hb : a + N - 1 - s = a + N - 1 - s := rfl
    rw [← hc]
    ring
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_singleton, Finset.mem_Ico] at hi hi'
    omega
  · rw [Finset.disjoint_left]
    intro i hi hi'
    simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_Ico] at hi hi'
    omega

/-- The real logarithmic potential of an interval at a real point. -/
theorem A0_real (x : ℝ) :
    P0.A0 (x : ℂ) =
      (∫ y in (1 / 4 : ℝ)..(5 / 4 : ℝ), Real.log |x - y|) +
        ∫ y in (0 : ℝ)..(2 : ℝ), Real.log |x - y| := by
  unfold P0.A0
  have h : ∀ y : ℝ, Real.log ‖(x : ℂ) - (y : ℂ)‖ = Real.log |x - y| := by
    intro y
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  simp_rw [h]

theorem pinFieldLower : PinFieldLower := by
  intro C
  have hm8 := C.m_ge_eight
  have hm : 0 < C.m := by omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hcard : (C.pinned.card : ℝ) * Real.log 2 = ∑ _s ∈ C.pinned, Real.log 2 := by
    rw [Finset.sum_const, nsmul_eq_mul]
  unfold pinField
  rw [hcard, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro s hs
  have hsI := C.pinned_subset hs
  simp only [pinnedUniverse, Finset.mem_Ico] at hsI
  -- the `I_m` block
  have hIeq : pinnedUniverse C.m = Finset.Ico (C.m / 4) (C.m / 4 + C.m) := by
    unfold pinnedUniverse; congr 1; omega
  have hI := pinnedQuadratureBound C.m (C.m / 4) C.m s hm hm hsI.1 (by omega)
  rw [← sum_ne_log_eq_factorials C.m (C.m / 4) C.m s hm hsI.1 (by omega)] at hI
  have hIa : ((C.m / 4 : ℕ) : ℝ) / (C.m : ℝ) = 1 / 4 := by
    rw [show C.m / 4 = k by omega, div_eq_iff hmR.ne', hk]; push_cast; ring
  have hIb : ((C.m / 4 + C.m : ℕ) : ℝ) / (C.m : ℝ) = 5 / 4 := by
    rw [show C.m / 4 + C.m = 5 * k by omega, div_eq_iff hmR.ne', hk]; push_cast; ring
  rw [hIa, hIb] at hI
  have hIlog : 0 ≤ Real.log ((C.m : ℝ) / ((rightOmittedCount (C.m / 4) C.m s + 1 : ℕ) : ℝ)) := by
    apply Real.log_nonneg
    rw [le_div_iff₀ (by positivity), one_mul]
    unfold rightOmittedCount
    exact_mod_cast (by omega : C.m / 4 + C.m - 1 - s + 1 ≤ C.m)
  -- the `J_m` block
  have hJeq : frequencyUniverse C.m = Finset.Ico 0 (0 + 2 * C.m) := by
    unfold frequencyUniverse; rw [Finset.range_eq_Ico, zero_add]
  have hJ := pinnedQuadratureBound C.m 0 (2 * C.m) s hm (by omega) (Nat.zero_le s) (by omega)
  rw [← sum_ne_log_eq_factorials C.m 0 (2 * C.m) s hm (Nat.zero_le s) (by omega)] at hJ
  have hJb : ((0 + 2 * C.m : ℕ) : ℝ) / (C.m : ℝ) = 2 := by
    rw [div_eq_iff hmR.ne']; push_cast; ring
  rw [hJb] at hJ
  simp only [Nat.cast_zero, zero_div] at hJ
  have hJlog : -Real.log 2 ≤
      Real.log ((C.m : ℝ) / ((rightOmittedCount 0 (2 * C.m) s + 1 : ℕ) : ℝ)) := by
    have hpos : (0 : ℝ) < ((rightOmittedCount 0 (2 * C.m) s + 1 : ℕ) : ℝ) := by positivity
    have hle : ((rightOmittedCount 0 (2 * C.m) s + 1 : ℕ) : ℝ) ≤ 2 * C.m := by
      unfold rightOmittedCount
      exact_mod_cast (by omega : 0 + 2 * C.m - 1 - s + 1 ≤ 2 * C.m)
    rw [Real.log_div hmR.ne' hpos.ne']
    have h1 := Real.log_le_log hpos hle
    rw [Real.log_mul (by norm_num) hmR.ne'] at h1
    linarith
  rw [A0_real, hIeq, hJeq]
  rw [ge_iff_le] at hI hJ
  nlinarith

/-! ## Contour points against the fixed grid -/

/-- One cell: left-endpoint quadrature of a function with one-sided
Lipschitz control. -/
theorem cell_left_endpoint_le (f : ℝ → ℝ) {a h L : ℝ} (hh : 0 ≤ h)
    (hint : IntervalIntegrable f volume a (a + h))
    (hlip : ∀ x ∈ Set.Icc a (a + h), f x ≤ f a + L * (x - a)) :
    (∫ x in a..(a + h), f x) ≤ h * f a + L * h ^ 2 / 2 := by
  have hle : a ≤ a + h := by linarith
  have hg : IntervalIntegrable (fun x => f a + L * (x - a)) volume a (a + h) := by
    apply Continuous.intervalIntegrable; fun_prop
  calc (∫ x in a..(a + h), f x) ≤ ∫ x in a..(a + h), (f a + L * (x - a)) :=
        intervalIntegral.integral_mono_on hle hint hg hlip
    _ = h * f a + L * h ^ 2 / 2 := by
        rw [intervalIntegral.integral_add intervalIntegrable_const
          (by apply Continuous.intervalIntegrable; fun_prop),
          intervalIntegral.integral_const, intervalIntegral.integral_const_mul,
          intervalIntegral.integral_sub intervalIntegral.intervalIntegrable_id
            intervalIntegrable_const, integral_id, intervalIntegral.integral_const]
        simp only [smul_eq_mul]
        ring

/-- Left-endpoint lattice quadrature on `[p/m, q/m]`. -/
theorem lattice_left_endpoint_le (f : ℝ → ℝ) (m : ℕ) (hm : 0 < m) (p q : ℕ) (hpq : p ≤ q)
    {L : ℝ} (hcont : ContinuousOn f (Set.Icc ((p : ℝ) / m) ((q : ℝ) / m)))
    (hlip : ∀ x ∈ Set.Icc ((p : ℝ) / m) ((q : ℝ) / m),
      ∀ y ∈ Set.Icc ((p : ℝ) / m) ((q : ℝ) / m), f x ≤ f y + L * |x - y|) :
    (m : ℝ) * (∫ x in ((p : ℝ) / m)..((q : ℝ) / m), f x) ≤
      (∑ i ∈ Finset.Ico p q, f ((i : ℝ) / m)) + ((q : ℝ) - p) * L / (2 * m) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  set a : ℕ → ℝ := fun i => (i : ℝ) / m with ha
  have hmono : ∀ i j : ℕ, i ≤ j → a i ≤ a j := by
    intro i j hij
    simp only [ha]
    apply div_le_div_of_nonneg_right _ hmR.le
    exact_mod_cast hij
  have hsub : ∀ i ∈ Finset.Ico p q, Set.Icc (a i) (a (i + 1)) ⊆
      Set.Icc ((p : ℝ) / m) ((q : ℝ) / m) := by
    intro i hi x hx
    rw [Finset.mem_Ico] at hi
    exact ⟨le_trans (hmono p i hi.1) hx.1, le_trans hx.2 (hmono (i + 1) q hi.2)⟩
  have hII : ∀ i ∈ Finset.Ico p q, IntervalIntegrable f volume (a i) (a (i + 1)) := by
    intro i hi
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le (hmono i (i + 1) (Nat.le_succ i))]
    exact hcont.mono (hsub i hi)
  have hsum := intervalIntegral.sum_integral_adjacent_intervals_Ico hpq
    (fun k hk => hII k (Finset.mem_Ico.mpr hk))
  simp only [ha] at hsum
  rw [← hsum, Finset.mul_sum]
  have hcell : ∀ i ∈ Finset.Ico p q,
      (m : ℝ) * (∫ x in ((i : ℝ) / m)..(((i + 1 : ℕ) : ℝ) / m), f x) ≤
        f ((i : ℝ) / m) + L / (2 * m) := by
    intro i hi
    have hstep : (((i + 1 : ℕ) : ℝ) / m) = (i : ℝ) / m + 1 / m := by
      push_cast; ring
    rw [hstep]
    have hcl := cell_left_endpoint_le f (a := (i : ℝ) / m) (h := 1 / m) (L := L)
      (by positivity) (by rw [← hstep]; exact hII i hi) (by
        intro x hx
        have hx' : x ∈ Set.Icc ((p : ℝ) / m) ((q : ℝ) / m) := by
          apply hsub i hi
          simp only [ha]
          rw [hstep]
          exact hx
        have hi' : (i : ℝ) / m ∈ Set.Icc ((p : ℝ) / m) ((q : ℝ) / m) := by
          apply hsub i hi
          simp only [ha]
          exact ⟨le_rfl, hmono i (i + 1) (Nat.le_succ i)⟩
        have := hlip x hx' _ hi'
        rwa [abs_of_nonneg (by linarith [hx.1])] at this)
    have : (m : ℝ) * (1 / m * f ((i : ℝ) / m) + L * (1 / m) ^ 2 / 2) =
        f ((i : ℝ) / m) + L / (2 * m) := by
      field_simp
    nlinarith
  calc (∑ i ∈ Finset.Ico p q, (m : ℝ) * ∫ x in ((i : ℝ) / m)..(((i + 1 : ℕ) : ℝ) / m), f x)
      ≤ ∑ i ∈ Finset.Ico p q, (f ((i : ℝ) / m) + L / (2 * m)) := Finset.sum_le_sum hcell
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_const, Nat.card_Ico, nsmul_eq_mul,
        Nat.cast_sub hpq]
      ring

/-- `x ↦ log |ζ - x|` is `1/d_+`-Lipschitz on `[0, 2]` for `ζ` on the base
ellipse. -/
theorem log_norm_sub_lip {ζ : ℂ} (hζ : ζ ∈ baseEllipseSet) {x y : ℝ}
    (hx : x ∈ Set.Icc (0 : ℝ) 2) (hy : y ∈ Set.Icc (0 : ℝ) 2) :
    Real.log ‖ζ - (x : ℂ)‖ ≤ Real.log ‖ζ - (y : ℂ)‖ + (1 / dPlus) * |x - y| := by
  have hdP : 0 < dPlus := by norm_num [dPlus]
  have hxl := mixedCellClearance_full.1 ζ hζ x hx
  have hyl := mixedCellClearance_full.1 ζ hζ y hy
  have hvpos : 0 < ‖ζ - (y : ℂ)‖ := lt_of_lt_of_le hdP hyl
  have hupos : 0 < ‖ζ - (x : ℂ)‖ := lt_of_lt_of_le hdP hxl
  have htri : ‖ζ - (x : ℂ)‖ ≤ ‖ζ - (y : ℂ)‖ + |x - y| := by
    calc ‖ζ - (x : ℂ)‖ = ‖(ζ - (y : ℂ)) + ((y : ℂ) - (x : ℂ))‖ := by ring_nf
      _ ≤ ‖ζ - (y : ℂ)‖ + ‖(y : ℂ) - (x : ℂ)‖ := norm_add_le _ _
      _ = ‖ζ - (y : ℂ)‖ + |x - y| := by
        rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
  have hlog := Real.log_le_sub_one_of_pos (div_pos hupos hvpos)
  rw [Real.log_div hupos.ne' hvpos.ne'] at hlog
  have hq : ‖ζ - (x : ℂ)‖ / ‖ζ - (y : ℂ)‖ - 1 ≤ |x - y| / dPlus := by
    rw [div_sub_one hvpos.ne', div_le_div_iff₀ hvpos hdP]
    have : (‖ζ - (x : ℂ)‖ - ‖ζ - (y : ℂ)‖) * dPlus ≤ |x - y| * dPlus := by
      apply mul_le_mul_of_nonneg_right _ hdP.le; linarith
    nlinarith [abs_nonneg (x - y)]
  have : |x - y| / dPlus = (1 / dPlus) * |x - y| := by ring
  linarith

theorem continuousOn_log_norm_sub {ζ : ℂ} (hζ : ζ ∈ baseEllipseSet) :
    ContinuousOn (fun x : ℝ => Real.log ‖ζ - (x : ℂ)‖) (Set.Icc (0 : ℝ) 2) := by
  apply ContinuousOn.log
  · fun_prop
  · intro x hx
    have hdP : 0 < dPlus := by norm_num [dPlus]
    have := mixedCellClearance_full.1 ζ hζ x hx
    exact (lt_of_lt_of_le hdP this).ne'

theorem contFieldLower : ContFieldLower := by
  intro C
  have hm8 := C.m_ge_eight
  have hm : 0 < C.m := by omega
  have hmR : (0 : ℝ) < C.m := by exact_mod_cast hm
  obtain ⟨k, hk⟩ := C.four_dvd_m
  have hdP : 0 < dPlus := by norm_num [dPlus]
  have hcard : (C.contourCount : ℝ) * (3 / (2 * dPlus)) =
      ∑ _a : Fin C.contourCount, 3 / (2 * dPlus) := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  unfold contField
  rw [hcard, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_le_sum
  intro a _
  have hζ := C.contour_mem a
  set f : ℝ → ℝ := fun x => Real.log ‖C.contour a - (x : ℂ)‖ with hf
  have hlipI : ∀ {p q : ℕ}, (0 : ℝ) ≤ (p : ℝ) / C.m → (q : ℝ) / C.m ≤ 2 →
      ∀ x ∈ Set.Icc ((p : ℝ) / C.m) ((q : ℝ) / C.m),
      ∀ y ∈ Set.Icc ((p : ℝ) / C.m) ((q : ℝ) / C.m), f x ≤ f y + (1 / dPlus) * |x - y| := by
    intro p q hp hq x hx y hy
    exact log_norm_sub_lip hζ ⟨by linarith [hx.1], by linarith [hx.2]⟩
      ⟨by linarith [hy.1], by linarith [hy.2]⟩
  have hcontI : ∀ {p q : ℕ}, (0 : ℝ) ≤ (p : ℝ) / C.m → (q : ℝ) / C.m ≤ 2 →
      ContinuousOn f (Set.Icc ((p : ℝ) / C.m) ((q : ℝ) / C.m)) := by
    intro p q hp hq
    exact (continuousOn_log_norm_sub hζ).mono (fun x hx => ⟨by linarith [hx.1], by linarith [hx.2]⟩)
  -- `I_m`
  have hIa : ((C.m / 4 : ℕ) : ℝ) / (C.m : ℝ) = 1 / 4 := by
    rw [show C.m / 4 = k by omega, div_eq_iff hmR.ne', hk]; push_cast; ring
  have hIb : ((5 * C.m / 4 : ℕ) : ℝ) / (C.m : ℝ) = 5 / 4 := by
    rw [show 5 * C.m / 4 = 5 * k by omega, div_eq_iff hmR.ne', hk]; push_cast; ring
  have hI := lattice_left_endpoint_le f C.m hm (C.m / 4) (5 * C.m / 4) (by omega)
    (hcontI (by rw [hIa]; norm_num) (by rw [hIb]; norm_num))
    (hlipI (by rw [hIa]; norm_num) (by rw [hIb]; norm_num))
  rw [hIa, hIb] at hI
  have hIc : ((5 * C.m / 4 : ℕ) : ℝ) - ((C.m / 4 : ℕ) : ℝ) = C.m := by
    rw [show 5 * C.m / 4 = 5 * k by omega, show C.m / 4 = k by omega, hk]; push_cast; ring
  rw [hIc] at hI
  -- `J_m`
  have hJb : ((2 * C.m : ℕ) : ℝ) / (C.m : ℝ) = 2 := by
    rw [div_eq_iff hmR.ne']; push_cast; ring
  have hJ := lattice_left_endpoint_le f C.m hm 0 (2 * C.m) (by omega)
    (hcontI (by simp) (by rw [hJb])) (hlipI (by simp) (by rw [hJb]))
  rw [hJb] at hJ
  simp only [Nat.cast_zero, zero_div, sub_zero] at hJ
  have hA : P0.A0 (C.contour a) =
      (∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ), f x) + ∫ x in (0 : ℝ)..(2 : ℝ), f x := rfl
  rw [hA]
  have hsI : (∑ i ∈ pinnedUniverse C.m,
      Real.log ‖C.contour a - (((i : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖) =
      ∑ i ∈ Finset.Ico (C.m / 4) (5 * C.m / 4), f ((i : ℝ) / C.m) := rfl
  have hsJ : (∑ j ∈ frequencyUniverse C.m,
      Real.log ‖C.contour a - (((j : ℝ) / (C.m : ℝ) : ℝ) : ℂ)‖) =
      ∑ i ∈ Finset.range (2 * C.m), f ((i : ℝ) / C.m) := rfl
  rw [hsI, hsJ, Finset.range_eq_Ico]
  have e1 : (C.m : ℝ) * (1 / dPlus) / (2 * C.m) = 1 / (2 * dPlus) := by
    field_simp
  have e2 : (2 * (C.m : ℝ)) * (1 / dPlus) / (2 * C.m) = 1 / dPlus := by
    field_simp
  have e3 : 1 / (2 * dPlus) + 1 / dPlus = 3 / (2 * dPlus) := by
    field_simp; ring
  push_cast at hJ
  rw [e1] at hI
  rw [e2] at hJ
  rw [mul_add]
  linarith

end

end Li2Lean.P0.CellBound
