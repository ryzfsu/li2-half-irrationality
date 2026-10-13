/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.TubeSweepPair
import Li2Lean.P0.TubeSweepFubini

/-! # Sweep energy bound `I(ν#) ≤ I(ν) + 2 s b`

For a finite measure `ν` carried by the tube `T_δ` (`0 ≤ δ ≤ 1/64`) with no
atoms and finite logarithmic self-energy, the swept measure
`ν# = ∫ ω_z dν(z)` (the actual `tubeSweep` family) satisfies

* `ν#` is carried by `Γ`, has the same mass, and has no atoms (output);
* the logarithmic kernel is integrable for `ν# ⊗ ν#` (output);
* `I(ν#) ≤ I(ν) + 2 s b` with `s = ν(ℂ)` and `b = ∫ e dν`.

The proof truncates first (`truncK ε`, valid at every pair of points, no
collision premise), applies the truncated two-sweep inequality under Fubini for
the bind, and passes to `ε → 0` by monotone convergence.
-/

open MeasureTheory ProbabilityTheory Filter Topology

namespace Li2Lean.P0.TubeEnergy

noncomputable section

open TubeInterior

/-- The sweep family as a Markov kernel. -/
def tubeKernel : Kernel ℂ ℂ := ⟨tubeSweep, measurable_tubeSweep⟩

instance : IsMarkovKernel tubeKernel := ⟨fun z => tubeSweep_isProbability z⟩

@[simp] theorem tubeKernel_apply (z : ℂ) : tubeKernel z = tubeSweep z := rfl

/-- The two-point sweep kernel `p ↦ ω_{p.1} ⊗ ω_{p.2}`. -/
def pairKernel : Kernel (ℂ × ℂ) (ℂ × ℂ) :=
  (tubeKernel.comap Prod.fst measurable_fst) ×ₖ (tubeKernel.comap Prod.snd measurable_snd)

theorem pairKernel_apply (p : ℂ × ℂ) :
    pairKernel p = (tubeSweep p.1).prod (tubeSweep p.2) := by
  rw [pairKernel, Kernel.prod_apply]
  rfl

instance : IsMarkovKernel pairKernel :=
  ⟨fun p => by rw [pairKernel_apply]; infer_instance⟩

/-- The swept measure `ν#`. -/
def tubeSwept (ν : Measure ℂ) : Measure ℂ := sweptMeasure ν tubeSweep

theorem tubeSwept_apply (ν : Measure ℂ) {s : Set ℂ} (hs : MeasurableSet s) :
    tubeSwept ν s = ∫⁻ z, tubeSweep z s ∂ν :=
  Measure.bind_apply hs measurable_tubeSweep.aemeasurable

theorem tubeSwept_univ (ν : Measure ℂ) : tubeSwept ν Set.univ = ν Set.univ := by
  rw [tubeSwept_apply ν MeasurableSet.univ]
  simp

instance (ν : Measure ℂ) [IsFiniteMeasure ν] : IsFiniteMeasure (tubeSwept ν) :=
  ⟨by rw [tubeSwept_univ]; exact measure_lt_top ν _⟩

theorem tubeSwept_boundary_support (ν : Measure ℂ) : tubeSwept ν Gammaᶜ = 0 := by
  rw [tubeSwept_apply ν TubeInterior.measurable_Gamma.compl]
  simp [tubeSweep_boundary_support]

theorem tubeSwept_ae_mem_Gamma (ν : Measure ℂ) : ∀ᵐ y ∂tubeSwept ν, y ∈ Gamma := by
  rw [ae_iff]; exact tubeSwept_boundary_support ν

/-- Atomlessness is an output of sweeping an atomless measure. -/
theorem tubeSwept_singleton (ν : Measure ℂ) (hatom : ∀ z, ν {z} = 0) (x : ℂ) :
    tubeSwept ν {x} = 0 := by
  rw [tubeSwept_apply ν (measurableSet_singleton x)]
  apply lintegral_eq_zero_of_ae_eq_zero
  have hne : ∀ᵐ z ∂ν, z ≠ x := by
    rw [ae_iff]; simpa using hatom x
  filter_upwards [hne] with z hz
  exact tubeSweep_singleton_of_ne hz

/-- The square of the bind is the bind of the pair kernel. -/
theorem tubeSwept_prod (ν : Measure ℂ) [IsFiniteMeasure ν] :
    (tubeSwept ν).prod (tubeSwept ν) = (ν.prod ν).bind pairKernel := by
  apply Measure.prod_eq
  intro s t hs ht
  rw [Measure.bind_apply (hs.prod ht) pairKernel.measurable.aemeasurable]
  simp_rw [pairKernel_apply, Measure.prod_prod]
  rw [tubeSwept_apply ν hs, tubeSwept_apply ν ht]
  exact lintegral_prod_mul (f := fun z => tubeSweep z s) (g := fun z => tubeSweep z t)
    ((Measure.measurable_coe hs).comp measurable_tubeSweep).aemeasurable
    ((Measure.measurable_coe ht).comp measurable_tubeSweep).aemeasurable

/-! ## Elementary bounds on the tube -/

theorem norm_le_of_mem_tube {δ : ℝ} {z : ℂ} (hz : z ∈ tube δ) : ‖z‖ ≤ 4 + δ := by
  obtain ⟨y, hy, hyd⟩ :=
    TubeInterior.isCompact_Gamma.exists_infDist_eq_dist (Set.range_nonempty gammaPoint) z
  change Metric.infDist z Gamma ≤ δ at hz
  rw [hyd, dist_eq_norm] at hz
  have := TubeVariance.norm_le_four_of_mem_Gamma hy
  calc ‖z‖ = ‖(z - y) + y‖ := by ring_nf
    _ ≤ ‖z - y‖ + ‖y‖ := norm_add_le _ _
    _ ≤ 4 + δ := by linarith

theorem norm_sub_le_nine_of_mem_tube {δ : ℝ} (hδ : δ ≤ tubeRadiusMax) {z w : ℂ}
    (hz : z ∈ tube δ) (hw : w ∈ tube δ) : ‖z - w‖ ≤ 9 := by
  have h1 := norm_le_of_mem_tube hz
  have h2 := norm_le_of_mem_tube hw
  norm_num [tubeRadiusMax] at hδ
  calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le _ _
    _ ≤ 9 := by linarith

theorem ae_prod_mem_tube {δ : ℝ} (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ) : ∀ᵐ p ∂ν.prod ν, p.1 ∈ tube δ ∧ p.2 ∈ tube δ := by
  have h1 := (Measure.quasiMeasurePreserving_fst (μ := ν) (ν := ν)).ae hsupp
  have h2 := (Measure.quasiMeasurePreserving_snd (μ := ν) (ν := ν)).ae hsupp
  filter_upwards [h1, h2] with p hp1 hp2
  exact ⟨hp1, hp2⟩

theorem ae_prod_ne (ν : Measure ℂ) [IsFiniteMeasure ν] (hatom : ∀ z, ν {z} = 0) :
    ∀ᵐ p ∂ν.prod ν, p.1 ≠ p.2 := by
  rw [ae_iff]
  have hset : {p : ℂ × ℂ | ¬p.1 ≠ p.2} = Set.diagonal ℂ := by
    ext p; simp [Set.mem_diagonal_iff]
  rw [hset, Measure.prod_apply measurableSet_diagonal]
  have hpre : ∀ x : ℂ, Prod.mk x ⁻¹' Set.diagonal ℂ = {x} := by
    intro x; ext y; simp [Set.mem_diagonal_iff, eq_comm]
  simp_rw [hpre, hatom]
  simp

theorem tubeCorrection_bounds {δ : ℝ} (hδ : 0 ≤ δ) {z : ℂ} (hz : z ∈ tube δ) :
    0 ≤ tubeCorrection z ∧ tubeCorrection z ≤ δ / semiMinor :=
  ellipseExteriorCorrection_bound hδ hz

theorem integrable_tubeCorrection {δ : ℝ} (hδ : 0 ≤ δ) (ν : Measure ℂ) [IsFiniteMeasure ν]
    (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ) : Integrable tubeCorrection ν := by
  apply (integrable_const (δ / semiMinor)).mono' measurable_tubeCorrection.aestronglyMeasurable
  filter_upwards [hsupp] with z hz
  have h := tubeCorrection_bounds hδ hz
  rw [Real.norm_of_nonneg h.1]; exact h.2

theorem measurable_realLogKernel_prod :
    Measurable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) := by
  unfold realLogKernel; fun_prop

/-! ## The truncated sweep bound -/

/-- Truncated logarithmic energy. -/
def truncEnergy (ε : ℝ) (μ : Measure ℂ) : ℝ := ∫ p, truncK ε p.1 p.2 ∂μ.prod μ

/-- The truncated energy of the swept measure is the `ν ⊗ ν` average of the
two-sweep truncated energies. -/
theorem truncEnergy_tubeSwept_eq {ε : ℝ} (hε : 0 < ε) (hε8 : ε ≤ 8)
    (ν : Measure ℂ) [IsFiniteMeasure ν] :
    truncEnergy ε (tubeSwept ν) =
      ∫ p, (∫ q, truncK ε q.1 q.2 ∂(tubeSweep p.1).prod (tubeSweep p.2)) ∂ν.prod ν := by
  have hint := integrable_truncK_prod_of_Gamma hε hε8 (tubeSwept ν) (tubeSwept ν)
    (tubeSwept_ae_mem_Gamma ν) (tubeSwept_ae_mem_Gamma ν)
  rw [tubeSwept_prod] at hint
  unfold truncEnergy
  rw [tubeSwept_prod]
  have hcomp := ProbabilityTheory.Kernel.integral_comp
    (κ := Kernel.const Unit (ν.prod ν)) (η := pairKernel) (a := ())
    (f := fun q : ℂ × ℂ => truncK ε q.1 q.2) hint
  have hb : (pairKernel ∘ₖ Kernel.const Unit (ν.prod ν)) () = (ν.prod ν).bind pairKernel := by
    rw [Kernel.comp_apply, Kernel.const_apply]
  rw [hb] at hcomp
  simpa only [pairKernel_apply, Kernel.const_apply] using hcomp

theorem truncEnergy_tubeSwept_le {δ ε : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (hε : 0 < ε) (hε1 : ε ≤ 1)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (hatom : ∀ z, ν {z} = 0)
    (hI : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (ν.prod ν)) :
    truncEnergy ε (tubeSwept ν) ≤
      (∫ p, realLogKernel p.1 p.2 ∂ν.prod ν) +
        2 * ν.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
  have hε8 : ε ≤ 8 := by linarith
  have hε9 : ε ≤ 9 := by linarith
  rw [truncEnergy_tubeSwept_eq hε hε8]
  -- integrability of the averaged two-sweep energy
  set M : ℝ := |Real.log ε| + |Real.log 8|
  have hpair_meas : StronglyMeasurable
      (fun p : ℂ × ℂ => ∫ q, truncK ε q.1 q.2 ∂pairKernel p) :=
    StronglyMeasurable.integral_kernel_prod_right'
      (f := fun x : (ℂ × ℂ) × (ℂ × ℂ) => truncK ε x.2.1 x.2.2)
      ((continuous_truncK hε).stronglyMeasurable.comp_measurable measurable_snd)
  have hpair_int : Integrable
      (fun p : ℂ × ℂ => ∫ q, truncK ε q.1 q.2 ∂(tubeSweep p.1).prod (tubeSweep p.2))
      (ν.prod ν) := by
    simp_rw [← pairKernel_apply]
    apply (integrable_const M).mono' hpair_meas.aestronglyMeasurable
    filter_upwards with p
    rw [pairKernel_apply]
    have hb : ∀ᵐ q ∂(tubeSweep p.1).prod (tubeSweep p.2), ‖truncK ε q.1 q.2‖ ≤ M := by
      filter_upwards [ae_prod_mem_Gamma _ _ (tubeSweep_ae_mem_Gamma p.1)
        (tubeSweep_ae_mem_Gamma p.2)] with q hq
      rw [Real.norm_eq_abs]
      exact abs_truncK_le hε hε8 (norm_sub_le_eight_of_mem_Gamma hq.1 hq.2)
    have := norm_integral_le_of_norm_le_const hb
    simpa using this
  -- integrability of the comparison integrand
  have hK_int : Integrable (fun p : ℂ × ℂ => truncK ε p.1 p.2) (ν.prod ν) := by
    apply (integrable_const (|Real.log ε| + |Real.log 9|)).mono'
      (continuous_truncK hε).aestronglyMeasurable
    filter_upwards [ae_prod_mem_tube ν hsupp] with p hp
    rw [Real.norm_eq_abs]
    exact abs_truncK_le hε hε9 (norm_sub_le_nine_of_mem_tube hδmax hp.1 hp.2)
  have he := integrable_tubeCorrection hδ ν hsupp
  have he1 : Integrable (fun p : ℂ × ℂ => tubeCorrection p.1) (ν.prod ν) :=
    he.comp_fst ν
  have he2 : Integrable (fun p : ℂ × ℂ => tubeCorrection p.2) (ν.prod ν) :=
    he.comp_snd ν
  calc (∫ p, (∫ q, truncK ε q.1 q.2 ∂(tubeSweep p.1).prod (tubeSweep p.2)) ∂ν.prod ν)
      ≤ ∫ p, (truncK ε p.1 p.2 + tubeCorrection p.1 + tubeCorrection p.2) ∂ν.prod ν :=
        integral_mono hpair_int ((hK_int.add he1).add he2)
          (fun p => tubeSweep_pair_truncK_le hε hε8 p.1 p.2)
    _ = (∫ p, truncK ε p.1 p.2 ∂ν.prod ν) +
          2 * ν.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
        rw [integral_add (f := fun p : ℂ × ℂ => truncK ε p.1 p.2 + tubeCorrection p.1)
            (hK_int.add he1) he2,
          integral_add (f := fun p : ℂ × ℂ => truncK ε p.1 p.2) hK_int he1,
          integral_fun_fst (μ := ν) (ν := ν) tubeCorrection,
          integral_fun_snd (μ := ν) (ν := ν) tubeCorrection]
        simp only [smul_eq_mul]
        ring
    _ ≤ (∫ p, realLogKernel p.1 p.2 ∂ν.prod ν) +
          2 * ν.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
        have := integral_mono_ae hK_int hI
          ((ae_prod_ne ν hatom).mono fun p hp => truncK_le_realLogKernel hε hp)
        linarith

/-! ## Monotone convergence `ε → 0` -/

/-- The paper's sweep energy inequality for the actual harmonic sweep. -/
theorem tubeSwept_energy_le {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (hatom : ∀ z, ν {z} = 0)
    (hI : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (ν.prod ν)) :
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) ((tubeSwept ν).prod (tubeSwept ν)) ∧
    (∫ p, realLogKernel p.1 p.2 ∂(tubeSwept ν).prod (tubeSwept ν)) ≤
      (∫ p, realLogKernel p.1 p.2 ∂ν.prod ν) +
        2 * ν.real Set.univ * ∫ z, tubeCorrection z ∂ν := by
  set μ2 := (tubeSwept ν).prod (tubeSwept ν) with hμ2
  set R := (∫ p, realLogKernel p.1 p.2 ∂ν.prod ν) +
        2 * ν.real Set.univ * ∫ z, tubeCorrection z ∂ν with hR
  set c : ℝ := Real.log 8
  have hc : 0 < c := Real.log_pos (by norm_num)
  set ε : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1) with hεdef
  have hεpos : ∀ n, 0 < ε n := fun n => by simp only [ε]; positivity
  have hε1 : ∀ n, ε n ≤ 1 := fun n => by
    simp only [ε]
    rw [div_le_one (by positivity)]
    linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  have hεanti : Antitone ε := by
    intro m n hmn
    simp only [ε]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast Nat.add_le_add_right hmn 1
  have hΓ2 : ∀ᵐ p ∂μ2, p.1 ∈ Gamma ∧ p.2 ∈ Gamma :=
    ae_prod_mem_Gamma _ _ (tubeSwept_ae_mem_Gamma ν) (tubeSwept_ae_mem_Gamma ν)
  have hne2 : ∀ᵐ p ∂μ2, p.1 ≠ p.2 :=
    ae_prod_ne (tubeSwept ν) (tubeSwept_singleton ν hatom)
  -- the truncated integrands, shifted to be nonnegative
  set f : ℕ → ℂ × ℂ → ENNReal :=
    fun n p => ENNReal.ofReal (truncK (ε n) p.1 p.2 + c) with hf
  set F : ℂ × ℂ → ENNReal := fun p => ENNReal.ofReal (realLogKernel p.1 p.2 + c) with hF
  have hK0_ge : ∀ᵐ p ∂μ2, -c ≤ realLogKernel p.1 p.2 := by
    filter_upwards [hΓ2] with p hp
    by_cases h : p.1 = p.2
    · simp [realLogKernel, h]; exact hc.le
    · have h8 := norm_sub_le_eight_of_mem_Gamma hp.1 hp.2
      have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr h)
      unfold realLogKernel
      exact neg_le_neg (Real.log_le_log hpos h8)
  have htr_int : ∀ n, Integrable (fun p : ℂ × ℂ => truncK (ε n) p.1 p.2 + c) μ2 := fun n =>
    (integrable_truncK_prod_of_Gamma (hεpos n) (by linarith [hε1 n]) _ _
      (tubeSwept_ae_mem_Gamma ν) (tubeSwept_ae_mem_Gamma ν)).add (integrable_const c)
  have htr_nonneg : ∀ n, 0 ≤ᵐ[μ2] (fun p : ℂ × ℂ => truncK (ε n) p.1 p.2 + c) := by
    intro n
    filter_upwards [hΓ2] with p hp
    have := neg_log_le_truncK (hεpos n) (by linarith [hε1 n] : ε n ≤ 8)
      (norm_sub_le_eight_of_mem_Gamma hp.1 hp.2)
    show 0 ≤ truncK (ε n) p.1 p.2 + c
    linarith
  -- each truncated lintegral is bounded
  have hbound : ∀ n, ∫⁻ p, f n p ∂μ2 ≤ ENNReal.ofReal (R + c * μ2.real Set.univ) := by
    intro n
    simp only [hf]
    rw [← ofReal_integral_eq_lintegral_ofReal (htr_int n) (htr_nonneg n),
      integral_add (integrable_truncK_prod_of_Gamma (hεpos n) (by linarith [hε1 n]) _ _
        (tubeSwept_ae_mem_Gamma ν) (tubeSwept_ae_mem_Gamma ν)) (integrable_const c)]
    apply ENNReal.ofReal_le_ofReal
    have := truncEnergy_tubeSwept_le hδ hδmax (hεpos n) (hε1 n) ν hsupp hatom hI
    simp only [truncEnergy] at this
    rw [integral_const, smul_eq_mul]
    linarith
  -- monotone convergence
  have hmeas : ∀ n, AEMeasurable (f n) μ2 := fun n =>
    ((continuous_truncK (hεpos n)).add continuous_const).measurable.ennreal_ofReal.aemeasurable
  have hmono : ∀ᵐ p ∂μ2, Monotone fun n => f n p := by
    filter_upwards with p
    intro m n hmn
    apply ENNReal.ofReal_le_ofReal
    linarith [truncK_antitone (hεpos n) (hεanti hmn) p.1 p.2]
  have htend : ∀ᵐ p ∂μ2, Tendsto (fun n => f n p) atTop (𝓝 (F p)) := by
    filter_upwards [hne2] with p hp
    have hpos : 0 < ‖p.1 - p.2‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hp)
    obtain ⟨N, hN⟩ := exists_nat_one_div_lt hpos
    apply tendsto_const_nhds.congr'
    filter_upwards [eventually_ge_atTop N] with n hn
    have hle : ε n ≤ ‖p.1 - p.2‖ := by
      have : ε n ≤ ε N := hεanti hn
      simp only [ε] at this ⊢
      linarith
    simp only [hf, hF, truncK_eq_of_le hle]
  have hlim := lintegral_tendsto_of_tendsto_of_monotone hmeas hmono htend
  have hFle : ∫⁻ p, F p ∂μ2 ≤ ENNReal.ofReal (R + c * μ2.real Set.univ) :=
    le_of_tendsto' hlim hbound
  -- integrability of the shifted kernel
  have hshift_nonneg : 0 ≤ᵐ[μ2] (fun p : ℂ × ℂ => realLogKernel p.1 p.2 + c) := by
    filter_upwards [hK0_ge] with p hp
    show 0 ≤ realLogKernel p.1 p.2 + c
    linarith
  have hshift_int : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2 + c) μ2 := by
    refine ⟨(measurable_realLogKernel_prod.add measurable_const).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hshift_nonneg]
    exact lt_of_le_of_lt hFle ENNReal.ofReal_lt_top
  have hK_int : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) μ2 := by
    have := hshift_int.sub (integrable_const c)
    convert this using 1
    funext p
    simp only [Pi.sub_apply]
    ring
  refine ⟨hK_int, ?_⟩
  -- pass to the real inequality
  have hR_nonneg : 0 ≤ R + c * μ2.real Set.univ := by
    have h0 := htr_nonneg 0
    have hi := integral_nonneg_of_ae h0
    rw [integral_add (integrable_truncK_prod_of_Gamma (hεpos 0) (by linarith [hε1 0]) _ _
        (tubeSwept_ae_mem_Gamma ν) (tubeSwept_ae_mem_Gamma ν)) (integrable_const c),
      integral_const, smul_eq_mul] at hi
    have := truncEnergy_tubeSwept_le hδ hδmax (hεpos 0) (hε1 0) ν hsupp hatom hI
    simp only [truncEnergy] at this
    linarith
  have hreal : ∫ p, (realLogKernel p.1 p.2 + c) ∂μ2 ≤ R + c * μ2.real Set.univ := by
    rw [← ENNReal.ofReal_le_ofReal_iff hR_nonneg,
      ofReal_integral_eq_lintegral_ofReal hshift_int hshift_nonneg]
    exact hFle
  rw [integral_add hK_int (integrable_const c), integral_const, smul_eq_mul] at hreal
  linarith

/-- Packaged sweep statement: mass, support, atomlessness and energy, all as outputs. -/
theorem tubeSwept_properties {δ : ℝ} (hδ : 0 ≤ δ) (hδmax : δ ≤ tubeRadiusMax)
    (ν : Measure ℂ) [IsFiniteMeasure ν] (hsupp : ∀ᵐ z ∂ν, z ∈ tube δ)
    (hatom : ∀ z, ν {z} = 0)
    (hI : Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) (ν.prod ν)) :
    tubeSwept ν Set.univ = ν Set.univ ∧
    tubeSwept ν Gammaᶜ = 0 ∧
    (∀ x, tubeSwept ν {x} = 0) ∧
    Integrable (fun p : ℂ × ℂ => realLogKernel p.1 p.2) ((tubeSwept ν).prod (tubeSwept ν)) ∧
    (∫ p, realLogKernel p.1 p.2 ∂(tubeSwept ν).prod (tubeSwept ν)) ≤
      (∫ p, realLogKernel p.1 p.2 ∂ν.prod ν) +
        2 * ν.real Set.univ * ∫ z, tubeCorrection z ∂ν ∧
    0 ≤ (∫ z, tubeCorrection z ∂ν) ∧
    (∫ z, tubeCorrection z ∂ν) ≤ ν.real Set.univ * (δ / semiMinor) := by
  have hE := tubeSwept_energy_le hδ hδmax ν hsupp hatom hI
  refine ⟨tubeSwept_univ ν, tubeSwept_boundary_support ν, tubeSwept_singleton ν hatom,
    hE.1, hE.2, integral_nonneg_of_ae ?_, ?_⟩
  · filter_upwards [hsupp] with z hz
    exact (tubeCorrection_bounds hδ hz).1
  · calc (∫ z, tubeCorrection z ∂ν) ≤ ∫ _z, δ / semiMinor ∂ν :=
          integral_mono_ae (integrable_tubeCorrection hδ ν hsupp) (integrable_const _)
            (hsupp.mono fun z hz => (tubeCorrection_bounds hδ hz).2)
      _ = ν.real Set.univ * (δ / semiMinor) := by rw [integral_const, smul_eq_mul]

end
end Li2Lean.P0.TubeEnergy
