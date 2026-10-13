/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigOneBodyBound
import Li2Lean.P0.ActualFrequencyTailFactor
import Li2Lean.P0.ConfigCstarNumeric
import Li2Lean.P0.P0CoefficientEvaluationBridge
import Li2Lean.P0.WeightedCoefficientStep
import Li2Lean.P0.ProductIntegralBound

/-!
# Coefficient step: assembly from the two analytic inputs

This file proves the order-theoretic and counting part of the coefficient
step of paper v13 `p0-analytic.tex` (ll. 620--747) against the canonical
declarations:

* `E m (20m)` is bounded by the per-configuration bound times the
  `2^m` pinned choices, the `binom(39m/2, m)` retained frequency sets, and the
  factorial-normalized contour volume `(mA)^d/d! ≤ e^{mA}` (ll. 709--713);
* the frequency tail factor (`full_cutoffENN_actual_tail_factor`) passes this
  to the literal full envelope `EInfinity`;
* the linear constant check `c_* + log 39 + 1 + A < 56` (l. 459/712) and the
  tail budget `300 + 1/3 + 1/3 < 301` close the target exponent.

The two analytic inputs remain explicit and are stated with their canonical
types: the per-configuration bound restricted to the retained frequency head
(`ConfigFinalBoundLiteralHead`, weaker than `ConfigFinalBoundLiteral`) and the
signed coefficient envelope `‖G_m(β)‖ ≤ EInfinity`.  Neither is a restatement
of the conclusion: the first is a pointwise bound for one configuration, the
second has no decay rate at all.
-/

open MeasureTheory
open scoped BigOperators

namespace Li2Lean.P0.CoefficientAssembly

open Li2Lean.P0
open Li2Lean.P0.Config
open Li2Lean.P0.FrequencyCutoff

noncomputable section

/-! ## The per-configuration input on the retained frequency head -/

/-- The pointwise exponent of the literal C-A bound (`ConfigFinalBound`). -/
def configExponent (alpha : ℝ) (m : ℕ) : ℝ :=
  -alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log (m : ℝ) +
    cStar * (m : ℝ) + 300 + 1 / 3

/-- The literal per-configuration bound for configurations whose frequencies
lie in the retained head `R ⊆ {g+1, …, 20m}` (paper v13 ll. 613--618: only
these configurations enter the variational bound).  It is implied by the
unrestricted `ConfigFinalBoundLiteral`. -/
def ConfigFinalBoundLiteralHead (alpha : ℝ) : Prop :=
  ∀ C : FiniteConfiguration, (∀ r ∈ C.frequency, r ≤ 20 * C.m) →
    literalConfigQWeight C = 0 ∨
      (0 < literalConfigQWeight C ∧
        Real.log (literalConfigQWeight C) ≤ configExponent alpha C.m)

theorem configFinalBoundLiteralHead_of_literal {alpha : ℝ}
    (h : ConfigFinalBoundLiteral alpha) : ConfigFinalBoundLiteralHead alpha :=
  fun C _ => h C

/-- Pointwise consequence on the literal contour integrand for a retained tuple. -/
theorem contourQValue_le_exp_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) (r : IncreasingTuple (m / 2) m)
    (hr : r ∈ cutoffTuples (m / 2) m (20 * m)) (u : Fin (m - S.card) → ℝ) :
    contourQValue S h4 hSI r.val r.property.1 (fun i => p0EllipsePoint m (u i)) ≤
      Real.exp (configExponent alpha m) := by
  rw [← literalConfigQWeight_mkTuple_eq hm8 h4 S hSI r u]
  have hhead : ∀ a ∈ (mkTupleConfiguration hm8 h4 S hSI r u).frequency,
      a ≤ 20 * (mkTupleConfiguration hm8 h4 S hSI r u).m := by
    intro a ha
    change a ∈ tupleSet r at ha
    rcases (mem_tupleSet r a).mp ha with ⟨i, rfl⟩
    exact (mem_cutoffTuples r).mp hr i
  rcases h _ hhead with hzero | ⟨hpos, hlog⟩
  · rw [hzero]
    exact (Real.exp_pos _).le
  · calc
      literalConfigQWeight (mkTupleConfiguration hm8 h4 S hSI r u) =
          Real.exp (Real.log
            (literalConfigQWeight (mkTupleConfiguration hm8 h4 S hSI r u))) :=
        (Real.exp_log hpos).symm
      _ ≤ Real.exp (configExponent alpha m) := Real.exp_le_exp.mpr hlog

/-! ## Contour arc density -/

/-- The scaled ellipse speed is at most `m A`, `A = 12783/10000`. -/
theorem norm_p0EllipseTangent_le (m : ℕ) (u : ℝ) :
    ‖p0EllipseTangent m u‖ ≤ (m : ℝ) * (12783 / 10000 : ℝ) := by
  unfold p0EllipseTangent
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (Nat.cast_nonneg m)]
  apply mul_le_mul_of_nonneg_left _ (Nat.cast_nonneg m)
  set w : ℂ := Complex.ofReal (-((12783 : ℝ) / 10000) * Real.sin u) +
      Complex.I * Complex.ofReal (((229 : ℝ) / 200) * Real.cos u) with hw
  have hre : w.re = -((12783 : ℝ) / 10000) * Real.sin u := by
    rw [hw, Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have him : w.im = ((229 : ℝ) / 200) * Real.cos u := by
    rw [hw, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re,
      Complex.I_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  have hsq : ‖w‖ ^ 2 ≤ ((12783 : ℝ) / 10000) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    have hs := Real.sin_sq_add_cos_sq u
    have hc2 : 0 ≤ Real.cos u ^ 2 := sq_nonneg _
    nlinarith
  exact le_of_pow_le_pow_left₀ two_ne_zero (by norm_num) hsq

theorem arcDensity_nonneg (m : ℕ) (u : ℝ) : 0 ≤ contourArcDensity m u := by
  unfold contourArcDensity
  positivity

theorem contourArcDensity_le (m : ℕ) (u : ℝ) :
    contourArcDensity m u ≤ (m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi) := by
  unfold contourArcDensity
  exact div_le_div_of_nonneg_right (norm_p0EllipseTangent_le m u) (by positivity)

/-! ## The finite cutoff envelope `E m (20m)` -/

/-- Number of retained frequency tuples, `binom(39m/2, m)`. -/
def headTupleCount (m : ℕ) : ℕ := (cutoffTuples (m / 2) m (20 * m)).card

/-- Pointwise bound of the summed literal integrand for one pinned set. -/
theorem finiteEnvelopeSum_le_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) (u : Fin (m - S.card) → ℝ) :
    ∑ r ∈ cutoffTuples (m / 2) m (20 * m), FrequencyLimit.envelopeTerm m h4 S hSI r u ≤
      (headTupleCount m : ℝ) * Real.exp (configExponent alpha m) *
        ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^ (m - S.card) := by
  have hdens : ∏ i : Fin (m - S.card), contourArcDensity m (u i) ≤
      ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^ (m - S.card) := by
    calc
      ∏ i : Fin (m - S.card), contourArcDensity m (u i) ≤
          ∏ _i : Fin (m - S.card), (m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi) :=
        Finset.prod_le_prod₀ (fun i _ => arcDensity_nonneg m (u i))
          (fun i _ => contourArcDensity_le m (u i))
      _ = _ := by simp [div_pow]
  have hterm : ∀ r ∈ cutoffTuples (m / 2) m (20 * m),
      FrequencyLimit.envelopeTerm m h4 S hSI r u ≤
        Real.exp (configExponent alpha m) *
          ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^ (m - S.card) := by
    intro r hr
    unfold FrequencyLimit.envelopeTerm
    exact mul_le_mul (contourQValue_le_exp_of_head h hm8 h4 S hSI r hr u) hdens
      (Finset.prod_nonneg (fun i _ => arcDensity_nonneg m (u i)))
      (Real.exp_pos _).le
  calc
    ∑ r ∈ cutoffTuples (m / 2) m (20 * m), FrequencyLimit.envelopeTerm m h4 S hSI r u ≤
        ∑ _r ∈ cutoffTuples (m / 2) m (20 * m),
          Real.exp (configExponent alpha m) *
            ((m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi)) ^ (m - S.card) :=
      Finset.sum_le_sum hterm
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, headTupleCount]
      ring

/-- Real mass of the contour parameter product measure. -/
theorem productMeasure_real_univ (d : ℕ) :
    (ContourKit.productMeasure (d := d) contourParameterMeasure).real Set.univ =
      (2 * Real.pi) ^ d := by
  unfold ContourKit.productMeasure contourParameterMeasure
  rw [pi_real_mass_eq_pow, Fintype.card_fin]
  congr 1
  rw [Measure.real_def, Measure.restrict_apply_univ, Real.volume_Icc,
    ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
  ring

instance productMeasure_isFinite (d : ℕ) :
    IsFiniteMeasure (ContourKit.productMeasure (d := d) contourParameterMeasure) := by
  unfold ContourKit.productMeasure contourParameterMeasure
  infer_instance

/-- One pinned set contributes at most `N e^B (mA)^d / d! ≤ N e^B e^{mA}`. -/
theorem contourEContribution_le_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) :
    contourEContribution m (20 * m) h4 S hSI ≤
      (headTupleCount m : ℝ) * Real.exp (configExponent alpha m) *
        Real.exp ((m : ℝ) * (12783 / 10000 : ℝ)) := by
  rw [FrequencyLimit.contourEContribution_eq_cutoff]
  set d := m - S.card with hd
  set K : ℝ := (m : ℝ) * (12783 / 10000 : ℝ) / (2 * Real.pi) with hK
  set c : ℝ := (headTupleCount m : ℝ) * Real.exp (configExponent alpha m) with hc
  have hc0 : 0 ≤ c := by positivity
  have hint : (∫ u : Fin d → ℝ,
        ∑ r ∈ cutoffTuples (m / 2) m (20 * m), FrequencyLimit.envelopeTerm m h4 S hSI r u
        ∂(ContourKit.productMeasure contourParameterMeasure)) ≤
      (2 * Real.pi) ^ d * (c * K ^ d) := by
    calc
      _ ≤ ∫ _u : Fin d → ℝ, c * K ^ d
            ∂(ContourKit.productMeasure contourParameterMeasure) :=
        integral_mono (FrequencyLimit.integrable_finite_envelope m (20 * m)
            (by omega) h4 S hSI) (integrable_const _)
          (fun u => finiteEnvelopeSum_le_of_head h hm8 h4 S hSI u)
      _ = (2 * Real.pi) ^ d * (c * K ^ d) := by
        rw [integral_const, smul_eq_mul, productMeasure_real_univ]
  have hvol : (2 * Real.pi) ^ d * K ^ d = ((m : ℝ) * (12783 / 10000 : ℝ)) ^ d := by
    rw [← mul_pow, hK]
    congr 1
    field_simp
  have hexp := FrequencyHeadCount.factorial_normalized_volume_le_exp
    (m := m) (d := d) (A := (12783 / 10000 : ℝ)) (by norm_num)
  have hfac : 0 < (Nat.factorial d : ℝ) := by exact_mod_cast Nat.factorial_pos d
  calc
    (Nat.factorial d : ℝ)⁻¹ * (∫ u : Fin d → ℝ,
        ∑ r ∈ cutoffTuples (m / 2) m (20 * m), FrequencyLimit.envelopeTerm m h4 S hSI r u
        ∂(ContourKit.productMeasure contourParameterMeasure)) ≤
        (Nat.factorial d : ℝ)⁻¹ * ((2 * Real.pi) ^ d * (c * K ^ d)) :=
      mul_le_mul_of_nonneg_left hint (by positivity)
    _ = c * (((m : ℝ) * (12783 / 10000 : ℝ)) ^ d / (Nat.factorial d : ℝ)) := by
      rw [← hvol]
      field_simp
    _ ≤ c * Real.exp ((m : ℝ) * (12783 / 10000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hexp hc0

/-- The finite cutoff envelope at `H = 20m` (paper v13 ll. 709--713). -/
theorem E_twentyM_le_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m) :
    E m (20 * m) h4 ≤
      (2 : ℝ) ^ m * ((headTupleCount m : ℝ) * Real.exp (configExponent alpha m) *
        Real.exp ((m : ℝ) * (12783 / 10000 : ℝ))) := by
  classical
  unfold E
  have hcard : ((Iset m).powerset.card : ℝ) = (2 : ℝ) ^ m := by
    rw [Finset.card_powerset, Iset_card]
    push_cast
    ring
  calc
    (∑ S ∈ (Iset m).powerset,
        if hSI : S ⊆ Iset m then contourEContribution m (20 * m) h4 S hSI else 0) ≤
        ∑ _S ∈ (Iset m).powerset,
          (headTupleCount m : ℝ) * Real.exp (configExponent alpha m) *
            Real.exp ((m : ℝ) * (12783 / 10000 : ℝ)) := by
      apply Finset.sum_le_sum
      intro S hS
      have hSI : S ⊆ Iset m := Finset.mem_powerset.mp hS
      rw [dite_eq_left hSI]
      exact contourEContribution_le_of_head h hm8 h4 S hSI
    _ = _ := by
      rw [Finset.sum_const, nsmul_eq_mul, hcard]

/-! ## Counting: `2^m binom(39m/2, m) ≤ (39e)^m` -/

theorem headTupleCount_eq {m : ℕ} (h4 : 4 ∣ m) :
    headTupleCount m = Nat.choose (39 * m / 2) m := by
  unfold headTupleCount
  rw [cutoffTuples_card_eq_frequencyHead_choose,
    FrequencyHeadCount.frequencyHeadUniverse_card h4]

/-- `binom(N,m) ≤ N^m/m!` and `m^m/m! ≤ e^m` give the paper's entropy bound
`2^m binom(39m/2, m) ≤ exp(m (log 39 + 1))` (v13 l. 709). -/
theorem two_pow_mul_headTupleCount_le {m : ℕ} (h4 : 4 ∣ m) :
    (2 : ℝ) ^ m * (headTupleCount m : ℝ) ≤
      Real.exp ((m : ℝ) * (Real.log 39 + 1)) := by
  rw [headTupleCount_eq h4]
  have hN : ((39 * m / 2 : ℕ) : ℝ) = (39 / 2 : ℝ) * (m : ℝ) := by
    obtain ⟨k, rfl⟩ := h4
    have : 39 * (4 * k) / 2 = 78 * k := by omega
    rw [this]
    push_cast
    ring
  have hchoose : (Nat.choose (39 * m / 2) m : ℝ) ≤
      ((39 * m / 2 : ℕ) : ℝ) ^ m / (Nat.factorial m : ℝ) :=
    Nat.choose_le_pow_div m (39 * m / 2)
  have hfac : (m : ℝ) ^ m / (Nat.factorial m : ℝ) ≤ Real.exp (m : ℝ) :=
    Real.pow_div_factorial_le_exp (m : ℝ) (Nat.cast_nonneg m) m
  have h39 : (39 : ℝ) ^ m = Real.exp ((m : ℝ) * Real.log 39) := by
    rw [← Real.log_pow, Real.exp_log (by positivity)]
  calc
    (2 : ℝ) ^ m * (Nat.choose (39 * m / 2) m : ℝ) ≤
        (2 : ℝ) ^ m * (((39 * m / 2 : ℕ) : ℝ) ^ m / (Nat.factorial m : ℝ)) :=
      mul_le_mul_of_nonneg_left hchoose (by positivity)
    _ = (39 : ℝ) ^ m * ((m : ℝ) ^ m / (Nat.factorial m : ℝ)) := by
      rw [hN, mul_pow, show (2 : ℝ) ^ m * ((39 / 2 : ℝ) ^ m * (m : ℝ) ^ m /
          (Nat.factorial m : ℝ)) = ((2 : ℝ) * (39 / 2)) ^ m * ((m : ℝ) ^ m /
          (Nat.factorial m : ℝ)) by rw [mul_pow]; ring]
      norm_num
    _ ≤ (39 : ℝ) ^ m * Real.exp (m : ℝ) :=
      mul_le_mul_of_nonneg_left hfac (by positivity)
    _ = Real.exp ((m : ℝ) * (Real.log 39 + 1)) := by
      rw [h39, ← Real.exp_add]
      ring_nf

/-! ## The linear budget -/

theorem cStar_lt : cStar < (49979 / 1000 : ℝ) := by
  unfold cStar dPlus dMinus
  exact ConfigCstarNumeric.cstar_expression_lt_v10

/-- The complete exponent check: count, contour volume, tail factor and the
pointwise exponent fit inside `-alpha m^2 + 10 m log m + 56 m + 301`. -/
theorem exponent_budget (alpha : ℝ) (m : ℕ) :
    configExponent alpha m + (m : ℝ) * (Real.log 39 + 1) +
        (m : ℝ) * (12783 / 10000 : ℝ) + 1 / 3 ≤
      -alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log (m : ℝ) +
        56 * (m : ℝ) + 301 := by
  have hb := FrequencyHeadCount.paper_linear_budget_lt_56 cStar_lt
  have hm : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  unfold configExponent
  nlinarith

/-- `E m (20m)` with the full exponent. -/
theorem tail_mul_E_twentyM_le_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m) :
    FrequencyLimit.actualFrequencyTailFactor m * E m (20 * m) h4 ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log (m : ℝ) +
        56 * (m : ℝ) + 301) := by
  have hE := E_twentyM_le_of_head h hm8 h4
  have hcount := two_pow_mul_headTupleCount_le h4
  have hY : E m (20 * m) h4 ≤
      Real.exp (configExponent alpha m + (m : ℝ) * (Real.log 39 + 1) +
        (m : ℝ) * (12783 / 10000 : ℝ)) := by
    calc
      E m (20 * m) h4 ≤ (2 : ℝ) ^ m * ((headTupleCount m : ℝ) *
          Real.exp (configExponent alpha m) *
          Real.exp ((m : ℝ) * (12783 / 10000 : ℝ))) := hE
      _ = ((2 : ℝ) ^ m * (headTupleCount m : ℝ)) *
          (Real.exp (configExponent alpha m) *
            Real.exp ((m : ℝ) * (12783 / 10000 : ℝ))) := by ring
      _ ≤ Real.exp ((m : ℝ) * (Real.log 39 + 1)) *
          (Real.exp (configExponent alpha m) *
            Real.exp ((m : ℝ) * (12783 / 10000 : ℝ))) :=
        mul_le_mul_of_nonneg_right hcount (by positivity)
      _ = _ := by
        rw [← Real.exp_add, ← Real.exp_add]
        ring_nf
  have htail_nonneg : 0 ≤ FrequencyLimit.actualFrequencyTailFactor m := by
    unfold FrequencyLimit.actualFrequencyTailFactor
    positivity
  calc
    FrequencyLimit.actualFrequencyTailFactor m * E m (20 * m) h4 ≤
        FrequencyLimit.actualFrequencyTailFactor m *
          Real.exp (configExponent alpha m + (m : ℝ) * (Real.log 39 + 1) +
            (m : ℝ) * (12783 / 10000 : ℝ)) :=
      mul_le_mul_of_nonneg_left hY htail_nonneg
    _ ≤ Real.exp (configExponent alpha m + (m : ℝ) * (Real.log 39 + 1) +
            (m : ℝ) * (12783 / 10000 : ℝ) + 1 / 3) :=
      FrequencyLimit.actualFrequencyTailFactor_mul_exp_le m _
    _ ≤ _ := Real.exp_le_exp.mpr (exponent_budget alpha m)

/-- The literal full envelope obeys the target decay (tail factor included). -/
theorem EInfinity_le_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) {m : ℕ} (hm8 : 8 ≤ m) (h4 : 4 ∣ m) :
    FrequencyLimit.EInfinity m h4 ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 + 10 * (m : ℝ) * Real.log (m : ℝ) +
        56 * (m : ℝ) + 301) := by
  have hm : 0 < m := by omega
  obtain ⟨-, hle⟩ := FrequencyLimit.full_cutoffENN_actual_tail_factor m hm h4
  have hnn : 0 ≤ FrequencyLimit.actualFrequencyTailFactor m * E m (20 * m) h4 :=
    mul_nonneg (by unfold FrequencyLimit.actualFrequencyTailFactor; positivity)
      (FrequencyLimit.E_nonneg m (20 * m) h4)
  have hreal : FrequencyLimit.EInfinity m h4 ≤
      FrequencyLimit.actualFrequencyTailFactor m * E m (20 * m) h4 := by
    have hle' : FrequencyLimit.EInfinityENN m h4 ≤
        ENNReal.ofReal (FrequencyLimit.actualFrequencyTailFactor m * E m (20 * m) h4) :=
      hle
    have h' := ENNReal.toReal_mono ENNReal.ofReal_ne_top hle'
    rw [ENNReal.toReal_ofReal hnn] at h'
    unfold FrequencyLimit.EInfinity
    rw [← FrequencyLimit.EInfinityENN_eq_fullEnvelope m hm h4]
    exact h'
  exact hreal.trans (tail_mul_E_twentyM_le_of_head h hm8 h4)

/-- Every finite cutoff `E m H` is below the full envelope, hence obeys the
same decay.  This is the `weighted_decay_bound` field of
`P0WeightedCoefficientStepAt`, produced from the per-configuration input. -/
theorem E_le_EInfinity {m : ℕ} (hm : 0 < m) (h4 : 4 ∣ m) (H : ℕ)
    (hfin : FrequencyLimit.fullEnvelope m h4 ≠ ⊤) :
    E m H h4 ≤ FrequencyLimit.EInfinity m h4 := by
  have hle : FrequencyLimit.finiteEnvelope m H h4 ≤ FrequencyLimit.fullEnvelope m h4 := by
    rw [FrequencyLimit.fullEnvelope_eq_iSup_finiteEnvelope m hm h4]
    exact le_iSup (fun H => FrequencyLimit.finiteEnvelope m H h4) H
  have h' := ENNReal.toReal_mono hfin hle
  rw [FrequencyLimit.finiteEnvelope_eq_ofReal m H hm h4,
    ENNReal.toReal_ofReal (FrequencyLimit.E_nonneg m H h4)] at h'
  exact h'

theorem weighted_decay_bound_of_head {alpha : ℝ}
    (h : ConfigFinalBoundLiteralHead alpha) :
    ∀ (m H : ℕ) (_hm : 8 ≤ m) (h4 : 4 ∣ m), 20 * m ≤ H →
      weightedCoefficientMass m H h4 ≤
        Real.exp (-alpha * (m : ℝ) ^ 2 +
          10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301) := by
  intro m H hm8 h4 _
  have hm : 0 < m := by omega
  have hfin : FrequencyLimit.fullEnvelope m h4 ≠ ⊤ := by
    rw [← FrequencyLimit.EInfinityENN_eq_fullEnvelope m hm h4]
    exact (FrequencyLimit.full_cutoffENN_actual_tail_factor m hm h4).1
  rw [weightedCoefficientMass_eq_E]
  exact (E_le_EInfinity hm h4 H hfin).trans (EInfinity_le_of_head h hm8 h4)

end

end Li2Lean.P0.CoefficientAssembly
