/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.P0.ConfigLogEnclosures
import Li2Lean.P0.DualL6Admissible

namespace Li2Lean

/-!
Paper-specific rational endpoint of the P0 dual certificate. The continuum
inequality and the C-A cell checks remain separate obligations.
-/

/-- The contour threshold `h_eta` in v10 `sec-dual.tex`, docs/6333 §5. -/
def p0DualEtaThreshold : ℚ := -(669 : ℚ) / 200

/-- The frequency threshold `h_mu` in v10 `sec-dual.tex`, docs/6333 §5. -/
def p0DualFrequencyThreshold : ℚ := 71 / 25

/-- The strict reference-energy lower bound from C-A, docs/6333 §5. -/
def p0DualQLogLower : ℚ := -(438334707 : ℚ) / 1000000000

/-- The pinned positive-part upper bound from C-A, docs/6333 §5. -/
def p0DualPinnedPenaltyUpper : ℚ :=
  6905963574153 / 81920000000000

/-- The full frequency positive-part upper bound from C-A and the tail proof. -/
def p0DualFrequencyPenaltyUpper : ℚ :=
  38158094390353 / 409600000000000

/-- Rational upper bound for `log 2` used in the final aggregation. -/
def p0DualLogTwoUpper : ℚ :=
  693147180560 / 1000000000000

/-- Lower endpoint obtained by substituting the v10 C-A bounds into (5.2). -/
def p0DualRationalLower : ℚ :=
  (9 / 2 : ℚ) - 2 * p0DualLogTwoUpper + p0DualQLogLower +
    p0DualEtaThreshold + p0DualFrequencyThreshold -
    p0DualPinnedPenaltyUpper - p0DualFrequencyPenaltyUpper

/-- Exact arithmetic check for the finite rational aggregation. -/
theorem p0DualRationalLower_exact :
    p0DualRationalLower = 81629602143693 / 40960000000000 := by
  norm_num [p0DualRationalLower, p0DualLogTwoUpper, p0DualQLogLower,
    p0DualEtaThreshold, p0DualFrequencyThreshold,
    p0DualPinnedPenaltyUpper, p0DualFrequencyPenaltyUpper]

/-- The rational endpoint exceeds the target `1992909/10^6` from (5.9). -/
theorem p0DualRationalLower_gt_target :
    (1992909 / 1000000 : ℚ) < p0DualRationalLower := by
  rw [p0DualRationalLower_exact]
  norm_num

/-- Parameterized form: every rational target at most `1992909/10^6`
(for instance the slack target `397/200`) lies below the dual endpoint. -/
theorem p0DualRationalLower_gt_of_le {alpha0 : ℚ}
    (h0 : alpha0 ≤ 1992909 / 1000000) :
    alpha0 < p0DualRationalLower :=
  lt_of_le_of_lt h0 p0DualRationalLower_gt_target

/--
Rational aggregation of the dual estimate (5.2) and the certified bounds
(5.7), stated against the exact rational endpoint `p0DualRationalLower`.
Its premises are the still-open analytic/certificate outputs; this lemma
proves only their rational aggregation, not those outputs.
-/
theorem p0DualRationalLower_lt_of_certificate
    {alpha qLog pinnedPenalty frequencyPenalty : ℝ}
    (hQLog : (p0DualQLogLower : ℝ) < qLog)
    (hPinned : pinnedPenalty ≤ (p0DualPinnedPenaltyUpper : ℝ))
    (hFrequency : frequencyPenalty ≤ (p0DualFrequencyPenaltyUpper : ℝ))
    (hDual : (9 / 2 : ℝ) - 2 * Real.log 2 + qLog +
      (p0DualEtaThreshold : ℝ) + (p0DualFrequencyThreshold : ℝ) -
      pinnedPenalty - frequencyPenalty ≤ alpha) :
    (p0DualRationalLower : ℝ) < alpha := by
  have hLogTwo : Real.log 2 ≤ (p0DualLogTwoUpper : ℝ) := by
    simpa [p0DualLogTwoUpper] using
      Li2Lean.P0.ConfigLogEnclosures.logTwo_tight_enclosure_v10.2
  have hLogTwo' : Real.log 2 ≤ (693147180560 : ℝ) / 1000000000000 := by
    simpa [p0DualLogTwoUpper] using hLogTwo
  have hQLog' : -(438334707 : ℝ) / 1000000000 < qLog := by
    simpa [p0DualQLogLower] using hQLog
  have hPinned' : pinnedPenalty ≤
      (6905963574153 : ℝ) / 81920000000000 := by
    simpa [p0DualPinnedPenaltyUpper] using hPinned
  have hFrequency' : frequencyPenalty ≤
      (38158094390353 : ℝ) / 409600000000000 := by
    simpa [p0DualFrequencyPenaltyUpper] using hFrequency
  have hDual' : (9 / 2 : ℝ) - 2 * Real.log 2 + qLog +
      (-(669 : ℝ) / 200) + (71 : ℝ) / 25 -
      pinnedPenalty - frequencyPenalty ≤ alpha := by
    simpa [p0DualEtaThreshold, p0DualFrequencyThreshold] using hDual
  rw [p0DualRationalLower_exact]
  push_cast
  calc
    (81629602143693 : ℝ) / 40960000000000 <
        (9 / 2 : ℝ) - 2 * Real.log 2 + qLog +
          (-(669 : ℝ) / 200) + (71 : ℝ) / 25 -
          pinnedPenalty - frequencyPenalty := by
      linarith [hLogTwo', hQLog', hPinned', hFrequency']
    _ ≤ alpha := hDual'

/--
Parameterized numerical implication of (5.2) and (5.7): any target `alpha0`
not exceeding the rational endpoint is strictly below `alpha`.
-/
theorem p0DualAlphaLowerFromCertificate_of_le
    {alpha0 alpha qLog pinnedPenalty frequencyPenalty : ℝ}
    (h0 : alpha0 ≤ (p0DualRationalLower : ℝ))
    (hQLog : (p0DualQLogLower : ℝ) < qLog)
    (hPinned : pinnedPenalty ≤ (p0DualPinnedPenaltyUpper : ℝ))
    (hFrequency : frequencyPenalty ≤ (p0DualFrequencyPenaltyUpper : ℝ))
    (hDual : (9 / 2 : ℝ) - 2 * Real.log 2 + qLog +
      (p0DualEtaThreshold : ℝ) + (p0DualFrequencyThreshold : ℝ) -
      pinnedPenalty - frequencyPenalty ≤ alpha) :
    alpha0 < alpha :=
  lt_of_le_of_lt h0
    (p0DualRationalLower_lt_of_certificate hQLog hPinned hFrequency hDual)

/--
Final numerical implication of the dual estimate (5.2) and the certified
bounds (5.7), at the paper target `1992909/10^6`. Its premises are the
still-open analytic/certificate outputs; this lemma proves only their
rational aggregation, not those outputs.
-/
theorem p0DualAlphaLowerFromCertificate
    {alpha qLog pinnedPenalty frequencyPenalty : ℝ}
    (hQLog : (p0DualQLogLower : ℝ) < qLog)
    (hPinned : pinnedPenalty ≤ (p0DualPinnedPenaltyUpper : ℝ))
    (hFrequency : frequencyPenalty ≤ (p0DualFrequencyPenaltyUpper : ℝ))
    (hDual : (9 / 2 : ℝ) - 2 * Real.log 2 + qLog +
      (p0DualEtaThreshold : ℝ) + (p0DualFrequencyThreshold : ℝ) -
      pinnedPenalty - frequencyPenalty ≤ alpha) :
    (1992909 / 1000000 : ℝ) < alpha := by
  have hTarget : (1992909 / 1000000 : ℝ) ≤ (p0DualRationalLower : ℝ) := by
    rw [p0DualRationalLower_exact]
    norm_num
  exact p0DualAlphaLowerFromCertificate_of_le hTarget hQLog hPinned
    hFrequency hDual

/-- A typed L8 dual certificate bounds `alphaGamma` below by every target
not exceeding the rational endpoint. -/
theorem p0DualCertificate_alpha_lower_of_le {F : P0Family} {alpha0 : ℝ}
    (h0 : alpha0 ≤ (p0DualRationalLower : ℝ))
    (certificate : P0DualCertificate F) :
    alpha0 < certificate.alphaGamma := by
  exact p0DualAlphaLowerFromCertificate_of_le h0
    (by simpa [p0DualQLogLower] using certificate.qLog_lower)
    (by simpa [p0DualPinnedPenaltyUpper] using certificate.pinnedPenalty_upper)
    (by simpa [p0DualFrequencyPenaltyUpper] using certificate.frequencyPenalty_upper)
    (by
      simpa [p0DualEtaThreshold, p0DualFrequencyThreshold] using
        certificate.duality_lower)

/-- A typed L8 dual certificate yields the advertised numerical alpha bound. -/
theorem p0DualCertificate_alpha_lower {F : P0Family}
    (certificate : P0DualCertificate F) :
    (1992909 / 1000000 : ℝ) < certificate.alphaGamma := by
  exact p0DualCertificate_alpha_lower_of_le
    (by rw [p0DualRationalLower_exact]; norm_num) certificate

/-- Parameterized form of the conditional L8 output. -/
theorem p0DualAlphaLowerFromOutput_of_le {F : P0Family} {alpha0 : ℝ}
    (h0 : alpha0 ≤ (p0DualRationalLower : ℝ))
    (hbase : F.a = 2) (houtput : L8P0DualCertificateOutput F) :
    ∃ certificate : P0DualCertificate F,
      alpha0 < certificate.alphaGamma := by
  rcases houtput hbase with ⟨certificate⟩
  exact ⟨certificate, p0DualCertificate_alpha_lower_of_le h0 certificate⟩

/-- The conditional L8 output exposes a certificate with the same bound. -/
theorem p0DualAlphaLowerFromOutput {F : P0Family}
    (hbase : F.a = 2) (houtput : L8P0DualCertificateOutput F) :
    ∃ certificate : P0DualCertificate F,
      (1992909 / 1000000 : ℝ) < certificate.alphaGamma := by
  rcases houtput hbase with ⟨certificate⟩
  exact ⟨certificate, p0DualCertificate_alpha_lower certificate⟩
open MeasureTheory

namespace P0

open L6Admissible

noncomputable section

/-! ### L6-backed first-variation fields

The fields below are the literal `sec-dual` first variations written on the
finite-energy admissible domain.  Their definitions keep the regularized
frequency term `-3 log (1+t)` in the energy identity rather than hiding it in
`Wmu`; this is the cancellation used by the L6 quadratic inequality.
-/

/-- Contour first-variation field `W_eta` for an admissible reference. -/
noncomputable def p0DualWeta (M₀ : P0AdmissibleMeasures) (z : ℂ) : ℝ :=
  p0CompanionField z - 2 * L6Variations.l6LogPotential M₀.eta z -
    L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z

/-- Frequency first-variation field `W_mu` after reflection to the real axis. -/
noncomputable def p0DualWmu (M₀ : P0AdmissibleMeasures) (t : ℝ) : ℝ :=
  B0 t - psi t -
    2 * L6Variations.l6LogPotential (p0FrequencyMeasure M₀) (-(t : ℂ)) -
    L6Variations.l6LogPotential M₀.eta (-(t : ℂ))

/-- The contour field is integrable whenever the self and cross energies are. -/
theorem p0DualWeta_integrable (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M)
    (hcross : L6Admissible.P0L6CrossEnergy M M₀) :
    Integrable (p0DualWeta M₀) M.eta := by
  have hη := L6Variations.integrable_potential hcross.eta_eta₀
  have hφ := L6Variations.integrable_potential hcross.eta_freq₀
  have hsum := hfin.2.1.add ((hη.const_mul (-2)).sub hφ)
  convert hsum using 1
  funext z
  simp [p0DualWeta]
  ring

/-- The frequency field is integrable on the original positive-real measure. -/
theorem p0DualWmu_integrable (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M)
    (hcross : L6Admissible.P0L6CrossEnergy M M₀) :
    Integrable (p0DualWmu M₀) M.mu := by
  have hφ := L6Variations.integrable_potential hcross.freq_freq₀
  have hη := L6Variations.integrable_potential
    (L6Variations.integrable_kernel_swap hcross.eta₀_freq)
  have hpot : Integrable
      (fun z : ℂ => -2 * L6Variations.l6LogPotential
        (p0FrequencyMeasure M₀) z -
        L6Variations.l6LogPotential M₀.eta z) (p0FrequencyMeasure M) :=
    (hφ.const_mul (-2)).sub hη
  have hpot' : Integrable
      (fun t : ℝ => -2 * L6Variations.l6LogPotential
        (p0FrequencyMeasure M₀) (-(t : ℂ)) -
        L6Variations.l6LogPotential M₀.eta (-(t : ℂ))) M.mu := by
    rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure]
    exact (integrable_map_measure hpot.aestronglyMeasurable
      L6Admissible.measurable_reflect.aemeasurable).mp hpot
  have hlog := L6Admissible.mu_log_moment M hfin
  have hbase : Integrable (fun t : ℝ => B0 t - psi t) M.mu := by
    have hreg := hfin.2.2.1
    have hthree := hlog.const_mul 3
    have hsum := hreg.add hthree
    convert hsum using 1
    funext t
    simp [p0RegularizedFrequencyField]
  have hsum := hbase.add hpot'
  convert hsum using 1
  funext t
  simp [p0DualWmu]
  ring

/-- The reflected frequency potential integral is exactly its real-axis form. -/
theorem p0Dual_frequency_potential_integral
    (M M₀ : P0AdmissibleMeasures)
    (hcross : L6Admissible.P0L6CrossEnergy M M₀) :
    (∫ z, (-2 * L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z -
      L6Variations.l6LogPotential M₀.eta z) ∂(p0FrequencyMeasure M)) =
      ∫ t, (-2 * L6Variations.l6LogPotential (p0FrequencyMeasure M₀)
        (-(t : ℂ)) - L6Variations.l6LogPotential M₀.eta (-(t : ℂ))) ∂M.mu := by
  have hφ := L6Variations.integrable_potential hcross.freq_freq₀
  have hη := L6Variations.integrable_potential
    (L6Variations.integrable_kernel_swap hcross.eta₀_freq)
  have hpot : Integrable
      (fun z : ℂ => -2 * L6Variations.l6LogPotential
        (p0FrequencyMeasure M₀) z - L6Variations.l6LogPotential M₀.eta z)
      (p0FrequencyMeasure M) := (hφ.const_mul (-2)).sub hη
  rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure]
  exact integral_map L6Admissible.measurable_reflect.aemeasurable
    hpot.aestronglyMeasurable

/-- L6 positivity plus the two literal `h_eta-P`, `h_mu-T` caps. -/
theorem p0Dual_regularizedEnergy_ge_of_caps
    (M M₀ : P0AdmissibleMeasures)
    (hfin : P0FiniteEnergyCondition M)
    (hfin₀ : P0FiniteEnergyCondition M₀)
    (hcross : L6Admissible.P0L6CrossEnergy M M₀)
    (hEta hMu P T : ℝ)
    (hEtaCap : hEta - P ≤ ∫ z, p0DualWeta M₀ z ∂M.eta)
    (hMuCap : hMu - T ≤ ∫ t, p0DualWmu M₀ t ∂M.mu) :
    (9 / 2 : ℝ) - 2 * ell +
        L6Variations.l6QLog M₀.eta (p0FrequencyMeasure M₀) +
        hEta + hMu - P - T ≤ p0RegularizedEnergyValue M := by
  have hquad := L6Admissible.p0_dualLower_regularizedQuadratic_ge
    M M₀ hfin hfin₀ hcross
  have hWeta := p0DualWeta_integrable M M₀ hfin hcross
  have hWmu := p0DualWmu_integrable M M₀ hfin hcross
  have hη := L6Variations.integrable_potential hcross.eta_eta₀
  have hφ := L6Variations.integrable_potential hcross.eta_freq₀
  have hWeta_expand :
      (∫ z, p0DualWeta M₀ z ∂M.eta) =
        (∫ z, p0CompanionField z ∂M.eta) +
        (∫ z, (-2 * L6Variations.l6LogPotential M₀.eta z -
          L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z) ∂M.eta) := by
    have hsum : Integrable
        (fun z => p0CompanionField z -
          2 * L6Variations.l6LogPotential M₀.eta z) M.eta :=
      hfin.2.1.sub (hη.const_mul 2)
    calc
      (∫ z, p0DualWeta M₀ z ∂M.eta) =
          ∫ z, (p0CompanionField z -
            2 * L6Variations.l6LogPotential M₀.eta z) -
            L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z ∂M.eta := by
              congr 1
      _ = (∫ z, p0CompanionField z ∂M.eta) +
          (∫ z, (-2 * L6Variations.l6LogPotential M₀.eta z -
            L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z) ∂M.eta) := by
            have hcomb :
                (∫ z, (-2 * L6Variations.l6LogPotential M₀.eta z -
                  L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z) ∂M.eta) =
                  -2 * (∫ z, L6Variations.l6LogPotential M₀.eta z ∂M.eta) -
                    ∫ z, L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z ∂M.eta := by
              calc
                _ = ∫ z, (-(2 * L6Variations.l6LogPotential M₀.eta z) -
                    L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z) ∂M.eta := by
                      congr 1
                      funext z
                      ring
                _ = (∫ z, -(2 * L6Variations.l6LogPotential M₀.eta z) ∂M.eta) -
                    ∫ z, L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z ∂M.eta := by
                      have hi := integral_sub (hη.const_mul 2).neg hφ
                      convert hi using 1 <;> simp <;> ring
                _ = _ := by
                      rw [integral_neg, integral_const_mul]
                      ring
            rw [integral_sub hsum hφ,
              integral_sub hfin.2.1 (hη.const_mul 2), integral_const_mul,
              hcomb]
            ring
  have hfreq := p0Dual_frequency_potential_integral M M₀ hcross
  have hpot' : Integrable
      (fun t : ℝ => -2 * L6Variations.l6LogPotential
        (p0FrequencyMeasure M₀) (-(t : ℂ)) -
        L6Variations.l6LogPotential M₀.eta (-(t : ℂ))) M.mu := by
    have hφ' := L6Variations.integrable_potential hcross.freq_freq₀
    have hη' := L6Variations.integrable_potential
      (L6Variations.integrable_kernel_swap hcross.eta₀_freq)
    have hpot0 : Integrable
        (fun z : ℂ => -2 * L6Variations.l6LogPotential
          (p0FrequencyMeasure M₀) z - L6Variations.l6LogPotential M₀.eta z)
        (p0FrequencyMeasure M) := (hφ'.const_mul (-2)).sub hη'
    rw [p0FrequencyMeasure, p0ReflectedFrequencyMeasure]
    exact (integrable_map_measure hpot0.aestronglyMeasurable
      L6Admissible.measurable_reflect.aemeasurable).mp hpot0
  have hlog := L6Admissible.mu_log_moment M hfin
  have hreg := hfin.2.2.1
  have hbase : Integrable (fun t : ℝ => B0 t - psi t) M.mu := by
    have hsum := hreg.add (hlog.const_mul 3)
    convert hsum using 1
    funext t
    simp [p0RegularizedFrequencyField]
  have hbase_sub_log :
      (∫ t, p0RegularizedFrequencyField t ∂M.mu) =
        (∫ t, B0 t - psi t ∂M.mu) -
          3 * (∫ t, Real.log (1 + t) ∂M.mu) := by
    have heq : (fun t : ℝ => p0RegularizedFrequencyField t) =
        (fun t => (B0 t - psi t) - 3 * Real.log (1 + t)) := by
      funext t
      simp [p0RegularizedFrequencyField]
    rw [heq, integral_sub hbase (hlog.const_mul 3), integral_const_mul]
  have hWmu_expand :
      (∫ t, p0DualWmu M₀ t ∂M.mu) =
        (∫ t, p0RegularizedFrequencyField t ∂M.mu) +
        (∫ z, (-2 * L6Variations.l6LogPotential (p0FrequencyMeasure M₀) z -
          L6Variations.l6LogPotential M₀.eta z) ∂(p0FrequencyMeasure M)) +
        3 * (∫ t, Real.log (1 + t) ∂M.mu) := by
    have hfun : (fun t : ℝ => p0DualWmu M₀ t) =
        (fun t => (B0 t - psi t) +
          (-2 * L6Variations.l6LogPotential (p0FrequencyMeasure M₀) (-(t : ℂ)) -
            L6Variations.l6LogPotential M₀.eta (-(t : ℂ)))) := by
      funext t
      simp [p0DualWmu]
      ring
    rw [hfun, integral_add hbase hpot', hbase_sub_log, hfreq]
    ring
  have henergy :
      (9 / 2 : ℝ) - 2 * ell +
        L6Variations.l6QLog M₀.eta (p0FrequencyMeasure M₀) +
        (∫ z, p0DualWeta M₀ z ∂M.eta) +
        (∫ t, p0DualWmu M₀ t ∂M.mu) ≤ p0RegularizedEnergyValue M := by
    rw [p0RegularizedEnergyValue]
    linarith [hquad, hWeta_expand, hWmu_expand]
  linarith [henergy, hEtaCap, hMuCap]

theorem p0DualExtendedInfimum_ge_of_finiteCases_local {X : Type*}
    (E : X → WithTop ℝ) (finite : X → Prop) [DecidablePred finite]
    (value : X → ℝ) (b : ℝ)
    (hNonempty : Nonempty X)
    (hE : ∀ x, E x = if finite x then (value x : WithTop ℝ) else ⊤)
    (hBound : ∀ x, finite x → b ≤ value x) :
    (b : WithTop ℝ) ≤ sInf (Set.range E) := by
  classical
  apply le_csInf
  · rcases hNonempty with ⟨x⟩
    exact ⟨E x, x, rfl⟩
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    rw [hE x]
    by_cases hx : finite x
    · rw [if_pos hx]
      exact_mod_cast hBound x hx
    · rw [if_neg hx]
      exact le_top

/-- Uniform literal caps imply the lower bound for the full extended infimum. -/
theorem p0AlphaGamma_ge_of_L6_caps
    (M₀ : P0AdmissibleMeasures)
    (hfin₀ : P0FiniteEnergyCondition M₀)
    (hEta hMu P T : ℝ)
    (hCaps : ∀ M : P0AdmissibleMeasures,
      P0FiniteEnergyCondition M →
      ∃ hcross : L6Admissible.P0L6CrossEnergy M M₀,
        hEta - P ≤ ∫ z, p0DualWeta M₀ z ∂M.eta ∧
        hMu - T ≤ ∫ t, p0DualWmu M₀ t ∂M.mu) :
    ((9 / 2 : ℝ) - 2 * ell +
      L6Variations.l6QLog M₀.eta (p0FrequencyMeasure M₀) +
      hEta + hMu - P - T : WithTop ℝ) ≤ alphaGamma := by
  classical
  have hEnergyCases : ∀ M : P0AdmissibleMeasures,
      p0ExtendedEnergy M =
        if P0FiniteEnergyCondition M then
          (p0RegularizedEnergyValue M : WithTop ℝ) else ⊤ := by
    intro M
    rfl
  have hInf := p0DualExtendedInfimum_ge_of_finiteCases_local
    p0ExtendedEnergy P0FiniteEnergyCondition p0RegularizedEnergyValue
    ((9 / 2 : ℝ) - 2 * ell +
      L6Variations.l6QLog M₀.eta (p0FrequencyMeasure M₀) +
      hEta + hMu - P - T)
    ⟨M₀⟩ hEnergyCases (by
      intro M hM
      obtain ⟨hcross, hEtaCap, hMuCap⟩ := hCaps M hM
      exact p0Dual_regularizedEnergy_ge_of_caps M M₀ hM hfin₀ hcross
        hEta hMu P T hEtaCap hMuCap)
  simpa [alphaGamma] using hInf

end

end P0

end Li2Lean
