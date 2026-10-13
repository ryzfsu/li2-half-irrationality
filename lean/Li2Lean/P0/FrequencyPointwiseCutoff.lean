/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyFiniteCutoff
import Li2Lean.P0.FrequencyRatio

open Finset

namespace Li2Lean.P0.FrequencyFinite

open Li2Lean.P0.FrequencyLeaf

noncomputable section

/-! The exact finite v10 frequency cutoff with the analytic ratio discharged.
The coordinate hypotheses are the two explicit bounds on the paper's scaled
ellipse, and the contour dimension is exactly `m - S.card`. -/

/-- The proved analytic estimate applied to the canonical largest-frequency
replacement on the actual finite tail family. -/
theorem canonicalReplacement_ratio {m M : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (S : Finset ℕ) (hSI : S ⊆ I_m m)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    ∀ R ∈ tailFamily m M,
      frequencyFactor m (m / 2) S R (m - S.card) Z ≤
        ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (largest R : ℝ) ^ 2) *
          weight (m / 2) (largest R)) *
          frequencyFactor m (m / 2) S (replacement m R) (m - S.card) Z := by
  intro R hR
  have hadm := ((mem_finiteFamily_iff _ _ _ _).mp (mem_sdiff.mp hR).1).1
  have hrmem := largest_mem R (tail_nonempty hm hR)
  have hr := tail_largest_gt hR
  have h := leastUnused_frequencyFactor_le hm hm4 S R hSI hadm (largest R)
    hrmem hr (fun u hu => le_largest R u hu) Z hZre hZnorm
  dsimp only at h
  simpa only [replacement,
    site_eq_leastUnused m R hadm (largest R) hrmem (show m / 2 + m < largest R by omega)]
    using h

/-- The exact finite `Z_M-Z_{20m} ≤ b_m Z_M` inequality of v10, Section
`sec:frequency`, with all replacement and ratio inputs proved. -/
theorem frequencyZ_tail_bound {m M : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hM : 20 * m ≤ M)
    (S : Finset ℕ) (hSI : S ⊆ I_m m)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    frequencyZ m M S (m - S.card) Z - frequencyZ m (20 * m) S (m - S.card) Z ≤
      FrequencyGenerating.tailCoefficient m * frequencyZ m M S (m - S.card) Z :=
  finiteFrequencyTail_of_ratio hm hM S (m - S.card) Z
    (canonicalReplacement_ratio hm hm4 S hSI Z hZre hZnorm)

/-- Pointwise finite-cutoff form of v10 `eq:frequency-cutoff`, for every
valid size, pinned subset, and contour configuration obeying the paper's
explicit ellipse bounds. No replacement, fiber, ratio, or scalar-tail
estimate remains as a hypothesis. -/
theorem frequencyZ_cutoff {m M : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hM : 20 * m ≤ M)
    (S : Finset ℕ) (hSI : S ⊆ I_m m)
    (Z : Fin (m - S.card) → ℂ)
    (hZre : ∀ z, -(m : ℝ) / 6 < (Z z).re)
    (hZnorm : ∀ z, ‖Z z‖ < 5 * (m : ℝ) / 2) :
    frequencyZ m M S (m - S.card) Z ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        frequencyZ m (20 * m) S (m - S.card) Z :=
  finiteFrequencyCutoff_of_ratio hm hM S (m - S.card) Z
    (canonicalReplacement_ratio hm hm4 S hSI Z hZre hZnorm)

end

end Li2Lean.P0.FrequencyFinite
