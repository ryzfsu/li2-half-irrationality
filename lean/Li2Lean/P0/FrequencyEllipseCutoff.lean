/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyPointwiseCutoff
import Li2Lean.P0.FrequencyEllipse

open Finset

namespace Li2Lean.P0.FrequencyFinite

open Li2Lean.P0.FrequencyLeaf

noncomputable section

/-- The paper's `Z_M-Z_{20m} ≤ b_m Z_M` on the literal scaled ellipse.
All replacement, geometric, fiber, and tail estimates are discharged. -/
theorem frequencyZ_p0Ellipse_tail_bound {m M : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hM : 20 * m ≤ M)
    (S : Finset ℕ) (hSI : S ⊆ I_m m) (u : Fin (m - S.card) → ℝ) :
    frequencyZ m M S (m - S.card) (fun z => p0EllipsePoint m (u z)) -
        frequencyZ m (20 * m) S (m - S.card) (fun z => p0EllipsePoint m (u z)) ≤
      FrequencyGenerating.tailCoefficient m *
        frequencyZ m M S (m - S.card) (fun z => p0EllipsePoint m (u z)) :=
  frequencyZ_tail_bound hm hm4 hM S hSI (fun z => p0EllipsePoint m (u z))
    (fun z => p0EllipsePoint_re_lower hm (u z))
    (fun z => p0EllipsePoint_norm_upper hm (u z))

/-- The exact finite frequency cutoff of v10 on `mΓ`, using the actual
`p0EllipsePoint` from the frozen construction. The only hypotheses are the
paper's valid size, finite cutoff, and pinned-subset conditions. -/
theorem frequencyZ_p0Ellipse_cutoff {m M : ℕ}
    (hm : 0 < m) (hm4 : 4 ∣ m) (hM : 20 * m ≤ M)
    (S : Finset ℕ) (hSI : S ⊆ I_m m) (u : Fin (m - S.card) → ℝ) :
    frequencyZ m M S (m - S.card) (fun z => p0EllipsePoint m (u z)) ≤
      (1 + (3 / 160 : ℝ) * (1 / 2 : ℝ) ^ m) *
        frequencyZ m (20 * m) S (m - S.card) (fun z => p0EllipsePoint m (u z)) :=
  frequencyZ_cutoff hm hm4 hM S hSI (fun z => p0EllipsePoint m (u z))
    (fun z => p0EllipsePoint_re_lower hm (u z))
    (fun z => p0EllipsePoint_norm_upper hm (u z))

end

end Li2Lean.P0.FrequencyFinite
