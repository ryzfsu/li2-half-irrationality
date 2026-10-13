/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.Kit.L3WeightedPrime
import Li2Lean.Vendor.PNT.Consequences

open Filter
open Asymptotics
open Topology

namespace Li2Lean

/--
The `chebyshev_asymptotic` result from Alex Kontorovich's
PrimeNumberTheoremAnd repository at commit
`c39a751132c88b6e8080b74c74023fd95b3d8be0`, vendored under
`Li2Lean/Vendor/PNT` (Apache-2.0; see THIRD_PARTY_NOTICES.md), states `θ ~[atTop] id`;
converting asymptotic equivalence gives the exact Mathlib Chebyshev `hPNT`
contract used by the L3 layer.
-/
theorem hPNT_of_primeNumberTheoremAnd : hPNT := by
  change Tendsto (Chebyshev.theta / (fun x : ℝ => x)) atTop (𝓝 (1 : ℝ))
  have hθ : Chebyshev.theta ~[atTop] id := chebyshev_asymptotic
  have hdenom : ∀ᶠ x : ℝ in atTop, (fun y : ℝ => y) x ≠ 0 := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with x hx
    exact ne_of_gt hx
  have hlim := (isEquivalent_iff_tendsto_one hdenom).mp hθ
  exact hlim

/-- Apply the now-unconditional PNT input to the conditional L3 prime-sum layer. -/
theorem l3WeightedPrimeLimit_unconditional_of_hL3
    (hL3 : L3WeightedPrimeLimit) :
    ∀ P : PrimeAffineProfile,
      Tendsto (fun x : ℝ => weightedPrimeSum P x / x) atTop
        (𝓝 (∫ t : ℝ, P.eval t)) :=
  hL3 hPNT_of_primeNumberTheoremAnd

/-- The literal finite piecewise-affine prime-sum limit is unconditional. -/
theorem l3WeightedPrimeLimit_unconditional :
    ∀ P : PrimeAffineProfile,
      Tendsto (fun x : ℝ => weightedPrimeSum P x / x) atTop
        (𝓝 (∫ t : ℝ, P.eval t)) := by
  exact l3WeightedPrimeLimit_from_hPNT hPNT_of_primeNumberTheoremAnd

end Li2Lean
