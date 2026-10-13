/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Kit.EndpointCriterion

namespace Li2Lean

/-- L1 endpoint contradiction theorem, frozen in LayerInterfaces. -/
theorem l1_endpoint_criterion : L1EndpointCriterion := by
  intro x certificate
  exact ContourKit.endpoint_criterion certificate

end Li2Lean
