/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceQLogOutsideData
namespace Li2Lean.P0.ActualReferenceQLogOutsideCheck
open CA.Contour CA.Contour.QI
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000
theorem endpoint_128 : QI.sub_le (primitiveI (edgeQ 128)) (endpointLit.getD 128 ⟨0,0⟩) = true := by
  decide +kernel
end Li2Lean.P0.ActualReferenceQLogOutsideCheck
