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
theorem endpoint_000 : QI.sub_le (primitiveI (edgeQ 0)) (endpointLit.getD 0 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_001 : QI.sub_le (primitiveI (edgeQ 1)) (endpointLit.getD 1 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_002 : QI.sub_le (primitiveI (edgeQ 2)) (endpointLit.getD 2 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_003 : QI.sub_le (primitiveI (edgeQ 3)) (endpointLit.getD 3 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_004 : QI.sub_le (primitiveI (edgeQ 4)) (endpointLit.getD 4 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_005 : QI.sub_le (primitiveI (edgeQ 5)) (endpointLit.getD 5 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_006 : QI.sub_le (primitiveI (edgeQ 6)) (endpointLit.getD 6 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_007 : QI.sub_le (primitiveI (edgeQ 7)) (endpointLit.getD 7 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_008 : QI.sub_le (primitiveI (edgeQ 8)) (endpointLit.getD 8 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_009 : QI.sub_le (primitiveI (edgeQ 9)) (endpointLit.getD 9 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_010 : QI.sub_le (primitiveI (edgeQ 10)) (endpointLit.getD 10 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_011 : QI.sub_le (primitiveI (edgeQ 11)) (endpointLit.getD 11 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_012 : QI.sub_le (primitiveI (edgeQ 12)) (endpointLit.getD 12 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_013 : QI.sub_le (primitiveI (edgeQ 13)) (endpointLit.getD 13 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_014 : QI.sub_le (primitiveI (edgeQ 14)) (endpointLit.getD 14 ⟨0,0⟩) = true := by
  decide +kernel
theorem endpoint_015 : QI.sub_le (primitiveI (edgeQ 15)) (endpointLit.getD 15 ⟨0,0⟩) = true := by
  decide +kernel
end Li2Lean.P0.ActualReferenceQLogOutsideCheck
