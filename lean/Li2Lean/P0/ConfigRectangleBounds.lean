/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigRectangleRows

namespace Li2Lean.P0.ConfigRectangleBounds
open Li2Lean.P0.CA.Pinned Li2Lean.P0.ConfigQLogDecomposition
set_option maxRecDepth 100000
set_option maxHeartbeats 64000000

theorem pinned_check : QI.subset (rowsI 32 pinnedRows) ⟨-90874/100000, -90873/100000⟩ = true := by decide +kernel
theorem frequency_check : QI.subset (rowsI 160 frequencyRows) ⟨-54305/100000, -54304/100000⟩ = true := by decide +kernel
theorem cross_check : QI.subset (rowsI 32 crossRows) ⟨57429/100000, 57430/100000⟩ = true := by decide +kernel

theorem pinnedSelfEnergy_bounds : (-90874/100000 : ℝ) ≤ pinnedSelfEnergy ∧
    pinnedSelfEnergy ≤ (-90873/100000 : ℝ) := by
  have h := QI.mem_of_subset pinned_check pinnedRows_sound
  norm_num [QI.Contains] at h ⊢
  exact h

theorem frequencySelfEnergy_bounds : (-54305/100000 : ℝ) ≤ frequencySelfEnergy ∧
    frequencySelfEnergy ≤ (-54304/100000 : ℝ) := by
  have h := QI.mem_of_subset frequency_check frequencyRows_sound
  norm_num [QI.Contains] at h ⊢
  exact h

theorem pinnedFrequencyCross_bounds : (57429/100000 : ℝ) ≤ pinnedFrequencyCross ∧
    pinnedFrequencyCross ≤ (57430/100000 : ℝ) := by
  have h := QI.mem_of_subset cross_check crossRows_sound
  norm_num [QI.Contains] at h ⊢
  exact h
end Li2Lean.P0.ConfigRectangleBounds

#print axioms Li2Lean.P0.ConfigRectangleBounds.pinnedSelfEnergy_bounds
#print axioms Li2Lean.P0.ConfigRectangleBounds.frequencySelfEnergy_bounds
#print axioms Li2Lean.P0.ConfigRectangleBounds.pinnedFrequencyCross_bounds
