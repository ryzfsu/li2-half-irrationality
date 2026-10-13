/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ReferenceSupportCaps
import Li2Lean.P0.ReferenceFiniteEnergyAssembly

namespace Li2Lean.P0

open L6Admissible

noncomputable section

/-- The actual finite-energy reference has finite L6 cross energy with every
admissible finite-energy competitor. The support-local positive-kernel caps
control all four cross terms without requiring compact support of the
competitor's frequency measure. -/
theorem p0L6CrossEnergy_actual_reference
    (M : P0AdmissibleMeasures) (hM : P0FiniteEnergyCondition M) :
    P0L6CrossEnergy M
      (p0ReferenceMeasures p0ReferenceFiniteEnergyData_literal) := by
  exact p0L6CrossEnergy_of_literal_reference_support_caps M hM
    p0ReferenceFiniteEnergyData_literal

#print axioms p0L6CrossEnergy_actual_reference

end
end Li2Lean.P0
