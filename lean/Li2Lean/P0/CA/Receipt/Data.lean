/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Data.Contour00
import Li2Lean.P0.CA.Receipt.Data.Contour01
import Li2Lean.P0.CA.Receipt.Data.Pinned00
import Li2Lean.P0.CA.Receipt.Data.Pinned01
import Li2Lean.P0.CA.Receipt.Data.Pinned02
import Li2Lean.P0.CA.Receipt.Data.Pinned03
import Li2Lean.P0.CA.Receipt.Data.Frequency00
import Li2Lean.P0.CA.Receipt.Data.Frequency01
import Li2Lean.P0.CA.Receipt.Data.Frequency02
import Li2Lean.P0.CA.Receipt.Data.Frequency03
import Li2Lean.P0.CA.Receipt.Data.Frequency04
import Li2Lean.P0.CA.Receipt.Data.Frequency05
import Li2Lean.P0.CA.Receipt.Data.Frequency06
import Li2Lean.P0.CA.Receipt.Data.Frequency07

/-!
# The C-A 397/200 slack row tables

Concatenation of the generated shards (2511 contour, 8192 pinned, 16384
frequency rows) with their exact chains, exact spent-penalty masses, the
contour spent floor, and the frequency right-endpoint floor. Everything is
derived from the per-shard kernel checks.
-/

namespace Li2Lean.P0.CA.Receipt.Data

open Li2Lean.F_L8
open Li2Lean.P0.CA.Receipt

/-- All contour rows, in increasing order. -/
def contourRows : List ReceiptCell :=
  contourRows00 ++ contourRows01

theorem contourRows_length : contourRows.length = 2511 := by
  simp only [contourRows, List.length_append, contourRows00_length, contourRows01_length]

theorem contourRows_chain : ExactChain contourRows (0 : ℚ) (1 : ℚ) := by
  unfold contourRows
  exact (exactChain_append (List.ne_nil_of_length_pos (by rw [contourRows01_length]; norm_num))
    (chainCheck_sound contourRows00_chain)
    (chainCheck_sound contourRows01_chain))

/-- All pinned rows, in increasing order. -/
def pinnedRows : List ReceiptCell :=
  pinnedRows00 ++ pinnedRows01 ++ pinnedRows02 ++ pinnedRows03

theorem pinnedRows_length : pinnedRows.length = 8192 := by
  simp only [pinnedRows, List.length_append, pinnedRows00_length, pinnedRows01_length, pinnedRows02_length, pinnedRows03_length]

theorem pinnedRows_chain : ExactChain pinnedRows (1 / 4 : ℚ) (5 / 4 : ℚ) := by
  unfold pinnedRows
  exact (exactChain_append (List.ne_nil_of_length_pos (by rw [pinnedRows03_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [pinnedRows02_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [pinnedRows01_length]; norm_num))
    (chainCheck_sound pinnedRows00_chain)
    (chainCheck_sound pinnedRows01_chain))
    (chainCheck_sound pinnedRows02_chain))
    (chainCheck_sound pinnedRows03_chain))

/-- All frequency rows, in increasing order. -/
def frequencyRows : List ReceiptCell :=
  frequencyRows00 ++ frequencyRows01 ++ frequencyRows02 ++ frequencyRows03 ++ frequencyRows04 ++ frequencyRows05 ++ frequencyRows06 ++ frequencyRows07

theorem frequencyRows_length : frequencyRows.length = 16384 := by
  simp only [frequencyRows, List.length_append, frequencyRows00_length, frequencyRows01_length, frequencyRows02_length, frequencyRows03_length, frequencyRows04_length, frequencyRows05_length, frequencyRows06_length, frequencyRows07_length]

theorem frequencyRows_chain : ExactChain frequencyRows (1 / 2 : ℚ) (81 / 10 : ℚ) := by
  unfold frequencyRows
  exact (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows07_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows06_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows05_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows04_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows03_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows02_length]; norm_num))
    (exactChain_append (List.ne_nil_of_length_pos (by rw [frequencyRows01_length]; norm_num))
    (chainCheck_sound frequencyRows00_chain)
    (chainCheck_sound frequencyRows01_chain))
    (chainCheck_sound frequencyRows02_chain))
    (chainCheck_sound frequencyRows03_chain))
    (chainCheck_sound frequencyRows04_chain))
    (chainCheck_sound frequencyRows05_chain))
    (chainCheck_sound frequencyRows06_chain))
    (chainCheck_sound frequencyRows07_chain))

theorem contourRows_penalty :
    penaltyMass hEtaQ contourAllowance contourRows = 0 := by
  rw [contourRows, penaltyMass_append, contourRows00_penalty, contourRows01_penalty]
  norm_num [pinnedPenaltyQ, frequencyPenaltyQ]

theorem pinnedRows_penalty :
    penaltyMass hEtaQ realAllowance pinnedRows = pinnedPenaltyQ := by
  rw [pinnedRows, penaltyMass_append, penaltyMass_append, penaltyMass_append, pinnedRows00_penalty, pinnedRows01_penalty, pinnedRows02_penalty, pinnedRows03_penalty]
  norm_num [pinnedPenaltyQ, frequencyPenaltyQ]

theorem frequencyRows_penalty :
    penaltyMass hMuQ realAllowance frequencyRows = frequencyPenaltyQ := by
  rw [frequencyRows, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, penaltyMass_append, frequencyRows00_penalty, frequencyRows01_penalty, frequencyRows02_penalty, frequencyRows03_penalty, frequencyRows04_penalty, frequencyRows05_penalty, frequencyRows06_penalty, frequencyRows07_penalty]
  norm_num [pinnedPenaltyQ, frequencyPenaltyQ]

/-- Every spent contour row clears the contour threshold. -/
theorem contourRows_floor :
    ∀ c ∈ contourRows, hEtaQ + contourAllowance ≤ c.lower := by
  apply floorCheck_sound
  rw [contourRows, floorCheck_append, contourRows00_floor, contourRows01_floor]
  rfl

/-- Every frequency row reaching `81/10` clears the frequency threshold. -/
theorem frequencyRows_endpoint :
    ∀ c ∈ frequencyRows, (81 / 10 : ℚ) ≤ c.hi → hMuQ + realAllowance ≤ c.lower := by
  apply endpointCheck_sound
  rw [frequencyRows, endpointCheck_append, endpointCheck_append, endpointCheck_append, endpointCheck_append, endpointCheck_append, endpointCheck_append, endpointCheck_append, frequencyRows00_endpoint, frequencyRows01_endpoint, frequencyRows02_endpoint, frequencyRows03_endpoint, frequencyRows04_endpoint, frequencyRows05_endpoint, frequencyRows06_endpoint, frequencyRows07_endpoint]
  rfl

end Li2Lean.P0.CA.Receipt.Data
