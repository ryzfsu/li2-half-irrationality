/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Data
import Li2Lean.P0.CA.Frequency.Rows

/-!
# Data identity: receipt frequency rows = CA-F frequency rows

`Receipt.Data.frequencyRows` (CA-R) and `CA.Frequency.frequencyRows` (CA-F),
both generated from `frequency_cells.csv` (SHA-256 `d6295c9c…`), are the same
list of rational cells. Checked by the kernel.
-/

set_option maxRecDepth 100000

namespace Li2Lean.P0.CA.Wire

theorem frequencyRows_eq : Receipt.Data.frequencyRows = CA.Frequency.frequencyRows := by
  decide +kernel

end Li2Lean.P0.CA.Wire
