/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Receipt.Data
import Li2Lean.P0.ConfigData

/-!
# Data identity: receipt pinned rows = `ConfigData.pinnedCells`

`Receipt.Data.pinnedRows` (CA-R, from `pinned_cells.csv`, SHA-256 `5d47648d…`)
and `ConfigData.pinnedCells` (the list for which CA-P proved every row) are the
same list of rational cells. Checked by the kernel.
-/

set_option maxRecDepth 100000

namespace Li2Lean.P0.CA.Wire

theorem pinnedRows_eq : Receipt.Data.pinnedRows = ConfigData.pinnedCells := by
  decide +kernel

end Li2Lean.P0.CA.Wire
