/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateHighChecker

/-! Certificate data for the eleven high-ratio cells: floors, threshold order,
the v13 row/column potentials re-indexed by (group, digit, block), and the
`p0A2HighProfile` line of the containing profile piece. -/

namespace Li2Lean.P0.Integerization

def p0HighCellData : List HCell := [
  { cell := { lo := ((1 : ℚ) / 2), hi := ((7 : ℚ) / 12), A := 0, B := 2, C := 3, Q := 0, perm := ![3, 1, 0, 2] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (0, 2, false, 1), (0, 2, true, 2), (1, 1, false, 0), (1, 1, true, 1), (1, 2, false, 0), (1, 2, true, 1), (2, 1, false, 1), (2, 1, true, 2), (3, 0, false, 0), (3, 0, true, 1), (3, 1, false, 0), (3, 1, true, 1), (4, 0, false, 0), (4, 0, true, 1), (4, 1, false, 0), (4, 1, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (0, 3, 0), (1, 0, 0), (1, 1, 0), (1, 2, 0), (1, 3, 0), (2, 0, -1), (2, 1, -1), (2, 2, -1), (2, 3, -1), (3, 0, 0), (3, 1, 0), (3, 2, 0), (3, 3, 0), (4, 0, 0), (4, 1, 0), (4, 2, 0)],
    icpt := (1 : ℚ), slope := (0 : ℚ) },
  { cell := { lo := ((7 : ℚ) / 12), hi := ((5 : ℚ) / 8), A := 0, B := 2, C := 3, Q := 0, perm := ![1, 3, 2, 0] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (0, 2, false, 1), (0, 2, true, 2), (1, 1, false, 1), (1, 1, true, 2), (2, 1, false, 1), (2, 1, true, 2), (3, 1, false, 1), (3, 1, true, 2), (4, 0, false, 0), (4, 0, true, 1), (4, 1, false, 0), (4, 1, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (0, 3, 0), (1, 0, 0), (1, 1, 0), (1, 2, 0), (1, 3, 0), (2, 0, -1), (2, 1, -1), (2, 2, -1), (2, 3, -1), (3, 0, -1), (3, 1, -1), (3, 2, -1), (4, 0, 0), (4, 1, 0), (4, 2, 0)],
    icpt := ((-3 : ℚ) / 4), slope := (3 : ℚ) },
  { cell := { lo := ((5 : ℚ) / 8), hi := ((2 : ℚ) / 3), A := 0, B := 1, C := 3, Q := 0, perm := ![2, 3, 0, 1] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (1, 1, false, 1), (1, 1, true, 2), (2, 1, false, 1), (2, 1, true, 2), (3, 0, false, 0), (3, 0, true, 1), (3, 1, false, 0), (3, 1, true, 1), (4, 0, false, 1), (4, 0, true, 2)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (0, 3, 0), (1, 0, 0), (1, 1, 0), (1, 2, 0), (2, 0, -1), (2, 1, -1), (2, 2, -1), (3, 0, 0), (3, 1, 0), (3, 2, 0), (4, 0, -1), (4, 1, -1), (4, 2, -1)],
    icpt := ((1 : ℚ) / 2), slope := (1 : ℚ) },
  { cell := { lo := ((2 : ℚ) / 3), hi := ((3 : ℚ) / 4), A := 0, B := 1, C := 2, Q := 0, perm := ![3, 0, 1, 2] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (1, 1, false, 1), (1, 1, true, 2), (2, 0, false, 0), (2, 0, true, 1), (2, 1, false, 0), (2, 1, true, 1), (3, 0, false, 1), (3, 0, true, 2), (4, 0, false, 0), (4, 0, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (1, 0, -1), (1, 1, -1), (1, 2, -1), (2, 0, 0), (2, 1, 0), (2, 2, 0), (3, 0, -1), (3, 1, -1), (3, 2, -1), (4, 0, 0), (4, 1, 0)],
    icpt := ((-3 : ℚ) / 2), slope := (4 : ℚ) },
  { cell := { lo := ((3 : ℚ) / 4), hi := ((5 : ℚ) / 6), A := 0, B := 1, C := 2, Q := 0, perm := ![0, 3, 2, 1] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (1, 0, false, 0), (1, 0, true, 1), (1, 1, false, 0), (1, 1, true, 1), (2, 0, false, 0), (2, 0, true, 1), (2, 1, false, 0), (2, 1, true, 1), (3, 0, false, 0), (3, 0, true, 1), (3, 1, false, 0), (3, 1, true, 1), (4, 0, false, 0), (4, 0, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (1, 0, 1), (1, 1, 1), (1, 2, 1), (2, 0, 0), (2, 1, 0), (2, 2, 0), (3, 0, 0), (3, 1, 0), (4, 0, 0), (4, 1, 0)],
    icpt := ((-3 : ℚ) / 4), slope := (3 : ℚ) },
  { cell := { lo := ((5 : ℚ) / 6), hi := ((7 : ℚ) / 8), A := 0, B := 1, C := 2, Q := 0, perm := ![0, 2, 3, 1] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (1, 0, false, 0), (1, 0, true, 1), (1, 1, false, 0), (1, 1, true, 1), (2, 0, false, 0), (2, 0, true, 1), (2, 1, false, 0), (2, 1, true, 1), (3, 0, false, 0), (3, 0, true, 1), (3, 1, false, 0), (3, 1, true, 1), (4, 0, false, 0), (4, 0, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (1, 0, 1), (1, 1, 1), (1, 2, 1), (2, 0, 1), (2, 1, 1), (3, 0, 0), (3, 1, 0), (4, 0, 0), (4, 1, 0)],
    icpt := ((7 : ℚ) / 4), slope := (0 : ℚ) },
  { cell := { lo := ((7 : ℚ) / 8), hi := (1 : ℚ), A := 0, B := 1, C := 2, Q := 0, perm := ![2, 0, 1, 3] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (1, 1, false, 0), (1, 1, true, 1), (2, 0, false, 0), (2, 0, true, 1), (2, 1, false, 0), (2, 1, true, 1), (3, 0, false, 0), (3, 0, true, 1), (4, 0, false, 0), (4, 0, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (0, 2, 0), (1, 0, 1), (1, 1, 1), (2, 0, 1), (2, 1, 1), (3, 0, 0), (3, 1, 1), (4, 0, 0), (4, 1, 0)],
    icpt := ((7 : ℚ) / 4), slope := (0 : ℚ) },
  { cell := { lo := (1 : ℚ), hi := ((5 : ℚ) / 4), A := 0, B := 1, C := 1, Q := 0, perm := ![1, 0, 3, 2] },
    up := [(0, 1, false, 1), (0, 1, true, 2), (2, 0, false, 1), (2, 0, true, 1), (3, 0, false, 1), (3, 0, true, 1), (4, 0, false, 1), (4, 0, true, 1)],
    vp := [(0, 0, 0), (0, 1, 0), (1, 0, -1), (1, 1, 0), (2, 0, -1), (2, 1, 1), (3, 0, -1), (3, 1, 0), (4, 0, -1)],
    icpt := ((15 : ℚ) / 4), slope := (-2 : ℚ) },
  { cell := { lo := ((5 : ℚ) / 4), hi := ((7 : ℚ) / 4), A := 0, B := 0, C := 1, Q := 0, perm := ![0, 2, 3, 1] },
    up := [(1, 0, false, 0), (1, 0, true, 0), (2, 0, false, 0), (2, 0, true, 0), (3, 0, false, 0), (3, 0, true, 0)],
    vp := [(0, 0, 0), (0, 1, 1), (1, 0, 0), (1, 1, 2), (2, 0, 0), (3, 0, 0), (4, 0, 0)],
    icpt := ((15 : ℚ) / 4), slope := (-2 : ℚ) },
  { cell := { lo := ((7 : ℚ) / 4), hi := (2 : ℚ), A := 0, B := 0, C := 1, Q := 0, perm := ![2, 0, 1, 3] },
    up := [(2, 0, false, 0), (2, 0, true, 0)],
    vp := [(0, 0, 0), (0, 1, 1), (1, 0, 0), (2, 0, 0), (3, 0, 0), (4, 0, 0)],
    icpt := (2 : ℚ), slope := (-1 : ℚ) },
  { cell := { lo := (2 : ℚ), hi := ((5 : ℚ) / 2), A := 0, B := 0, C := 0, Q := 0, perm := ![0, 1, 3, 2] },
    up := [(1, 0, false, 0), (1, 0, true, 0)],
    vp := [(0, 0, 0), (1, 0, 0), (2, 0, 0), (3, 0, 0)],
    icpt := (0 : ℚ), slope := (0 : ℚ) }
]

/-- The eleven high cells are certified. -/
theorem p0HighData_ok : p0HighCellData.all HCell.ok = true := by
  decide +kernel

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0HighData_ok
