/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.Factors
import Li2Lean.P0.SeedLiteral.Row00
import Li2Lean.P0.SeedLiteral.Row01
import Li2Lean.P0.SeedLiteral.Row02
import Li2Lean.P0.SeedLiteral.Row03
import Li2Lean.P0.SeedLiteral.Row04
import Li2Lean.P0.SeedLiteral.Row05
import Li2Lean.P0.SeedLiteral.Row06
import Li2Lean.P0.SeedLiteral.Row07
import Li2Lean.P0.SeedLiteral.Row08
import Li2Lean.P0.SeedLiteral.Row09
import Li2Lean.P0.SeedLiteral.Row10
import Li2Lean.P0.SeedLiteral.Row11
import Li2Lean.P0.SeedLiteral.Row12
import Li2Lean.P0.SeedLiteral.Row13
import Li2Lean.P0.SeedLiteral.Row14
import Li2Lean.P0.SeedLiteral.Row15
import Li2Lean.P0.SeedLiteral.Row16
import Li2Lean.P0.SeedLiteral.Row17
import Li2Lean.P0.SeedLiteral.Row18
import Li2Lean.P0.SeedLiteral.Row19
import Li2Lean.P0.SeedLiteral.Row20
import Li2Lean.P0.SeedLiteral.Row21
import Li2Lean.P0.SeedLiteral.Row22
import Li2Lean.P0.SeedLiteral.Row23
import Li2Lean.P0.SeedLiteral.Row24
import Li2Lean.P0.SeedLiteral.Row25
import Li2Lean.P0.SeedLiteral.Row26
import Li2Lean.P0.SeedLiteral.Row27
import Li2Lean.P0.SeedLiteral.Row28
import Li2Lean.P0.SeedLiteral.Row29
import Li2Lean.P0.SeedLiteral.Row30
import Li2Lean.P0.SeedLiteral.Row31
import Li2Lean.P0.SeedLiteral.Row32
import Li2Lean.P0.SeedLiteral.Row33
import Li2Lean.P0.SeedLiteral.Row34
import Li2Lean.P0.SeedLiteral.Row35
import Li2Lean.P0.SeedLiteral.Row36
import Li2Lean.P0.SeedLiteral.Row37
import Li2Lean.P0.SeedLiteral.Row38
import Li2Lean.P0.SeedLiteral.Row39
import Li2Lean.P0.SeedLiteral.Row40
import Li2Lean.P0.SeedLiteral.Row41
import Li2Lean.P0.SeedLiteral.Row42
import Li2Lean.P0.SeedLiteral.Row43
import Li2Lean.P0.SeedLiteral.Row44
import Li2Lean.P0.SeedLiteral.Row45
import Li2Lean.P0.SeedLiteral.Row46
import Li2Lean.P0.SeedLiteral.Row47
import Li2Lean.P0.SeedLiteral.Row48
import Li2Lean.P0.SeedLiteral.Row49
import Li2Lean.P0.SeedLiteral.Row50
import Li2Lean.P0.SeedLiteral.Row51
import Li2Lean.P0.SeedLiteral.Row52
import Li2Lean.P0.SeedLiteral.Row53
import Li2Lean.P0.SeedLiteral.Row54
import Li2Lean.P0.SeedLiteral.Row55
import Li2Lean.P0.SeedLiteral.Row56
import Li2Lean.P0.SeedLiteral.Row57
import Li2Lean.P0.SeedLiteral.Row58
import Li2Lean.P0.SeedLiteral.Row59
import Li2Lean.P0.SeedLiteral.Row60
import Li2Lean.P0.SeedLiteral.Row61
import Li2Lean.P0.SeedLiteral.Row62
import Li2Lean.P0.SeedLiteral.Row63

namespace Li2Lean.P0.SeedLiteral
set_option maxRecDepth 1000000

set_option maxHeartbeats 10000000 in
theorem p0_seed_lu : aMat = lMat * uMat := by
  funext i j
  fin_cases i
  · exact p0_row00 j
  · exact p0_row01 j
  · exact p0_row02 j
  · exact p0_row03 j
  · exact p0_row04 j
  · exact p0_row05 j
  · exact p0_row06 j
  · exact p0_row07 j
  · exact p0_row08 j
  · exact p0_row09 j
  · exact p0_row10 j
  · exact p0_row11 j
  · exact p0_row12 j
  · exact p0_row13 j
  · exact p0_row14 j
  · exact p0_row15 j
  · exact p0_row16 j
  · exact p0_row17 j
  · exact p0_row18 j
  · exact p0_row19 j
  · exact p0_row20 j
  · exact p0_row21 j
  · exact p0_row22 j
  · exact p0_row23 j
  · exact p0_row24 j
  · exact p0_row25 j
  · exact p0_row26 j
  · exact p0_row27 j
  · exact p0_row28 j
  · exact p0_row29 j
  · exact p0_row30 j
  · exact p0_row31 j
  · exact p0_row32 j
  · exact p0_row33 j
  · exact p0_row34 j
  · exact p0_row35 j
  · exact p0_row36 j
  · exact p0_row37 j
  · exact p0_row38 j
  · exact p0_row39 j
  · exact p0_row40 j
  · exact p0_row41 j
  · exact p0_row42 j
  · exact p0_row43 j
  · exact p0_row44 j
  · exact p0_row45 j
  · exact p0_row46 j
  · exact p0_row47 j
  · exact p0_row48 j
  · exact p0_row49 j
  · exact p0_row50 j
  · exact p0_row51 j
  · exact p0_row52 j
  · exact p0_row53 j
  · exact p0_row54 j
  · exact p0_row55 j
  · exact p0_row56 j
  · exact p0_row57 j
  · exact p0_row58 j
  · exact p0_row59 j
  · exact p0_row60 j
  · exact p0_row61 j
  · exact p0_row62 j
  · exact p0_row63 j

theorem lMat_lower : lMat.IsLowerTriangular := by
  decide

theorem uMat_upper : uMat.IsUpperTriangular := by
  decide

theorem lMat_det : lMat.det = 1 := by
  rw [Matrix.det_of_isLowerTriangular lMat lMat_lower]
  decide

theorem uMat_det : uMat.det = 30 := by
  rw [Matrix.det_of_isUpperTriangular uMat_upper]
  decide

theorem p0_G32_zero_mod83 : aMat.det = 30 := by
  rw [p0_seed_lu, Matrix.det_mul, lMat_det, uMat_det]
  norm_num

#print axioms p0_G32_zero_mod83
end Li2Lean.P0.SeedLiteral
