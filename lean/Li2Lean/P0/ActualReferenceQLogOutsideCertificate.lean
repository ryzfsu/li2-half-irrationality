/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ActualReferenceQLogOutsideShard00
import Li2Lean.P0.ActualReferenceQLogOutsideShard01
import Li2Lean.P0.ActualReferenceQLogOutsideShard02
import Li2Lean.P0.ActualReferenceQLogOutsideShard03
import Li2Lean.P0.ActualReferenceQLogOutsideShard04
import Li2Lean.P0.ActualReferenceQLogOutsideShard05
import Li2Lean.P0.ActualReferenceQLogOutsideShard06
import Li2Lean.P0.ActualReferenceQLogOutsideShard07
import Li2Lean.P0.ActualReferenceQLogOutsideShard08

open scoped BigOperators
namespace Li2Lean.P0.ActualReferenceQLogOutsideCheck
open CA.Contour CA.Contour.QI
set_option maxRecDepth 100000
set_option maxHeartbeats 20000000

theorem endpoints_ok (j : ℕ) (hj : j < 129) :
    QI.sub_le (primitiveI (edgeQ j)) (endpointLit.getD j ⟨0,0⟩) = true := by
  interval_cases j
  · exact endpoint_000
  · exact endpoint_001
  · exact endpoint_002
  · exact endpoint_003
  · exact endpoint_004
  · exact endpoint_005
  · exact endpoint_006
  · exact endpoint_007
  · exact endpoint_008
  · exact endpoint_009
  · exact endpoint_010
  · exact endpoint_011
  · exact endpoint_012
  · exact endpoint_013
  · exact endpoint_014
  · exact endpoint_015
  · exact endpoint_016
  · exact endpoint_017
  · exact endpoint_018
  · exact endpoint_019
  · exact endpoint_020
  · exact endpoint_021
  · exact endpoint_022
  · exact endpoint_023
  · exact endpoint_024
  · exact endpoint_025
  · exact endpoint_026
  · exact endpoint_027
  · exact endpoint_028
  · exact endpoint_029
  · exact endpoint_030
  · exact endpoint_031
  · exact endpoint_032
  · exact endpoint_033
  · exact endpoint_034
  · exact endpoint_035
  · exact endpoint_036
  · exact endpoint_037
  · exact endpoint_038
  · exact endpoint_039
  · exact endpoint_040
  · exact endpoint_041
  · exact endpoint_042
  · exact endpoint_043
  · exact endpoint_044
  · exact endpoint_045
  · exact endpoint_046
  · exact endpoint_047
  · exact endpoint_048
  · exact endpoint_049
  · exact endpoint_050
  · exact endpoint_051
  · exact endpoint_052
  · exact endpoint_053
  · exact endpoint_054
  · exact endpoint_055
  · exact endpoint_056
  · exact endpoint_057
  · exact endpoint_058
  · exact endpoint_059
  · exact endpoint_060
  · exact endpoint_061
  · exact endpoint_062
  · exact endpoint_063
  · exact endpoint_064
  · exact endpoint_065
  · exact endpoint_066
  · exact endpoint_067
  · exact endpoint_068
  · exact endpoint_069
  · exact endpoint_070
  · exact endpoint_071
  · exact endpoint_072
  · exact endpoint_073
  · exact endpoint_074
  · exact endpoint_075
  · exact endpoint_076
  · exact endpoint_077
  · exact endpoint_078
  · exact endpoint_079
  · exact endpoint_080
  · exact endpoint_081
  · exact endpoint_082
  · exact endpoint_083
  · exact endpoint_084
  · exact endpoint_085
  · exact endpoint_086
  · exact endpoint_087
  · exact endpoint_088
  · exact endpoint_089
  · exact endpoint_090
  · exact endpoint_091
  · exact endpoint_092
  · exact endpoint_093
  · exact endpoint_094
  · exact endpoint_095
  · exact endpoint_096
  · exact endpoint_097
  · exact endpoint_098
  · exact endpoint_099
  · exact endpoint_100
  · exact endpoint_101
  · exact endpoint_102
  · exact endpoint_103
  · exact endpoint_104
  · exact endpoint_105
  · exact endpoint_106
  · exact endpoint_107
  · exact endpoint_108
  · exact endpoint_109
  · exact endpoint_110
  · exact endpoint_111
  · exact endpoint_112
  · exact endpoint_113
  · exact endpoint_114
  · exact endpoint_115
  · exact endpoint_116
  · exact endpoint_117
  · exact endpoint_118
  · exact endpoint_119
  · exact endpoint_120
  · exact endpoint_121
  · exact endpoint_122
  · exact endpoint_123
  · exact endpoint_124
  · exact endpoint_125
  · exact endpoint_126
  · exact endpoint_127
  · exact endpoint_128

def densityQ (j : ℕ) : ℚ := 32 * (ConfigData.frequencyMassUnits.getD j 0 : ℚ) / 1000000000000

theorem densityQ_zero (j : ℕ) (hlo : 128 ≤ j) (hhi : j < 160) : densityQ j = 0 := by
  interval_cases j <;> decide +kernel

theorem edgeQ_ge (j : ℕ) : (1/2:ℚ) ≤ edgeQ j := by
  unfold edgeQ
  have h : (0:ℚ) ≤ j := Nat.cast_nonneg j
  linarith

theorem endpointLit_mem (j : ℕ) (hj : j < 129) :
    (endpointLit.getD j ⟨0,0⟩).mem (primitive (edgeQ j)) :=
  mem_of_sub_le (endpoints_ok j hj) (primitiveI_mem (edgeQ_ge j))

noncomputable def frequencyContourEndpoint : ℝ :=
  ∑ j ∈ Finset.range 160, (densityQ j : ℝ) *
    (primitive (edgeQ (j+1)) - primitive (edgeQ j))

def frequencyContourEndpointI : QI := sumIdx 160 (fun j =>
  if densityQ j = 0 then pt 0 else rnd (smul (densityQ j)
    (sub (endpointLit.getD (j+1) ⟨0,0⟩) (endpointLit.getD j ⟨0,0⟩))))

theorem frequencyContourEndpointI_mem : frequencyContourEndpointI.mem frequencyContourEndpoint := by
  apply mem_sumIdx
  intro j hj
  by_cases hz : densityQ j = 0
  · simp only [hz, if_pos, Rat.cast_zero, zero_mul]
    simpa using mem_pt 0
  · have hj128 : j < 128 := by
      by_contra hn
      exact hz (densityQ_zero j (by omega) hj)
    simp only [hz, if_false]
    exact mem_rnd (mem_smul (densityQ j) (mem_sub
      (endpointLit_mem (j+1) (by omega)) (endpointLit_mem j (by omega))))

theorem frequencyContourEndpointI_lower_check :
    (350421/1000000:ℚ) ≤ frequencyContourEndpointI.lo := by decide +kernel

theorem frequencyContourEndpoint_lower :
    (350421/1000000:ℝ) ≤ frequencyContourEndpoint := by
  have h : ((350421/1000000:ℚ):ℝ) ≤ (frequencyContourEndpointI.lo:ℝ) :=
    Rat.cast_le.mpr frequencyContourEndpointI_lower_check
  exact (by norm_num at h ⊢; exact h.trans frequencyContourEndpointI_mem.1)

end Li2Lean.P0.ActualReferenceQLogOutsideCheck
#print axioms Li2Lean.P0.ActualReferenceQLogOutsideCheck.frequencyContourEndpoint_lower
