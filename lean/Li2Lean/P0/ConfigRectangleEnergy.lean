/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigRectangleTable
import Li2Lean.P0.ConfigQLogDecomposition

namespace Li2Lean.P0.ConfigRectangleBounds
open Li2Lean.P0.CA.Pinned Li2Lean.LogSegment
open Li2Lean.P0.ConfigSegment Li2Lean.P0.ConfigQLogSegments
open Li2Lean.P0.ConfigQLogDecomposition
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def diffRect (i j : ℕ) : QI :=
  QI.add (QI.sub (QI.sub (meshH ((i:ℤ)+1-j)) (meshH ((i:ℤ)-j)))
    (meshH ((i:ℤ)-(j:ℤ)))) (meshH ((i:ℤ)-(j+1)))

theorem diffRect_sound (s : ℝ) (i j : ℕ) :
    (diffRect i j).Contains (rectangleLogValue (referenceCellLeft s i)
      (referenceCellRight s i) (referenceCellLeft s j) (referenceCellRight s j)) := by
  unfold diffRect
  have h := QI.mem_add (QI.mem_sub (QI.mem_sub (meshH_sound ((i:ℤ)+1-j))
    (meshH_sound ((i:ℤ)-j))) (meshH_sound ((i:ℤ)-j))) (meshH_sound ((i:ℤ)-(j+1)))
  convert h using 1
  unfold rectangleLogValue referenceCellLeft referenceCellRight
  push_cast
  congr 2 <;> congr 1 <;> ring

def plusRect (i j : ℕ) : QI :=
  QI.add (QI.sub (QI.sub (meshH (26+(i:ℤ)+j)) (meshH (25+(i:ℤ)+j)))
    (meshH (25+(i:ℤ)+j))) (meshH (24+(i:ℤ)+j))

theorem plusRect_sound (i j : ℕ) :
    (plusRect i j).Contains (rectangleLogAddValue (referenceCellLeft (1/4) i)
      (referenceCellRight (1/4) i) (referenceCellLeft (1/2) j) (referenceCellRight (1/2) j)) := by
  unfold plusRect
  have h := QI.mem_add (QI.mem_sub (QI.mem_sub (meshH_sound (26+(i:ℤ)+j))
    (meshH_sound (25+(i:ℤ)+j))) (meshH_sound (25+(i:ℤ)+j))) (meshH_sound (24+(i:ℤ)+j))
  convert h using 1
  unfold rectangleLogAddValue referenceCellLeft referenceCellRight
  push_cast
  congr 2 <;> congr 1 <;> ring

def densityQ (u : List ℕ) (j : ℕ) : ℚ := 32 * (u.getD j 0 : ℚ) / 1000000000000

theorem densityQ_cast (u : List ℕ) (j : ℕ) :
    (densityQ u j : ℝ) = referenceDensity u j := by
  simp [densityQ, referenceDensity, ConfigData.referenceDenominator]

def energyI (m n : ℕ) (u v : List ℕ) (r : ℕ → ℕ → QI) : QI :=
  sumIdx m (fun i => sumIdx n (fun j => QI.smul (densityQ u i * densityQ v j) (r i j)))

theorem energyI_sound (m n : ℕ) (u v : List ℕ) (r : ℕ → ℕ → QI)
    (f : ℕ → ℕ → ℝ) (h : ∀ i < m, ∀ j < n, (r i j).Contains (f i j)) :
    (energyI m n u v r).Contains (∑ i ∈ Finset.range m, ∑ j ∈ Finset.range n,
      referenceDensity u i * referenceDensity v j * f i j) := by
  apply sumIdx_sound
  intro i hi
  apply sumIdx_sound
  intro j hj
  simpa only [Rat.cast_mul, densityQ_cast] using
    QI.mem_smul (densityQ u i * densityQ v j) (h i hi j hj)

def pinnedI : QI := energyI 32 32 ConfigData.pinnedMassUnits ConfigData.pinnedMassUnits diffRect
def frequencyI : QI := energyI 160 160 ConfigData.frequencyMassUnits ConfigData.frequencyMassUnits diffRect
def crossI : QI := energyI 32 160 ConfigData.pinnedMassUnits ConfigData.frequencyMassUnits plusRect

theorem pinnedI_sound : pinnedI.Contains pinnedSelfEnergy := by
  rw [pinnedSelfEnergy, pinnedSelfEnergy_eq_rectangleSum]
  exact energyI_sound _ _ _ _ _ _ (fun i _ j _ => diffRect_sound (1/4) i j)
theorem frequencyI_sound : frequencyI.Contains frequencySelfEnergy := by
  rw [frequencySelfEnergy, frequencySelfEnergy_eq_rectangleSum]
  exact energyI_sound _ _ _ _ _ _ (fun i _ j _ => diffRect_sound (1/2) i j)
theorem crossI_sound : crossI.Contains pinnedFrequencyCross := by
  rw [pinnedFrequencyCross, pinnedReflectedFrequencyEnergy_eq_rectangleSum]
  exact energyI_sound _ _ _ _ _ _ (fun i _ j _ => plusRect_sound i j)

end Li2Lean.P0.ConfigRectangleBounds
