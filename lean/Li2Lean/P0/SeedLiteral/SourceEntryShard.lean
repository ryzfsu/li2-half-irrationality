/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.SeedLiteral.Factors

namespace Li2Lean.P0.SeedLiteral

set_option maxRecDepth 1000000

def choose83 (n k : Nat) : F83 := ((Nat.choose n k % 83 : Nat) : F83)

def sourceU (n : Nat) : F83 := (2 : F83) ^ n * choose83 (n + 16) 16

def sourceT (n : Nat) : F83 :=
  (Finset.range n).sum (fun r => sourceU (n - (r + 1)) / (r + 1 : F83)) +
  (2 : F83) ^ n * (Finset.range 16).sum (fun k =>
    (-1 : F83) ^ k * choose83 (n + 16) (15 - k) *
      ((2 : F83) ^ (k + 1) - 1) / (k + 1 : F83))

def sourceC (i j : Nat) : F83 :=
  if i = j then
    -sourceU i * (Finset.range 16).sum (fun r => 1 / (i + r + 1 : F83))
  else (sourceU i - sourceU j) / ((j : F83) - (i : F83))

def sourceBdiag (i : Nat) : F83 :=
  (Finset.range i).sum (fun r =>
    sourceU (i - (r + 1)) / ((r + 1 : F83) ^ 2)) -
  (2 : F83) ^ i * (Finset.range 15).sum (fun k =>
    (-1 : F83) ^ (k + 2) * choose83 (i + 16) (14 - k) /
      (k + 2 : F83) *
      (Finset.range (k + 1)).sum (fun h =>
        ((2 : F83) ^ (h + 1) - 1) / (h + 1 : F83)))

def sourceB (i j : Nat) : F83 :=
  if i = j then sourceBdiag i
  else (sourceT i - sourceT j) / ((j : F83) - (i : F83))

/-- The native 64-by-64 seed source entry, with top and bottom blocks. -/
def sourceEntry (r c : Nat) : F83 :=
  if r < 32 then sourceC (r + 8) c else sourceB (r - 32 + 8) c

set_option maxHeartbeats 5000000 in
/-- The first 8-by-8 source block agrees entrywise with the frozen seed data. -/
theorem source_block8 (i j : Fin 8) :
    sourceEntry i.val j.val = ((aTable[i.val]!)[j.val]! : F83) := by
  fin_cases i <;> fin_cases j
  all_goals norm_num [sourceEntry, sourceC, sourceU, choose83, Nat.choose, aTable]
  all_goals try rw [div_eq_mul_inv]
  all_goals first
    | (apply ZMod.val_injective 83; decide +kernel)
    | (left; apply ZMod.val_injective 83; decide +kernel)

set_option maxHeartbeats 5000000 in
theorem source_block8_eq_aMat (i j : Fin 8) :
    sourceEntry i.val j.val = aMat (⟨i.val, by omega⟩ : Fin 64)
      (⟨j.val, by omega⟩ : Fin 64) := by
  rw [source_block8]
  rfl

#print axioms source_block8
#print axioms source_block8_eq_aMat

end Li2Lean.P0.SeedLiteral
