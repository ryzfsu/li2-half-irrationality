/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.IntegerizationTables.Data

namespace Li2Lean
namespace IntegerizationTables

theorem rangeAll_iff_finAll (n : ℕ) (p : ℕ → Bool) :
    (List.range n).all p = true ↔ ∀ i : Fin n, p i.val = true := by
  rw [List.all_eq_true]
  constructor
  · intro h i
    exact h i.val (List.mem_range.mpr i.isLt)
  · intro h j hj
    exact h ⟨j, List.mem_range.mp hj⟩

theorem shapeChecks_eq_true_iff (C : PotentialCertificate) :
    C.shapeChecks = true ↔ C.tableShape := by
  constructor
  · intro h
    simp only [PotentialCertificate.shapeChecks, Bool.and_eq_true] at h
    rcases h with ⟨⟨hcore, hrows⟩, hcols⟩
    have hcore' := of_decide_eq_true hcore
    rcases hcore' with ⟨hlo, hrowLen, hcolLen, hpairs⟩
    have hrows' : ∀ i : Fin C.rows.length,
        (getRow C.rows i.val).cell < C.groups.length := by
      intro i
      have hi := (rangeAll_iff_finAll C.rows.length _).mp hrows i
      exact of_decide_eq_true hi
    have hcols' : ∀ j : Fin C.cols.length,
        (getCol C.cols j.val).cell < C.groups.length := by
      intro j
      have hj := (rangeAll_iff_finAll C.cols.length _).mp hcols j
      exact of_decide_eq_true hj
    exact ⟨hlo, hrowLen, hcolLen, hrows', hcols', hpairs⟩
  · rintro ⟨hlo, hrowLen, hcolLen, hrows, hcols, hpairs⟩
    have hrows' : (List.range C.rows.length).all
        (fun i => decide ((getRow C.rows i).cell < C.groups.length)) = true :=
      (rangeAll_iff_finAll C.rows.length _).mpr fun i => decide_eq_true_eq.mpr (hrows i)
    have hcols' : (List.range C.cols.length).all
        (fun j => decide ((getCol C.cols j).cell < C.groups.length)) = true :=
      (rangeAll_iff_finAll C.cols.length _).mpr fun j => decide_eq_true_eq.mpr (hcols j)
    simp [PotentialCertificate.shapeChecks, hlo, hrowLen, hcolLen, hpairs, hrows', hcols']

theorem pairChecks_eq_true_iff (C : PotentialCertificate) :
    C.pairChecks = true ↔ C.potentialPairsValid := by
  constructor
  · intro h
    simp only [PotentialCertificate.pairChecks] at h
    have hrows : ∀ i : Fin C.rows.length,
        (List.range C.cols.length).all (fun j =>
          decide (baseEntryBound (getRow C.rows i.val) (getCol C.cols j) ≤
            rowPot C i.val + colPot C j) &&
          (if (getRow C.rows i.val).cell = (getCol C.cols j).cell then
            decide (sameCellEntryBound (getRow C.rows i.val) (getCol C.cols j) ≤
              rowPot C i.val + colPot C j)
           else true)) = true := by
      exact (rangeAll_iff_finAll C.rows.length _).mp h
    intro i j
    have hpair := (rangeAll_iff_finAll C.cols.length _).mp (hrows i) j
    rw [Bool.and_eq_true] at hpair
    rcases hpair with ⟨hbase, hsame⟩
    refine ⟨of_decide_eq_true hbase, ?_⟩
    intro hcell
    rw [if_pos hcell] at hsame
    exact of_decide_eq_true hsame
  · intro h
    simp only [PotentialCertificate.pairChecks]
    apply (rangeAll_iff_finAll C.rows.length _).mpr
    intro i
    apply (rangeAll_iff_finAll C.cols.length _).mpr
    intro j
    have hp := h i j
    rcases hp with ⟨hbase, hsame⟩
    rw [Bool.and_eq_true_iff]
    constructor
    · exact decide_eq_true_eq.mpr hbase
    · by_cases hcell : (getRow C.rows i.val).cell = (getCol C.cols j.val).cell
      · rw [if_pos hcell]
        exact decide_eq_true_eq.mpr (hsame hcell)
      · rw [if_neg hcell]

theorem widthsCheck_eq_true_iff (C : PotentialCertificate) :
    C.widthsCheck = true ↔ C.widthsPartition := by
  simp [PotentialCertificate.widthsCheck, PotentialCertificate.widthsPartition,
    decide_eq_true_eq]

theorem objectiveCheck_eq_true_iff (C : PotentialCertificate) :
    C.objectiveCheck = true ↔ C.objectiveValid := by
  simp [PotentialCertificate.objectiveCheck, PotentialCertificate.objectiveValid,
    decide_eq_true_eq]

theorem checks_eq_true_iff (C : PotentialCertificate) :
    C.checks = true ↔ C.valid := by
  constructor
  · intro h
    simp only [PotentialCertificate.checks, Bool.and_eq_true] at h
    rcases h with ⟨⟨⟨hshape, hpair⟩, hwidth⟩, hobjective⟩
    exact ⟨(shapeChecks_eq_true_iff C).mp hshape,
      (widthsCheck_eq_true_iff C).mp hwidth,
      (pairChecks_eq_true_iff C).mp hpair,
      (objectiveCheck_eq_true_iff C).mp hobjective⟩
  · rintro ⟨hshape, hwidth, hpair, hobjective⟩
    simp only [PotentialCertificate.checks, Bool.and_eq_true]
    exact ⟨⟨⟨(shapeChecks_eq_true_iff C).mpr hshape,
        (pairChecks_eq_true_iff C).mpr hpair⟩,
      (widthsCheck_eq_true_iff C).mpr hwidth⟩,
      (objectiveCheck_eq_true_iff C).mpr hobjective⟩

theorem checker_sound (C : PotentialCertificate) (h : C.checks = true) : C.valid :=
  checks_eq_true_iff C |>.mp h

def PotentialCertificate.cellEntryBound (C : PotentialCertificate)
    (i : Fin C.rows.length) (j : Fin C.cols.length) : ℤ :=
  let r := getRow C.rows i.val
  let c := getCol C.cols j.val
  if r.cell = c.cell then sameCellEntryBound r c else baseEntryBound r c

theorem cellEntryBound_le_potential (C : PotentialCertificate)
    (hvalid : C.valid) (i : Fin C.rows.length) (j : Fin C.cols.length) :
    C.cellEntryBound i j ≤ rowPot C i.val + colPot C j.val := by
  rcases hvalid with ⟨_, _, hpairs, _⟩
  dsimp [PotentialCertificate.cellEntryBound]
  by_cases hcell : (getRow C.rows i.val).cell = (getCol C.cols j.val).cell
  · rw [if_pos hcell]
    exact (hpairs i j).2 hcell
  · rw [if_neg hcell]
    exact (hpairs i j).1

theorem potential_sum_bound {m n : ℕ} (C : PotentialCertificate)
    (hvalid : C.valid) (rows : Fin m → Fin C.rows.length)
    (cols : Fin n → Fin C.cols.length) (matching : Fin m ≃ Fin n) :
    (∑ i : Fin m,
      baseEntryBound (getRow C.rows (rows i).val)
        (getCol C.cols (cols (matching i)).val)) ≤
      (∑ i : Fin m, rowPot C (rows i).val) +
        (∑ j : Fin n, colPot C (cols j).val) := by
  rcases hvalid with ⟨_, _, hpairs, _⟩
  have hle : ∀ i : Fin m,
      baseEntryBound (getRow C.rows (rows i).val)
          (getCol C.cols (cols (matching i)).val) ≤
        rowPot C (rows i).val + colPot C (cols (matching i)).val := by
    intro i
    exact (hpairs (rows i) (cols (matching i))).1
  calc
    (∑ i : Fin m,
      baseEntryBound (getRow C.rows (rows i).val)
        (getCol C.cols (cols (matching i)).val)) ≤
      (∑ i : Fin m,
        (rowPot C (rows i).val + colPot C (cols (matching i)).val)) := by
          apply Finset.sum_le_sum
          intro i hi
          exact hle i
    _ = (∑ i : Fin m, rowPot C (rows i).val) +
        (∑ i : Fin m, colPot C (cols (matching i)).val) := by
          rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, rowPot C (rows i).val) +
        (∑ j : Fin n, colPot C (cols j).val) := by
          have hperm :
              (∑ i : Fin m, colPot C (cols (matching i)).val) =
                ∑ j : Fin n, colPot C (cols j).val :=
            Equiv.sum_comp matching (fun j => colPot C (cols j).val)
          rw [hperm]

theorem potential_sum_bound_of_le {m n : ℕ} (C : PotentialCertificate)
    (hvalid : C.valid) (rows : Fin m → Fin C.rows.length)
    (cols : Fin n → Fin C.cols.length) (matching : Fin m ≃ Fin n)
    (w : Fin m → Fin n → ℤ)
    (hw : ∀ i : Fin m,
      w i (matching i) ≤ C.cellEntryBound (rows i) (cols (matching i))) :
    (∑ i : Fin m, w i (matching i)) ≤
      (∑ i : Fin m, rowPot C (rows i).val) +
        (∑ j : Fin n, colPot C (cols j).val) := by
  have hle : ∀ i : Fin m,
      w i (matching i) ≤
        rowPot C (rows i).val + colPot C (cols (matching i)).val := by
    intro i
    exact (hw i).trans (cellEntryBound_le_potential C hvalid (rows i)
      (cols (matching i)))
  calc
    (∑ i : Fin m, w i (matching i)) ≤
        ∑ i : Fin m, (rowPot C (rows i).val + colPot C (cols (matching i)).val) := by
      apply Finset.sum_le_sum
      intro i hi
      exact hle i
    _ = (∑ i : Fin m, rowPot C (rows i).val) +
        (∑ i : Fin m, colPot C (cols (matching i)).val) := by
      rw [Finset.sum_add_distrib]
    _ = (∑ i : Fin m, rowPot C (rows i).val) +
        (∑ j : Fin n, colPot C (cols j).val) := by
      have hperm :
          (∑ i : Fin m, colPot C (cols (matching i)).val) =
            ∑ j : Fin n, colPot C (cols j).val :=
        Equiv.sum_comp matching (fun j => colPot C (cols j).val)
      rw [hperm]

end IntegerizationTables
end Li2Lean

#print axioms Li2Lean.IntegerizationTables.checks_eq_true_iff
#print axioms Li2Lean.IntegerizationTables.checker_sound
#print axioms Li2Lean.IntegerizationTables.cellEntryBound_le_potential
#print axioms Li2Lean.IntegerizationTables.potential_sum_bound
#print axioms Li2Lean.IntegerizationTables.potential_sum_bound_of_le
