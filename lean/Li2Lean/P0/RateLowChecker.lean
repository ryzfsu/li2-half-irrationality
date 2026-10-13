/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateLowTail
import Li2Lean.P0.RateCellCore

/-!
# Certified low-ratio cells

On a certified cell (`RCell.ok`) with `hi ≤ 1/2`, the two v13 low assignment
bounds are exact affine forms in `(m, p)`: the residue counts are constant on
each of the five residue groups and the group widths are affine.  The check
`p0LowPieceOK` compares the chosen bound with a profile piece at the two
interval endpoints; soundness gives `W ≤ icpt·m + slope·p` for every actual
prime ratio strictly inside the interval.
-/

namespace Li2Lean.P0.Integerization

open Finset

/-- Indicator of a boolean. -/
def p0B2Z (b : Bool) : ℤ := if b then 1 else 0

/-- Sum of five affine forms. -/
def p0AffSum5 (f : Fin 5 → RAff) : RAff := f 0 + f 1 + f 2 + f 3 + f 4

theorem p0AffSum5_val (f : Fin 5 → RAff) (m p : ℚ) :
    (p0AffSum5 f).val m p = ∑ g : Fin 5, (f g).val m p := by
  simp [p0AffSum5, Fin.sum_univ_five]

namespace RCell

/-- Both-block row count of a residue in group `g`. -/
def lowRow (c : RCell) (g : Fin 5) : ℤ :=
  2 * ((c.B : ℤ) + p0B2Z (c.pattern g 1) - c.A - p0B2Z (c.pattern g 0))

/-- Column count of a residue in group `g`. -/
def lowCol (c : RCell) (g : Fin 5) : ℤ := c.C + p0B2Z (c.pattern g 2)

/-- Per-residue summand of the bound `m + S_U`. -/
def lowF1 (c : RCell) (g : Fin 5) : ℤ :=
  if c.pattern g 3 then min (c.lowRow g) (c.lowCol g) else 0

/-- Per-residue summand of the bound `3m - 2K_I - K_J + S_K`. -/
def lowF2 (c : RCell) (g : Fin 5) : ℤ :=
  if c.pattern g 3 then c.lowCol g else min (c.lowRow g) (c.lowCol g) - c.lowRow g

/-- The chosen low bound as an affine form. -/
def lowE (c : RCell) (k : Bool) : RAff :=
  ⟨1, 0⟩ + p0AffSum5 (fun g => RAff.smul (if k then c.lowF1 g else c.lowF2 g) (c.width g))

end RCell

/-- Finite certificate for one low-ratio profile piece `icpt + slope ρ`. -/
def p0LowPieceOK (c : RCell) (icpt slope : ℚ) (k : Bool) : Bool :=
  c.ok && decide (c.hi ≤ 1 / 2) && ((⟨icpt, slope⟩ : RAff) - c.lowE k).nonnegOn c.lo c.hi

section

variable {c : RCell} {m p : ℕ}

theorem p0Cell_resCnt (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (g : Fin 5) (v : ℕ)
    (hv1 : p0CutAct c m p g.castSucc ≤ v) (hv2 : v < p0CutAct c m p g.succ) :
    v < p ∧
    (p0ResCnt p (m / 4) v : ℤ) = c.A + p0B2Z (c.pattern g 0) ∧
    (p0ResCnt p (m / 4 + m) v : ℤ) = c.B + p0B2Z (c.pattern g 1) ∧
    (p0ResCnt p (2 * m) v : ℤ) = c.C + p0B2Z (c.pattern g 2) ∧
    (p0PrimeCarry p (m / 2) v = 0 ↔ c.pattern g 3 = true) := by
  have hvp : v < p := by
    have := p0Cell_cut_mono hc h4 hm hp hlo hhi (Fin.le_last g.succ)
    have h5 : p0CutAct c m p (Fin.last 5) = p := rfl
    omega
  obtain ⟨hA, hB, hC, hQ⟩ := p0Cell_floors hc h4 hm hlo hhi
  have bits := p0Cell_bits hc h4 hm hp hlo hhi g v hv1 hv2
  have b0 := bits 0
  have b1 := bits 1
  have b2 := bits 2
  have b3 := bits 3
  simp only [p0Thr, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons,
    Matrix.cons_val_two, Matrix.tail_cons, Matrix.cons_val_three] at b0 b1 b2 b3
  refine ⟨hvp, ?_, ?_, ?_, ?_⟩
  · rw [p0ResCnt_eq hp hvp, hA, ← b0]
    unfold p0B2Z
    by_cases h : v < m / 4 % p
    · simp [h]
    · simp [h]
  · rw [p0ResCnt_eq hp hvp, hB, ← b1]
    unfold p0B2Z
    by_cases h : v < (m / 4 + m) % p
    · simp [h]
    · simp [h]
  · rw [p0ResCnt_eq hp hvp, hC, ← b2]
    unfold p0B2Z
    by_cases h : v < 2 * m % p
    · simp [h]
    · simp [h]
  · rw [← b3]
    unfold p0PrimeCarry
    rw [Nat.mod_eq_of_lt hvp]
    constructor
    · intro h
      split at h
      · simp at h
      · simp only [decide_eq_true_eq]
        omega
    · intro h
      simp only [decide_eq_true_eq] at h
      rw [if_neg (by omega)]

/-- Soundness of a certified low piece. -/
theorem p0Low_cell_bound (icpt slope : ℚ) (k : Bool) (hok : p0LowPieceOK c icpt slope k = true)
    (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) :
    ((p0RateAssignMax p m : ℤ) : ℚ) ≤ icpt * m + slope * p := by
  simp only [p0LowPieceOK, Bool.and_eq_true] at hok
  obtain ⟨⟨hc, hhalf⟩, hpiece⟩ := hok
  have hhalf := of_decide_eq_true hhalf
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hpg : p ≤ m / 2 := by
    have h1 : (p : ℚ) < m / 2 := by nlinarith
    obtain ⟨t, rfl⟩ := h4
    have : (p : ℚ) < (2 * t : ℕ) := by push_cast at h1 ⊢; linarith
    have : p < 2 * t := by exact_mod_cast this
    omega
  -- the residue sums of both bounds as group sums
  have hsum : ∀ (F : ℤ → ℤ → Bool → ℤ) (Fc : Fin 5 → ℤ),
      (∀ g : Fin 5, Fc g = F (c.lowRow g) (c.lowCol g) (c.pattern g 3)) →
      (∑ v ∈ range p, F (p0RowRes p m v) (p0ColRes p m v) (decide (p0PrimeCarry p (m / 2) v = 0)) : ℚ) =
        (p0AffSum5 (fun g => RAff.smul (Fc g) (c.width g))).val m p := by
    intro F Fc hF
    have hg := p0Cell_group_sum hc h4 hm hp hlo hhi
      (fun v => F (p0RowRes p m v) (p0ColRes p m v) (decide (p0PrimeCarry p (m / 2) v = 0))) Fc
      (by
        intro g v hv1 hv2
        obtain ⟨hvp, e0, e1, e2, e3⟩ := p0Cell_resCnt hc h4 hm hp hlo hhi g v hv1 hv2
        rw [hF g]
        have hr : (p0RowRes p m v : ℤ) = c.lowRow g := by
          rw [p0RowRes_eq p m v hp hvp, e0, e1]; unfold RCell.lowRow; ring
        have hcl : (p0ColRes p m v : ℤ) = c.lowCol g := by
          rw [p0ColRes_eq, e2]; rfl
        have hk : decide (p0PrimeCarry p (m / 2) v = 0) = c.pattern g 3 := by
          rw [Bool.eq_iff_iff, decide_eq_true_iff, e3]
        rw [hr, hcl, hk])
    have hq := congrArg (fun z : ℤ => (z : ℚ)) hg
    simp only [Int.cast_sum] at hq
    rw [hq, p0AffSum5_val]
    apply Finset.sum_congr rfl
    intro g _
    rw [RAff.val_smul]
    have hw : ((((p0CutAct c m p g.succ : ℕ) : ℤ) - p0CutAct c m p g.castSucc : ℤ) : ℚ) =
        (c.width g).val m p := by
      unfold RCell.width
      rw [RAff.val_sub, ← p0Cell_cut_val hc h4 hm hp hlo hhi,
        ← p0Cell_cut_val hc h4 hm hp hlo hhi]
      push_cast; ring
    push_cast at hw ⊢
    rw [hw]; ring
  have hE : ((p0RateAssignMax p m : ℤ) : ℚ) ≤ (c.lowE k).val m p := by
    cases k
    · -- second bound
      have hb := p0RateAssignMax_le p m _ (fun σ => p0Low_assign_bound2 p m hp hpg σ)
      have hs := hsum (fun R C u => if u then (C : ℤ) else min R C - R) c.lowF2
        (fun g => by unfold RCell.lowF2; rfl)
      have hq : ((p0RateAssignMax p m : ℤ) : ℚ) ≤
          (m : ℚ) + (∑ v ∈ range p, (if decide (p0PrimeCarry p (m / 2) v = 0) then
            (p0ColRes p m v : ℤ) else min (p0RowRes p m v : ℤ) (p0ColRes p m v) - p0RowRes p m v : ℤ) : ℚ) := by
        have hrw : ∀ v ∈ range p,
            ((if p0PrimeCarry p (m / 2) v = 0 then (p0ColRes p m v : ℤ) else 0) -
              (if p0PrimeCarry p (m / 2) v = 1 then (p0RowRes p m v : ℤ) else 0) +
              (if p0PrimeCarry p (m / 2) v = 1 then
                (min (p0RowRes p m v) (p0ColRes p m v) : ℤ) else 0)) =
            (if decide (p0PrimeCarry p (m / 2) v = 0) then (p0ColRes p m v : ℤ)
              else min (p0RowRes p m v : ℤ) (p0ColRes p m v) - p0RowRes p m v) := by
          intro v _
          have hκ := p0PrimeCarry_le_one p (m / 2) v
          by_cases h0 : p0PrimeCarry p (m / 2) v = 0
          · simp [h0]
          · have h1 : p0PrimeCarry p (m / 2) v = 1 := by omega
            simp [h1]
            push_cast
            ring
        rw [Finset.sum_congr rfl hrw] at hb
        exact_mod_cast hb
      beta_reduce at hs
      have hgoal : (c.lowE false).val m p =
          (m : ℚ) + (p0AffSum5 (fun g => RAff.smul (c.lowF2 g) (c.width g))).val m p := by
        simp only [RCell.lowE, RAff.val_add, RAff.val_mk, Bool.false_eq_true, ↓reduceIte]
        ring
      rw [hgoal, ← hs]
      exact hq
    · have hb := p0RateAssignMax_le p m _ (fun σ => p0Low_assign_bound1 p m hp hpg σ)
      have hs := hsum (fun R C u => if u then min R C else 0) c.lowF1
        (fun g => by unfold RCell.lowF1; rfl)
      have hq : ((p0RateAssignMax p m : ℤ) : ℚ) ≤
          (m : ℚ) + (∑ v ∈ range p, (if decide (p0PrimeCarry p (m / 2) v = 0) then
            min (p0RowRes p m v : ℤ) (p0ColRes p m v) else 0 : ℤ) : ℚ) := by
        have hrw : ∀ v ∈ range p,
            (if p0PrimeCarry p (m / 2) v = 0 then
              (min (p0RowRes p m v) (p0ColRes p m v) : ℤ) else 0) =
            (if decide (p0PrimeCarry p (m / 2) v = 0) then
              min (p0RowRes p m v : ℤ) (p0ColRes p m v) else 0) := by
          intro v _
          by_cases h0 : p0PrimeCarry p (m / 2) v = 0 <;> simp [h0]
        rw [Finset.sum_congr rfl hrw] at hb
        exact_mod_cast hb
      beta_reduce at hs
      have hgoal : (c.lowE true).val m p =
          (m : ℚ) + (p0AffSum5 (fun g => RAff.smul (c.lowF1 g) (c.width g))).val m p := by
        simp only [RCell.lowE, RAff.val_add, RAff.val_mk, ↓reduceIte]
        ring
      rw [hgoal, ← hs]
      exact hq
  have hP := RAff.nonneg_of_nonnegOn _ hmQ hlo.le hhi.le hpiece
  rw [RAff.val_sub, RAff.val_mk] at hP
  linarith

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0Low_cell_bound
