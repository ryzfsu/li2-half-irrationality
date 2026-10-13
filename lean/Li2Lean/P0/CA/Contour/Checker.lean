/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.Eval
import Li2Lean.P0.CA.Contour.Taylor
import Li2Lean.Kit.RationalTangent

/-!
# The reflected contour row checker and its soundness

A group carries one untrusted expansion hint `t` (the point
`θ₀ = 2 arctan t`, at which the actual field and its derivative are enclosed
once) and a list of receipt cells `⟨lo, hi, lower⟩` in units of `π`.
`checkGrp g = true` (a Boolean computation over `ℚ`) implies, for every cell
of the group and every `u ∈ [lo, hi]`,
`lower ≤ Weta actualReference (p0EllipsePoint 1 (π u))`: the receipt cell
satisfies `modelRemainderValid` with its ORIGINAL lower bound.
-/

namespace Li2Lean.P0.CA.Contour

open QI Li2Lean.F_L8

structure Cell where
  lo : ℚ
  hi : ℚ
  lower : ℚ
  deriving Repr, DecidableEq

def Cell.cell (c : Cell) : ReceiptCell := ⟨c.lo, c.hi, c.lower⟩

structure Grp where
  t : ℚ
  cells : List Cell
  deriving Repr

/-- Second-order lower bound on the cell from enclosures at `θ₀`. -/
def cellLower (W D T : QI) (c : Cell) : ℚ :=
  W.lo + (mul D ⟨PI.lo * c.lo - T.hi, PI.hi * c.hi - T.lo⟩).lo -
    1100 * max ((PI.lo * c.lo - T.hi) ^ 2) ((PI.hi * c.hi - T.lo) ^ 2)

def checkCell (W D T : QI) (c : Cell) : Bool :=
  decide (0 ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ 1 ∧ c.lower ≤ cellLower W D T c) &&
    (if c.lo = 0 then decide (c.lower ≤ (WI 1 0).lo) else true) &&
    (if c.hi = 1 then decide (c.lower ≤ (WI (-1) 0).lo) else true)

def allCells (W D T : QI) : List Cell → Bool
  | [] => true
  | c :: cs => checkCell W D T c && allCells W D T cs

def grpCheckAt (g : Grp) (wd : QI × QI) (T : QI) : Bool := allCells wd.1 wd.2 T g.cells

def checkGrp (g : Grp) : Bool :=
  decide (0 < g.t) &&
    grpCheckAt g (WDI (ContourKit.weierstrassCos g.t) (ContourKit.weierstrassSin g.t))
      (smul 2 (atanI g.t))

def allGrp : List Grp → Bool
  | [] => true
  | g :: gs => checkGrp g && allGrp gs

/-- The literal contour target function. -/
noncomputable def target (u : ℝ) : ℝ :=
  Config.Weta ConfigReferenceSymmetry.actualReference
    (Li2Lean.p0EllipsePoint 1 (Real.pi * u))

theorem target_eq (u : ℝ) : target u = Wform (Real.pi * u) := weta_ellipse_eq_Wform _

theorem sq_le_max_of_mem {x a b : ℝ} (ha : a ≤ x) (hb : x ≤ b) :
    x ^ 2 ≤ max (a ^ 2) (b ^ 2) := by
  rcases le_total 0 x with hx | hx
  · exact le_max_of_le_right (by nlinarith)
  · exact le_max_of_le_left (by nlinarith)

theorem checkCell_sound {W D T : QI} {θ0 : ℝ} (hθ0 : θ0 ∈ Set.Ioo 0 Real.pi)
    (hW : W.mem (Wform θ0)) (hD : D.mem (W1 θ0)) (hT : T.mem θ0)
    {c : Cell} (h : checkCell W D T c = true) {u : ℝ}
    (hlo : (c.lo : ℝ) ≤ u) (hhi : u ≤ (c.hi : ℝ)) : (c.lower : ℝ) ≤ target u := by
  simp only [checkCell, Bool.and_eq_true] at h
  obtain ⟨⟨hmain, hend0⟩, hend1⟩ := h
  obtain ⟨h0lo, hlohi, hhi1, hlow⟩ := of_decide_eq_true hmain
  have h0loR : (0 : ℝ) ≤ c.lo := by exact_mod_cast h0lo
  have hhi1R : (c.hi : ℝ) ≤ 1 := by exact_mod_cast hhi1
  rw [target_eq]
  rcases eq_or_lt_of_le (le_trans h0loR hlo) with hu0 | hu0
  · have hlo0 : c.lo = 0 := by
      have : (c.lo : ℝ) = 0 := le_antisymm (hu0 ▸ hlo) h0loR
      exact_mod_cast this
    rw [if_pos hlo0] at hend0
    have hb : (c.lower : ℝ) ≤ ((WI 1 0).lo : ℝ) := by exact_mod_cast of_decide_eq_true hend0
    have hm := WI_mem (θ := 0) (c := 1) (s := 0) (by simp) (by simp)
    rw [← hu0, mul_zero]
    exact hb.trans hm.1
  rcases eq_or_lt_of_le (le_trans hhi hhi1R) with hu1 | hu1
  · have hhi1' : c.hi = 1 := by
      have : (c.hi : ℝ) = 1 := le_antisymm hhi1R (hu1 ▸ hhi)
      exact_mod_cast this
    rw [if_pos hhi1'] at hend1
    have hb : (c.lower : ℝ) ≤ ((WI (-1) 0).lo : ℝ) := by exact_mod_cast of_decide_eq_true hend1
    have hm := WI_mem (θ := Real.pi) (c := -1) (s := 0) (by simp) (by simp)
    rw [hu1, mul_one]
    exact hb.trans hm.1
  set θ := Real.pi * u
  have hθ : θ ∈ Set.Ioo 0 Real.pi := ⟨mul_pos Real.pi_pos hu0, by
    have := mul_lt_mul_of_pos_left hu1 Real.pi_pos; simpa using this⟩
  have hTay := taylor_lower hθ hθ0
  have hpi := PI_mem
  have hd : (QI.mk (PI.lo * c.lo - T.hi) (PI.hi * c.hi - T.lo)).mem (θ - θ0) := by
    constructor
    · push_cast
      have : (PI.lo : ℝ) * c.lo ≤ Real.pi * u :=
        mul_le_mul hpi.1 hlo h0loR Real.pi_pos.le
      linarith [hT.2]
    · push_cast
      have h0u : (0 : ℝ) ≤ u := le_of_lt hu0
      have : Real.pi * u ≤ (PI.hi : ℝ) * c.hi :=
        mul_le_mul hpi.2 hhi h0u (le_trans Real.pi_pos.le hpi.2)
      linarith [hT.1]
  have hprod := mem_mul hD hd
  have hsq := sq_le_max_of_mem hd.1 hd.2
  have hlowR : (c.lower : ℝ) ≤ (cellLower W D T c : ℝ) := by exact_mod_cast hlow
  unfold cellLower at hlowR
  push_cast at hlowR hsq
  nlinarith [hW.1, hprod.1, hTay, hsq]

theorem allCells_mem {W D T : QI} {cs : List Cell} (h : allCells W D T cs = true) {c : Cell}
    (hc : c ∈ cs) : checkCell W D T c = true := by
  induction cs with
  | nil => simp at hc
  | cons a cs ih =>
      simp only [allCells, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hc with rfl | hc
      · exact h.1
      · exact ih h.2 hc

theorem checkGrp_sound {g : Grp} (h : checkGrp g = true) {c : Cell} (hc : c ∈ g.cells)
    {u : ℝ} (hlo : (c.lo : ℝ) ≤ u) (hhi : u ≤ (c.hi : ℝ)) : (c.lower : ℝ) ≤ target u := by
  simp only [checkGrp, Bool.and_eq_true] at h
  obtain ⟨ht, hcells⟩ := h
  have htR : (0 : ℝ) < g.t := by exact_mod_cast of_decide_eq_true ht
  set θ0 := 2 * Real.arctan (g.t : ℝ)
  have hθ0 : θ0 ∈ Set.Ioo 0 Real.pi := by
    have a1 : 0 < Real.arctan (g.t : ℝ) := by
      have := Real.arctan_strictMono htR; simpa using this
    have a2 := Real.arctan_lt_pi_div_two (g.t : ℝ)
    constructor <;> linarith
  have hc0 : Real.cos θ0 = (ContourKit.weierstrassCos g.t : ℝ) := ContourKit.cos_two_arctan_rat _
  have hs0 : Real.sin θ0 = (ContourKit.weierstrassSin g.t : ℝ) := ContourKit.sin_two_arctan_rat _
  have hT : (smul 2 (atanI g.t)).mem θ0 := by
    have := mem_smul 2 (atanI_mem g.t); simpa [θ0] using this
  unfold grpCheckAt at hcells
  rw [WDI_eq] at hcells
  exact checkCell_sound hθ0 (WI_mem hc0 hs0) (DI_mem hc0 hs0) hT
    (allCells_mem hcells hc) hlo hhi

theorem allGrp_mem {gs : List Grp} (h : allGrp gs = true) {g : Grp} (hg : g ∈ gs) :
    checkGrp g = true := by
  induction gs with
  | nil => simp at hg
  | cons a gs ih =>
      simp only [allGrp, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hg with rfl | hg
      · exact h.1
      · exact ih h.2 hg

/-- Soundness in the `ReceiptCell.modelRemainderValid` form, with the
original cell lower bound (no allowance subtracted). -/
theorem checkGrp_valid {g : Grp} (h : checkGrp g = true) {c : Cell} (hc : c ∈ g.cells)
    (hw : c.cell.lo ≤ c.cell.hi) : c.cell.modelRemainderValid target hw := by
  intro x hx
  have hx' : (c.lo : ℝ) ≤ x ∧ x ≤ (c.hi : ℝ) := hx
  have := checkGrp_sound h hc hx'.1 hx'.2
  simp only [ReceiptCell.model, _root_.ContourKit.horner, Cell.cell, Rat.cast_zero, neg_zero,
    mul_zero, add_zero]
  linarith

end Li2Lean.P0.CA.Contour
