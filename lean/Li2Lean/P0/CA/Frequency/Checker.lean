/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.FixTerms
import Li2Lean.P0.CA.Frequency.ContourFix
import Li2Lean.Agents.F_L8.Types

/-!
# CA-F: the reflected frequency-row checker and its soundness

`rowCheck` is a Boolean over `ℚ`.  For a row `[lo, hi]` with `1/2 ≤ lo` it
bounds `Config.Wmu actualReference` from below on the whole closed row:

* `t log 2 ≥ lo * l2lo` and the constant uses `l2hi`;
* every merged term `c F(t + e)` is bounded by the exact hull of `F` on
  `[lo + e, hi + e]` (piecewise monotonicity of `F`, including the
  singular point `0` and the turning points `±1`);
* the contour term is bounded by monotonicity, `nu(t) ≤ nu(hi) ≤ nuHi hi`.

`rowCheck_sound` turns `rowCheck c = true` into the ORIGINAL row's
`modelRemainderValid` for the actual function; no allowance is used.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.LogSegment Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.ConfigContourReference Li2Lean.F_L8

/-- A data row in integer form: `lo = ln/ld`, `hi = hn/hd`, rational floor. -/
abbrev RowI := ℤ × ℕ × ℤ × ℕ × ℚ

/-- The receipt cell denoted by an integer row. -/
def RowI.toCell (r : RowI) : ReceiptCell :=
  ⟨(r.1 : ℚ) / r.2.1, (r.2.2.1 : ℚ) / r.2.2.2.1, r.2.2.2.2⟩

/-- The rational lower bound for `Wmu` on `[ln/ld, hn/hd]`: fixed-point term
sum plus the rational linear and contour parts. -/
def rowLowerI (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : ℚ :=
  ((termsLowM ln ld hn hd freqTermsI : ℤ) : ℚ) / twoE +
    (-1 / 2 - l2hi / 2 + (ln : ℚ) / ld * l2lo - nuHiF ((hn : ℚ) / hd))

/-- The reflected row check. -/
def rowCheckI (r : RowI) : Bool :=
  decide (0 < r.2.1) && decide (0 < r.2.2.2.1) && decide ((r.2.1 : ℤ) ≤ 2 * r.1) &&
    decide (r.2.2.2.2 ≤ rowLowerI r.1 r.2.1 r.2.2.1 r.2.2.2.1)

/-- Pointwise lower bound for the actual `Wmu` on a checked interval. -/
theorem rowLowerI_le {ln hn : ℤ} {ld hd : ℕ} (hld : 0 < ld) (hhd : 0 < hd)
    (h0 : (ld : ℤ) ≤ 2 * ln) {x : ℝ}
    (hlo : (ln : ℝ) / ld ≤ x) (hhi : x ≤ (hn : ℝ) / hd) :
    (rowLowerI ln ld hn hd : ℝ) ≤ Config.Wmu actualReference x := by
  have hldR : (0 : ℝ) < ld := by exact_mod_cast hld
  have hhdR : (0 : ℝ) < hd := by exact_mod_cast hhd
  have h0R : (1 / 2 : ℝ) ≤ (ln : ℝ) / ld := by
    rw [le_div_iff₀ hldR]
    have : (ld : ℝ) ≤ 2 * ln := by exact_mod_cast h0
    linarith
  have hhiR : (((hn : ℚ) / hd : ℚ) : ℝ) = (hn : ℝ) / hd := by
    simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast]
  have hhiQ : (1 / 2 : ℚ) ≤ (hn : ℚ) / hd := by
    have h1 : (((1 / 2 : ℚ)) : ℝ) ≤ (((hn : ℚ) / hd : ℚ) : ℝ) := by
      rw [hhiR]
      have : (((1 / 2 : ℚ)) : ℝ) = 1 / 2 := by norm_num
      rw [this]
      exact le_trans h0R (le_trans hlo hhi)
    exact Rat.cast_le.mp h1
  rw [actualWmu_eq_freqTerms]
  have hnu1 := contourNeg_monotoneOn (Set.mem_Ici.mpr (le_trans h0R hlo))
    (Set.mem_Ici.mpr (le_trans h0R (le_trans hlo hhi))) hhi
  have hnu2 := contourReferencePotential_neg_le_nuHiF hhiQ
  rw [hhiR] at hnu2
  have hterms := termsLowM_le hld hhd hlo hhi freqTermsI freqTermsI_pos
  rw [freqTermsI_toQ] at hterms
  have hl2a := l2lo_le
  have hl2b := le_l2hi
  have hl2pos : (0 : ℝ) ≤ l2lo := by norm_num [l2lo]
  have hlin : (ln : ℝ) / ld * l2lo ≤ x * Real.log 2 :=
    mul_le_mul hlo hl2a hl2pos (by linarith)
  simp only at hnu1
  unfold rowLowerI
  push_cast
  linarith

/-- Soundness of the reflected checker: the ORIGINAL row floor is a valid
zero-remainder model for the actual frequency first variation. -/
theorem row_valid_of_lower {ln hn : ℤ} {ld hd : ℕ} {low : ℚ} (hld : 0 < ld) (hhd : 0 < hd)
    (h0 : (ld : ℤ) ≤ 2 * ln) (hlow : low ≤ rowLowerI ln ld hn hd)
    (hw : (RowI.toCell (ln, ld, hn, hd, low)).lo ≤ (RowI.toCell (ln, ld, hn, hd, low)).hi) :
    (RowI.toCell (ln, ld, hn, hd, low)).modelRemainderValid (Config.Wmu actualReference) hw := by
  unfold ReceiptCell.modelRemainderValid ContourKit.TaylorLowerRemainderValid
  intro x hx
  simp only [ReceiptCell.model, ContourKit.QInterval.Contains, RowI.toCell] at hx
  obtain ⟨hxlo, hxhi⟩ := hx
  simp only [Rat.cast_div, Rat.cast_intCast, Rat.cast_natCast] at hxlo hxhi
  have hb := rowLowerI_le hld hhd h0 hxlo hxhi
  have hl : (low : ℝ) ≤ rowLowerI ln ld hn hd := by exact_mod_cast hlow
  simp [ReceiptCell.model, ContourKit.horner, RowI.toCell]
  linarith

theorem rowCheckI_sound {r : RowI} (h : rowCheckI r = true) (hw : r.toCell.lo ≤ r.toCell.hi) :
    r.toCell.modelRemainderValid (Config.Wmu actualReference) hw := by
  obtain ⟨ln, ld, hn, hd, low⟩ := r
  simp only [rowCheckI, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hld, hhd⟩, h0⟩, hlow⟩ := h
  exact row_valid_of_lower hld hhd h0 hlow hw

/-- List form of the soundness theorem (independent rows). -/
theorem rowsI_valid_of_check {rows : List RowI} (h : rows.all rowCheckI = true) :
    ∀ c ∈ rows.map RowI.toCell, ∀ hw : c.lo ≤ c.hi,
      c.modelRemainderValid (Config.Wmu actualReference) hw := by
  intro c hc hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  exact rowCheckI_sound (List.all_eq_true.mp h r hr) hw

/-! ## Chained check: each endpoint's logarithms are computed once -/

/-- The single bound (lower or upper by coefficient sign) of one term at `p/q`. -/
def endVal (p : ℤ) (q : ℕ) (t : TermI) : ℤ :=
  if 0 ≤ t.1 then pLoM (p * t.2.2.2 + t.2.2.1 * q) (q * t.2.2.2)
  else pHiM (p * t.2.2.2 + t.2.2.1 * q) (q * t.2.2.2)

def hullLoV (p1 : ℤ) (q1 : ℕ) (p2 : ℤ) (q2 : ℕ) (v1 v2 : ℤ) : ℤ :=
  if p1 < q1 ∧ (q2 : ℤ) < p2 then min (min v1 v2) (-(twoE : ℤ)) else min v1 v2

def hullHiV (p1 : ℤ) (q1 : ℕ) (p2 : ℤ) (q2 : ℕ) (v1 v2 : ℤ) : ℤ :=
  if p1 < -(q1 : ℤ) ∧ -(q2 : ℤ) < p2 then max (max v1 v2) twoE else max v1 v2

def termLowV (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) (t : TermI) (v1 v2 : ℤ) : ℤ :=
  if 0 ≤ t.1 then
    fdiv (t.1 * hullLoV (ln * t.2.2.2 + t.2.2.1 * ld) (ld * t.2.2.2)
      (hn * t.2.2.2 + t.2.2.1 * hd) (hd * t.2.2.2) v1 v2) t.2.1
  else
    fdiv (t.1 * hullHiV (ln * t.2.2.2 + t.2.2.1 * ld) (ld * t.2.2.2)
      (hn * t.2.2.2 + t.2.2.1 * hd) (hd * t.2.2.2) v1 v2) t.2.1

theorem termLowV_eq (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) (t : TermI) :
    termLowV ln ld hn hd t (endVal ln ld t) (endVal hn hd t) = termLowM ln ld hn hd t := by
  unfold termLowV endVal termLowM hullLoV hullHiV hullLoM hullHiM
  split_ifs <;> rfl

def termsLowV (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : List TermI → List ℤ → List ℤ → ℤ
  | t :: l, v1 :: w1, v2 :: w2 => termLowV ln ld hn hd t v1 v2 + termsLowV ln ld hn hd l w1 w2
  | _, _, _ => 0

theorem termsLowV_eq (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) (L : List TermI) :
    termsLowV ln ld hn hd L (L.map (endVal ln ld)) (L.map (endVal hn hd)) =
      termsLowM ln ld hn hd L := by
  induction L with
  | nil => rfl
  | cons t l ih => simp only [List.map_cons, termsLowV, termsLowM, ih, termLowV_eq]

def rowLowerV (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) (vl vh : List ℤ) : ℚ :=
  ((termsLowV ln ld hn hd freqTermsI vl vh : ℤ) : ℚ) / twoE +
    (-1 / 2 - l2hi / 2 + (ln : ℚ) / ld * l2lo - nuHiF ((hn : ℚ) / hd))

/-- Endpoint vector of term bounds at `p/q`. -/
def endVals (p : ℤ) (q : ℕ) : List ℤ := freqTermsI.map (endVal p q)

theorem rowLowerV_eq (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) :
    rowLowerV ln ld hn hd (endVals ln ld) (endVals hn hd) = rowLowerI ln ld hn hd := by
  unfold rowLowerV rowLowerI endVals
  rw [termsLowV_eq]

/-- Chained reflected check: rows must be adjacent (exact integer endpoints)
and each row is checked with the carried left-endpoint vector. -/
def chainCheck : List RowI → ℤ → ℕ → List ℤ → Bool
  | [], _, _, _ => true
  | r :: rs, ln, ld, vl =>
      (decide (r.1 = ln) && decide (r.2.1 = ld) && decide (0 < ld) &&
        decide (0 < r.2.2.2.1) && decide ((ld : ℤ) ≤ 2 * ln) &&
        decide (r.2.2.2.2 ≤ rowLowerV ln ld r.2.2.1 r.2.2.2.1 vl (endVals r.2.2.1 r.2.2.2.1))) &&
      chainCheck rs r.2.2.1 r.2.2.2.1 (endVals r.2.2.1 r.2.2.2.1)

/-- Shard entry point. -/
def shardCheck : List RowI → Bool
  | [] => true
  | r :: rs => chainCheck (r :: rs) r.1 r.2.1 (endVals r.1 r.2.1)

theorem chainCheck_sound : ∀ (rows : List RowI) (ln : ℤ) (ld : ℕ),
    chainCheck rows ln ld (endVals ln ld) = true →
    ∀ r ∈ rows, ∀ hw : r.toCell.lo ≤ r.toCell.hi,
      r.toCell.modelRemainderValid (Config.Wmu actualReference) hw
  | [], _, _, _ => by simp
  | r :: rs, ln, ld, h => by
      obtain ⟨rln, rld, rhn, rhd, rlow⟩ := r
      simp only [chainCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, hld⟩, hhd⟩, h0⟩, hlow⟩, hrest⟩ := h
      subst h1 h2
      intro r' hr' hw
      rcases List.mem_cons.mp hr' with rfl | hmem
      · rw [rowLowerV_eq] at hlow
        exact row_valid_of_lower hld hhd h0 hlow hw
      · exact chainCheck_sound rs rhn rhd hrest r' hmem hw

theorem shardCheck_sound {rows : List RowI} (h : shardCheck rows = true) :
    ∀ c ∈ rows.map RowI.toCell, ∀ hw : c.lo ≤ c.hi,
      c.modelRemainderValid (Config.Wmu actualReference) hw := by
  intro c hc hw
  obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hc
  cases rows with
  | nil => simp at hr
  | cons r0 rs => exact chainCheck_sound (r0 :: rs) r0.1 r0.2.1 h r hr hw

/-- Validity of every row of a cell list for the actual frequency function. -/
def CellsValid (l : List ReceiptCell) : Prop :=
  ∀ c ∈ l, ∀ hw : c.lo ≤ c.hi, c.modelRemainderValid (Config.Wmu actualReference) hw

theorem cellsValid_append {l1 l2 : List ReceiptCell} (h1 : CellsValid l1)
    (h2 : CellsValid l2) : CellsValid (l1 ++ l2) := by
  intro c hc hw
  rcases List.mem_append.mp hc with h | h
  · exact h1 c h hw
  · exact h2 c h hw

theorem shardCheck_valid {rows : List RowI} (h : shardCheck rows = true) :
    CellsValid (rows.map RowI.toCell) :=
  shardCheck_sound h

end Li2Lean.P0.CA.Frequency
