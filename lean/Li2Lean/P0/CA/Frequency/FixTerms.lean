/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.FixArith
import Li2Lean.P0.CA.Frequency.Terms

/-!
# CA-F fixed-point bounds for `F` and for the merged term sum

Mantissa (`/ 2^60`) lower/upper bounds for `F(p/q) = (p/q)(log|p/q| - 1)`,
its exact hull on an interval (via `primitive_lower_hull` /
`primitive_upper_hull`), and the lower bound of `sum c_i F(t + e_i)` for an
integer-quadruple term table that is kernel-identified with `freqTerms`.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.LogSegment

/-- Floor division by a positive natural. -/
def fdiv (n : ℤ) (d : ℕ) : ℤ := n / (d : ℤ)

/-- Ceiling division by a positive natural. -/
def cdivI (n : ℤ) (d : ℕ) : ℤ := -((-n) / (d : ℤ))

theorem fdiv_le (n : ℤ) {d : ℕ} (hd : 0 < d) : ((fdiv n d : ℤ) : ℝ) ≤ (n : ℝ) / d := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast hd
  rw [le_div_iff₀ hdR]
  have h := Int.ediv_mul_le n (show (d : ℤ) ≠ 0 by exact_mod_cast hd.ne')
  have h' : ((n / (d : ℤ) * (d : ℤ) : ℤ) : ℝ) ≤ (n : ℝ) := by exact_mod_cast h
  push_cast at h'
  exact h'

theorem le_cdivI (n : ℤ) {d : ℕ} (hd : 0 < d) : (n : ℝ) / d ≤ ((cdivI n d : ℤ) : ℝ) := by
  have h := fdiv_le (-n) hd
  unfold fdiv at h
  unfold cdivI
  push_cast at h ⊢
  rw [neg_div] at h
  linarith

/-- Mantissa lower bound of `F(p/q)`. -/
def pLoM (p : ℤ) (q : ℕ) : ℤ :=
  if p = 0 then 0
  else if 0 < p then fdiv (p * ((logMant p.natAbs q).1 - twoE)) q
  else fdiv (p * ((logMant p.natAbs q).2 - twoE)) q

/-- Mantissa upper bound of `F(p/q)`. -/
def pHiM (p : ℤ) (q : ℕ) : ℤ :=
  if p = 0 then 0
  else if 0 < p then cdivI (p * ((logMant p.natAbs q).2 - twoE)) q
  else cdivI (p * ((logMant p.natAbs q).1 - twoE)) q

theorem natAbs_div_cast {p : ℤ} {q : ℕ} (hp : p ≠ 0) :
    Real.log (((p.natAbs : ℕ) : ℝ) / q) = Real.log |(p : ℝ) / q| := by
  rw [abs_div, Nat.abs_cast, Nat.cast_natAbs, Int.cast_abs]

theorem pLoM_le (p : ℤ) {q : ℕ} (hq : 0 < q) :
    ((pLoM p q : ℤ) : ℝ) / twoE ≤ primitive ((p : ℝ) / q) := by
  have hE := twoE_cast_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold pLoM
  split_ifs with h0 hpos
  · simp [h0]
  · have hpa : 0 < p.natAbs := Int.natAbs_pos.mpr h0
    obtain ⟨hb, _⟩ := logMant_sound hpa hq
    rw [natAbs_div_cast h0] at hb
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpos
    have hf := fdiv_le (p * ((logMant p.natAbs q).1 - twoE)) hq
    unfold primitive
    rw [div_le_iff₀ hE]
    push_cast at hf
    have hu : (0 : ℝ) < (p : ℝ) / q := div_pos hpR hqR
    have key : (p : ℝ) * (((logMant p.natAbs q).1 : ℝ) - twoE) / q =
        ((p : ℝ) / q) * (((logMant p.natAbs q).1 : ℝ) / twoE - 1) * twoE := by
      field_simp
    have hm : ((p : ℝ) / q) * (((logMant p.natAbs q).1 : ℝ) / twoE - 1) ≤
        ((p : ℝ) / q) * (Real.log |(p : ℝ) / q| - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hu.le
    nlinarith
  · have hneg : p < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
    have hpa : 0 < p.natAbs := Int.natAbs_pos.mpr h0
    obtain ⟨_, hb⟩ := logMant_sound hpa hq
    rw [natAbs_div_cast h0] at hb
    have hpR : (p : ℝ) < 0 := by exact_mod_cast hneg
    have hf := fdiv_le (p * ((logMant p.natAbs q).2 - twoE)) hq
    unfold primitive
    rw [div_le_iff₀ hE]
    push_cast at hf
    have hu : (p : ℝ) / q < 0 := div_neg_of_neg_of_pos hpR hqR
    have key : (p : ℝ) * (((logMant p.natAbs q).2 : ℝ) - twoE) / q =
        ((p : ℝ) / q) * (((logMant p.natAbs q).2 : ℝ) / twoE - 1) * twoE := by
      field_simp
    have hm : ((p : ℝ) / q) * (((logMant p.natAbs q).2 : ℝ) / twoE - 1) ≤
        ((p : ℝ) / q) * (Real.log |(p : ℝ) / q| - 1) :=
      mul_le_mul_of_nonpos_left (by linarith) hu.le
    nlinarith

theorem le_pHiM (p : ℤ) {q : ℕ} (hq : 0 < q) :
    primitive ((p : ℝ) / q) ≤ ((pHiM p q : ℤ) : ℝ) / twoE := by
  have hE := twoE_cast_pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  unfold pHiM
  split_ifs with h0 hpos
  · simp [h0]
  · have hpa : 0 < p.natAbs := Int.natAbs_pos.mpr h0
    obtain ⟨_, hb⟩ := logMant_sound hpa hq
    rw [natAbs_div_cast h0] at hb
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpos
    have hf := le_cdivI (p * ((logMant p.natAbs q).2 - twoE)) hq
    unfold primitive
    rw [le_div_iff₀ hE]
    push_cast at hf
    have hu : (0 : ℝ) < (p : ℝ) / q := div_pos hpR hqR
    have key : (p : ℝ) * (((logMant p.natAbs q).2 : ℝ) - twoE) / q =
        ((p : ℝ) / q) * (((logMant p.natAbs q).2 : ℝ) / twoE - 1) * twoE := by
      field_simp
    have hm : ((p : ℝ) / q) * (Real.log |(p : ℝ) / q| - 1) ≤
        ((p : ℝ) / q) * (((logMant p.natAbs q).2 : ℝ) / twoE - 1) :=
      mul_le_mul_of_nonneg_left (by linarith) hu.le
    nlinarith
  · have hneg : p < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
    have hpa : 0 < p.natAbs := Int.natAbs_pos.mpr h0
    obtain ⟨hb, _⟩ := logMant_sound hpa hq
    rw [natAbs_div_cast h0] at hb
    have hpR : (p : ℝ) < 0 := by exact_mod_cast hneg
    have hf := le_cdivI (p * ((logMant p.natAbs q).1 - twoE)) hq
    unfold primitive
    rw [le_div_iff₀ hE]
    push_cast at hf
    have hu : (p : ℝ) / q < 0 := div_neg_of_neg_of_pos hpR hqR
    have key : (p : ℝ) * (((logMant p.natAbs q).1 : ℝ) - twoE) / q =
        ((p : ℝ) / q) * (((logMant p.natAbs q).1 : ℝ) / twoE - 1) * twoE := by
      field_simp
    have hm : ((p : ℝ) / q) * (Real.log |(p : ℝ) / q| - 1) ≤
        ((p : ℝ) / q) * (((logMant p.natAbs q).1 : ℝ) / twoE - 1) :=
      mul_le_mul_of_nonpos_left (by linarith) hu.le
    nlinarith

/-- Mantissa lower hull of `F` on `[p1/q1, p2/q2]`. -/
def hullLoM (p1 : ℤ) (q1 : ℕ) (p2 : ℤ) (q2 : ℕ) : ℤ :=
  if p1 < q1 ∧ (q2 : ℤ) < p2 then min (min (pLoM p1 q1) (pLoM p2 q2)) (-(twoE : ℤ))
  else min (pLoM p1 q1) (pLoM p2 q2)

/-- Mantissa upper hull of `F` on `[p1/q1, p2/q2]`. -/
def hullHiM (p1 : ℤ) (q1 : ℕ) (p2 : ℤ) (q2 : ℕ) : ℤ :=
  if p1 < -(q1 : ℤ) ∧ -(q2 : ℤ) < p2 then max (max (pHiM p1 q1) (pHiM p2 q2)) twoE
  else max (pHiM p1 q1) (pHiM p2 q2)

theorem lt_one_iff_num {p : ℤ} {q : ℕ} (hq : 0 < q) : (p : ℝ) / q < 1 ↔ p < q := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_lt_one hqR]
  exact_mod_cast Iff.rfl

theorem hullLoM_le {p1 p2 : ℤ} {q1 q2 : ℕ} (hq1 : 0 < q1) (hq2 : 0 < q2) {u : ℝ}
    (hxu : (p1 : ℝ) / q1 ≤ u) (huy : u ≤ (p2 : ℝ) / q2) :
    ((hullLoM p1 q1 p2 q2 : ℤ) : ℝ) / twoE ≤ primitive u := by
  have hE := twoE_cast_pos
  have hm : ((min (pLoM p1 q1) (pLoM p2 q2) : ℤ) : ℝ) / twoE ≤
      min (primitive ((p1 : ℝ) / q1)) (primitive ((p2 : ℝ) / q2)) := by
    push_cast
    rw [← min_div_div_right hE.le]
    exact min_le_min (pLoM_le p1 hq1) (pLoM_le p2 hq2)
  unfold hullLoM
  rcases primitive_lower_hull hxu huy with h | ⟨hx, hy, h⟩
  · split_ifs
    · refine le_trans ?_ (le_trans hm h)
      apply div_le_div_of_nonneg_right _ hE.le
      exact_mod_cast min_le_left _ _
    · exact le_trans hm h
  · have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
    have hx' : p1 < q1 := (lt_one_iff_num hq1).mp hx
    have hy' : (q2 : ℤ) < p2 := by
      rw [lt_div_iff₀ hq2R, one_mul] at hy
      exact_mod_cast hy
    simp only [hx', hy', and_self, ↓reduceIte]
    refine le_trans ?_ h
    rw [div_le_iff₀ hE]
    have : ((min (min (pLoM p1 q1) (pLoM p2 q2)) (-(twoE : ℤ)) : ℤ) : ℝ) ≤ -(twoE : ℝ) := by
      exact_mod_cast min_le_right _ _
    linarith

theorem le_hullHiM {p1 p2 : ℤ} {q1 q2 : ℕ} (hq1 : 0 < q1) (hq2 : 0 < q2) {u : ℝ}
    (hxu : (p1 : ℝ) / q1 ≤ u) (huy : u ≤ (p2 : ℝ) / q2) :
    primitive u ≤ ((hullHiM p1 q1 p2 q2 : ℤ) : ℝ) / twoE := by
  have hE := twoE_cast_pos
  have hm : max (primitive ((p1 : ℝ) / q1)) (primitive ((p2 : ℝ) / q2)) ≤
      ((max (pHiM p1 q1) (pHiM p2 q2) : ℤ) : ℝ) / twoE := by
    push_cast
    rw [← max_div_div_right hE.le]
    exact max_le_max (le_pHiM p1 hq1) (le_pHiM p2 hq2)
  unfold hullHiM
  rcases primitive_upper_hull hxu huy with h | ⟨hx, hy, h⟩
  · split_ifs
    · refine le_trans (le_trans h hm) ?_
      apply div_le_div_of_nonneg_right _ hE.le
      exact_mod_cast le_max_left _ _
    · exact le_trans h hm
  · have hq1R : (0 : ℝ) < q1 := by exact_mod_cast hq1
    have hq2R : (0 : ℝ) < q2 := by exact_mod_cast hq2
    have hx' : p1 < -(q1 : ℤ) := by
      rw [div_lt_iff₀ hq1R] at hx
      have : (p1 : ℝ) < -(q1 : ℝ) := by linarith
      exact_mod_cast this
    have hy' : -(q2 : ℤ) < p2 := by
      rw [lt_div_iff₀ hq2R] at hy
      have : -(q2 : ℝ) < p2 := by linarith
      exact_mod_cast this
    simp only [hx', hy', and_self, ↓reduceIte]
    refine le_trans h ?_
    rw [le_div_iff₀ hE]
    have : (twoE : ℝ) ≤ ((max (max (pHiM p1 q1) (pHiM p2 q2)) (twoE : ℤ) : ℤ) : ℝ) := by
      exact_mod_cast le_max_right _ _
    linarith

/-- An integer term: coefficient `cn/cd`, shift `en/ed`. -/
abbrev TermI := ℤ × ℕ × ℤ × ℕ

def TermI.toQ (t : TermI) : ℚ × ℚ := ((t.1 : ℚ) / t.2.1, (t.2.2.1 : ℚ) / t.2.2.2)

/-- Mantissa lower bound of `c F(t + e)` on `[ln/ld, hn/hd]`. -/
def termLowM (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) (t : TermI) : ℤ :=
  if 0 ≤ t.1 then
    fdiv (t.1 * hullLoM (ln * t.2.2.2 + t.2.2.1 * ld) (ld * t.2.2.2)
      (hn * t.2.2.2 + t.2.2.1 * hd) (hd * t.2.2.2)) t.2.1
  else
    fdiv (t.1 * hullHiM (ln * t.2.2.2 + t.2.2.1 * ld) (ld * t.2.2.2)
      (hn * t.2.2.2 + t.2.2.1 * hd) (hd * t.2.2.2)) t.2.1

def termsLowM (ln : ℤ) (ld : ℕ) (hn : ℤ) (hd : ℕ) : List TermI → ℤ
  | [] => 0
  | t :: l => termLowM ln ld hn hd t + termsLowM ln ld hn hd l

def TermI.pos (t : TermI) : Bool := decide (0 < t.2.1) && decide (0 < t.2.2.2)

theorem termLowM_le {ln hn : ℤ} {ld hd : ℕ} (hld : 0 < ld) (hhd : 0 < hd) {x : ℝ}
    (hxl : (ln : ℝ) / ld ≤ x) (hxh : x ≤ (hn : ℝ) / hd) (t : TermI) (ht : t.pos = true) :
    ((termLowM ln ld hn hd t : ℤ) : ℝ) / twoE ≤
      ((t.toQ.1 : ℚ) : ℝ) * primitive (x + ((t.toQ.2 : ℚ) : ℝ)) := by
  obtain ⟨cn, cd, en, ed⟩ := t
  simp only [TermI.pos, Bool.and_eq_true, decide_eq_true_eq] at ht
  obtain ⟨hcd, hed⟩ := ht
  have hE := twoE_cast_pos
  have hcdR : (0 : ℝ) < cd := by exact_mod_cast hcd
  have hedR : (0 : ℝ) < ed := by exact_mod_cast hed
  have hldR : (0 : ℝ) < ld := by exact_mod_cast hld
  have hhdR : (0 : ℝ) < hd := by exact_mod_cast hhd
  have hq1 : 0 < ld * ed := Nat.mul_pos hld hed
  have hq2 : 0 < hd * ed := Nat.mul_pos hhd hed
  have e1 : ((ln * ed + en * ld : ℤ) : ℝ) / ((ld * ed : ℕ) : ℝ) = (ln : ℝ) / ld + (en : ℝ) / ed := by
    push_cast; field_simp
  have e2 : ((hn * ed + en * hd : ℤ) : ℝ) / ((hd * ed : ℕ) : ℝ) = (hn : ℝ) / hd + (en : ℝ) / ed := by
    push_cast; field_simp
  have hx1 : ((ln * ed + en * ld : ℤ) : ℝ) / ((ld * ed : ℕ) : ℝ) ≤ x + (en : ℝ) / ed := by
    rw [e1]; linarith
  have hx2 : x + (en : ℝ) / ed ≤ ((hn * ed + en * hd : ℤ) : ℝ) / ((hd * ed : ℕ) : ℝ) := by
    rw [e2]; linarith
  simp only [termLowM, TermI.toQ]
  push_cast
  split_ifs with hc
  · have hH := hullLoM_le hq1 hq2 hx1 hx2
    have hf := fdiv_le (cn * hullLoM (ln * ↑ed + en * ↑ld) (ld * ed) (hn * ↑ed + en * ↑hd)
      (hd * ed)) hcd
    have hcR : (0 : ℝ) ≤ cn := by exact_mod_cast hc
    push_cast at hf hH
    rw [div_le_iff₀ hE]
    have hm := mul_le_mul_of_nonneg_left hH (div_nonneg hcR hcdR.le)
    have : (cn : ℝ) / cd * (((hullLoM (ln * ↑ed + en * ↑ld) (ld * ed) (hn * ↑ed + en * ↑hd)
        (hd * ed) : ℤ) : ℝ) / twoE) * twoE =
        (cn : ℝ) * ((hullLoM (ln * ↑ed + en * ↑ld) (ld * ed) (hn * ↑ed + en * ↑hd)
        (hd * ed) : ℤ) : ℝ) / cd := by
      field_simp
    nlinarith
  · have hH := le_hullHiM hq1 hq2 hx1 hx2
    have hf := fdiv_le (cn * hullHiM (ln * ↑ed + en * ↑ld) (ld * ed) (hn * ↑ed + en * ↑hd)
      (hd * ed)) hcd
    have hcR : (cn : ℝ) ≤ 0 := by exact_mod_cast (le_of_lt (lt_of_not_ge hc))
    push_cast at hf hH
    rw [div_le_iff₀ hE]
    have hm := mul_le_mul_of_nonpos_left hH (div_nonpos_of_nonpos_of_nonneg hcR hcdR.le)
    have : (cn : ℝ) / cd * (((hullHiM (ln * ↑ed + en * ↑ld) (ld * ed) (hn * ↑ed + en * ↑hd)
        (hd * ed) : ℤ) : ℝ) / twoE) * twoE =
        (cn : ℝ) * ((hullHiM (ln * ↑ed + en * ↑ld) (ld * ed) (hn * ↑ed + en * ↑hd)
        (hd * ed) : ℤ) : ℝ) / cd := by
      field_simp
    nlinarith

theorem termsLowM_le {ln hn : ℤ} {ld hd : ℕ} (hld : 0 < ld) (hhd : 0 < hd) {x : ℝ}
    (hxl : (ln : ℝ) / ld ≤ x) (hxh : x ≤ (hn : ℝ) / hd) (l : List TermI)
    (hl : l.all TermI.pos = true) :
    ((termsLowM ln ld hn hd l : ℤ) : ℝ) / twoE ≤ termsVal (l.map TermI.toQ) x := by
  induction l with
  | nil => simp [termsLowM]
  | cons t l ih =>
      simp only [List.all_cons, Bool.and_eq_true] at hl
      simp only [termsLowM, List.map_cons, termsVal_cons]
      push_cast
      rw [add_div]
      linarith [termLowM_le hld hhd hxl hxh t hl.1, ih hl.2]

/-- Literal integer form of the merged term table (generated). -/
def freqTermsI : List TermI := [
  ((-31249999999 : ℤ), 31250000000, (1 : ℤ), 4),
  ((1 : ℤ), 1, (2 : ℤ), 1),
  ((-2 : ℤ), 1, (0 : ℤ), 1),
  ((-3906249999 : ℤ), 3906250000, (-1 : ℤ), 2),
  ((-1 : ℤ), 3906250000, (-17 : ℤ), 32),
  ((38360141 : ℤ), 125000000, (-25 : ℤ), 32),
  ((3286706291 : ℤ), 15625000000, (-13 : ℤ), 16),
  ((3762297 : ℤ), 31250000, (-27 : ℤ), 32),
  ((752802623 : ℤ), 7812500000, (-7 : ℤ), 8),
  ((1223131873 : ℤ), 15625000000, (-29 : ℤ), 32),
  ((1037836169 : ℤ), 15625000000, (-15 : ℤ), 16),
  ((899221991 : ℤ), 15625000000, (-31 : ℤ), 32),
  ((792084751 : ℤ), 15625000000, (-1 : ℤ), 1),
  ((707049449 : ℤ), 15625000000, (-33 : ℤ), 32),
  ((79625447 : ℤ), 1953125000, (-17 : ℤ), 16),
  ((578957103 : ℤ), 15625000000, (-35 : ℤ), 32),
  ((529354129 : ℤ), 15625000000, (-9 : ℤ), 8),
  ((486957403 : ℤ), 15625000000, (-37 : ℤ), 32),
  ((90055951 : ℤ), 3125000000, (-19 : ℤ), 16),
  ((83623327 : ℤ), 3125000000, (-39 : ℤ), 32),
  ((48716503 : ℤ), 1953125000, (-5 : ℤ), 4),
  ((18222657 : ℤ), 781250000, (-41 : ℤ), 32),
  ((342160999 : ℤ), 15625000000, (-21 : ℤ), 16),
  ((80463047 : ℤ), 3906250000, (-43 : ℤ), 32),
  ((6069949 : ℤ), 312500000, (-11 : ℤ), 8),
  ((71756983 : ℤ), 3906250000, (-45 : ℤ), 32),
  ((5437333 : ℤ), 312500000, (-23 : ℤ), 16),
  ((51633061 : ℤ), 3125000000, (-47 : ℤ), 32),
  ((7669329 : ℤ), 488281250, (-3 : ℤ), 2),
  ((117052299 : ℤ), 7812500000, (-49 : ℤ), 32),
  ((111643969 : ℤ), 7812500000, (-25 : ℤ), 16),
  ((213449691 : ℤ), 15625000000, (-51 : ℤ), 32),
  ((102092179 : ℤ), 7812500000, (-13 : ℤ), 8),
  ((195764319 : ℤ), 15625000000, (-53 : ℤ), 32),
  ((187920367 : ℤ), 15625000000, (-27 : ℤ), 16),
  ((180374751 : ℤ), 15625000000, (-55 : ℤ), 32),
  ((173615207 : ℤ), 15625000000, (-7 : ℤ), 4),
  ((20902237 : ℤ), 1953125000, (-57 : ℤ), 32),
  ((40301847 : ℤ), 3906250000, (-29 : ℤ), 16),
  ((77736843 : ℤ), 7812500000, (-59 : ℤ), 32),
  ((75039857 : ℤ), 7812500000, (-15 : ℤ), 8),
  ((36293019 : ℤ), 3906250000, (-61 : ℤ), 32),
  ((8787927 : ℤ), 976562500, (-31 : ℤ), 16),
  ((136142743 : ℤ), 15625000000, (-63 : ℤ), 32),
  ((65851071 : ℤ), 7812500000, (-2 : ℤ), 1),
  ((25564087 : ℤ), 3125000000, (-65 : ℤ), 32),
  ((124069531 : ℤ), 15625000000, (-33 : ℤ), 16),
  ((60312953 : ℤ), 7812500000, (-67 : ℤ), 32),
  ((58547979 : ℤ), 7812500000, (-17 : ℤ), 8),
  ((113986959 : ℤ), 15625000000, (-69 : ℤ), 32),
  ((111044631 : ℤ), 15625000000, (-35 : ℤ), 16),
  ((27019527 : ℤ), 3906250000, (-71 : ℤ), 32),
  ((52629813 : ℤ), 7812500000, (-9 : ℤ), 4),
  ((102772949 : ℤ), 15625000000, (-73 : ℤ), 32),
  ((100246233 : ℤ), 15625000000, (-37 : ℤ), 16),
  ((24461391 : ℤ), 3906250000, (-75 : ℤ), 32),
  ((47784633 : ℤ), 7812500000, (-19 : ℤ), 8),
  ((18707067 : ℤ), 3125000000, (-77 : ℤ), 32),
  ((91324699 : ℤ), 15625000000, (-39 : ℤ), 16),
  ((89508753 : ℤ), 15625000000, (-79 : ℤ), 32),
  ((17510377 : ℤ), 3125000000, (-5 : ℤ), 2),
  ((21436983 : ℤ), 3906250000, (-81 : ℤ), 32),
  ((841741 : ℤ), 156250000, (-41 : ℤ), 16),
  ((82339603 : ℤ), 15625000000, (-83 : ℤ), 32),
  ((80979709 : ℤ), 15625000000, (-21 : ℤ), 8),
  ((79453429 : ℤ), 15625000000, (-85 : ℤ), 32),
  ((1219367 : ℤ), 244140625, (-43 : ℤ), 16),
  ((76578647 : ℤ), 15625000000, (-87 : ℤ), 32),
  ((4706601 : ℤ), 976562500, (-11 : ℤ), 4),
  ((2314921 : ℤ), 488281250, (-89 : ℤ), 32),
  ((72862761 : ℤ), 15625000000, (-45 : ℤ), 16),
  ((71785761 : ℤ), 15625000000, (-91 : ℤ), 32),
  ((70669681 : ℤ), 15625000000, (-23 : ℤ), 8),
  ((69659703 : ℤ), 15625000000, (-93 : ℤ), 32),
  ((34374821 : ℤ), 7812500000, (-47 : ℤ), 16),
  ((16936443 : ℤ), 3906250000, (-95 : ℤ), 32),
  ((33410967 : ℤ), 7812500000, (-3 : ℤ), 1),
  ((13198583 : ℤ), 3125000000, (-97 : ℤ), 32),
  ((651633 : ℤ), 156250000, (-49 : ℤ), 16),
  ((6440791 : ℤ), 1562500000, (-99 : ℤ), 32),
  ((12734303 : ℤ), 3125000000, (-25 : ℤ), 8),
  ((12599251 : ℤ), 3125000000, (-101 : ℤ), 32),
  ((31169731 : ℤ), 7812500000, (-51 : ℤ), 16),
  ((30870909 : ℤ), 7812500000, (-103 : ℤ), 32),
  ((15293791 : ℤ), 3906250000, (-13 : ℤ), 4),
  ((60646123 : ℤ), 15625000000, (-105 : ℤ), 32),
  ((2406453 : ℤ), 625000000, (-53 : ℤ), 16),
  ((29856761 : ℤ), 7812500000, (-107 : ℤ), 32),
  ((59278837 : ℤ), 15625000000, (-27 : ℤ), 8),
  ((29417927 : ℤ), 7812500000, (-109 : ℤ), 32),
  ((58488879 : ℤ), 15625000000, (-55 : ℤ), 16),
  ((14544603 : ℤ), 3906250000, (-111 : ℤ), 32),
  ((57935419 : ℤ), 15625000000, (-7 : ℤ), 2),
  ((28856697 : ℤ), 7812500000, (-113 : ℤ), 32),
  ((28762677 : ℤ), 7812500000, (-57 : ℤ), 16),
  ((57415573 : ℤ), 15625000000, (-115 : ℤ), 32),
  ((5730891 : ℤ), 1562500000, (-29 : ℤ), 8),
  ((57192343 : ℤ), 15625000000, (-117 : ℤ), 32),
  ((57221479 : ℤ), 15625000000, (-59 : ℤ), 16),
  ((11442831 : ℤ), 3125000000, (-119 : ℤ), 32),
  ((28661041 : ℤ), 7812500000, (-15 : ℤ), 4),
  ((57470049 : ℤ), 15625000000, (-121 : ℤ), 32),
  ((57710559 : ℤ), 15625000000, (-61 : ℤ), 16),
  ((58023019 : ℤ), 15625000000, (-123 : ℤ), 32),
  ((29187569 : ℤ), 7812500000, (-31 : ℤ), 8),
  ((29381953 : ℤ), 7812500000, (-125 : ℤ), 32),
  ((59356607 : ℤ), 15625000000, (-63 : ℤ), 16),
  ((59926873 : ℤ), 15625000000, (-127 : ℤ), 32),
  ((12154207 : ℤ), 3125000000, (-4 : ℤ), 1),
  ((30760751 : ℤ), 7812500000, (-129 : ℤ), 32),
  ((2506879 : ℤ), 625000000, (-65 : ℤ), 16),
  ((638511 : ℤ), 156250000, (-131 : ℤ), 32),
  ((65289551 : ℤ), 15625000000, (-33 : ℤ), 8),
  ((67023471 : ℤ), 15625000000, (-133 : ℤ), 32),
  ((68975459 : ℤ), 15625000000, (-67 : ℤ), 16),
  ((17865123 : ℤ), 3906250000, (-135 : ℤ), 32),
  ((4652349 : ℤ), 976562500, (-17 : ℤ), 4),
  ((9752753 : ℤ), 1953125000, (-137 : ℤ), 32),
  ((826993 : ℤ), 156250000, (-69 : ℤ), 16),
  ((4431411 : ℤ), 781250000, (-139 : ℤ), 32),
  ((1208259 : ℤ), 195312500, (-35 : ℤ), 8),
  ((21606077 : ℤ), 3125000000, (-141 : ℤ), 32),
  ((128766113 : ℤ), 15625000000, (-71 : ℤ), 16),
  ((151361701 : ℤ), 15625000000, (-143 : ℤ), 32),
  ((366287711 : ℤ), 15625000000, (-9 : ℤ), 2),
  ((-1 : ℤ), 31250000000, (9 : ℤ), 32),
  ((1652688729 : ℤ), 15625000000, (11 : ℤ), 32),
  ((3935557171 : ℤ), 15625000000, (3 : ℤ), 8),
  ((2695470163 : ℤ), 31250000000, (13 : ℤ), 32),
  ((2236180223 : ℤ), 31250000000, (7 : ℤ), 16),
  ((843114239 : ℤ), 15625000000, (15 : ℤ), 32),
  ((278515883 : ℤ), 6250000000, (1 : ℤ), 2),
  ((1186618919 : ℤ), 31250000000, (17 : ℤ), 32),
  ((13038037 : ℤ), 390625000, (9 : ℤ), 16),
  ((941178087 : ℤ), 31250000000, (19 : ℤ), 32),
  ((869963531 : ℤ), 31250000000, (5 : ℤ), 8),
  ((824823987 : ℤ), 31250000000, (21 : ℤ), 32),
  ((200866313 : ℤ), 7812500000, (11 : ℤ), 16),
  ((404427127 : ℤ), 15625000000, (23 : ℤ), 32),
  ((26371667 : ℤ), 976562500, (3 : ℤ), 4),
  ((962530933 : ℤ), 31250000000, (25 : ℤ), 32),
  ((51003939 : ℤ), 1562500000, (13 : ℤ), 16),
  ((1379299937 : ℤ), 15625000000, (27 : ℤ), 32)]

theorem freqTermsI_toQ : freqTermsI.map TermI.toQ = freqTerms := by decide +kernel

theorem freqTermsI_pos : freqTermsI.all TermI.pos = true := by decide +kernel

end Li2Lean.P0.CA.Frequency
