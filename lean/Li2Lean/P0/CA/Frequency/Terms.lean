/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.Arith
import Li2Lean.P0.ConfigSlackSemanticIdentity

/-!
# CA-F: the actual `Wmu` as a finite combination of the primitive `F`

Starting from `ConfigSlackSemanticIdentity.actualWmu_eq_endpoints` (the
literal frequency first variation with exact segment endpoint sums), the
function `Config.Wmu actualReference` is written as
`-1/2 - log 2 / 2 + t log 2 + sum_i c_i F(t + e_i) - contourPotential(-t)`
with rational `(c_i, e_i)` read directly from the Appendix A arrays in
`ConfigData`.  Equal shifts are merged (density jumps), and the merged list
is checked by the kernel against a literal table used by the row checker.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.LogSegment Li2Lean.P0.ConfigSegment Li2Lean.P0.ConfigReferenceSymmetry
open Li2Lean.P0.ConfigContourReference

/-- Value of a coefficient/shift list: `sum c * F(t + e)`. -/
noncomputable def termsVal (l : List (ℚ × ℚ)) (t : ℝ) : ℝ :=
  (l.map fun p => (p.1 : ℝ) * primitive (t + (p.2 : ℝ))).sum

@[simp] theorem termsVal_nil (t : ℝ) : termsVal [] t = 0 := rfl

@[simp] theorem termsVal_cons (p : ℚ × ℚ) (l : List (ℚ × ℚ)) (t : ℝ) :
    termsVal (p :: l) t = (p.1 : ℝ) * primitive (t + (p.2 : ℝ)) + termsVal l t := by
  simp [termsVal]

theorem termsVal_append (l m : List (ℚ × ℚ)) (t : ℝ) :
    termsVal (l ++ m) t = termsVal l t + termsVal m t := by
  simp [termsVal]

theorem termsVal_flatMap_range (n : ℕ) (g : ℕ → List (ℚ × ℚ)) (t : ℝ) :
    termsVal ((List.range n).flatMap g) t = ∑ j ∈ Finset.range n, termsVal (g j) t := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, termsVal_append, ih,
        Finset.sum_range_succ]
      simp [termsVal]

/-- Rational frequency reference density `32 m_j / D`. -/
def freqDensQ (j : ℕ) : ℚ :=
  32 * (Li2Lean.P0.ConfigData.frequencyMassUnits.getD j 0 : ℚ) /
    (Li2Lean.P0.ConfigData.referenceDenominator : ℚ)

/-- Rational pinned reference density `32 m_k / D`. -/
def pinDensQ (k : ℕ) : ℚ :=
  32 * (Li2Lean.P0.ConfigData.pinnedMassUnits.getD k 0 : ℚ) /
    (Li2Lean.P0.ConfigData.referenceDenominator : ℚ)

theorem freqDensQ_cast (j : ℕ) :
    (freqDensQ j : ℝ) = referenceDensity Li2Lean.P0.ConfigData.frequencyMassUnits j := by
  unfold freqDensQ referenceDensity; push_cast; rfl

theorem pinDensQ_cast (k : ℕ) :
    (pinDensQ k : ℝ) = referenceDensity Li2Lean.P0.ConfigData.pinnedMassUnits k := by
  unfold pinDensQ referenceDensity; push_cast; rfl

/-- The two frequency-cell terms of `-2 * frequencyReferencePotential t`. -/
def freqPair (j : ℕ) : List (ℚ × ℚ) :=
  [(-2 * freqDensQ j, -(1 / 2 + (j : ℚ) / 32)),
   (2 * freqDensQ j, -(1 / 2 + ((j + 1 : ℕ) : ℚ) / 32))]

/-- The two pinned-cell terms of `-pinnedReferencePotential (-t)`. -/
def pinPair (k : ℕ) : List (ℚ × ℚ) :=
  [(-pinDensQ k, 1 / 4 + ((k + 1 : ℕ) : ℚ) / 32),
   (pinDensQ k, 1 / 4 + (k : ℚ) / 32)]

/-- The unmerged term list: `B0`, `-psi`, the frequency and pinned segments. -/
def rawTerms : List (ℚ × ℚ) :=
  [(1, 5 / 4), (-1, 1 / 4), (1, 2), (-1, 0), (-1, 0), (1, -(1 / 2))] ++
    (List.range 160).flatMap freqPair ++ (List.range 32).flatMap pinPair

theorem psi_eq_primitive (t : ℝ) :
    Config.psi t = primitive t - primitive (t - 1 / 2) + 1 / 2 +
      Real.log 2 / 2 - t * Real.log 2 := by
  unfold Config.psi
  rw [primitive_eq, primitive_eq, one_div, Real.log_inv]
  ring

/-- The literal frequency first variation in coefficient/shift form. -/
theorem actualWmu_eq_rawTerms (t : ℝ) :
    Config.Wmu actualReference t =
      -1 / 2 - Real.log 2 / 2 + t * Real.log 2 + termsVal rawTerms t -
        contourReferencePotential (-(t : ℂ)) := by
  rw [Li2Lean.P0.ConfigSlackSemanticIdentity.actualWmu_eq_endpoints, psi_eq_primitive]
  have hfreq : termsVal ((List.range 160).flatMap freqPair) t =
      -(2 * ∑ j ∈ Finset.range 160,
        referenceDensity Li2Lean.P0.ConfigData.frequencyMassUnits j *
          (primitive (t - referenceCellLeft (1 / 2) j) -
            primitive (t - referenceCellRight (1 / 2) j))) := by
    rw [termsVal_flatMap_range, Finset.mul_sum, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [freqPair, termsVal_cons, termsVal_nil, referenceCellLeft,
      referenceCellRight, ← freqDensQ_cast]
    push_cast
    simp only [← sub_eq_add_neg]
    ring
  have hpin : termsVal ((List.range 32).flatMap pinPair) t =
      -(∑ j ∈ Finset.range 32,
        referenceDensity Li2Lean.P0.ConfigData.pinnedMassUnits j *
          (primitive (t + referenceCellRight (1 / 4) j) -
            primitive (t + referenceCellLeft (1 / 4) j))) := by
    rw [termsVal_flatMap_range, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [pinPair, termsVal_cons, termsVal_nil, referenceCellLeft,
      referenceCellRight, ← pinDensQ_cast]
    push_cast
    ring
  unfold rawTerms
  rw [termsVal_append, termsVal_append, hfreq, hpin]
  simp only [termsVal_cons, termsVal_nil]
  push_cast
  simp only [← sub_eq_add_neg, add_zero]
  ring

/-! ## Merging equal shifts -/

def insertTerm (p : ℚ × ℚ) : List (ℚ × ℚ) → List (ℚ × ℚ)
  | [] => [p]
  | q :: l => if q.2 = p.2 then (q.1 + p.1, q.2) :: l else q :: insertTerm p l

def mergeTerms (l : List (ℚ × ℚ)) : List (ℚ × ℚ) :=
  (l.foldl (fun acc p => insertTerm p acc) []).filter (fun p => decide (p.1 ≠ 0))

theorem termsVal_insertTerm (p : ℚ × ℚ) (l : List (ℚ × ℚ)) (t : ℝ) :
    termsVal (insertTerm p l) t = (p.1 : ℝ) * primitive (t + (p.2 : ℝ)) + termsVal l t := by
  induction l with
  | nil => simp [insertTerm]
  | cons q l ih =>
      simp only [insertTerm]
      split_ifs with h
      · simp only [termsVal_cons, h]
        push_cast
        ring
      · simp only [termsVal_cons, ih]
        ring

theorem termsVal_foldl (l acc : List (ℚ × ℚ)) (t : ℝ) :
    termsVal (l.foldl (fun acc p => insertTerm p acc) acc) t = termsVal acc t + termsVal l t := by
  induction l generalizing acc with
  | nil => simp
  | cons p l ih =>
      simp only [List.foldl_cons, ih, termsVal_insertTerm, termsVal_cons]
      ring

theorem termsVal_filter (l : List (ℚ × ℚ)) (t : ℝ) :
    termsVal (l.filter (fun p => decide (p.1 ≠ 0))) t = termsVal l t := by
  induction l with
  | nil => simp
  | cons p l ih =>
      by_cases h : p.1 = 0
      · rw [List.filter_cons]
        simpa [h] using ih
      · rw [List.filter_cons]
        simpa [h] using ih

theorem termsVal_mergeTerms (l : List (ℚ × ℚ)) (t : ℝ) :
    termsVal (mergeTerms l) t = termsVal l t := by
  unfold mergeTerms
  rw [termsVal_filter, termsVal_foldl]
  simp

/-- Literal merged coefficient/shift table (generated by
`tools/ca_freq/gen_freq_rows.py`, checked by `freqTerms_eq`). -/
def freqTerms : List (ℚ × ℚ) := [
  ((-31249999999 / 31250000000 : ℚ), (1 / 4 : ℚ)), ((1 : ℚ), (2 : ℚ)),
  ((-2 : ℚ), (0 : ℚ)), ((-3906249999 / 3906250000 : ℚ), (-1 / 2 : ℚ)),
  ((-1 / 3906250000 : ℚ), (-17 / 32 : ℚ)), ((38360141 / 125000000 : ℚ), (-25 / 32 : ℚ)),
  ((3286706291 / 15625000000 : ℚ), (-13 / 16 : ℚ)), ((3762297 / 31250000 : ℚ), (-27 / 32 : ℚ)),
  ((752802623 / 7812500000 : ℚ), (-7 / 8 : ℚ)), ((1223131873 / 15625000000 : ℚ), (-29 / 32 : ℚ)),
  ((1037836169 / 15625000000 : ℚ), (-15 / 16 : ℚ)), ((899221991 / 15625000000 : ℚ), (-31 / 32 : ℚ)),
  ((792084751 / 15625000000 : ℚ), (-1 : ℚ)), ((707049449 / 15625000000 : ℚ), (-33 / 32 : ℚ)),
  ((79625447 / 1953125000 : ℚ), (-17 / 16 : ℚ)), ((578957103 / 15625000000 : ℚ), (-35 / 32 : ℚ)),
  ((529354129 / 15625000000 : ℚ), (-9 / 8 : ℚ)), ((486957403 / 15625000000 : ℚ), (-37 / 32 : ℚ)),
  ((90055951 / 3125000000 : ℚ), (-19 / 16 : ℚ)), ((83623327 / 3125000000 : ℚ), (-39 / 32 : ℚ)),
  ((48716503 / 1953125000 : ℚ), (-5 / 4 : ℚ)), ((18222657 / 781250000 : ℚ), (-41 / 32 : ℚ)),
  ((342160999 / 15625000000 : ℚ), (-21 / 16 : ℚ)), ((80463047 / 3906250000 : ℚ), (-43 / 32 : ℚ)),
  ((6069949 / 312500000 : ℚ), (-11 / 8 : ℚ)), ((71756983 / 3906250000 : ℚ), (-45 / 32 : ℚ)),
  ((5437333 / 312500000 : ℚ), (-23 / 16 : ℚ)), ((51633061 / 3125000000 : ℚ), (-47 / 32 : ℚ)),
  ((7669329 / 488281250 : ℚ), (-3 / 2 : ℚ)), ((117052299 / 7812500000 : ℚ), (-49 / 32 : ℚ)),
  ((111643969 / 7812500000 : ℚ), (-25 / 16 : ℚ)), ((213449691 / 15625000000 : ℚ), (-51 / 32 : ℚ)),
  ((102092179 / 7812500000 : ℚ), (-13 / 8 : ℚ)), ((195764319 / 15625000000 : ℚ), (-53 / 32 : ℚ)),
  ((187920367 / 15625000000 : ℚ), (-27 / 16 : ℚ)), ((180374751 / 15625000000 : ℚ), (-55 / 32 : ℚ)),
  ((173615207 / 15625000000 : ℚ), (-7 / 4 : ℚ)), ((20902237 / 1953125000 : ℚ), (-57 / 32 : ℚ)),
  ((40301847 / 3906250000 : ℚ), (-29 / 16 : ℚ)), ((77736843 / 7812500000 : ℚ), (-59 / 32 : ℚ)),
  ((75039857 / 7812500000 : ℚ), (-15 / 8 : ℚ)), ((36293019 / 3906250000 : ℚ), (-61 / 32 : ℚ)),
  ((8787927 / 976562500 : ℚ), (-31 / 16 : ℚ)), ((136142743 / 15625000000 : ℚ), (-63 / 32 : ℚ)),
  ((65851071 / 7812500000 : ℚ), (-2 : ℚ)), ((25564087 / 3125000000 : ℚ), (-65 / 32 : ℚ)),
  ((124069531 / 15625000000 : ℚ), (-33 / 16 : ℚ)), ((60312953 / 7812500000 : ℚ), (-67 / 32 : ℚ)),
  ((58547979 / 7812500000 : ℚ), (-17 / 8 : ℚ)), ((113986959 / 15625000000 : ℚ), (-69 / 32 : ℚ)),
  ((111044631 / 15625000000 : ℚ), (-35 / 16 : ℚ)), ((27019527 / 3906250000 : ℚ), (-71 / 32 : ℚ)),
  ((52629813 / 7812500000 : ℚ), (-9 / 4 : ℚ)), ((102772949 / 15625000000 : ℚ), (-73 / 32 : ℚ)),
  ((100246233 / 15625000000 : ℚ), (-37 / 16 : ℚ)), ((24461391 / 3906250000 : ℚ), (-75 / 32 : ℚ)),
  ((47784633 / 7812500000 : ℚ), (-19 / 8 : ℚ)), ((18707067 / 3125000000 : ℚ), (-77 / 32 : ℚ)),
  ((91324699 / 15625000000 : ℚ), (-39 / 16 : ℚ)), ((89508753 / 15625000000 : ℚ), (-79 / 32 : ℚ)),
  ((17510377 / 3125000000 : ℚ), (-5 / 2 : ℚ)), ((21436983 / 3906250000 : ℚ), (-81 / 32 : ℚ)),
  ((841741 / 156250000 : ℚ), (-41 / 16 : ℚ)), ((82339603 / 15625000000 : ℚ), (-83 / 32 : ℚ)),
  ((80979709 / 15625000000 : ℚ), (-21 / 8 : ℚ)), ((79453429 / 15625000000 : ℚ), (-85 / 32 : ℚ)),
  ((1219367 / 244140625 : ℚ), (-43 / 16 : ℚ)), ((76578647 / 15625000000 : ℚ), (-87 / 32 : ℚ)),
  ((4706601 / 976562500 : ℚ), (-11 / 4 : ℚ)), ((2314921 / 488281250 : ℚ), (-89 / 32 : ℚ)),
  ((72862761 / 15625000000 : ℚ), (-45 / 16 : ℚ)), ((71785761 / 15625000000 : ℚ), (-91 / 32 : ℚ)),
  ((70669681 / 15625000000 : ℚ), (-23 / 8 : ℚ)), ((69659703 / 15625000000 : ℚ), (-93 / 32 : ℚ)),
  ((34374821 / 7812500000 : ℚ), (-47 / 16 : ℚ)), ((16936443 / 3906250000 : ℚ), (-95 / 32 : ℚ)),
  ((33410967 / 7812500000 : ℚ), (-3 : ℚ)), ((13198583 / 3125000000 : ℚ), (-97 / 32 : ℚ)),
  ((651633 / 156250000 : ℚ), (-49 / 16 : ℚ)), ((6440791 / 1562500000 : ℚ), (-99 / 32 : ℚ)),
  ((12734303 / 3125000000 : ℚ), (-25 / 8 : ℚ)), ((12599251 / 3125000000 : ℚ), (-101 / 32 : ℚ)),
  ((31169731 / 7812500000 : ℚ), (-51 / 16 : ℚ)), ((30870909 / 7812500000 : ℚ), (-103 / 32 : ℚ)),
  ((15293791 / 3906250000 : ℚ), (-13 / 4 : ℚ)), ((60646123 / 15625000000 : ℚ), (-105 / 32 : ℚ)),
  ((2406453 / 625000000 : ℚ), (-53 / 16 : ℚ)), ((29856761 / 7812500000 : ℚ), (-107 / 32 : ℚ)),
  ((59278837 / 15625000000 : ℚ), (-27 / 8 : ℚ)), ((29417927 / 7812500000 : ℚ), (-109 / 32 : ℚ)),
  ((58488879 / 15625000000 : ℚ), (-55 / 16 : ℚ)), ((14544603 / 3906250000 : ℚ), (-111 / 32 : ℚ)),
  ((57935419 / 15625000000 : ℚ), (-7 / 2 : ℚ)), ((28856697 / 7812500000 : ℚ), (-113 / 32 : ℚ)),
  ((28762677 / 7812500000 : ℚ), (-57 / 16 : ℚ)), ((57415573 / 15625000000 : ℚ), (-115 / 32 : ℚ)),
  ((5730891 / 1562500000 : ℚ), (-29 / 8 : ℚ)), ((57192343 / 15625000000 : ℚ), (-117 / 32 : ℚ)),
  ((57221479 / 15625000000 : ℚ), (-59 / 16 : ℚ)), ((11442831 / 3125000000 : ℚ), (-119 / 32 : ℚ)),
  ((28661041 / 7812500000 : ℚ), (-15 / 4 : ℚ)), ((57470049 / 15625000000 : ℚ), (-121 / 32 : ℚ)),
  ((57710559 / 15625000000 : ℚ), (-61 / 16 : ℚ)), ((58023019 / 15625000000 : ℚ), (-123 / 32 : ℚ)),
  ((29187569 / 7812500000 : ℚ), (-31 / 8 : ℚ)), ((29381953 / 7812500000 : ℚ), (-125 / 32 : ℚ)),
  ((59356607 / 15625000000 : ℚ), (-63 / 16 : ℚ)), ((59926873 / 15625000000 : ℚ), (-127 / 32 : ℚ)),
  ((12154207 / 3125000000 : ℚ), (-4 : ℚ)), ((30760751 / 7812500000 : ℚ), (-129 / 32 : ℚ)),
  ((2506879 / 625000000 : ℚ), (-65 / 16 : ℚ)), ((638511 / 156250000 : ℚ), (-131 / 32 : ℚ)),
  ((65289551 / 15625000000 : ℚ), (-33 / 8 : ℚ)), ((67023471 / 15625000000 : ℚ), (-133 / 32 : ℚ)),
  ((68975459 / 15625000000 : ℚ), (-67 / 16 : ℚ)), ((17865123 / 3906250000 : ℚ), (-135 / 32 : ℚ)),
  ((4652349 / 976562500 : ℚ), (-17 / 4 : ℚ)), ((9752753 / 1953125000 : ℚ), (-137 / 32 : ℚ)),
  ((826993 / 156250000 : ℚ), (-69 / 16 : ℚ)), ((4431411 / 781250000 : ℚ), (-139 / 32 : ℚ)),
  ((1208259 / 195312500 : ℚ), (-35 / 8 : ℚ)), ((21606077 / 3125000000 : ℚ), (-141 / 32 : ℚ)),
  ((128766113 / 15625000000 : ℚ), (-71 / 16 : ℚ)), ((151361701 / 15625000000 : ℚ), (-143 / 32 : ℚ)),
  ((366287711 / 15625000000 : ℚ), (-9 / 2 : ℚ)), ((-1 / 31250000000 : ℚ), (9 / 32 : ℚ)),
  ((1652688729 / 15625000000 : ℚ), (11 / 32 : ℚ)), ((3935557171 / 15625000000 : ℚ), (3 / 8 : ℚ)),
  ((2695470163 / 31250000000 : ℚ), (13 / 32 : ℚ)), ((2236180223 / 31250000000 : ℚ), (7 / 16 : ℚ)),
  ((843114239 / 15625000000 : ℚ), (15 / 32 : ℚ)), ((278515883 / 6250000000 : ℚ), (1 / 2 : ℚ)),
  ((1186618919 / 31250000000 : ℚ), (17 / 32 : ℚ)), ((13038037 / 390625000 : ℚ), (9 / 16 : ℚ)),
  ((941178087 / 31250000000 : ℚ), (19 / 32 : ℚ)), ((869963531 / 31250000000 : ℚ), (5 / 8 : ℚ)),
  ((824823987 / 31250000000 : ℚ), (21 / 32 : ℚ)), ((200866313 / 7812500000 : ℚ), (11 / 16 : ℚ)),
  ((404427127 / 15625000000 : ℚ), (23 / 32 : ℚ)), ((26371667 / 976562500 : ℚ), (3 / 4 : ℚ)),
  ((962530933 / 31250000000 : ℚ), (25 / 32 : ℚ)), ((51003939 / 1562500000 : ℚ), (13 / 16 : ℚ)),
  ((1379299937 / 15625000000 : ℚ), (27 / 32 : ℚ))]

theorem freqTerms_eq : mergeTerms rawTerms = freqTerms := by
  decide +kernel

/-- The literal frequency first variation with merged coefficients. -/
theorem actualWmu_eq_freqTerms (t : ℝ) :
    Config.Wmu actualReference t =
      -1 / 2 - Real.log 2 / 2 + t * Real.log 2 + termsVal freqTerms t -
        contourReferencePotential (-(t : ℂ)) := by
  rw [actualWmu_eq_rawTerms, ← freqTerms_eq, termsVal_mergeTerms]

end Li2Lean.P0.CA.Frequency
