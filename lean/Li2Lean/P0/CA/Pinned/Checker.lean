/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Pinned.ContourPolynomial
import Li2Lean.P0.CA.Pinned.Moments
import Li2Lean.P0.ConfigSlackSemanticIdentity
import Li2Lean.P0.ConfigData
import Li2Lean.Agents.F_L8.Types

/-!
# One reflected checker for the pinned C-A rows

`pinnedWeta x = Config.Weta actualReference x` is rewritten, for
`x ∈ [1/4, 5/4]`, as a finite sum of terms `c * F(x + s)` with
`F(u) = u (log |u| - 1)`, plus `-x log 2`, a constant, and twice the contour
moment polynomial.  On the chunk `[1/4 + j/32, 1/4 + (j+1)/32]` the two terms
whose singular point is a chunk edge are bounded by exact monotone hulls; every
other term, the contour polynomial, the linear term and the constant are
combined into one certified polynomial model.  `chunkCheck` is a Boolean over
`ℚ`; `chunkCheck_sound` turns it into the raw `modelRemainderValid` of every
row of the chunk (original cell lower bound, no allowance subtracted).
-/

namespace Li2Lean.P0.CA.Pinned

open Li2Lean.LogSegment
open Li2Lean.F_L8
open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigFejerLog
open Li2Lean.P0.PinnedRow1ClosedForm

/-! ## The term decomposition of the actual field -/

def rhoP (j : ℕ) : ℚ := 32 * (Li2Lean.P0.ConfigData.pinnedMassUnits.getD j 0 : ℚ) / 1000000000000
def rhoF (j : ℕ) : ℚ :=
  32 * (Li2Lean.P0.ConfigData.frequencyMassUnits.getD j 0 : ℚ) / 1000000000000

def baseTerms : List (ℚ × ℚ) :=
  [(1, -(1 / 4)), (-1, -(5 / 4)), (1, 0), (-1, -2), (-1, 1 / 2), (1, 0)]

def pinTerms : List (ℚ × ℚ) :=
  (List.range 32).flatMap (fun j =>
    [(-2 * rhoP j, -(1 / 4 + (j : ℚ) / 32)), (2 * rhoP j, -(1 / 4 + ((j + 1 : ℕ) : ℚ) / 32))])

def freqTerms : List (ℚ × ℚ) :=
  (List.range 160).flatMap (fun j =>
    [(-rhoF j, 1 / 2 + ((j + 1 : ℕ) : ℚ) / 32), (rhoF j, 1 / 2 + (j : ℚ) / 32)])

def wetaTerms : List (ℚ × ℚ) := baseTerms ++ pinTerms ++ freqTerms

noncomputable def termSum (l : List (ℚ × ℚ)) (x : ℝ) : ℝ :=
  (l.map (fun p => (p.1 : ℝ) * primitive (x + p.2))).sum

theorem termSum_nil (x : ℝ) : termSum [] x = 0 := by simp [termSum]

theorem termSum_cons (p : ℚ × ℚ) (l : List (ℚ × ℚ)) (x : ℝ) :
    termSum (p :: l) x = (p.1 : ℝ) * primitive (x + p.2) + termSum l x := by
  simp [termSum]

theorem termSum_append (l m : List (ℚ × ℚ)) (x : ℝ) :
    termSum (l ++ m) x = termSum l x + termSum m x := by
  simp [termSum, List.map_append, List.sum_append]

theorem termSum_flatMap_range (n : ℕ) (g : ℕ → List (ℚ × ℚ)) (x : ℝ) :
    termSum ((List.range n).flatMap g) x = ∑ j ∈ Finset.range n, termSum (g j) x := by
  induction n with
  | zero => simp [termSum]
  | succ n ih =>
      rw [List.range_succ, List.flatMap_append, termSum_append, ih, Finset.sum_range_succ]
      simp [List.flatMap]

noncomputable def constK : ℝ :=
  -(1 / 2) - (1 / 2) * Real.log 2 -
    2 * ((267885951940 / 1000000000000 : ℝ) * Real.log contourScale)

noncomputable section

theorem pinnedWeta_terms (x : ℝ) (hxlo : 1 / 4 ≤ x) (hxhi : x ≤ 5 / 4) :
    Li2Lean.P0.ConfigContourSelfPotential.pinnedWeta x =
      termSum wetaTerms x - x * Real.log 2 + constK + 2 * contourQ x := by
  unfold Li2Lean.P0.ConfigContourSelfPotential.pinnedWeta
  rw [Li2Lean.P0.ConfigSlackSemanticIdentity.actualWeta_ofReal_eq_endpoints,
    contourPotential_eq_poly x hxlo hxhi]
  have hpin : termSum pinTerms x = -2 * ∑ j ∈ Finset.range 32,
      referenceDensity Li2Lean.P0.ConfigData.pinnedMassUnits j *
        (primitive (x - referenceCellLeft (1 / 4) j) -
          primitive (x - referenceCellRight (1 / 4) j)) := by
    rw [pinTerms, termSum_flatMap_range, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro j _
    simp only [termSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      referenceDensity, referenceCellLeft, referenceCellRight, rhoP,
      Li2Lean.P0.ConfigData.referenceDenominator]
    push_cast
    ring_nf
  have hfreq : termSum freqTerms x = -∑ j ∈ Finset.range 160,
      referenceDensity Li2Lean.P0.ConfigData.frequencyMassUnits j *
        (primitive (x + referenceCellRight (1 / 2) j) -
          primitive (x + referenceCellLeft (1 / 2) j)) := by
    rw [freqTerms, termSum_flatMap_range, ← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro j _
    simp only [termSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil,
      referenceDensity, referenceCellLeft, referenceCellRight, rhoF,
      Li2Lean.P0.ConfigData.referenceDenominator]
    push_cast
    ring_nf
  have hbase : termSum baseTerms x =
      primitive (x - 1 / 4) - primitive (x - 5 / 4) + (primitive x - primitive (x - 2)) -
        (primitive (x + 1 / 2) - primitive x) := by
    simp only [baseTerms, termSum, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
    push_cast
    ring_nf
  rw [wetaTerms, termSum_append, termSum_append, hpin, hfreq, hbase]
  have hl : Real.log (1 / 2 : ℝ) = -Real.log 2 := by
    rw [one_div, Real.log_inv]
  rw [hl]
  unfold constK
  ring

end

/-! ## Splitting the terms on one chunk -/

structure Split where
  accL : ℚ
  accR : ℚ
  model : Model
  ok : Bool

def splitAll (x0 ρ sL sR : ℚ) (n : ℕ) : List (ℚ × ℚ) → Split
  | [] => ⟨0, 0, Model.zero, true⟩
  | p :: ps =>
      let st := splitAll x0 ρ sL sR n ps
      if p.1 = 0 then st
      else if p.2 = sL then { st with accL := st.accL + p.1 }
      else if p.2 = sR then { st with accR := st.accR + p.1 }
      else if 2 * ρ ≤ |x0 + p.2| then { st with model := (termModel p.1 x0 p.2 ρ n).add st.model }
      else { st with ok := false }

theorem splitAll_sound (x0 ρ sL sR : ℚ) (n : ℕ) (hρ : 0 < ρ) :
    ∀ l : List (ℚ × ℚ), (splitAll x0 ρ sL sR n l).ok = true →
      ∃ g : ℝ → ℝ, (splitAll x0 ρ sL sR n l).model.Holds g ρ ∧
        ∀ t : ℝ, termSum l ((x0 : ℝ) + t) =
          ((splitAll x0 ρ sL sR n l).accL : ℝ) * primitive ((x0 : ℝ) + t + sL) +
          ((splitAll x0 ρ sL sR n l).accR : ℝ) * primitive ((x0 : ℝ) + t + sR) + g t
  | [], _ => ⟨fun _ => 0, Model.zero_holds ρ, by intro t; simp [splitAll, termSum]⟩
  | p :: ps, hok => by
      simp only [splitAll] at hok ⊢
      split_ifs at hok ⊢ with h0 hL hR hS
      · obtain ⟨g, hg, he⟩ := splitAll_sound x0 ρ sL sR n hρ ps hok
        refine ⟨g, hg, fun t => ?_⟩
        rw [termSum_cons, he t, h0]; push_cast; ring
      · obtain ⟨g, hg, he⟩ := splitAll_sound x0 ρ sL sR n hρ ps hok
        refine ⟨g, hg, fun t => ?_⟩
        rw [termSum_cons, he t, hL]; push_cast; ring
      · obtain ⟨g, hg, he⟩ := splitAll_sound x0 ρ sL sR n hρ ps hok
        refine ⟨g, hg, fun t => ?_⟩
        rw [termSum_cons, he t, hR]; push_cast; ring
      · obtain ⟨g, hg, he⟩ := splitAll_sound x0 ρ sL sR n hρ ps hok
        refine ⟨fun t => (p.1 : ℝ) * primitive ((x0 : ℝ) + t + p.2) + g t,
          Model.add_holds (termModel_holds p.1 x0 p.2 ρ n hρ hS) hg, fun t => ?_⟩
        rw [termSum_cons, he t]
        have : (x0 : ℝ) + t + (p.2 : ℝ) = ((x0 : ℝ) + t) + p.2 := rfl
        ring

/-! ## The contour moment polynomial model -/

def contourAux (x0 : ℚ) : ℕ → Model × List ℚ × List ℚ
  | 0 => (Model.zero, [2], [psW0 x0, psK])
  | n + 1 =>
      let r := contourAux x0 n
      ((r.1.add (Model.ofScaledPoly (QI.smul (2 / (n : ℚ)) (momentTable.getD n ⟨0, 0⟩))
          r.2.1)).round,
        r.2.2, psNext x0 r.2.1 r.2.2)

theorem hornerR_psNext (x0 : ℚ) (a b : List ℚ) (t : ℝ) :
    hornerR (castL (psNext x0 a b)) t =
      ((psW0 x0 : ℝ) + (psK : ℝ) * t) * hornerR (castL b) t -
        (1333 / 24233 : ℝ) * hornerR (castL a) t := by
  rw [psNext, castL_addQ, hornerR_addR, hornerR_mulTrace]
  have : castL (a.map (fun c => -psQ * c)) = scaleR ((-psQ : ℚ) : ℝ) (castL a) :=
    castL_map_mul _ _
  rw [this, hornerR_scaleR]
  simp only [psQ]; push_cast; ring

theorem contourAux_spec (x0 : ℚ) (ρ : ℚ) :
    ∀ n, n ≤ 49 →
      (∀ t : ℝ, hornerR (castL (contourAux x0 n).2.1) t = row1PairPowerSum ((x0 : ℝ) + t) n ∧
        hornerR (castL (contourAux x0 n).2.2) t = row1PairPowerSum ((x0 : ℝ) + t) (n + 1)) ∧
      (contourAux x0 n).1.Holds (fun t => ∑ i ∈ Finset.range n,
        2 * (contourMoment i * (row1PairPowerSum ((x0 : ℝ) + t) i / (i : ℝ)))) ρ
  | 0, _ => by
      refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
      · simp [contourAux, castL, hornerR, row1PairPowerSum]
      · simp only [contourAux, castL, hornerR, zero_add]
        rw [row1PairPowerSum_one, trace_eq]; ring
      · simpa [contourAux] using Model.zero_holds ρ
  | n + 1, hn => by
      obtain ⟨hps, hM⟩ := contourAux_spec x0 ρ n (by omega)
      refine ⟨fun t => ⟨?_, ?_⟩, ?_⟩
      · simp only [contourAux]; exact (hps t).2
      · simp only [contourAux]
        rw [hornerR_psNext, (hps t).1, (hps t).2, ← trace_eq,
          row1PairPowerSum_recurrence]
      · simp only [contourAux]
        apply Model.round_holds
        have hz := QI.mem_smul (2 / (n : ℚ)) (moment_mem n (by omega))
        have h2 := Model.ofScaledPoly_holds hz (contourAux x0 n).2.1 ρ
        have h3 := Model.add_holds hM h2
        intro t ht
        obtain ⟨cs, hcs, he⟩ := h3 t ht
        refine ⟨cs, hcs, ?_⟩
        beta_reduce at he ⊢
        rw [Finset.sum_range_succ]
        convert he using 2
        rw [(hps t).1]
        push_cast
        ring

/-! ## The chunk model and the checker -/

def chunkX0 (j : ℕ) : ℚ := 1 / 4 + (2 * (j : ℚ) + 1) / 64
def chunkRho : ℚ := 1 / 64
def chunkSL (j : ℕ) : ℚ := -(1 / 4 + (j : ℚ) / 32)
def chunkSR (j : ℕ) : ℚ := -(1 / 4 + ((j : ℚ) + 1) / 32)
def seriesDegree : ℕ := 18
def modelDegree : ℕ := 20

/-- Enclosure of the constant `constK`. -/
def constKI : QI :=
  QI.add (QI.pt (-(1 / 2)))
    (QI.add (QI.smul (-(1 / 2)) LOG2)
      (QI.smul (-(2 * (267885951940 / 1000000000000))) (logI (24233 / 20000))))

theorem constKI_mem : constKI.Contains constK := by
  have h1 := QI.mem_smul (-(1 / 2)) log2_mem
  have h2 := QI.mem_smul (-(2 * (267885951940 / 1000000000000)))
    (logI_sound (q := 24233 / 20000) (by norm_num))
  have h := QI.mem_add (QI.mem_pt (-(1 / 2))) (QI.mem_add h1 h2)
  have e : constK = ((-(1 / 2) : ℚ) : ℝ) + (((-(1 / 2) : ℚ) : ℝ) * Real.log 2 +
      ((-(2 * (267885951940 / 1000000000000)) : ℚ) : ℝ) * Real.log ((24233 / 20000 : ℚ) : ℝ)) := by
    unfold constK contourScale; push_cast; ring
  unfold constKI; rw [e]; exact h

def linModel (x0 : ℚ) : Model := ⟨[QI.smul (-x0) LOG2, QI.smul (-1) LOG2], 0⟩

theorem linModel_holds (x0 ρ : ℚ) :
    (linModel x0).Holds (fun t => -(((x0 : ℝ) + t) * Real.log 2)) ρ := by
  intro t _
  refine ⟨[-(x0 : ℝ) * Real.log 2, -1 * Real.log 2],
    List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil), ?_⟩
  · simpa using QI.mem_smul (-x0) log2_mem
  · simpa using QI.mem_smul (-1) log2_mem
  · first
      | (simp [hornerR, linModel]; done)
      | (simp [hornerR, linModel]; ring_nf; done)
      | (simp [hornerR, linModel]; ring_nf; simp)

def constModel : Model := ⟨[constKI], 0⟩

theorem constModel_holds (ρ : ℚ) : constModel.Holds (fun _ => constK) ρ := by
  intro t _
  exact ⟨[constK], List.Forall₂.cons constKI_mem List.Forall₂.nil, by simp [hornerR, constModel]⟩

def chunkSplit (j : ℕ) : Split :=
  splitAll (chunkX0 j) chunkRho (chunkSL j) (chunkSR j) seriesDegree wetaTerms

def chunkModel (j : ℕ) : Model :=
  ((((chunkSplit j).model.add (contourAux (chunkX0 j) 49).1).add
    (linModel (chunkX0 j))).add constModel).round

def rowCheck (j : ℕ) (p : List ℚ) (e aL aR : ℚ) (c : ReceiptCell) : Bool :=
  decide (chunkX0 j - chunkRho ≤ c.lo ∧ c.lo ≤ c.hi ∧ c.hi ≤ chunkX0 j + chunkRho) &&
    hullOK (chunkSL j) c.lo c.hi && hullOK (chunkSR j) c.lo c.hi &&
    decide (c.lower ≤ hullLower aL (chunkSL j) c.lo c.hi + hullLower aR (chunkSR j) c.lo c.hi +
      polyLower p (c.lo - chunkX0 j) (c.hi - chunkX0 j) - e)

/-- Model stage: the literal polynomial `p`, error `e`, and hull coefficients are
those of the certified chunk model. -/
def modelCheck (j : ℕ) (p : List ℚ) (e aL aR : ℚ) : Bool :=
  (chunkSplit j).ok && decide ((chunkSplit j).accL = aL ∧ (chunkSplit j).accR = aR) &&
    decide ((chunkModel j).eps + normErr chunkRho (chunkModel j).coeffs p ≤ e)

def rowsCheck (j : ℕ) (p : List ℚ) (e aL aR : ℚ) (rows : List ReceiptCell) : Bool :=
  rows.all (rowCheck j p e aL aR)

/-- Batched evaluation: a long `List.all` is split into kernel-sized pieces. -/
theorem all_of_batches {α : Type*} (f : α → Bool) (k : ℕ) :
    ∀ (nb : ℕ) (L : List α), (∀ b < nb, ((L.drop (k * b)).take k).all f = true) →
      L.length ≤ k * nb → L.all f = true
  | 0, L, _, hl => by
      have : L = [] := List.eq_nil_of_length_eq_zero (by simpa using hl)
      simp [this]
  | nb + 1, L, h, hl => by
      rw [← List.take_append_drop k L, List.all_append, Bool.and_eq_true]
      refine ⟨by simpa using h 0 (by omega), ?_⟩
      apply all_of_batches f k nb (L.drop k)
      · intro b hb
        have := h (b + 1) (by omega)
        rwa [List.drop_drop, show k + k * b = k * (b + 1) by ring]
      · simp only [List.length_drop]
        have : k * (nb + 1) = k * nb + k := by ring
        omega

theorem modelRemainderValid_of_lower {f : ℝ → ℝ} {c : ReceiptCell} (hw : c.lo ≤ c.hi)
    (h : ∀ x : ℝ, (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) → (c.lower : ℝ) ≤ f x) :
    c.modelRemainderValid f hw := by
  intro x hx
  have := h x hx.1 hx.2
  simp only [ReceiptCell.model, ContourKit.horner, Rat.cast_zero, neg_zero, mul_zero,
    add_zero]
  linarith

theorem chunk_sound (j : ℕ) (hj : j < 32) (p : List ℚ) (e aL aR : ℚ)
    (hm : modelCheck j p e aL aR = true) (c : ReceiptCell)
    (hc : rowCheck j p e aL aR c = true) (x : ℝ) (hxlo : (c.lo : ℝ) ≤ x)
    (hxhi : x ≤ (c.hi : ℝ)) :
    (c.lower : ℝ) ≤ Li2Lean.P0.ConfigContourSelfPotential.pinnedWeta x := by
  simp only [modelCheck, Bool.and_eq_true, decide_eq_true_eq] at hm
  obtain ⟨⟨hok, haL, haR⟩, heps⟩ := hm
  simp only [rowCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hlo, -, hhi⟩, hokL⟩, hokR⟩, hlow⟩ := hc
  have hρ : (0 : ℚ) < chunkRho := by norm_num [chunkRho]
  set x0 := chunkX0 j
  set t : ℝ := x - x0 with htdef
  have hjR : (j : ℝ) ≤ 31 := by exact_mod_cast (by omega : j ≤ 31)
  have hloR : ((x0 - chunkRho : ℚ) : ℝ) ≤ c.lo := by exact_mod_cast hlo
  have hhiR : (c.hi : ℝ) ≤ ((x0 + chunkRho : ℚ) : ℝ) := by exact_mod_cast hhi
  have ht : |t| ≤ (chunkRho : ℝ) := by
    rw [abs_le]; push_cast at hloR hhiR; constructor <;> linarith
  have hx14 : (1 / 4 : ℝ) ≤ x := by
    have : ((x0 - chunkRho : ℚ) : ℝ) = 1 / 4 + (j : ℝ) / 32 := by
      simp only [x0, chunkX0, chunkRho]; push_cast; ring
    have h0 : (0 : ℝ) ≤ j := by positivity
    linarith
  have hx54 : x ≤ 5 / 4 := by
    have : ((x0 + chunkRho : ℚ) : ℝ) = 1 / 4 + ((j : ℝ) + 1) / 32 := by
      simp only [x0, chunkX0, chunkRho]; push_cast; ring
    linarith
  obtain ⟨g, hg, hsplit⟩ := splitAll_sound x0 chunkRho (chunkSL j) (chunkSR j)
    seriesDegree hρ wetaTerms hok
  have haL' : (splitAll x0 chunkRho (chunkSL j) (chunkSR j) seriesDegree wetaTerms).accL = aL :=
    haL
  have haR' : (splitAll x0 chunkRho (chunkSL j) (chunkSR j) seriesDegree wetaTerms).accR = aR :=
    haR
  have hxeq : (x0 : ℝ) + t = x := by rw [htdef]; ring
  -- the full model
  have hfull : (chunkModel j).Holds (fun t => g t + 2 * contourQ ((x0 : ℝ) + t) +
      -(((x0 : ℝ) + t) * Real.log 2) + constK) chunkRho := by
    unfold chunkModel
    apply Model.round_holds
    have hc := (contourAux_spec x0 chunkRho 49 le_rfl).2
    have hc' : (contourAux x0 49).1.Holds (fun t => 2 * contourQ ((x0 : ℝ) + t)) chunkRho := by
      intro t ht
      obtain ⟨cs, hcs, he⟩ := hc t ht
      refine ⟨cs, hcs, ?_⟩
      beta_reduce at he ⊢
      unfold contourQ; rw [Finset.mul_sum]; exact he
    exact Model.add_holds (Model.add_holds (Model.add_holds hg hc') (linModel_holds x0 _))
      (constModel_holds _)
  have hpoint := Model.point_sound (le_of_lt hρ) hfull p ht
  simp only [hxeq] at hpoint
  have hepsR : (((chunkModel j).eps + normErr chunkRho (chunkModel j).coeffs p : ℚ) : ℝ) ≤ e := by
    exact_mod_cast heps
  have hpoly := polyLower_le p (a := c.lo - x0) (b := c.hi - x0) (t := t)
    (by push_cast; linarith) (by push_cast; linarith)
  have hL := hullLower_le (C := aL) hokL hxlo hxhi
  have hR := hullLower_le (C := aR) hokR hxlo hxhi
  have hW := pinnedWeta_terms x hx14 hx54
  have hs := hsplit t
  rw [hxeq, haL', haR'] at hs
  have hlowR : (c.lower : ℝ) ≤ (hullLower aL (chunkSL j) c.lo c.hi : ℝ) +
      (hullLower aR (chunkSR j) c.lo c.hi : ℝ) +
      (polyLower p (c.lo - x0) (c.hi - x0) : ℝ) - e := by exact_mod_cast hlow
  have hab := (abs_le.mp hpoint).1
  calc (c.lower : ℝ) ≤ (hullLower aL (chunkSL j) c.lo c.hi : ℝ) +
      (hullLower aR (chunkSR j) c.lo c.hi : ℝ) +
      (polyLower p (c.lo - x0) (c.hi - x0) : ℝ) - e := hlowR
    _ ≤ (aL : ℝ) * primitive (x + chunkSL j) + (aR : ℝ) * primitive (x + chunkSR j) +
        (hornerR (castL p) t - e) := by linarith
    _ ≤ (aL : ℝ) * primitive (x + chunkSL j) + (aR : ℝ) * primitive (x + chunkSR j) +
        (g t + 2 * contourQ x + -(x * Real.log 2) + constK) := by linarith
    _ = Li2Lean.P0.ConfigContourSelfPotential.pinnedWeta x := by rw [hW, hs]; ring

theorem chunk_valid (j : ℕ) (hj : j < 32) (p : List ℚ) (e aL aR : ℚ)
    (hm : modelCheck j p e aL aR = true) (rows : List ReceiptCell)
    (hr : rowsCheck j p e aL aR rows = true) :
    ∀ c ∈ rows, ∀ hw : c.lo ≤ c.hi,
      c.modelRemainderValid Li2Lean.P0.ConfigContourSelfPotential.pinnedWeta hw := by
  intro c hc hw
  unfold rowsCheck at hr
  rw [List.all_eq_true] at hr
  exact modelRemainderValid_of_lower hw (fun x hxlo hxhi =>
    chunk_sound j hj p e aL aR hm c (hr c hc) x hxlo hxhi)

end Li2Lean.P0.CA.Pinned
