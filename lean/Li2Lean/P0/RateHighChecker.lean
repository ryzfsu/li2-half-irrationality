/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateLowChecker

/-!
# Certified high-ratio cells (v13 Table `tab:p0-high-potentials`)

For `p > g = m/2` the negated source entry bound depends only on the carry
bits, the base-`p` digits, the block, and whether the residues agree.  Integer
row and column potentials indexed by `(group, digit, block)` that dominate
every realizable pair give, along any permutation, the bound
`Σ_rows u + Σ_cols v`, an exact affine form in `(m, p)` on a certified cell.
-/

namespace Li2Lean.P0.Integerization

open Finset

/-- The first-moment bit `θ` for carry `κ` and digit `d`. -/
def p0HTheta (κ d : ℕ) : ℤ := if 1 ≤ d then (κ : ℤ) - 1 else 0

/-- Negated high-range entry bound in terms of carries, digits, block and residue
agreement. -/
def p0WHigh (κi di : ℕ) (lower : Bool) (κj dj : ℕ) (same : Bool) : ℤ :=
  if same ∧ di = dj then (if lower then (if 1 ≤ di then 2 - (κi : ℤ) else 0) else 0)
  else (if same then 1 else 0) -
    (if lower then min (p0HTheta κi di) (p0HTheta κj dj) else min (κi : ℤ) κj)

theorem p0_eq_iff_mod_div {p i j : ℕ} : i = j ↔ (i % p = j % p ∧ i / p = j / p) := by
  constructor
  · rintro rfl; exact ⟨rfl, rfl⟩
  · rintro ⟨h1, h2⟩
    rw [← Nat.div_add_mod i p, ← Nat.div_add_mod j p, h1, h2]

theorem p0RateWeight_high (p m : ℕ) (hgp : m / 2 < p) (r c : Fin (2 * m)) :
    p0RateWeight p m r c =
      p0WHigh (p0PrimeCarry p (m / 2) (p0SourceRowIndex m r)) (p0SourceRowIndex m r / p)
        (decide (¬ r.val < m)) (p0PrimeCarry p (m / 2) c.val) (c.val / p)
        (decide (p0SourceRowIndex m r % p = c.val % p)) := by
  have hp : 0 < p := by omega
  have hng : ¬ p ≤ m / 2 := by omega
  have hθ : ∀ n, p0PrimeTheta p (m / 2) n = p0HTheta (p0PrimeCarry p (m / 2) n) (n / p) := by
    intro n
    unfold p0PrimeTheta p0HTheta
    have : (p ≤ n ∨ p ≤ m / 2) ↔ 1 ≤ n / p := by
      rw [Nat.le_div_iff_mul_le hp]; omega
    by_cases h : 1 ≤ n / p
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h]
  have hdiag : ∀ n, p0PrimeDiagBLower p (m / 2) n =
      if 1 ≤ n / p then (p0PrimeCarry p (m / 2) n : ℤ) - 2 else 0 := by
    intro n
    unfold p0PrimeDiagBLower
    have : (p ≤ n ∨ 2 * p ≤ m / 2) ↔ 1 ≤ n / p := by
      rw [Nat.le_div_iff_mul_le hp]; omega
    by_cases h : 1 ≤ n / p
    · rw [if_pos (this.mpr h), if_pos h]
    · rw [if_neg (fun h' => h (this.mp h')), if_neg h, if_neg hng]
  unfold p0RateWeight p0PrimeEntryLower p0WHigh
  simp only [hθ, hdiag]
  generalize p0SourceRowIndex m r = i
  generalize c.val = j
  have hij : i = j ↔ (i % p = j % p ∧ i / p = j / p) := p0_eq_iff_mod_div
  by_cases hr : r.val < m
  · simp only [hr, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, if_neg hng]
    by_cases he : i = j
    · subst he
      simp
    · have hne : ¬ (i % p = j % p ∧ i / p = j / p) := fun h => he (hij.mpr h)
      by_cases hs : i % p = j % p
      · have hd : ¬ i / p = j / p := fun h => hne ⟨hs, h⟩
        simp [he, hs, hd]
      · simp [he, hs]
  · simp only [hr, not_false_eq_true, decide_true, ↓reduceIte]
    by_cases he : i = j
    · subst he
      simp only [and_self, ↓reduceIte, decide_true]
      split_ifs <;> ring
    · have hne : ¬ (i % p = j % p ∧ i / p = j / p) := fun h => he (hij.mpr h)
      by_cases hs : i % p = j % p
      · have hd : ¬ i / p = j / p := fun h => hne ⟨hs, h⟩
        simp [he, hs, hd]
      · simp [he, hs]

/-- Sum of `f (a + k)` for `k < n`, as a list computation. -/
def p0LSum (a n : ℕ) (f : ℕ → ℤ) : ℤ := ((List.range n).map (fun k => f (a + k))).sum

theorem p0LSum_eq (a n : ℕ) (f : ℕ → ℤ) :
    p0LSum a n f = ∑ d ∈ Ico a (a + n), f d := by
  rw [Finset.sum_Ico_eq_sum_range, Nat.add_sub_cancel_left]
  unfold p0LSum
  induction n with
  | zero => simp
  | succ n ih => rw [List.range_succ, List.map_append, List.sum_append, ih, Finset.sum_range_succ]; simp

/-- A certified high cell with integer potentials and a profile line. -/
structure HCell where
  cell : RCell
  up : List (ℕ × ℕ × Bool × ℤ)
  vp : List (ℕ × ℕ × ℤ)
  icpt : ℚ
  slope : ℚ
  deriving DecidableEq

namespace HCell

def U (h : HCell) (g d : ℕ) (b : Bool) : ℤ :=
  match h.up.find? (fun x => decide (x.1 = g ∧ x.2.1 = d ∧ x.2.2.1 = b)) with
  | some x => x.2.2.2
  | none => 0

def V (h : HCell) (g d : ℕ) : ℤ :=
  match h.vp.find? (fun x => decide (x.1 = g ∧ x.2.1 = d)) with
  | some x => x.2.2
  | none => 0

def dLo (h : HCell) (g : Fin 5) : ℕ := h.cell.A + if h.cell.pattern g 0 then 1 else 0
def dHi (h : HCell) (g : Fin 5) : ℕ := h.cell.B + if h.cell.pattern g 1 then 1 else 0
def dJ (h : HCell) (g : Fin 5) : ℕ := h.cell.C + if h.cell.pattern g 2 then 1 else 0
def kap (h : HCell) (g : Fin 5) : ℕ := if h.cell.pattern g 3 then 0 else 1

/-- All realizable row/column type pairs satisfy the potential inequality. -/
def pairsOK (h : HCell) : Bool :=
  (List.finRange 5).all fun g1 =>
    (List.range' (h.dLo g1) (h.dHi g1 - h.dLo g1)).all fun d1 =>
      [false, true].all fun b =>
        (List.finRange 5).all fun g2 =>
          (List.range (h.dJ g2)).all fun d2 =>
            decide (p0WHigh (h.kap g1) d1 b (h.kap g2) d2 false ≤ h.U g1 d1 b + h.V g2 d2) &&
            (if g1 = g2 then
              decide (p0WHigh (h.kap g1) d1 b (h.kap g2) d2 true ≤ h.U g1 d1 b + h.V g2 d2)
            else true)

/-- Per-residue potential mass of group `g`. -/
def gmass (h : HCell) (g : Fin 5) : ℤ :=
  p0LSum (h.dLo g) (h.dHi g - h.dLo g) (fun d => h.U g d false + h.U g d true) +
    p0LSum 0 (h.dJ g) (fun d => h.V g d)

def objective (h : HCell) : RAff :=
  p0AffSum5 (fun g => RAff.smul (h.gmass g) (h.cell.width g))

def ok (h : HCell) : Bool :=
  h.cell.ok && decide (1 / 2 ≤ h.cell.lo) &&
    (List.finRange 5).all (fun g => decide (h.dLo g ≤ h.dHi g)) && h.pairsOK &&
    ((⟨h.icpt, h.slope⟩ : RAff) - h.objective).nonnegOn h.cell.lo h.cell.hi

end HCell

/-- Group index of a residue: the number of thresholds at or below it. -/
def p0GroupIdx (m p v : ℕ) : ℕ := (univ.filter (fun k : Fin 4 => p0Thr m p k ≤ v)).card

section

variable {c : RCell} {m p : ℕ}

theorem p0GroupIdx_eq (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (g : Fin 5) (v : ℕ)
    (hv1 : p0CutAct c m p g.castSucc ≤ v) (hv2 : v < p0CutAct c m p g.succ) :
    p0GroupIdx m p v = g.val := by
  obtain ⟨_, hperm, _⟩ := p0Cell_ok_parts hc
  have hsurj : Function.Surjective c.perm := hperm
  have hinj : Function.Injective c.perm := Finite.injective_iff_surjective.mpr hsurj
  have bits := p0Cell_bits hc h4 hm hp hlo hhi g v hv1 hv2
  have hset : univ.filter (fun k : Fin 4 => p0Thr m p k ≤ v) =
      (univ.filter (fun j : Fin 4 => j.val < g.val)).map ⟨c.perm, hinj⟩ := by
    ext k
    obtain ⟨j, rfl⟩ := hsurj k
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map,
      Function.Embedding.coeFn_mk]
    have hb := bits (c.perm j)
    constructor
    · intro hle
      refine ⟨j, ?_, rfl⟩
      have hf : decide (v < p0Thr m p (c.perm j)) = false := by simp; omega
      rw [hf] at hb
      simp only [RCell.pattern] at hb
      by_contra hcon
      have : ∃ j' : Fin 4, g.val ≤ j'.val ∧ c.perm j' = c.perm j := ⟨j, by omega, rfl⟩
      simp [this] at hb
    · rintro ⟨j', hj', hjj⟩
      have := hinj hjj
      subst this
      have hpat : c.pattern g (c.perm j') = false := by
        simp only [RCell.pattern, decide_eq_false_iff_not, not_exists, not_and]
        intro j'' hj'' hjj''
        have := hinj hjj''
        subst this
        omega
      rw [hpat] at hb
      simp at hb
      omega
  unfold p0GroupIdx
  rw [hset, Finset.card_map]
  have : (univ.filter (fun j : Fin 4 => j.val < g.val)).card = g.val := by
    have hg := g.isLt
    have e : univ.filter (fun j : Fin 4 => j.val < g.val) =
        (Finset.range g.val).attachFin (fun n hn => by simp at hn; omega) := by
      ext j; simp
    rw [e, Finset.card_attachFin, Finset.card_range]
  exact this

theorem p0_digit_ge {p N i v : ℕ} (hp : 0 < p) (hv : i % p = v) (hN : N ≤ i) :
    p0ResCnt p N v ≤ i / p := by
  have hvp : v < p := hv ▸ Nat.mod_lt i hp
  rw [p0ResCnt_eq hp hvp]
  have hi := Nat.div_add_mod i p
  have hNd := Nat.div_add_mod N p
  have hNm := Nat.mod_lt N hp
  rw [hv] at hi
  generalize i / p = a at *
  generalize N / p = b at *
  generalize N % p = r at *
  rcases Nat.lt_or_ge a b with hlt | hge
  · have h1 : p * (a + 1) ≤ p * b := Nat.mul_le_mul_left p hlt
    rw [Nat.mul_succ] at h1
    generalize p * a = A at *
    generalize p * b = B at *
    omega
  · rcases Nat.lt_or_ge b a with hlt' | hle'
    · split <;> omega
    · have hab : a = b := le_antisymm hle' hge
      subst hab
      generalize p * a = A at *
      split <;> omega

theorem p0_digit_lt {p N i v : ℕ} (hp : 0 < p) (hv : i % p = v) (hN : i < N) :
    i / p < p0ResCnt p N v := by
  have hvp : v < p := hv ▸ Nat.mod_lt i hp
  rw [p0ResCnt_eq hp hvp]
  have hi := Nat.div_add_mod i p
  have hNd := Nat.div_add_mod N p
  have hNm := Nat.mod_lt N hp
  rw [hv] at hi
  generalize i / p = a at *
  generalize N / p = b at *
  generalize N % p = r at *
  rcases Nat.lt_or_ge a b with hlt | hge
  · split <;> omega
  · rcases Nat.lt_or_ge b a with hlt' | hle'
    · have h1 : p * (b + 1) ≤ p * a := Nat.mul_le_mul_left p hlt'
      rw [Nat.mul_succ] at h1
      generalize p * a = A at *
      generalize p * b = B at *
      omega
    · have hab : a = b := le_antisymm hle' hge
      subst hab
      generalize p * a = A at *
      split <;> omega

end

section

variable {m p : ℕ}

theorem p0SourceRowIndex_range (m : ℕ) (r : Fin (2 * m)) :
    m / 4 ≤ p0SourceRowIndex m r ∧ p0SourceRowIndex m r < m / 4 + m := by
  have hr := r.isLt
  unfold p0SourceRowIndex
  split <;> omega

theorem HCell.ok_parts {h : HCell} (hok : h.ok = true) :
    h.cell.ok = true ∧ 1 / 2 ≤ h.cell.lo ∧ (∀ g : Fin 5, h.dLo g ≤ h.dHi g) ∧
      h.pairsOK = true ∧
      ((⟨h.icpt, h.slope⟩ : RAff) - h.objective).nonnegOn h.cell.lo h.cell.hi = true := by
  simp only [HCell.ok, Bool.and_eq_true, List.all_eq_true, List.mem_finRange, forall_const,
    decide_eq_true_eq] at hok
  obtain ⟨⟨⟨⟨hc, hhalf⟩, hd⟩, hpairs⟩, hobj⟩ := hok
  exact ⟨hc, hhalf, hd, hpairs, hobj⟩

/-- Residue data of a group member in a certified cell. -/
theorem p0Cell_member {h : HCell} (hc : h.cell.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : h.cell.lo * m < p) (hhi : p < h.cell.hi * m) (v : ℕ) (hv : v < p) :
    ∃ g : Fin 5, p0GroupIdx m p v = g.val ∧
      p0ResCnt p (m / 4) v = h.dLo g ∧ p0ResCnt p (m / 4 + m) v = h.dHi g ∧
      p0ResCnt p (2 * m) v = h.dJ g ∧ p0PrimeCarry p (m / 2) v = h.kap g := by
  obtain ⟨g, hv1, hv2⟩ := p0Cell_group_exists hc h4 hm hp hlo hhi v hv
  obtain ⟨_, e0, e1, e2, e3⟩ := p0Cell_resCnt hc h4 hm hp hlo hhi g v hv1 hv2
  refine ⟨g, p0GroupIdx_eq hc h4 hm hp hlo hhi g v hv1 hv2, ?_, ?_, ?_, ?_⟩
  · have : (p0ResCnt p (m / 4) v : ℤ) = (h.dLo g : ℤ) := by
      rw [e0]; unfold HCell.dLo p0B2Z; split <;> simp
    exact_mod_cast this
  · have : (p0ResCnt p (m / 4 + m) v : ℤ) = (h.dHi g : ℤ) := by
      rw [e1]; unfold HCell.dHi p0B2Z; split <;> simp
    exact_mod_cast this
  · have : (p0ResCnt p (2 * m) v : ℤ) = (h.dJ g : ℤ) := by
      rw [e2]; unfold HCell.dJ p0B2Z; split <;> simp
    exact_mod_cast this
  · have hκ := p0PrimeCarry_le_one p (m / 2) v
    unfold HCell.kap
    by_cases hpat : h.cell.pattern g 3 = true
    · rw [if_pos hpat]; exact e3.mpr hpat
    · rw [if_neg hpat]
      have : p0PrimeCarry p (m / 2) v ≠ 0 := fun h0 => hpat (e3.mp h0)
      omega

/-- Soundness of a certified high cell. -/
theorem p0High_cell_bound (h : HCell) (hok : h.ok = true) (h4 : 4 ∣ m) (hm : 0 < m)
    (hp : 0 < p) (hlo : h.cell.lo * m < p) (hhi : p < h.cell.hi * m) :
    ((p0RateAssignMax p m : ℤ) : ℚ) ≤ h.icpt * m + h.slope * p := by
  obtain ⟨hc, hhalf, hdl, hpairs, hobj⟩ := HCell.ok_parts hok
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hgp : m / 2 < p := by
    have h1 : (m : ℚ) / 2 < p := by nlinarith
    obtain ⟨t, rfl⟩ := h4
    have : ((2 * t : ℕ) : ℚ) < p := by push_cast at h1 ⊢; linarith
    have : 2 * t < p := by exact_mod_cast this
    omega
  set G := fun v => p0GroupIdx m p v
  let Ur : Fin (2 * m) → ℤ := fun r =>
    h.U (G (p0SourceRowIndex m r % p)) (p0SourceRowIndex m r / p) (decide (¬ r.val < m))
  let Vc : Fin (2 * m) → ℤ := fun c => h.V (G (c.val % p)) (c.val / p)
  -- pair inequality
  have hpair : ∀ r c : Fin (2 * m), p0RateWeight p m r c ≤ Ur r + Vc c := by
    intro r c
    rw [p0RateWeight_high p m hgp r c]
    simp only [Ur, Vc, G]
    have hiR := p0SourceRowIndex_range m r
    have hcl := c.isLt
    generalize decide (¬ r.val < m) = b
    generalize p0SourceRowIndex m r = i at *
    generalize c.val = j at *
    obtain ⟨g1, hG1, hl1, hh1, _, hk1⟩ :=
      p0Cell_member (h := h) hc h4 hm hp hlo hhi (i % p) (Nat.mod_lt _ hp)
    obtain ⟨g2, hG2, _, _, hj2, hk2⟩ :=
      p0Cell_member (h := h) hc h4 hm hp hlo hhi (j % p) (Nat.mod_lt _ hp)
    have hd1lo : h.dLo g1 ≤ i / p := hl1 ▸ p0_digit_ge hp rfl hiR.1
    have hd1hi : i / p < h.dHi g1 := hh1 ▸ p0_digit_lt hp rfl hiR.2
    have hd2 : j / p < h.dJ g2 := hj2 ▸ p0_digit_lt hp rfl (by omega)
    have hκi : p0PrimeCarry p (m / 2) i = h.kap g1 := by rw [← p0PrimeCarry_mod]; exact hk1
    have hκj : p0PrimeCarry p (m / 2) j = h.kap g2 := by rw [← p0PrimeCarry_mod]; exact hk2
    rw [hκi, hκj, hG1, hG2]
    have hall := hpairs
    simp only [HCell.pairsOK, List.all_eq_true, List.mem_finRange, forall_const,
      List.mem_range'_1, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at hall
    have hb : b ∈ [false, true] := by cases b <;> simp
    have hx := hall g1 (i / p) ⟨hd1lo, by omega⟩ b hb g2 (j / p) hd2
    obtain ⟨hfalse, htrue⟩ := hx
    by_cases hs : i % p = j % p
    · have hg : g1 = g2 := by
        apply Fin.ext
        rw [← hG1, ← hG2, hs]
      subst hg
      rw [if_pos rfl] at htrue
      simpa [hs] using htrue
    · simpa [hs] using hfalse
  -- sum of potentials
  have hsumU : ∑ r, Ur r = ∑ g : Fin 5,
      (((p0CutAct h.cell m p g.succ : ℕ) : ℤ) - p0CutAct h.cell m p g.castSucc) *
        (∑ d ∈ Ico (h.dLo g) (h.dHi g), (h.U g d false + h.U g d true)) := by
    have e1 : ∑ r, Ur r = ∑ x ∈ range m,
        (h.U (G ((m / 4 + x) % p)) ((m / 4 + x) / p) false +
          h.U (G ((m / 4 + x) % p)) ((m / 4 + x) / p) true) := by
      simp only [Ur, p0SourceRowIndex]
      rw [Fin.sum_univ_eq_sum_range (fun x => h.U (G ((m / 4 + if x < m then x else x - m) % p))
        ((m / 4 + if x < m then x else x - m) / p) (decide (¬ x < m))), two_mul,
        Finset.sum_range_add, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x hx
      have hxm := Finset.mem_range.mp hx
      simp [hxm]
    rw [e1, p0_sum_window_digits hp
      (fun v d => h.U (G v) d false + h.U (G v) d true) (m / 4) m]
    apply p0Cell_group_sum hc h4 hm hp hlo hhi
    intro g v hv1 hv2
    obtain ⟨hvp, _, _, _, _⟩ := p0Cell_resCnt hc h4 hm hp hlo hhi g v hv1 hv2
    obtain ⟨g', hG, hl, hh, _, _⟩ := p0Cell_member (h := h) hc h4 hm hp hlo hhi v hvp
    have hgg : g' = g := by
      apply Fin.ext
      rw [← hG]
      exact p0GroupIdx_eq hc h4 hm hp hlo hhi g v hv1 hv2
    subst hgg
    simp only [G, hG, hl, hh]
  have hsumV : ∑ c, Vc c = ∑ g : Fin 5,
      (((p0CutAct h.cell m p g.succ : ℕ) : ℤ) - p0CutAct h.cell m p g.castSucc) *
        (∑ d ∈ range (h.dJ g), h.V g d) := by
    have e1 : ∑ c, Vc c = ∑ x ∈ range (2 * m), h.V (G (x % p)) (x / p) := by
      simp only [Vc]
      exact Fin.sum_univ_eq_sum_range (fun x => h.V (G (x % p)) (x / p)) (2 * m)
    rw [e1, p0_sum_range_digits hp (fun v d => h.V (G v) d) (2 * m)]
    apply p0Cell_group_sum hc h4 hm hp hlo hhi
    intro g v hv1 hv2
    obtain ⟨hvp, _, _, _, _⟩ := p0Cell_resCnt hc h4 hm hp hlo hhi g v hv1 hv2
    obtain ⟨g', hG, _, _, hj, _⟩ := p0Cell_member (h := h) hc h4 hm hp hlo hhi v hvp
    have hgg : g' = g := by
      apply Fin.ext
      rw [← hG]
      exact p0GroupIdx_eq hc h4 hm hp hlo hhi g v hv1 hv2
    subst hgg
    simp only [G, hG, hj]
  have hgm : ∀ g : Fin 5, h.gmass g =
      (∑ d ∈ Ico (h.dLo g) (h.dHi g), (h.U g d false + h.U g d true)) +
        ∑ d ∈ range (h.dJ g), h.V g d := by
    intro g
    unfold HCell.gmass
    rw [p0LSum_eq, p0LSum_eq, Nat.add_sub_cancel' (hdl g), zero_add, Finset.range_eq_Ico]
  have hobjval : (((∑ r, Ur r + ∑ c, Vc c : ℤ)) : ℚ) = h.objective.val m p := by
    rw [hsumU, hsumV, ← Finset.sum_add_distrib]
    unfold HCell.objective
    rw [p0AffSum5_val]
    push_cast
    apply Finset.sum_congr rfl
    intro g _
    rw [RAff.val_smul, hgm g]
    have hw : (((p0CutAct h.cell m p g.succ : ℕ) : ℚ) - p0CutAct h.cell m p g.castSucc) =
        (h.cell.width g).val m p := by
      unfold RCell.width
      rw [RAff.val_sub, ← p0Cell_cut_val hc h4 hm hp hlo hhi,
        ← p0Cell_cut_val hc h4 hm hp hlo hhi]
    rw [← hw]
    push_cast
    ring
  have hmax : p0RateAssignMax p m ≤ ∑ r, Ur r + ∑ c, Vc c := by
    apply p0RateAssignMax_le
    intro σ
    calc ∑ i, p0RateWeight p m (σ i) i ≤ ∑ i, (Ur (σ i) + Vc i) :=
          Finset.sum_le_sum (fun i _ => hpair (σ i) i)
      _ = ∑ r, Ur r + ∑ c, Vc c := by
          rw [Finset.sum_add_distrib, Equiv.sum_comp σ Ur]
  have hP := RAff.nonneg_of_nonnegOn _ hmQ hlo.le hhi.le hobj
  rw [RAff.val_sub, RAff.val_mk] at hP
  have hmaxQ : ((p0RateAssignMax p m : ℤ) : ℚ) ≤ ((∑ r, Ur r + ∑ c, Vc c : ℤ) : ℚ) := by
    exact_mod_cast hmax
  rw [hobjval] at hmaxQ
  linarith

end


end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0RateWeight_high
#print axioms Li2Lean.P0.Integerization.p0High_cell_bound
