/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.FourierConst

/-!
# Reflected evaluator of the contour closed form and its derivative

`WI c s` and `DI c s` are computable rational intervals; when `cos θ = c`
and `sin θ = s` they contain `Wform θ` and `W1 θ` respectively.
-/

namespace Li2Lean.P0.CA.Contour

open QI Li2Lean.P0.ConfigContourSelfPotential Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigSegment

/-! ## Generic interval version of `segComb` -/

def ρpq (j : ℕ) : ℚ := 32 * (ConfigData.pinnedMassUnits.getD j 0 : ℚ) / 1000000000000
def ρfq (j : ℕ) : ℚ := 32 * (ConfigData.frequencyMassUnits.getD j 0 : ℚ) / 1000000000000

theorem ρpq_eq (j : ℕ) : ((ρpq j : ℚ) : ℝ) = ρp j := by
  simp [ρpq, ρp, referenceDensity, ConfigData.referenceDenominator]
theorem ρfq_eq (j : ℕ) : ((ρfq j : ℚ) : ℝ) = ρf j := by
  simp [ρfq, ρf, referenceDensity, ConfigData.referenceDenominator]

def segCombI (p f : ℕ → QI) (z0 z2 lin cst : QI) : QI :=
  sub (sub (sub (add (sub (p 0) (p 32)) (sub z0 z2)) (add (add lin (sub (f 0) z0)) cst))
      (smul 2 (sumIdx 32 (fun j => smul (ρpq j) (sub (p j) (p (j + 1)))))))
    (sumIdx 160 (fun j => smul (ρfq j) (sub (f (j + 1)) (f j))))

theorem segCombI_mem {p f : ℕ → QI} {z0 z2 lin cst : QI} {g : ℝ → ℝ} {L C : ℝ}
    (hp : ∀ j ≤ 32, (p j).mem (g (-(1 / 4 + (j : ℝ) / 32))))
    (hf : ∀ j ≤ 160, (f j).mem (g (1 / 2 + (j : ℝ) / 32)))
    (h0 : z0.mem (g 0)) (h2 : z2.mem (g (-2))) (hl : lin.mem L) (hc : cst.mem C) :
    (segCombI p f z0 z2 lin cst).mem (segComb g L C) := by
  have hp0 := hp 0 (by norm_num)
  have hp32 := hp 32 (by norm_num)
  have hf0 := hf 0 (by norm_num)
  norm_num at hp0 hp32 hf0
  have s1 : (sumIdx 32 (fun j => smul (ρpq j) (sub (p j) (p (j + 1))))).mem
      (∑ j ∈ Finset.range 32, ρp j * (g (-pL j) - g (-pR j))) := by
    apply mem_sumIdx
    intro j hj
    have := mem_smul (ρpq j) (mem_sub (hp j (by omega)) (hp (j + 1) (by omega)))
    rw [ρpq_eq] at this
    refine mem_of_eq this ?_
    simp only [pL, pR, referenceCellLeft, referenceCellRight]
  have s2 : (sumIdx 160 (fun j => smul (ρfq j) (sub (f (j + 1)) (f j)))).mem
      (∑ j ∈ Finset.range 160, ρf j * (g (fR j) - g (fL j))) := by
    apply mem_sumIdx
    intro j hj
    have := mem_smul (ρfq j) (mem_sub (hf (j + 1) (by omega)) (hf j (by omega)))
    rw [ρfq_eq] at this
    refine mem_of_eq this ?_
    simp only [fL, fR, referenceCellLeft, referenceCellRight]
  unfold segCombI segComb
  have := mem_sub (mem_sub (mem_sub (mem_add (mem_sub hp0 hp32) (mem_sub h0 h2))
    (mem_add (mem_add hl (mem_sub hf0 h0)) hc)) (by simpa using mem_smul 2 s1)) s2
  refine mem_of_eq this ?_
  norm_num

/-! ## Edge values -/

structure EV where
  g : QI
  l : QI
  a : QI

def edgeOf (u Y : ℚ) (l a : QI) : EV := ⟨rnd (add (smul u (sub l (pt 1))) (smul Y a)), l, a⟩

def edge (u Y : ℚ) : EV := edgeOf u Y (smul (1 / 2) (logI (u ^ 2 + Y ^ 2))) (atanI (u / Y))

def EV.ok (e : EV) (u Y : ℝ) : Prop :=
  e.g.mem (Gr u Y) ∧ e.l.mem (Real.log (u ^ 2 + Y ^ 2) / 2) ∧ e.a.mem (Real.arctan (u / Y))

theorem edge_ok (u Y : ℚ) : (edge u Y).ok u Y := by
  have hl : (smul (1 / 2) (logI (u ^ 2 + Y ^ 2))).mem (Real.log ((u : ℝ) ^ 2 + (Y : ℝ) ^ 2) / 2) := by
    have := mem_smul (1 / 2) (logI_mem (q := u ^ 2 + Y ^ 2) (by positivity))
    refine mem_of_eq this ?_
    push_cast; ring
  have ha : (atanI (u / Y)).mem (Real.arctan ((u : ℝ) / (Y : ℝ))) := by
    have := atanI_mem (u / Y); push_cast at this; exact this
  refine ⟨?_, hl, ha⟩
  unfold edge edgeOf
  apply mem_rnd
  have := mem_add (mem_smul u (mem_sub hl (mem_pt 1))) (mem_smul Y ha)
  refine mem_of_eq this ?_
  unfold Gr; push_cast; ring

/-! ## The ellipse point and edge lists -/

def ellXq (c : ℚ) : ℚ := 11281 / 10000 + 12783 / 10000 * c
def ellYq (s : ℚ) : ℚ := 229 / 200 * s

def pEdges (X Y : ℚ) : List EV := (List.range 33).map (fun (j : ℕ) => edge (X - (1 / 4 + (j : ℚ) / 32)) Y)
def fEdges (X Y : ℚ) : List EV := (List.range 161).map (fun (j : ℕ) => edge (X + (1 / 2 + (j : ℚ) / 32)) Y)

def dflt : EV := ⟨pt 0, pt 0, pt 0⟩

theorem getD_map_range {α : Type} (f : ℕ → α) (d : α) {n j : ℕ} (hj : j < n) :
    ((List.range n).map f).getD j d = f j := by
  rw [List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, List.getElem_range]

theorem pEdges_get (X Y : ℚ) {j : ℕ} (hj : j ≤ 32) :
    (pEdges X Y).getD j dflt = edge (X - (1 / 4 + (j : ℚ) / 32)) Y := by
  unfold pEdges; exact getD_map_range _ _ (by omega : j < 33)

theorem fEdges_get (X Y : ℚ) {j : ℕ} (hj : j ≤ 160) :
    (fEdges X Y).getD j dflt = edge (X + (1 / 2 + (j : ℚ) / 32)) Y := by
  unfold fEdges; exact getD_map_range _ _ (by omega : j < 161)

/-! ## Fourier part by an exact Chebyshev pass -/

structure FS where
  c0 : ℚ
  c1 : ℚ
  s0 : ℚ
  s1 : ℚ
  v : QI
  d : QI

def fstate (c s : ℚ) : ℕ → FS
  | 0 => ⟨1, c, 0, s, pt 0, pt 0⟩
  | n + 1 =>
      let t := fstate c s n
      ⟨t.c1, 2 * c * t.c1 - t.c0, t.s1, 2 * c * t.s1 - t.s0,
        rnd (add t.v (smul t.c1 (bLit.getD n ⟨0, 0⟩))),
        rnd (add t.d (smul ((n + 1 : ℚ) * t.s1) (bLit.getD n ⟨0, 0⟩)))⟩

theorem sin_rec (m : ℕ) (x : ℝ) :
    Real.sin ((m + 2 : ℕ) * x) = 2 * Real.cos x * Real.sin ((m + 1 : ℕ) * x) -
      Real.sin (m * x) := by
  have h1 : ((m + 2 : ℕ) : ℝ) * x = ((m + 1 : ℕ) : ℝ) * x + x := by push_cast; ring
  have h2 : (m : ℝ) * x = ((m + 1 : ℕ) : ℝ) * x - x := by push_cast; ring
  rw [h1, h2, Real.sin_add, Real.sin_sub]
  ring

theorem fstate_spec {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) (n : ℕ)
    (hn : n ≤ 48) :
    ((fstate c s n).c0 : ℝ) = Real.cos (n * θ) ∧
    ((fstate c s n).c1 : ℝ) = Real.cos ((n + 1 : ℕ) * θ) ∧
    ((fstate c s n).s0 : ℝ) = Real.sin (n * θ) ∧
    ((fstate c s n).s1 : ℝ) = Real.sin ((n + 1 : ℕ) * θ) ∧
    (fstate c s n).v.mem (∑ k ∈ Finset.range n, bR k * Real.cos ((k + 1 : ℝ) * θ)) ∧
    (fstate c s n).d.mem (∑ k ∈ Finset.range n, bR k * ((k + 1 : ℝ) * Real.sin ((k + 1 : ℝ) * θ))) := by
  induction n with
  | zero =>
      simp only [fstate]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> simp [hc, hs, QI.mem, pt]
  | succ n ih =>
      obtain ⟨a0, a1, b0, b1, hv, hd⟩ := ih (by omega)
      have hb := bLit_mem (n := n) (by omega)
      simp only [fstate]
      refine ⟨a1, ?_, b1, ?_, ?_, ?_⟩
      · rw [show n + 1 + 1 = n + 2 from rfl, cos_rec n θ, ← a1, ← a0, hc]; push_cast; ring
      · rw [show n + 1 + 1 = n + 2 from rfl, sin_rec n θ, ← b1, ← b0, hc]; push_cast; ring
      · apply mem_rnd
        rw [Finset.sum_range_succ]
        have := mem_add hv (mem_smul (fstate c s n).c1 hb)
        refine mem_of_eq this ?_
        rw [a1]; push_cast; ring
      · apply mem_rnd
        rw [Finset.sum_range_succ]
        have := mem_add hd (mem_smul ((n + 1 : ℚ) * (fstate c s n).s1) hb)
        refine mem_of_eq this ?_
        push_cast; rw [b1]; push_cast; ring

/-! ## The value and derivative evaluators -/

def MLC : QI := smul (267885951940 / 1000000000000) (logI (24233 / 20000))

theorem MLC_mem : MLC.mem (contourMass * Real.log contourScale) := by
  have := mem_smul (267885951940 / 1000000000000) (logI_mem (q := 24233 / 20000) (by norm_num))
  refine mem_of_eq this ?_
  simp [contourMass, contourScale]

def WIcore (X Y : ℚ) (pe fe : List EV) (e0 e2 : EV) (F : FS) : QI :=
  sub (segCombI (fun j => (pe.getD j dflt).g) (fun j => (fe.getD j dflt).g) e0.g e2.g
      (smul X L2) (add (pt (1 / 2)) (smul (1 / 2) L2)))
    (smul 2 (sub MLC F.v))

def DIcore (Xp Yp : ℚ) (pe fe : List EV) (e0 e2 : EV) (F : FS) : QI :=
  let ds : EV → QI := fun e => add (smul Xp e.l) (smul Yp e.a)
  sub (segCombI (fun j => ds (pe.getD j dflt)) (fun j => ds (fe.getD j dflt)) (ds e0) (ds e2)
      (smul Xp L2) (pt 0))
    (smul 2 F.d)

def WI (c s : ℚ) : QI :=
  WIcore (ellXq c) (ellYq s) (pEdges (ellXq c) (ellYq s)) (fEdges (ellXq c) (ellYq s))
    (edge (ellXq c) (ellYq s)) (edge (ellXq c - 2) (ellYq s)) (fstate c s 48)

def DI (c s : ℚ) : QI :=
  DIcore (-(12783 / 10000) * s) (229 / 200 * c) (pEdges (ellXq c) (ellYq s))
    (fEdges (ellXq c) (ellYq s)) (edge (ellXq c) (ellYq s)) (edge (ellXq c - 2) (ellYq s))
    (fstate c s 48)

/-- Value and derivative together (one shared edge evaluation). -/
def WDI (c s : ℚ) : QI × QI :=
  let X := ellXq c
  let Y := ellYq s
  let pe := pEdges X Y
  let fe := fEdges X Y
  let e0 := edge X Y
  let e2 := edge (X - 2) Y
  let F := fstate c s 48
  (WIcore X Y pe fe e0 e2 F, DIcore (-(12783 / 10000) * s) (229 / 200 * c) pe fe e0 e2 F)

theorem WDI_eq (c s : ℚ) : WDI c s = (WI c s, DI c s) := rfl

theorem ellX_eq {θ : ℝ} {c : ℚ} (hc : Real.cos θ = c) : ellX θ = ((ellXq c : ℚ) : ℝ) := by
  simp [ellX, ellXq, hc]

theorem ellY_eq {θ : ℝ} {s : ℚ} (hs : Real.sin θ = s) : ellY θ = ((ellYq s : ℚ) : ℝ) := by
  simp [ellY, ellYq, hs]

theorem pEdge_ok (X Y : ℚ) {j : ℕ} (hj : j ≤ 32) :
    ((pEdges X Y).getD j dflt).ok ((X : ℝ) + -(1 / 4 + (j : ℝ) / 32)) Y := by
  rw [pEdges_get X Y hj]
  have := edge_ok (X - (1 / 4 + (j : ℚ) / 32)) Y
  push_cast at this ⊢
  rwa [← sub_eq_add_neg]

theorem fEdge_ok (X Y : ℚ) {j : ℕ} (hj : j ≤ 160) :
    ((fEdges X Y).getD j dflt).ok ((X : ℝ) + (1 / 2 + (j : ℝ) / 32)) Y := by
  rw [fEdges_get X Y hj]
  have := edge_ok (X + (1 / 2 + (j : ℚ) / 32)) Y
  push_cast at this ⊢
  exact this

theorem WI_mem {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (WI c s).mem (Wform θ) := by
  rw [Wform_eq_comb, fourier_eq, ellX_eq hc, ellY_eq hs]
  obtain ⟨-, -, -, -, hv, -⟩ := fstate_spec hc hs 48 le_rfl
  unfold WI WIcore
  set X := ellXq c
  set Y := ellYq s
  apply mem_sub
  · apply segCombI_mem
    · intro j hj; exact (pEdge_ok X Y hj).1
    · intro j hj; exact (fEdge_ok X Y hj).1
    · simpa using (edge_ok X Y).1
    · have h := (edge_ok (X - 2) Y).1
      rwa [show (((X - 2 : ℚ)) : ℝ) = (X : ℝ) + -2 by push_cast; ring] at h
    · have := mem_smul X L2_mem; exact this
    · have := mem_add (mem_pt (1 / 2)) (mem_smul (1 / 2) L2_mem)
      refine mem_of_eq this ?_
      rw [show Real.log (1 / 2) = -Real.log 2 by rw [one_div, Real.log_inv]]
      push_cast; ring
  · have := mem_smul 2 (mem_sub MLC_mem hv)
    refine mem_of_eq this ?_
    push_cast; ring

theorem DI_mem {θ : ℝ} {c s : ℚ} (hc : Real.cos θ = c) (hs : Real.sin θ = s) :
    (DI c s).mem (W1 θ) := by
  obtain ⟨-, -, -, -, -, hd⟩ := fstate_spec hc hs 48 le_rfl
  unfold W1 DI DIcore
  rw [ellX_eq hc, ellY_eq hs]
  have hX1 : ellX1 θ = ((-(12783 / 10000) * s : ℚ) : ℝ) := by simp [ellX1, hs]
  have hY1 : ellY1 θ = ((229 / 200 * c : ℚ) : ℝ) := by simp [ellY1, hc]
  rw [hX1, hY1]
  set X := ellXq c
  set Y := ellYq s
  have hds : ∀ (e : EV) (u : ℝ), e.ok u Y →
      (add (smul (-(12783 / 10000) * s) e.l) (smul (229 / 200 * c) e.a)).mem
        (dGr u Y ((-(12783 / 10000) * s : ℚ) : ℝ) ((229 / 200 * c : ℚ) : ℝ)) := by
    intro e u he
    have := mem_add (mem_smul (-(12783 / 10000) * s) he.2.1) (mem_smul (229 / 200 * c) he.2.2)
    refine mem_of_eq this ?_
    unfold dGr; ring
  apply mem_sub
  · apply segCombI_mem
    · intro j hj; exact hds _ _ (pEdge_ok X Y hj)
    · intro j hj; exact hds _ _ (fEdge_ok X Y hj)
    · have := hds _ _ (edge_ok X Y); simpa using this
    · exact hds _ _ (by
        have h := edge_ok (X - 2) Y
        rwa [show (((X - 2 : ℚ)) : ℝ) = (X : ℝ) + -2 by push_cast; ring] at h)
    · exact mem_smul _ L2_mem
    · exact mem_pt 0 |> fun h => by simpa using h
  · have := mem_smul 2 hd
    refine mem_of_eq this ?_
    unfold F1; push_cast; ring

end Li2Lean.P0.CA.Contour
