/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Reflected rational interval and polynomial-model kit for pinned C-A rows

All executable objects are rational (`ℚ`) and are evaluated by the kernel.
Each operation has a real-valued containment theorem.  A `Model` is an
interval-coefficient polynomial in the local variable `t` plus a rational
uniform error; `Model.Holds` is its only semantic statement.
-/

namespace Li2Lean.P0.CA.Pinned

/-- A rational interval.  No ordering proof is stored; containment carries it. -/
structure QI where
  lo : ℚ
  hi : ℚ
  deriving DecidableEq, Repr

namespace QI

def Contains (I : QI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def pt (q : ℚ) : QI := ⟨q, q⟩
def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩
def neg (I : QI) : QI := ⟨-I.hi, -I.lo⟩
def sub (I J : QI) : QI := add I (neg J)
def smul (q : ℚ) (I : QI) : QI :=
  if 0 ≤ q then ⟨q * I.lo, q * I.hi⟩ else ⟨q * I.hi, q * I.lo⟩
def mul (I J : QI) : QI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩
/-- An absolute bound for every member. -/
def mag (I : QI) : ℚ := max |I.lo| |I.hi|

theorem mem_pt (q : ℚ) : (pt q).Contains (q : ℝ) := ⟨le_rfl, le_rfl⟩

theorem mem_add {I J : QI} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (add I J).Contains (x + y) := by
  simp only [Contains, add, Rat.cast_add] at *
  constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {I : QI} {x : ℝ} (hx : I.Contains x) : (neg I).Contains (-x) := by
  simp only [Contains, neg, Rat.cast_neg] at *
  constructor <;> linarith [hx.1, hx.2]

theorem mem_sub {I J : QI} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (sub I J).Contains (x - y) := by
  simpa [sub, sub_eq_add_neg] using mem_add hx (mem_neg hy)

theorem mem_smul (q : ℚ) {I : QI} {x : ℝ} (hx : I.Contains x) :
    (smul q I).Contains ((q : ℝ) * x) := by
  unfold smul
  split_ifs with hq
  · have hqR : (0 : ℝ) ≤ q := by exact_mod_cast hq
    simp only [Contains, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonneg_left hx.1 hqR, mul_le_mul_of_nonneg_left hx.2 hqR⟩
  · have hqR : (q : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hq)
    simp only [Contains, Rat.cast_mul]
    exact ⟨mul_le_mul_of_nonpos_left hx.2 hqR, mul_le_mul_of_nonpos_left hx.1 hqR⟩

private theorem corners_lower {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * y := by
  have hac : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*c :=
    le_trans (min_le_left _ _) (min_le_left _ _)
  have had : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ a*d :=
    le_trans (min_le_left _ _) (min_le_right _ _)
  have hbc : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*c :=
    le_trans (min_le_right _ _) (min_le_left _ _)
  have hbd : min (min (a*c) (a*d)) (min (b*c) (b*d)) ≤ b*d :=
    le_trans (min_le_right _ _) (min_le_right _ _)
  by_cases hy0 : 0 ≤ y
  · have hax := mul_le_mul_of_nonneg_right hx.1 hy0
    by_cases ha0 : 0 ≤ a
    · exact hac.trans ((mul_le_mul_of_nonneg_left hy.1 ha0).trans hax)
    · exact had.trans ((mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge ha0)).trans hax)
  · have hbx := mul_le_mul_of_nonpos_right hx.2 (le_of_not_ge hy0)
    by_cases hb0 : 0 ≤ b
    · exact hbc.trans ((mul_le_mul_of_nonneg_left hy.1 hb0).trans hbx)
    · exact hbd.trans ((mul_le_mul_of_nonpos_left hy.2 (le_of_not_ge hb0)).trans hbx)

private theorem corners_upper {a b c d x y : ℝ}
    (hx : a ≤ x ∧ x ≤ b) (hy : c ≤ y ∧ y ≤ d) :
    x * y ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have h := corners_lower (a := -b) (b := -a) (c := c) (d := d) (x := -x) (y := y)
    ⟨by linarith [hx.2], by linarith [hx.1]⟩ hy
  have e1 : min (min (-b * c) (-b * d)) (min (-a * c) (-a * d)) =
      -(max (max (a * c) (a * d)) (max (b * c) (b * d))) := by
    simp only [neg_mul, min_neg_neg]
    rw [max_comm (max (a * c) (a * d))]
  rw [e1] at h
  linarith

theorem mem_mul {I J : QI} {x y : ℝ} (hx : I.Contains x) (hy : J.Contains y) :
    (mul I J).Contains (x * y) := by
  simp only [Contains, mul, Rat.cast_min, Rat.cast_max, Rat.cast_mul] at *
  exact ⟨corners_lower hx hy, corners_upper hx hy⟩

theorem abs_le_mag {I : QI} {x : ℝ} (hx : I.Contains x) : |x| ≤ (I.mag : ℝ) := by
  have h1 : |(I.lo : ℝ)| ≤ (I.mag : ℝ) := by
    have : |I.lo| ≤ I.mag := le_max_left _ _
    exact_mod_cast this
  have h2 : |(I.hi : ℝ)| ≤ (I.mag : ℝ) := by
    have : |I.hi| ≤ I.mag := le_max_right _ _
    exact_mod_cast this
  rw [abs_le] at *
  constructor <;> linarith [hx.1, hx.2, h1.1, h2.2]

theorem lo_le_hi {I : QI} {x : ℝ} (hx : I.Contains x) : I.lo ≤ I.hi := by
  have : (I.lo : ℝ) ≤ I.hi := hx.1.trans hx.2
  exact_mod_cast this

/-! Outward rounding to dyadic rationals with denominator `2^128`. -/

def scale : ℚ := 340282366920938463463374607431768211456

def rdn (q : ℚ) : ℚ := ((q * scale).floor : ℚ) / scale
def rup (q : ℚ) : ℚ := -rdn (-q)

theorem rdn_le (q : ℚ) : rdn q ≤ q := by
  unfold rdn
  have hs : (0 : ℚ) < scale := by norm_num [scale]
  rw [div_le_iff₀ hs]
  exact Int.floor_le _

theorem le_rup (q : ℚ) : q ≤ rup q := by
  unfold rup
  have := rdn_le (-q)
  linarith

def round (I : QI) : QI := ⟨rdn I.lo, rup I.hi⟩

theorem mem_round {I : QI} {x : ℝ} (hx : I.Contains x) : (round I).Contains x := by
  have h1 : ((rdn I.lo : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast rdn_le I.lo
  have h2 : (I.hi : ℝ) ≤ ((rup I.hi : ℚ) : ℝ) := by exact_mod_cast le_rup I.hi
  exact ⟨h1.trans hx.1, hx.2.trans h2⟩

/-- Widen by a nonnegative radius. -/
def widen (I : QI) (e : ℚ) : QI := ⟨I.lo - e, I.hi + e⟩

theorem mem_widen {I : QI} {e : ℚ} {x y : ℝ} (hx : I.Contains x)
    (hxy : |y - x| ≤ (e : ℝ)) : (widen I e).Contains y := by
  rw [abs_le] at hxy
  simp only [Contains, widen, Rat.cast_sub, Rat.cast_add] at *
  constructor <;> linarith [hx.1, hx.2, hxy.1, hxy.2]

def subset (I J : QI) : Bool := decide (J.lo ≤ I.lo ∧ I.hi ≤ J.hi)

theorem mem_of_subset {I J : QI} (h : subset I J = true) {x : ℝ} (hx : I.Contains x) :
    J.Contains x := by
  have h' := of_decide_eq_true h
  have a : (J.lo : ℝ) ≤ I.lo := by exact_mod_cast h'.1
  have b : (I.hi : ℝ) ≤ J.hi := by exact_mod_cast h'.2
  exact ⟨a.trans hx.1, hx.2.trans b⟩

end QI

/-! ## Polynomials in ascending coefficient order -/

/-- Real Horner evaluation. -/
def hornerR : List ℝ → ℝ → ℝ
  | [], _ => 0
  | a :: as, t => a + t * hornerR as t

/-- Rational Horner evaluation (computable). -/
def hornerQ : List ℚ → ℚ → ℚ
  | [], _ => 0
  | a :: as, t => a + t * hornerQ as t

def castL : List ℚ → List ℝ
  | [] => []
  | a :: as => (a : ℝ) :: castL as

theorem hornerQ_cast (l : List ℚ) (q : ℚ) :
    ((hornerQ l q : ℚ) : ℝ) = hornerR (castL l) (q : ℝ) := by
  induction l with
  | nil => simp [hornerQ, hornerR, castL]
  | cons a as ih =>
      simp only [hornerQ, hornerR, castL, Rat.cast_add, Rat.cast_mul]
      rw [ih]

/-- Padded coefficient sum. -/
def addR : List ℝ → List ℝ → List ℝ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addR as bs

theorem hornerR_addR (l m : List ℝ) (t : ℝ) :
    hornerR (addR l m) t = hornerR l t + hornerR m t := by
  induction l generalizing m with
  | nil => simp [addR, hornerR]
  | cons a as ih =>
      cases m with
      | nil => simp [addR, hornerR]
      | cons b bs => simp only [addR, hornerR, ih]; ring

def addI : List QI → List QI → List QI
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => QI.add a b :: addI as bs

theorem forall2_addI {Is Js : List QI} {cs ds : List ℝ}
    (h1 : List.Forall₂ QI.Contains Is cs) (h2 : List.Forall₂ QI.Contains Js ds) :
    List.Forall₂ QI.Contains (addI Is Js) (addR cs ds) := by
  induction h1 generalizing Js ds with
  | nil => simpa [addI, addR] using h2
  | @cons I c Is cs hI _ ih =>
      cases h2 with
      | nil => exact List.Forall₂.cons hI (by assumption)
      | @cons J d Js ds hJ hrest =>
          exact List.Forall₂.cons (QI.mem_add hI hJ) (ih hrest)

/-- Padded rational coefficient sum. -/
def addQ : List ℚ → List ℚ → List ℚ
  | [], l => l
  | a :: as, [] => a :: as
  | a :: as, b :: bs => (a + b) :: addQ as bs

theorem castL_addQ (l m : List ℚ) : castL (addQ l m) = addR (castL l) (castL m) := by
  induction l generalizing m with
  | nil => simp [addQ, addR, castL]
  | cons a as ih =>
      cases m with
      | nil => simp [addQ, addR, castL]
      | cons b bs =>
          simp only [addQ, addR, castL, Rat.cast_add]
          rw [ih]

theorem castL_length (l : List ℚ) : (castL l).length = l.length := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [castL, ih]

theorem castL_append (l m : List ℚ) : castL (l ++ m) = castL l ++ castL m := by
  induction l with
  | nil => rfl
  | cons a as ih => simp [castL, ih]

/-- Real scalar multiple. -/
def scaleR (z : ℝ) (l : List ℝ) : List ℝ := l.map (fun a => z * a)

theorem hornerR_scaleR (z : ℝ) (l : List ℝ) (t : ℝ) :
    hornerR (scaleR z l) t = z * hornerR l t := by
  induction l with
  | nil => simp [scaleR, hornerR]
  | cons a as ih =>
      simp only [scaleR, List.map_cons, hornerR] at *
      rw [ih]; ring

theorem castL_map_mul (q : ℚ) (p : List ℚ) :
    castL (p.map (fun a => q * a)) = scaleR (q : ℝ) (castL p) := by
  induction p with
  | nil => rfl
  | cons a as ih => simp [castL, scaleR] at *; exact ih

/-- Interval constant times a rational polynomial. -/
def smulPoly (I : QI) (p : List ℚ) : List QI := p.map (fun a => QI.smul a I)

theorem forall2_smulPoly {I : QI} {z : ℝ} (hz : I.Contains z) (p : List ℚ) :
    List.Forall₂ QI.Contains (smulPoly I p) (scaleR z (castL p)) := by
  induction p with
  | nil => exact List.Forall₂.nil
  | cons a as ih =>
      refine List.Forall₂.cons ?_ ih
      have := QI.mem_smul a hz
      simpa [mul_comm] using this

/-- `t * p` -/
def mulX (l : List ℝ) : List ℝ := 0 :: l

theorem hornerR_mulX (l : List ℝ) (t : ℝ) : hornerR (mulX l) t = t * hornerR l t := by
  simp [mulX, hornerR]

/-! ## Interval-coefficient models -/

structure Model where
  coeffs : List QI
  eps : ℚ
  deriving Repr

/-- `f t` is within `eps` of a polynomial with coefficients in the stored
intervals, for every `|t| ≤ ρ`. -/
def Model.Holds (M : Model) (f : ℝ → ℝ) (ρ : ℚ) : Prop :=
  ∀ t : ℝ, |t| ≤ (ρ : ℝ) → ∃ cs : List ℝ,
    List.Forall₂ QI.Contains M.coeffs cs ∧ |f t - hornerR cs t| ≤ (M.eps : ℝ)

def Model.add (M N : Model) : Model := ⟨addI M.coeffs N.coeffs, M.eps + N.eps⟩

theorem Model.add_holds {M N : Model} {f g : ℝ → ℝ} {ρ : ℚ}
    (hM : M.Holds f ρ) (hN : N.Holds g ρ) : (M.add N).Holds (fun t => f t + g t) ρ := by
  intro t ht
  obtain ⟨cs, hcs, he⟩ := hM t ht
  obtain ⟨ds, hds, he'⟩ := hN t ht
  refine ⟨addR cs ds, forall2_addI hcs hds, ?_⟩
  rw [hornerR_addR]
  simp only [Model.add, Rat.cast_add]
  calc |f t + g t - (hornerR cs t + hornerR ds t)|
      = |(f t - hornerR cs t) + (g t - hornerR ds t)| := by ring_nf
    _ ≤ |f t - hornerR cs t| + |g t - hornerR ds t| := abs_add_le _ _
    _ ≤ _ := add_le_add he he'

def Model.zero : Model := ⟨[], 0⟩

theorem Model.zero_holds (ρ : ℚ) : Model.zero.Holds (fun _ => 0) ρ := by
  intro t _
  exact ⟨[], List.Forall₂.nil, by simp [Model.zero, hornerR]⟩

/-- An exact interval-scaled polynomial `z * p(t)` with `z ∈ I`. -/
def Model.ofScaledPoly (I : QI) (p : List ℚ) : Model := ⟨smulPoly I p, 0⟩

theorem Model.ofScaledPoly_holds {I : QI} {z : ℝ} (hz : I.Contains z) (p : List ℚ)
    (ρ : ℚ) : (Model.ofScaledPoly I p).Holds (fun t => z * hornerR (castL p) t) ρ := by
  intro t _
  refine ⟨scaleR z (castL p), forall2_smulPoly hz p, ?_⟩
  rw [hornerR_scaleR]; simp [Model.ofScaledPoly]

/-- Round every coefficient outward and the error upward. -/
def Model.round (M : Model) : Model := ⟨M.coeffs.map QI.round, QI.rup M.eps⟩

theorem Model.round_holds {M : Model} {f : ℝ → ℝ} {ρ : ℚ} (h : M.Holds f ρ) :
    M.round.Holds f ρ := by
  intro t ht
  obtain ⟨cs, hcs, he⟩ := h t ht
  refine ⟨cs, ?_, ?_⟩
  · have : ∀ {Is : List QI} {cs : List ℝ}, List.Forall₂ QI.Contains Is cs →
        List.Forall₂ QI.Contains (Is.map QI.round) cs := by
      intro Is cs h
      induction h with
      | nil => exact List.Forall₂.nil
      | cons hI _ ih => exact List.Forall₂.cons (QI.mem_round hI) ih
    exact this hcs
  · have : (M.eps : ℝ) ≤ (QI.rup M.eps : ℚ) := by exact_mod_cast QI.le_rup M.eps
    exact he.trans this

/-! ## Normalization to a point polynomial -/

def QI.dev (I : QI) (q : ℚ) : ℚ := max |I.lo - q| |I.hi - q|

theorem QI.abs_sub_le_dev {I : QI} {x : ℝ} (hx : I.Contains x) (q : ℚ) :
    |x - q| ≤ (I.dev q : ℝ) := by
  have h1 : |(I.lo : ℝ) - q| ≤ (I.dev q : ℝ) := by
    have : |I.lo - q| ≤ I.dev q := le_max_left _ _
    exact_mod_cast this
  have h2 : |(I.hi : ℝ) - q| ≤ (I.dev q : ℝ) := by
    have : |I.hi - q| ≤ I.dev q := le_max_right _ _
    exact_mod_cast this
  rw [abs_le] at *
  constructor <;> linarith [hx.1, hx.2, h1.1, h2.2]

/-- Error of replacing interval coefficients by points (missing entries are zero). -/
def tailErr (ρ : ℚ) : List ℚ → ℚ
  | [] => 0
  | q :: qs => |q| + ρ * tailErr ρ qs

/-- Structural in the first list (kernel-reducible). -/
def normErr (ρ : ℚ) : List QI → List ℚ → ℚ
  | [], qs => tailErr ρ qs
  | I :: Is, [] => I.mag + ρ * normErr ρ Is []
  | I :: Is, q :: qs => I.dev q + ρ * normErr ρ Is qs

private theorem step_bound {c q t h e r ρ : ℝ} (hc : |c - q| ≤ e) (ht : |t| ≤ ρ)
    (hh : |h| ≤ r) (hρ : 0 ≤ ρ) : |(c - q) + t * h| ≤ e + ρ * r := by
  have h1 : |t * h| ≤ ρ * r := by
    rw [abs_mul]; exact mul_le_mul ht hh (abs_nonneg _) hρ
  exact (abs_add_le _ _).trans (add_le_add hc h1)

private theorem key_eq (c q t H1 H2 : ℝ) :
    c + t * H1 - (q + t * H2) = (c - q) + t * (H1 - H2) := by ring

theorem normErr_sound {ρ : ℚ} (hρ : 0 ≤ ρ) {t : ℝ} (ht : |t| ≤ (ρ : ℝ)) :
    ∀ {Is : List QI} {cs : List ℝ} (qs : List ℚ), List.Forall₂ QI.Contains Is cs →
      |hornerR cs t - hornerR (castL qs) t| ≤ (normErr ρ Is qs : ℝ)
  | [], [], [], _ => by simp [hornerR, castL, normErr, tailErr]
  | [], [], q :: qs, _ => by
      have ih := normErr_sound hρ ht (Is := []) (cs := []) qs List.Forall₂.nil
      have hρ' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
      simp only [hornerR, castL, normErr, tailErr, Rat.cast_add, Rat.cast_mul,
        Rat.cast_abs] at ih ⊢
      have hb := step_bound (c := 0) (q := (q : ℝ)) (e := |(q : ℝ)|)
        (h := 0 - hornerR (castL qs) t) (by simp) ht ih hρ'
      calc |0 - ((q : ℝ) + t * hornerR (castL qs) t)| =
          |(0 - (q : ℝ)) + t * (0 - hornerR (castL qs) t)| := by congr 1; ring
        _ ≤ _ := hb
  | I :: Is, c :: cs, [], h => by
      cases h with
      | cons hI hrest =>
          have ih := normErr_sound hρ ht (Is := Is) (cs := cs) [] hrest
          have hρ' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
          simp only [hornerR, castL, normErr, Rat.cast_add, Rat.cast_mul] at ih ⊢
          have := step_bound (c := c) (q := 0) (by simpa using QI.abs_le_mag hI) ht ih hρ'
          rw [← key_eq] at this
          simpa using this
  | I :: Is, c :: cs, q :: qs, h => by
      cases h with
      | cons hI hrest =>
          have ih := normErr_sound hρ ht (Is := Is) (cs := cs) qs hrest
          have hρ' : (0 : ℝ) ≤ ρ := by exact_mod_cast hρ
          simp only [hornerR, castL, normErr, Rat.cast_add, Rat.cast_mul] at ih ⊢
          have := step_bound (QI.abs_sub_le_dev hI q) ht ih hρ'
          rw [← key_eq] at this
          exact this

/-- Point coefficients: rounded midpoints of the first `D` intervals. -/
def Model.mids (M : Model) (D : ℕ) : List ℚ :=
  (M.coeffs.take D).map (fun I => QI.rdn ((I.lo + I.hi) / 2))

theorem Model.point_sound {M : Model} {f : ℝ → ℝ} {ρ : ℚ} (hρ : 0 ≤ ρ)
    (h : M.Holds f ρ) (qs : List ℚ) {t : ℝ} (ht : |t| ≤ (ρ : ℝ)) :
    |f t - hornerR (castL qs) t| ≤ ((M.eps + normErr ρ M.coeffs qs : ℚ) : ℝ) := by
  obtain ⟨cs, hcs, he⟩ := h t ht
  have h2 := normErr_sound hρ ht qs hcs
  push_cast
  calc |f t - hornerR (castL qs) t|
      = |(f t - hornerR cs t) + (hornerR cs t - hornerR (castL qs) t)| := by ring_nf
    _ ≤ _ := (abs_add_le _ _).trans (add_le_add he h2)

/-! ## Lower bound of a point polynomial on a small interval -/

def hornerI : List ℚ → QI → QI
  | [], _ => QI.pt 0
  | a :: as, T => QI.add (QI.pt a) (QI.mul T (hornerI as T))

theorem hornerI_sound (p : List ℚ) {T : QI} {t : ℝ} (ht : T.Contains t) :
    (hornerI p T).Contains (hornerR (castL p) t) := by
  induction p with
  | nil => simpa [hornerI, hornerR, castL] using QI.mem_pt (0 : ℚ)
  | cons a as ih =>
      simpa [hornerI, hornerR, castL] using QI.mem_add (QI.mem_pt a) (QI.mem_mul ht ih)

def ddR : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 0
  | _ :: as, t, m => hornerR as t + m * ddR as t m

theorem hornerR_sub_eq (l : List ℝ) (t m : ℝ) :
    hornerR l t - hornerR l m = (t - m) * ddR l t m := by
  induction l with
  | nil => simp [hornerR, ddR]
  | cons a as ih =>
      simp only [hornerR, ddR]
      have : t * hornerR as t - m * hornerR as m =
          (t - m) * hornerR as t + m * (hornerR as t - hornerR as m) := by ring
      linear_combination this + m * ih

def ddI : List ℚ → QI → ℚ → QI
  | [], _, _ => QI.pt 0
  | _ :: as, T, m => QI.add (hornerI as T) (QI.smul m (ddI as T m))

theorem ddI_sound (p : List ℚ) {T : QI} {t : ℝ} (ht : T.Contains t) (m : ℚ) :
    (ddI p T m).Contains (ddR (castL p) t m) := by
  induction p with
  | nil => simpa [ddI, ddR, castL] using QI.mem_pt (0 : ℚ)
  | cons a as ih =>
      simpa [ddI, ddR, castL] using QI.mem_add (hornerI_sound as ht) (QI.mem_smul m ih)

/-- One pass: rounded interval Horner value and slope on `T`. -/
def hdI : List ℚ → QI → ℚ → QI × QI
  | [], _, _ => (QI.pt 0, QI.pt 0)
  | a :: as, T, m =>
      let r := hdI as T m
      (QI.round (QI.add (QI.pt a) (QI.mul T r.1)), QI.round (QI.add r.1 (QI.smul m r.2)))

theorem hdI_sound (p : List ℚ) {T : QI} {t : ℝ} (ht : T.Contains t) (m : ℚ) :
    (hdI p T m).1.Contains (hornerR (castL p) t) ∧
      (hdI p T m).2.Contains (ddR (castL p) t m) := by
  induction p with
  | nil => exact ⟨by simpa [hdI, hornerR, castL] using QI.mem_pt (0 : ℚ),
      by simpa [hdI, ddR, castL] using QI.mem_pt (0 : ℚ)⟩
  | cons a as ih =>
      refine ⟨?_, ?_⟩
      · simpa [hdI, hornerR, castL] using
          QI.mem_round (QI.mem_add (QI.mem_pt a) (QI.mem_mul ht ih.1))
      · simpa [hdI, ddR, castL] using QI.mem_round (QI.mem_add ih.1 (QI.mem_smul m ih.2))

/-- Rational lower bound for `p` on `[a,b]` by the exact slope form. -/
def polyLower (p : List ℚ) (a b : ℚ) : ℚ :=
  (hdI p (QI.pt ((a + b) / 2)) 0).1.lo -
    (hdI p ⟨a, b⟩ ((a + b) / 2)).2.mag * ((b - a) / 2)

theorem polyLower_le (p : List ℚ) {a b : ℚ} {t : ℝ} (hat : (a : ℝ) ≤ t)
    (htb : t ≤ (b : ℝ)) : (polyLower p a b : ℝ) ≤ hornerR (castL p) t := by
  set m : ℚ := (a + b) / 2
  have hT : (QI.mk a b).Contains t := ⟨hat, htb⟩
  have hdd := QI.abs_le_mag (hdI_sound p hT m).2
  have hsub := hornerR_sub_eq (castL p) t (m : ℝ)
  have hm := ((hdI_sound p (QI.mem_pt m) 0).1).1
  have hdist : |t - (m : ℝ)| ≤ (((b - a) / 2 : ℚ) : ℝ) := by
    simp only [m]; push_cast
    rw [abs_le]; constructor <;> linarith
  have hprod : |(t - m) * ddR (castL p) t m| ≤
      (((b - a) / 2 : ℚ) : ℝ) * ((hdI p ⟨a, b⟩ m).2.mag : ℝ) := by
    rw [abs_mul]
    exact mul_le_mul hdist hdd (abs_nonneg _) (le_trans (abs_nonneg _) hdist)
  have hlow := (abs_le.mp hprod).1
  unfold polyLower
  push_cast at hm hlow ⊢
  linarith

end Li2Lean.P0.CA.Pinned
