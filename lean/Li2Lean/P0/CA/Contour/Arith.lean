/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Rational interval arithmetic for the reflected contour checker

Plain rational intervals `[lo, hi]` with exact operations and an outward
dyadic rounding.  Every operation has a real-membership soundness lemma.
-/

namespace Li2Lean.P0.CA.Contour

/-- A rational interval; no ordering proof is stored (an empty interval
contains nothing, which keeps every soundness lemma trivially valid). -/
structure QI where
  lo : ℚ
  hi : ℚ
  deriving Repr

namespace QI

def mem (I : QI) (x : ℝ) : Prop := (I.lo : ℝ) ≤ x ∧ x ≤ (I.hi : ℝ)

def pt (q : ℚ) : QI := ⟨q, q⟩

def add (I J : QI) : QI := ⟨I.lo + J.lo, I.hi + J.hi⟩

def neg (I : QI) : QI := ⟨-I.hi, -I.lo⟩

def sub (I J : QI) : QI := ⟨I.lo - J.hi, I.hi - J.lo⟩

def smul (q : ℚ) (I : QI) : QI :=
  if 0 ≤ q then ⟨q * I.lo, q * I.hi⟩ else ⟨q * I.hi, q * I.lo⟩

def mul (I J : QI) : QI :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Rounding precision (bits). -/
def prec : ℕ := 40

/-- Downward dyadic rounding. -/
def rdn (x : ℚ) : ℚ := ((x.num * 2 ^ prec / (x.den : ℤ) : ℤ) : ℚ) / 2 ^ prec

def rup (x : ℚ) : ℚ := -rdn (-x)

def rnd (I : QI) : QI := ⟨rdn I.lo, rup I.hi⟩

theorem rdn_le (x : ℚ) : rdn x ≤ x := by
  unfold rdn
  have hd : (0 : ℤ) < x.den := by exact_mod_cast x.den_pos
  have h1 := Int.ediv_mul_le (x.num * 2 ^ prec) hd.ne'
  have h2 : ((x.num * 2 ^ prec / (x.den : ℤ) : ℤ) : ℚ) * (x.den : ℚ) ≤
      (x.num : ℚ) * 2 ^ prec := by exact_mod_cast h1
  have hdq : (0 : ℚ) < x.den := by exact_mod_cast x.den_pos
  have hp : (0 : ℚ) < 2 ^ prec := by positivity
  rw [div_le_iff₀ hp]
  have hx : (x.num : ℚ) / x.den = x := Rat.num_div_den x
  calc ((x.num * 2 ^ prec / (x.den : ℤ) : ℤ) : ℚ)
      ≤ (x.num : ℚ) * 2 ^ prec / x.den := by rw [le_div_iff₀ hdq]; exact h2
    _ = ((x.num : ℚ) / x.den) * 2 ^ prec := by ring
    _ = x * 2 ^ prec := by rw [hx]

theorem le_rup (x : ℚ) : x ≤ rup x := by
  unfold rup; have := rdn_le (-x); linarith

theorem mem_pt (q : ℚ) : (pt q).mem q := ⟨le_rfl, le_rfl⟩

theorem mem_add {I J : QI} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (add I J).mem (x + y) := by
  unfold mem add at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_neg {I : QI} {x : ℝ} (hx : I.mem x) : (neg I).mem (-x) := by
  unfold mem neg at *; push_cast; constructor <;> linarith [hx.1, hx.2]

theorem mem_sub {I J : QI} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (sub I J).mem (x - y) := by
  unfold mem sub at *; push_cast; constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]

theorem mem_smul (q : ℚ) {I : QI} {x : ℝ} (hx : I.mem x) : (smul q I).mem ((q : ℝ) * x) := by
  unfold mem smul at *
  split_ifs with h
  · have hq : (0 : ℝ) ≤ q := by exact_mod_cast h
    push_cast; constructor <;> nlinarith [hx.1, hx.2]
  · have hq : (q : ℝ) < 0 := by exact_mod_cast lt_of_not_ge h
    push_cast; constructor <;> nlinarith [hx.1, hx.2]

private theorem lin_bounds {k p q t : ℝ} (hp : p ≤ t) (hq : t ≤ q) :
    min (k * p) (k * q) ≤ k * t ∧ k * t ≤ max (k * p) (k * q) := by
  rcases le_total 0 k with hk | hk
  · constructor
    · exact (min_le_left _ _).trans (mul_le_mul_of_nonneg_left hp hk)
    · exact (mul_le_mul_of_nonneg_left hq hk).trans (le_max_right _ _)
  · constructor
    · exact (min_le_right _ _).trans (mul_le_mul_of_nonpos_left hq hk)
    · exact (mul_le_mul_of_nonpos_left hp hk).trans (le_max_left _ _)

theorem mem_mul {I J : QI} {x y : ℝ} (hx : I.mem x) (hy : J.mem y) :
    (mul I J).mem (x * y) := by
  unfold mem mul at *
  push_cast
  set a : ℝ := ((I.lo : ℚ) : ℝ)
  set b : ℝ := ((I.hi : ℚ) : ℝ)
  set c : ℝ := ((J.lo : ℚ) : ℝ)
  set d : ℝ := ((J.hi : ℚ) : ℝ)
  have hy1 := lin_bounds (k := x) hy.1 hy.2
  have hxc := lin_bounds (k := c) hx.1 hx.2
  have hxd := lin_bounds (k := d) hx.1 hx.2
  have hca : c * a = a * c := mul_comm c a
  have hcb : c * b = b * c := mul_comm c b
  have hda : d * a = a * d := mul_comm d a
  have hdb : d * b = b * d := mul_comm d b
  have hxc' : x * c = c * x := mul_comm x c
  have hxd' : x * d = d * x := mul_comm x d
  constructor
  · have e1 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * c := by
      rw [hxc']
      refine le_trans (le_min ?_ ?_) hxc.1
      · rw [hca]; exact (min_le_left _ _).trans (min_le_left _ _)
      · rw [hcb]; exact (min_le_right _ _).trans (min_le_left _ _)
    have e2 : min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ x * d := by
      rw [hxd']
      refine le_trans (le_min ?_ ?_) hxd.1
      · rw [hda]; exact (min_le_left _ _).trans (min_le_right _ _)
      · rw [hdb]; exact (min_le_right _ _).trans (min_le_right _ _)
    exact le_trans (le_min e1 e2) hy1.1
  · have e1 : x * c ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
      rw [hxc']
      refine le_trans hxc.2 (max_le ?_ ?_)
      · rw [hca]; exact (le_max_left _ _).trans (le_max_left _ _)
      · rw [hcb]; exact (le_max_left _ _).trans (le_max_right _ _)
    have e2 : x * d ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
      rw [hxd']
      refine le_trans hxd.2 (max_le ?_ ?_)
      · rw [hda]; exact (le_max_right _ _).trans (le_max_left _ _)
      · rw [hdb]; exact (le_max_right _ _).trans (le_max_right _ _)
    exact le_trans hy1.2 (max_le e1 e2)

theorem mem_rnd {I : QI} {x : ℝ} (hx : I.mem x) : (rnd I).mem x := by
  unfold mem rnd at *
  have h1 : ((rdn I.lo : ℚ) : ℝ) ≤ I.lo := by exact_mod_cast rdn_le I.lo
  have h2 : (I.hi : ℝ) ≤ ((rup I.hi : ℚ) : ℝ) := by exact_mod_cast le_rup I.hi
  constructor <;> linarith [hx.1, hx.2]

/-- Sum of `f j` for `j < n`. -/
def sumIdx : ℕ → (ℕ → QI) → QI
  | 0, _ => pt 0
  | n + 1, f => add (sumIdx n f) (f n)

theorem mem_sumIdx {n : ℕ} {f : ℕ → QI} {r : ℕ → ℝ} (h : ∀ j < n, (f j).mem (r j)) :
    (sumIdx n f).mem (∑ j ∈ Finset.range n, r j) := by
  induction n with
  | zero => simpa [sumIdx] using mem_pt 0
  | succ n ih =>
      rw [Finset.sum_range_succ]
      exact mem_add (ih fun j hj => h j (by omega)) (h n (by omega))

theorem mem_of_eq {I : QI} {x y : ℝ} (hx : I.mem x) (h : x = y) : I.mem y := h ▸ hx

end QI

end Li2Lean.P0.CA.Contour
