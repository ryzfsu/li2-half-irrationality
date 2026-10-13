/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ConfigLogTaylor
import Li2Lean.P0.ConfigLogEnclosures
import Li2Lean.Kit.LogSegment

/-!
# CA-F rational arithmetic for the frequency rows

Computable rational enclosures used by the reflected frequency-row checker:
outward dyadic rounding, logarithm bounds from the proved atanh remainder
(`ConfigLogTaylor.logPolynomial_remainder`) and the twelve-digit `log 2`
enclosure (`ConfigLogEnclosures.logTwo_tight_enclosure_v10`), bounds for the
literal C-A primitive `F(v) = v (log |v| - 1)`, its exact hull on an
interval, and integer square-root bounds.  Every definition is a Boolean or
rational computation; the soundness theorems are ordinary real-analysis
statements with no premises beyond positivity of the arguments.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.LogSegment Li2Lean.P0.ConfigLogTaylor

/-! ## Outward rounding -/

/-- Round down to the grid `1/S`. -/
def rdnAt (S q : ℚ) : ℚ := (⌊q * S⌋ : ℚ) / S

/-- Round up to the grid `1/S`. -/
def rupAt (S q : ℚ) : ℚ := (⌈q * S⌉ : ℚ) / S

theorem rdnAt_le {S : ℚ} (hS : 0 < S) (q : ℚ) : rdnAt S q ≤ q := by
  unfold rdnAt
  rw [div_le_iff₀ hS]
  exact Int.floor_le _

theorem le_rupAt {S : ℚ} (hS : 0 < S) (q : ℚ) : q ≤ rupAt S q := by
  unfold rupAt
  rw [le_div_iff₀ hS]
  exact Int.le_ceil _

/-- The row rounding scale `2^48`. -/
def roundScale : ℚ := 281474976710656

theorem roundScale_pos : (0 : ℚ) < roundScale := by norm_num [roundScale]

/-- Round down to the dyadic grid `2^-48`. -/
def rdn (q : ℚ) : ℚ := rdnAt roundScale q

/-- Round up to the dyadic grid `2^-48`. -/
def rup (q : ℚ) : ℚ := rupAt roundScale q

theorem rdn_le (q : ℚ) : rdn q ≤ q := rdnAt_le roundScale_pos q

theorem le_rup (q : ℚ) : q ≤ rup q := le_rupAt roundScale_pos q

theorem rdn_le_real (q : ℚ) {x : ℝ} (h : (q : ℝ) ≤ x) : (rdn q : ℝ) ≤ x :=
  le_trans (by exact_mod_cast rdn_le q) h

theorem le_rup_real (q : ℚ) {x : ℝ} (h : x ≤ (q : ℝ)) : x ≤ (rup q : ℝ) :=
  le_trans h (by exact_mod_cast le_rup q)

theorem half_le_cast {t : ℚ} (h : (1 / 2 : ℚ) ≤ t) : (1 / 2 : ℝ) ≤ (t : ℝ) := by
  have := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at this
  exact this

/-! ## Logarithm enclosures -/

/-- Lower `log 2` endpoint, from `logTwo_tight_enclosure_v10`. -/
def l2lo : ℚ := 693147180559 / 1000000000000

/-- Upper `log 2` endpoint, from `logTwo_tight_enclosure_v10`. -/
def l2hi : ℚ := 693147180560 / 1000000000000

theorem l2lo_le : (l2lo : ℝ) ≤ Real.log 2 := by
  have h := Li2Lean.P0.ConfigLogEnclosures.logTwo_tight_enclosure_v10.1
  simpa [l2lo] using h

theorem le_l2hi : Real.log 2 ≤ (l2hi : ℝ) := by
  have h := Li2Lean.P0.ConfigLogEnclosures.logTwo_tight_enclosure_v10.2
  simpa [l2hi] using h

/-- Number of odd atanh terms used for every logarithm. -/
def logTerms : ℕ := 5

/-- Twice the first `n` odd atanh terms, by structural recursion. -/
def oddSum (z : ℚ) : ℕ → ℚ
  | 0 => 0
  | k + 1 => oddSum z k + z ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ)

theorem two_mul_oddSum (q : ℚ) (n : ℕ) :
    2 * oddSum (logCoordinate q) n = logPolynomial q n := by
  unfold logPolynomial
  congr 1
  induction n with
  | zero => simp [oddSum]
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- Halve while above `3/2`; the pair `(m, k)` keeps `m * 2^k` fixed. -/
def halveLoop : ℕ → ℚ → ℕ → ℚ × ℕ
  | 0, m, k => (m, k)
  | fuel + 1, m, k => if 3 / 2 < m then halveLoop fuel (m / 2) (k + 1) else (m, k)

theorem halveLoop_spec (fuel : ℕ) (m : ℚ) (k : ℕ) (hm : 0 < m) :
    0 < (halveLoop fuel m k).1 ∧
      (halveLoop fuel m k).1 * 2 ^ (halveLoop fuel m k).2 = m * 2 ^ k := by
  induction fuel generalizing m k with
  | zero => exact ⟨hm, rfl⟩
  | succ fuel ih =>
      unfold halveLoop
      split_ifs with h
      · obtain ⟨h1, h2⟩ := ih (m / 2) (k + 1) (by positivity)
        refine ⟨h1, ?_⟩
        rw [h2, pow_succ]
        field_simp
      · exact ⟨hm, rfl⟩

/-- Logarithm enclosure for an argument at least one. -/
def logGe1 (x : ℚ) : ℚ × ℚ :=
  let r := halveLoop 64 x 0
  let p := 2 * oddSum (logCoordinate r.1) logTerms
  let e := logRemainder r.1 logTerms
  ((r.2 : ℚ) * l2lo + p - e, (r.2 : ℚ) * l2hi + p + e)

/-- Logarithm enclosure for every positive rational argument. -/
def logBnd (x : ℚ) : ℚ × ℚ :=
  if 1 ≤ x then logGe1 x else ((-(logGe1 x⁻¹).2), (-(logGe1 x⁻¹).1))

theorem logGe1_sound {x : ℚ} (hx : 0 < x) :
    ((logGe1 x).1 : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ ((logGe1 x).2 : ℝ) := by
  obtain ⟨hm, heq⟩ := halveLoop_spec 64 x 0 hx
  set m := (halveLoop 64 x 0).1 with hmdef
  set k := (halveLoop 64 x 0).2 with hkdef
  have hxR : (x : ℝ) = (m : ℝ) * 2 ^ k := by
    have := congrArg (fun q : ℚ => (q : ℝ)) heq
    push_cast at this
    simpa using this.symm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlog : Real.log (x : ℝ) = Real.log (m : ℝ) + (k : ℝ) * Real.log 2 := by
    rw [hxR, Real.log_mul hmR.ne' (by positivity), Real.log_pow]
  have hrem := logPolynomial_remainder hm logTerms
  rw [← two_mul_oddSum] at hrem
  have hb := abs_le.mp hrem
  have hk : (0 : ℝ) ≤ k := by positivity
  have h1 := mul_le_mul_of_nonneg_left l2lo_le hk
  have h2 := mul_le_mul_of_nonneg_left le_l2hi hk
  simp only [logGe1]
  rw [← hmdef, ← hkdef, hlog]
  push_cast at hb ⊢
  constructor <;> linarith [hb.1, hb.2]

theorem logBnd_sound {x : ℚ} (hx : 0 < x) :
    ((logBnd x).1 : ℝ) ≤ Real.log (x : ℝ) ∧ Real.log (x : ℝ) ≤ ((logBnd x).2 : ℝ) := by
  unfold logBnd
  split_ifs with h
  · exact logGe1_sound hx
  · have hi : 0 < x⁻¹ := inv_pos.mpr hx
    obtain ⟨h1, h2⟩ := logGe1_sound hi
    have hl : Real.log ((x⁻¹ : ℚ) : ℝ) = -Real.log (x : ℝ) := by
      push_cast
      exact Real.log_inv _
    rw [hl] at h1 h2
    push_cast
    constructor <;> linarith

/-! ## The literal primitive `F` -/

/-- Rational lower bound for `primitive u`. -/
def pLo (u : ℚ) : ℚ :=
  if u = 0 then 0
  else if 0 < u then rdn (u * ((logBnd u).1 - 1))
  else rdn (u * ((logBnd (-u)).2 - 1))

/-- Rational upper bound for `primitive u`. -/
def pHi (u : ℚ) : ℚ :=
  if u = 0 then 0
  else if 0 < u then rup (u * ((logBnd u).2 - 1))
  else rup (u * ((logBnd (-u)).1 - 1))

theorem pLo_le (u : ℚ) : (pLo u : ℝ) ≤ primitive (u : ℝ) := by
  unfold pLo
  split_ifs with h0 hpos
  · simp [h0]
  · apply rdn_le_real
    have hb := (logBnd_sound hpos).1
    have huR : (0 : ℝ) < u := by exact_mod_cast hpos
    unfold primitive
    rw [abs_of_pos huR]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) huR.le
  · have hneg : u < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
    have hb := (logBnd_sound (neg_pos.mpr hneg)).2
    apply rdn_le_real
    have huR : (u : ℝ) < 0 := by exact_mod_cast hneg
    unfold primitive
    rw [abs_of_neg huR]
    push_cast at hb ⊢
    exact mul_le_mul_of_nonpos_left (by linarith) huR.le

theorem le_pHi (u : ℚ) : primitive (u : ℝ) ≤ (pHi u : ℝ) := by
  unfold pHi
  split_ifs with h0 hpos
  · simp [h0]
  · apply le_rup_real
    have hb := (logBnd_sound hpos).2
    have huR : (0 : ℝ) < u := by exact_mod_cast hpos
    unfold primitive
    rw [abs_of_pos huR]
    push_cast
    exact mul_le_mul_of_nonneg_left (by linarith) huR.le
  · have hneg : u < 0 := lt_of_le_of_ne (not_lt.mp hpos) h0
    have hb := (logBnd_sound (neg_pos.mpr hneg)).1
    apply le_rup_real
    have huR : (u : ℝ) < 0 := by exact_mod_cast hneg
    unfold primitive
    rw [abs_of_neg huR]
    push_cast at hb ⊢
    exact mul_le_mul_of_nonpos_left (by linarith) huR.le

/-! ## Monotonicity of `F` on its three pieces -/

theorem primitive_monotoneOn_Ici : MonotoneOn primitive (Set.Ici (1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Ici 1) continuous_primitive.continuousOn
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1 : ℝ) < x := hx
    exact (hasDerivAt_primitive (by linarith : x ≠ 0)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Ici] at hx
    have hx1 : (1 : ℝ) < x := hx
    rw [(hasDerivAt_primitive (by linarith : x ≠ 0)).deriv]
    exact Real.log_nonneg (by rw [abs_of_pos (by linarith)]; linarith)

theorem primitive_monotoneOn_Iic : MonotoneOn primitive (Set.Iic (-1 : ℝ)) := by
  apply monotoneOn_of_deriv_nonneg (convex_Iic (-1)) continuous_primitive.continuousOn
  · intro x hx
    rw [interior_Iic] at hx
    have hx1 : x < -1 := hx
    exact (hasDerivAt_primitive (by linarith : x ≠ 0)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Iic] at hx
    have hx1 : x < -1 := hx
    rw [(hasDerivAt_primitive (by linarith : x ≠ 0)).deriv]
    exact Real.log_nonneg (by rw [abs_of_neg (by linarith)]; linarith)

theorem primitive_antitoneOn_nonneg : AntitoneOn primitive (Set.Icc (0 : ℝ) 1) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc 0 1) continuous_primitive.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_primitive (ne_of_gt hx.1)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_primitive (ne_of_gt hx.1)).deriv, abs_of_pos hx.1]
    exact Real.log_nonpos hx.1.le hx.2.le

theorem primitive_antitoneOn_nonpos : AntitoneOn primitive (Set.Icc (-1 : ℝ) 0) := by
  apply antitoneOn_of_deriv_nonpos (convex_Icc (-1) 0) continuous_primitive.continuousOn
  · intro x hx
    rw [interior_Icc] at hx
    exact (hasDerivAt_primitive (ne_of_lt hx.2)).differentiableAt.differentiableWithinAt
  · intro x hx
    rw [interior_Icc] at hx
    rw [(hasDerivAt_primitive (ne_of_lt hx.2)).deriv, abs_of_neg hx.2]
    exact Real.log_nonpos (by linarith [hx.2]) (by linarith [hx.1])

theorem primitive_antitoneOn_unit : AntitoneOn primitive (Set.Icc (-1 : ℝ) 1) := by
  intro a ha b hb hab
  rcases le_total b 0 with hb0 | hb0
  · exact primitive_antitoneOn_nonpos ⟨ha.1, le_trans hab hb0⟩ ⟨hb.1, hb0⟩ hab
  rcases le_total a 0 with ha0 | ha0
  · have h1 := primitive_antitoneOn_nonneg ⟨le_refl 0, by norm_num⟩ ⟨hb0, hb.2⟩ hb0
    have h2 := primitive_antitoneOn_nonpos ⟨ha.1, ha0⟩ ⟨by norm_num, le_refl 0⟩ ha0
    linarith
  · exact primitive_antitoneOn_nonneg ⟨ha0, ha.2⟩ ⟨hb0, hb.2⟩ hab

theorem primitive_one : primitive 1 = -1 := by simp [primitive]

theorem primitive_neg_one : primitive (-1) = 1 := by simp [primitive]

/-- Exact real hull of `F` from below on an interval. -/
theorem primitive_lower_hull {x y u : ℝ} (hxu : x ≤ u) (huy : u ≤ y) :
    min (primitive x) (primitive y) ≤ primitive u ∨
      (x < 1 ∧ 1 < y ∧ -1 ≤ primitive u) := by
  rcases le_total 1 u with hu1 | hu1
  · rcases lt_or_ge x 1 with hx1 | hx1
    · rcases lt_or_ge 1 y with hy1 | hy1
      · right
        refine ⟨hx1, hy1, ?_⟩
        rw [← primitive_one]
        exact primitive_monotoneOn_Ici (le_refl (1 : ℝ)) hu1 hu1
      · left
        have : u = y := le_antisymm huy (le_trans hy1 hu1)
        rw [this]
        exact min_le_right _ _
    · left
      exact le_trans (min_le_left _ _)
        (primitive_monotoneOn_Ici (Set.mem_Ici.mpr hx1)
          (Set.mem_Ici.mpr (le_trans hx1 hxu)) hxu)
  rcases le_total (-1) u with hum | hum
  · rcases le_or_gt y 1 with hy1 | hy1
    · left
      exact le_trans (min_le_right _ _)
        (primitive_antitoneOn_unit ⟨hum, hu1⟩ ⟨le_trans hum huy, hy1⟩ huy)
    · rcases lt_or_ge x 1 with hx1 | hx1
      · right
        refine ⟨hx1, hy1, ?_⟩
        rw [← primitive_one]
        exact primitive_antitoneOn_unit ⟨hum, hu1⟩ ⟨by norm_num, le_refl 1⟩ hu1
      · left
        have hux : u = x := le_antisymm (le_trans hu1 hx1) hxu
        rw [hux]
        exact min_le_left _ _
  · left
    exact le_trans (min_le_left _ _)
      (primitive_monotoneOn_Iic (Set.mem_Iic.mpr (le_trans hxu hum))
        (Set.mem_Iic.mpr hum) hxu)

/-- Exact real hull of `F` from above on an interval. -/
theorem primitive_upper_hull {x y u : ℝ} (hxu : x ≤ u) (huy : u ≤ y) :
    primitive u ≤ max (primitive x) (primitive y) ∨
      (x < -1 ∧ -1 < y ∧ primitive u ≤ 1) := by
  rcases le_total 1 u with hu1 | hu1
  · left
    exact le_trans
      (primitive_monotoneOn_Ici (Set.mem_Ici.mpr hu1)
        (Set.mem_Ici.mpr (le_trans hu1 huy)) huy) (le_max_right _ _)
  rcases le_total (-1) u with hum | hum
  · rcases le_or_gt (-1) x with hx1 | hx1
    · left
      exact le_trans
        (primitive_antitoneOn_unit ⟨hx1, le_trans hxu hu1⟩ ⟨hum, hu1⟩ hxu)
        (le_max_left _ _)
    · rcases lt_or_ge (-1) y with hy1 | hy1
      · right
        refine ⟨hx1, hy1, ?_⟩
        rw [← primitive_neg_one]
        exact primitive_antitoneOn_unit ⟨le_refl (-1), by norm_num⟩ ⟨hum, hu1⟩ hum
      · left
        have hu : u = y := le_antisymm huy (le_trans hy1 hum)
        rw [hu]
        exact le_max_right _ _
  · rcases le_or_gt y (-1) with hy1 | hy1
    · left
      exact le_trans
        (primitive_monotoneOn_Iic (Set.mem_Iic.mpr hum) (Set.mem_Iic.mpr hy1) huy)
        (le_max_right _ _)
    · rcases lt_or_ge x (-1) with hx1 | hx1
      · right
        refine ⟨hx1, hy1, ?_⟩
        rw [← primitive_neg_one]
        exact primitive_monotoneOn_Iic (Set.mem_Iic.mpr hum)
          (Set.mem_Iic.mpr (le_refl (-1))) hum
      · left
        have hu : u = x := le_antisymm (le_trans hum hx1) hxu
        rw [hu]
        exact le_max_left _ _

/-- Rational lower hull of `F` on `[x, y]`. -/
def hullLo (x y : ℚ) : ℚ :=
  if x < 1 ∧ 1 < y then min (min (pLo x) (pLo y)) (-1) else min (pLo x) (pLo y)

/-- Rational upper hull of `F` on `[x, y]`. -/
def hullHi (x y : ℚ) : ℚ :=
  if x < -1 ∧ -1 < y then max (max (pHi x) (pHi y)) 1 else max (pHi x) (pHi y)

theorem hullLo_le {x y : ℚ} {u : ℝ} (hxu : (x : ℝ) ≤ u) (huy : u ≤ (y : ℝ)) :
    (hullLo x y : ℝ) ≤ primitive u := by
  have hmin : ((min (pLo x) (pLo y) : ℚ) : ℝ) ≤ min (primitive x) (primitive y) := by
    push_cast
    exact min_le_min (pLo_le x) (pLo_le y)
  unfold hullLo
  rcases primitive_lower_hull hxu huy with h | ⟨hx, hy, h⟩
  · split_ifs
    · push_cast at hmin ⊢
      exact le_trans (min_le_left _ _) (le_trans hmin h)
    · exact le_trans hmin h
  · have hx' : x < 1 := by exact_mod_cast hx
    have hy' : 1 < y := by exact_mod_cast hy
    simp only [hx', hy', and_self, ↓reduceIte]
    push_cast
    exact le_trans (min_le_right _ _) h

theorem le_hullHi {x y : ℚ} {u : ℝ} (hxu : (x : ℝ) ≤ u) (huy : u ≤ (y : ℝ)) :
    primitive u ≤ (hullHi x y : ℝ) := by
  have hmax : max (primitive x) (primitive y) ≤ ((max (pHi x) (pHi y) : ℚ) : ℝ) := by
    push_cast
    exact max_le_max (le_pHi x) (le_pHi y)
  unfold hullHi
  rcases primitive_upper_hull hxu huy with h | ⟨hx, hy, h⟩
  · split_ifs
    · push_cast at hmax ⊢
      exact le_trans (le_trans h hmax) (le_max_left _ _)
    · exact le_trans h hmax
  · have hx' : x < -1 := by exact_mod_cast hx
    have hy' : -1 < y := by exact_mod_cast hy
    simp only [hx', hy', and_self, ↓reduceIte]
    push_cast
    exact le_trans h (le_max_right _ _)

/-! ## Square-root bounds -/

/-- Lower bound `floor(sqrt(floor(d S^2)))/S` for `sqrt d`. -/
def sqrtLoAt (S d : ℚ) : ℚ :=
  (Nat.sqrt ⌊d * S ^ 2⌋₊ : ℚ) / S

/-- Upper bound `(floor(sqrt(ceil(d S^2)))+1)/S` for `sqrt d`. -/
def sqrtHiAt (S d : ℚ) : ℚ :=
  ((Nat.sqrt ⌈d * S ^ 2⌉₊ + 1 : ℕ) : ℚ) / S

theorem sqrtLoAt_nonneg {S : ℚ} (hS : 0 < S) (d : ℚ) : 0 ≤ sqrtLoAt S d := by
  unfold sqrtLoAt
  positivity

theorem sqrtLoAt_le {S : ℚ} (hS : 0 < S) {d : ℚ} (hd : 0 ≤ d) :
    (sqrtLoAt S d : ℝ) ≤ Real.sqrt d := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  unfold sqrtLoAt
  push_cast
  set n := ⌊d * S ^ 2⌋₊
  have hn : (n : ℝ) ≤ (d : ℝ) * (S : ℝ) ^ 2 := by
    have := Nat.floor_le (mul_nonneg hd (sq_nonneg S))
    exact_mod_cast this
  have hsq : ((Nat.sqrt n : ℕ) : ℝ) ^ 2 ≤ (n : ℝ) := by exact_mod_cast Nat.sqrt_le' n
  have hnonneg : (0 : ℝ) ≤ (Nat.sqrt n : ℝ) / (S : ℝ) := by positivity
  rw [← Real.sqrt_sq hnonneg]
  apply Real.sqrt_le_sqrt
  rw [div_pow, div_le_iff₀ (by positivity)]
  linarith

theorem le_sqrtHiAt {S : ℚ} (hS : 0 < S) {d : ℚ} (hd : 0 ≤ d) :
    Real.sqrt d ≤ (sqrtHiAt S d : ℝ) := by
  have hs : (0 : ℝ) < S := by exact_mod_cast hS
  unfold sqrtHiAt
  push_cast
  set n := ⌈d * S ^ 2⌉₊
  have hn : (d : ℝ) * (S : ℝ) ^ 2 ≤ (n : ℝ) := by
    have := Nat.le_ceil (d * S ^ 2)
    exact_mod_cast this
  have hsq : (n : ℝ) < ((Nat.sqrt n : ℝ) + 1) ^ 2 := by
    have := Nat.lt_succ_sqrt' n
    exact_mod_cast this
  have hnonneg : (0 : ℝ) ≤ ((Nat.sqrt n : ℝ) + 1) / (S : ℝ) := by positivity
  rw [← Real.sqrt_sq hnonneg]
  apply Real.sqrt_le_sqrt
  rw [div_pow, le_div_iff₀ (by positivity)]
  linarith

/-! ## Interval products -/

/-- Lower bound of `a * b` for `a ∈ [alo, ahi]` and `b ∈ [blo, bhi]`. -/
def mulLo (alo ahi blo bhi : ℚ) : ℚ :=
  min (min (alo * blo) (alo * bhi)) (min (ahi * blo) (ahi * bhi))

/-- Upper bound of `a * b` for `a ∈ [alo, ahi]` and `b ∈ [blo, bhi]`. -/
def mulHi (alo ahi blo bhi : ℚ) : ℚ :=
  max (max (alo * blo) (alo * bhi)) (max (ahi * blo) (ahi * bhi))

theorem mul_mem_bounds {alo ahi blo bhi : ℚ} {a b : ℝ}
    (ha1 : (alo : ℝ) ≤ a) (ha2 : a ≤ ahi) (hb1 : (blo : ℝ) ≤ b) (hb2 : b ≤ bhi) :
    (mulLo alo ahi blo bhi : ℝ) ≤ a * b ∧ a * b ≤ (mulHi alo ahi blo bhi : ℝ) := by
  unfold mulLo mulHi
  push_cast
  constructor
  · rcases le_total 0 b with hb | hb
    · have h1 : (alo : ℝ) * b ≤ a * b := mul_le_mul_of_nonneg_right ha1 hb
      rcases le_total 0 (alo : ℝ) with hal | hal
      · have : (alo : ℝ) * blo ≤ alo * b := mul_le_mul_of_nonneg_left hb1 hal
        exact le_trans (min_le_left _ _) (le_trans (min_le_left _ _) (by linarith))
      · have : (alo : ℝ) * bhi ≤ alo * b := mul_le_mul_of_nonpos_left hb2 hal
        exact le_trans (min_le_left _ _) (le_trans (min_le_right _ _) (by linarith))
    · have h1 : (ahi : ℝ) * b ≤ a * b := mul_le_mul_of_nonpos_right ha2 hb
      rcases le_total 0 (ahi : ℝ) with hah | hah
      · have : (ahi : ℝ) * blo ≤ ahi * b := mul_le_mul_of_nonneg_left hb1 hah
        exact le_trans (min_le_right _ _) (le_trans (min_le_left _ _) (by linarith))
      · have : (ahi : ℝ) * bhi ≤ ahi * b := mul_le_mul_of_nonpos_left hb2 hah
        exact le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (by linarith))
  · rcases le_total 0 b with hb | hb
    · have h1 : a * b ≤ (ahi : ℝ) * b := mul_le_mul_of_nonneg_right ha2 hb
      rcases le_total 0 (ahi : ℝ) with hah | hah
      · have : (ahi : ℝ) * b ≤ ahi * bhi := mul_le_mul_of_nonneg_left hb2 hah
        exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_right _ _))
      · have : (ahi : ℝ) * b ≤ ahi * blo := mul_le_mul_of_nonpos_left hb1 hah
        exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_right _ _))
    · have h1 : a * b ≤ (alo : ℝ) * b := mul_le_mul_of_nonpos_right ha1 hb
      rcases le_total 0 (alo : ℝ) with hal | hal
      · have : (alo : ℝ) * b ≤ alo * bhi := mul_le_mul_of_nonneg_left hb2 hal
        exact le_trans (by linarith) (le_trans (le_max_right _ _) (le_max_left _ _))
      · have : (alo : ℝ) * b ≤ alo * blo := mul_le_mul_of_nonpos_left hb1 hal
        exact le_trans (by linarith) (le_trans (le_max_left _ _) (le_max_left _ _))

end Li2Lean.P0.CA.Frequency
