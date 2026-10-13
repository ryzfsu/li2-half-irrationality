/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.Arith

/-!
# CA-F fixed-point kernel arithmetic

Kernel-fast enclosures of `log` and of the C-A primitive `F` in dyadic
fixed point: a value is an integer mantissa `M` meaning `M / 2^60`.
Only `Nat`/`Int` operations occur (`Nat` ones are GMP-accelerated in the
kernel); all roundings are directed (`Nat` floor division, and ceiling by
`(p + q - 1) / q`).  Soundness reduces to the proved atanh remainder
`ConfigLogTaylor.logPolynomial_remainder` / `logPolynomial_le_log`.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.LogSegment Li2Lean.P0.ConfigLogTaylor

/-- The mantissa scale `2^60`. -/
def twoE : ℕ := 1152921504606846976

theorem twoE_pos : 0 < twoE := by norm_num [twoE]

theorem twoE_cast_pos : (0 : ℝ) < twoE := by exact_mod_cast twoE_pos

/-- Number of odd atanh terms in the fixed-point logarithm. -/
def nLog : ℕ := 5

/-- Ceiling division. -/
def cdiv (p q : ℕ) : ℕ := (p + q - 1) / q

theorem le_cdiv {p q : ℕ} (hq : 0 < q) : (p : ℝ) / q ≤ (cdiv p q : ℝ) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  rw [div_le_iff₀ hqR]
  have h1 := Nat.div_add_mod (p + q - 1) q
  have h2 := Nat.mod_lt (p + q - 1) hq
  have : p ≤ cdiv p q * q := by
    unfold cdiv
    have := Nat.mul_comm q ((p + q - 1) / q)
    omega
  exact_mod_cast this

theorem natDiv_le (p q : ℕ) : ((p / q : ℕ) : ℝ) ≤ (p : ℝ) / q := Nat.cast_div_le

/-- Doubling loop: returns `(b * 2^j, k + j)`, doubling while `2B ≤ a`. -/
def dblLoop : ℕ → ℕ → ℕ → ℕ → ℕ × ℕ
  | 0, _, B, k => (B, k)
  | fuel + 1, a, B, k => if 2 * B ≤ a then dblLoop fuel a (2 * B) (k + 1) else (B, k)

theorem dblLoop_spec (fuel a B k : ℕ) (hB : B ≤ a) :
    (dblLoop fuel a B k).1 ≤ a ∧
      (dblLoop fuel a B k).1 = B * 2 ^ ((dblLoop fuel a B k).2 - k) ∧
      k ≤ (dblLoop fuel a B k).2 := by
  induction fuel generalizing B k with
  | zero => simp [dblLoop, hB]
  | succ fuel ih =>
      unfold dblLoop
      split_ifs with h
      · obtain ⟨h1, h2, h3⟩ := ih (2 * B) (k + 1) h
        refine ⟨h1, ?_, by omega⟩
        rw [h2]
        have : (dblLoop fuel a (2 * B) (k + 1)).2 - k =
            ((dblLoop fuel a (2 * B) (k + 1)).2 - (k + 1)) + 1 := by omega
        rw [this, pow_succ]
        ring
      · simp [hB]

/-- Lower partial atanh sum (mantissa units), floor rounding. -/
def serLo (Z : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => serLo Z j + Z ^ (2 * j + 1) / ((2 * j + 1) * twoE ^ (2 * j))

/-- Upper partial atanh sum (mantissa units), ceiling rounding. -/
def serHi (Z : ℕ) : ℕ → ℕ
  | 0 => 0
  | j + 1 => serHi Z j + cdiv (Z ^ (2 * j + 1)) ((2 * j + 1) * twoE ^ (2 * j))

/-- Remainder `2 z^(2n+1) / (1 - z^2)` with `1 - z^2 = 4aB/(a+B)^2`. -/
def remHi (Z a B : ℕ) : ℕ :=
  cdiv (2 * Z ^ (2 * nLog + 1) * (a + B) ^ 2) (twoE ^ (2 * nLog) * (4 * a * B))

/-- Core: mantissa bounds of `log (a / B) + k log 2` for `B ≤ a`. -/
def logCore (a B k : ℕ) : ℕ × ℕ :=
  ((2 * serLo ((a - B) * twoE / (a + B)) nLog + k * 799144290324076111,
    2 * serHi ((a - B) * twoE / (a + B) + 1) nLog +
      remHi ((a - B) * twoE / (a + B) + 1) a B + k * 799144290325229033))

/-- Mantissa bounds of `log (a / b)` for `b ≤ a`. -/
def logMantGe (a b : ℕ) : ℕ × ℕ :=
  logCore a (dblLoop 64 a b 0).1 (dblLoop 64 a b 0).2

/-- Mantissa bounds of `log (a / b)` for positive `a, b`. -/
def logMant (a b : ℕ) : ℤ × ℤ :=
  if b ≤ a then ((logMantGe a b).1, (logMantGe a b).2)
  else (-((logMantGe b a).2 : ℤ), -((logMantGe b a).1 : ℤ))

theorem l2M_lo : ((799144290324076111 : ℕ) : ℝ) / twoE ≤ Real.log 2 := by
  refine le_trans ?_ l2lo_le
  rw [div_le_iff₀ twoE_cast_pos]
  norm_num [l2lo, twoE]

theorem l2M_hi : Real.log 2 ≤ ((799144290325229033 : ℕ) : ℝ) / twoE := by
  refine le_trans le_l2hi ?_
  rw [le_div_iff₀ twoE_cast_pos]
  norm_num [l2hi, twoE]

/-- Real form of the atanh partial sum. -/
noncomputable def atanhSum (z : ℝ) : ℕ → ℝ
  | 0 => 0
  | j + 1 => atanhSum z j + z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ)

theorem logPolynomial_cast (q : ℚ) (n : ℕ) :
    ((logPolynomial q n : ℚ) : ℝ) = 2 * atanhSum (logCoordinate q : ℝ) n := by
  unfold logPolynomial
  push_cast
  congr 1
  induction n with
  | zero => simp [atanhSum]
  | succ n ih => rw [Finset.sum_range_succ, ih]; simp [atanhSum]

theorem serLo_le {Z : ℕ} {z : ℝ} (hZ : (Z : ℝ) / twoE ≤ z) (n : ℕ) :
    (serLo Z n : ℝ) / twoE ≤ atanhSum z n := by
  have hz0 : 0 ≤ (Z : ℝ) / twoE := by positivity
  have hE := twoE_cast_pos
  induction n with
  | zero => simp [serLo, atanhSum]
  | succ j ih =>
      simp only [serLo, atanhSum]
      push_cast
      have hd : (0 : ℝ) < ((2 * j + 1) * twoE ^ (2 * j) : ℕ) := by
        have := twoE_pos; positivity
      have h1 := natDiv_le (Z ^ (2 * j + 1)) ((2 * j + 1) * twoE ^ (2 * j))
      have h2 : ((Z ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * twoE ^ (2 * j) : ℕ) : ℝ) / twoE =
          ((Z : ℝ) / twoE) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
        have hE0 : (twoE : ℝ) ≠ 0 := ne_of_gt hE
        push_cast
        have h2j : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
        rw [div_pow]
        field_simp
        ring
      have h3 : ((Z : ℝ) / twoE) ^ (2 * j + 1) ≤ z ^ (2 * j + 1) := pow_le_pow_left₀ hz0 hZ _
      have h4 : ((Z : ℝ) / twoE) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ≤
          z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right h3 (by positivity)
      have h5 : (((Z ^ (2 * j + 1) / ((2 * j + 1) * twoE ^ (2 * j)) : ℕ) : ℝ)) / twoE ≤
          ((Z ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * twoE ^ (2 * j) : ℕ) : ℝ) / twoE :=
        div_le_div_of_nonneg_right h1 hE.le
      rw [h2] at h5
      push_cast at h5 h4 ⊢
      rw [add_div]
      linarith

theorem le_serHi {Z : ℕ} {z : ℝ} (hz0 : 0 ≤ z) (hZ : z ≤ (Z : ℝ) / twoE) (n : ℕ) :
    atanhSum z n ≤ (serHi Z n : ℝ) / twoE := by
  have hE := twoE_cast_pos
  induction n with
  | zero => simp [serHi, atanhSum]
  | succ j ih =>
      simp only [serHi, atanhSum]
      have hd : 0 < (2 * j + 1) * twoE ^ (2 * j) := by have := twoE_pos; positivity
      have h1 := le_cdiv (p := Z ^ (2 * j + 1)) hd
      have h2 : ((Z ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * twoE ^ (2 * j) : ℕ) : ℝ) / twoE =
          ((Z : ℝ) / twoE) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) := by
        have hE0 : (twoE : ℝ) ≠ 0 := ne_of_gt hE
        push_cast
        have h2j : (2 * (j : ℝ) + 1) ≠ 0 := by positivity
        rw [div_pow]
        field_simp
        ring
      have h3 : z ^ (2 * j + 1) ≤ ((Z : ℝ) / twoE) ^ (2 * j + 1) := pow_le_pow_left₀ hz0 hZ _
      have h4 : z ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) ≤
          ((Z : ℝ) / twoE) ^ (2 * j + 1) / ((2 * j + 1 : ℕ) : ℝ) :=
        div_le_div_of_nonneg_right h3 (by positivity)
      have h5 : ((Z ^ (2 * j + 1) : ℕ) : ℝ) / (((2 * j + 1) * twoE ^ (2 * j) : ℕ) : ℝ) / twoE ≤
          ((cdiv (Z ^ (2 * j + 1)) ((2 * j + 1) * twoE ^ (2 * j)) : ℕ) : ℝ) / twoE :=
        div_le_div_of_nonneg_right h1 hE.le
      rw [h2] at h5
      push_cast at h5 h4 ⊢
      rw [add_div]
      linarith

theorem remainder_le {a B Zh : ℕ} {z : ℝ} (hB : 0 < B) (ha : 0 < a)
    (hz0 : 0 ≤ z) (hzh : z ≤ (Zh : ℝ) / twoE)
    (hz1 : 1 - z ^ 2 = 4 * a * B / ((a : ℝ) + B) ^ 2) :
    2 * (z ^ (2 * nLog + 1) / (1 - z ^ 2)) ≤ (remHi Zh a B : ℝ) / twoE := by
  have hE := twoE_cast_pos
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hd : 0 < twoE ^ (2 * nLog) * (4 * a * B) := by have := twoE_pos; positivity
  have hc := le_cdiv (p := 2 * Zh ^ (2 * nLog + 1) * (a + B) ^ 2) hd
  have hpow : z ^ (2 * nLog + 1) ≤ ((Zh : ℝ) / twoE) ^ (2 * nLog + 1) :=
    pow_le_pow_left₀ hz0 hzh _
  rw [hz1]
  have e1 : 2 * (z ^ (2 * nLog + 1) / (4 * a * B / ((a : ℝ) + B) ^ 2)) =
      z ^ (2 * nLog + 1) * (2 * ((a : ℝ) + B) ^ 2 / (4 * a * B)) := by
    field_simp
  have e2 : ((Zh : ℝ) / twoE) ^ (2 * nLog + 1) * (2 * ((a : ℝ) + B) ^ 2 / (4 * a * B)) =
      ((2 * Zh ^ (2 * nLog + 1) * (a + B) ^ 2 : ℕ) : ℝ) /
        ((twoE ^ (2 * nLog) * (4 * a * B) : ℕ) : ℝ) / twoE := by
    push_cast
    rw [div_pow, pow_succ (twoE : ℝ)]
    field_simp
  have hfac : (0 : ℝ) ≤ 2 * ((a : ℝ) + B) ^ 2 / (4 * a * B) := by positivity
  rw [e1]
  calc z ^ (2 * nLog + 1) * (2 * ((a : ℝ) + B) ^ 2 / (4 * a * B))
      ≤ ((Zh : ℝ) / twoE) ^ (2 * nLog + 1) * (2 * ((a : ℝ) + B) ^ 2 / (4 * a * B)) :=
        mul_le_mul_of_nonneg_right hpow hfac
    _ = _ := e2
    _ ≤ (remHi Zh a B : ℝ) / twoE := by
        unfold remHi
        exact div_le_div_of_nonneg_right hc hE.le

theorem logCore_sound {a B k : ℕ} (hB : 0 < B) (hBa : B ≤ a) :
    ((logCore a B k).1 : ℝ) / twoE ≤ Real.log ((a : ℝ) / B) + k * Real.log 2 ∧
      Real.log ((a : ℝ) / B) + k * Real.log 2 ≤ ((logCore a B k).2 : ℝ) / twoE := by
  have hE := twoE_cast_pos
  have ha : 0 < a := lt_of_lt_of_le hB hBa
  have haR : (0 : ℝ) < a := by exact_mod_cast ha
  have hBR : (0 : ℝ) < B := by exact_mod_cast hB
  have hBaR : (B : ℝ) ≤ a := by exact_mod_cast hBa
  set q : ℚ := (a : ℚ) / B with hqdef
  have hq1 : 1 ≤ q := by
    rw [hqdef, le_div_iff₀ (by exact_mod_cast hB)]
    simpa using (Nat.cast_le (α := ℚ)).mpr hBa
  have hqpos : 0 < q := lt_of_lt_of_le one_pos hq1
  have hqR : ((q : ℚ) : ℝ) = (a : ℝ) / B := by rw [hqdef]; push_cast; ring
  set z : ℝ := ((a : ℝ) - B) / (a + B) with hzdef
  have hzc : ((logCoordinate q : ℚ) : ℝ) = z := by
    unfold logCoordinate
    rw [hzdef]
    push_cast
    rw [hqR]
    field_simp
  have hz0 : 0 ≤ z := by
    rw [hzdef]
    exact div_nonneg (by linarith) (by positivity)
  have hz1 : 1 - z ^ 2 = 4 * a * B / ((a : ℝ) + B) ^ 2 := by
    rw [hzdef]; field_simp; ring
  set Z : ℕ := (a - B) * twoE / (a + B) with hZdef
  have hsub : (((a - B : ℕ)) : ℝ) = (a : ℝ) - B := by
    rw [Nat.cast_sub hBa]
  have hZlo : (Z : ℝ) / twoE ≤ z := by
    have h := natDiv_le ((a - B) * twoE) (a + B)
    rw [← hZdef] at h
    push_cast at h
    rw [hsub] at h
    rw [div_le_iff₀ hE, hzdef]
    calc (Z : ℝ) ≤ ((a : ℝ) - B) * twoE / (a + B) := h
      _ = ((a : ℝ) - B) / (a + B) * twoE := by ring
  have hZhi : z ≤ ((Z + 1 : ℕ) : ℝ) / twoE := by
    have h2 := Nat.lt_mul_div_succ ((a - B) * twoE) (show 0 < a + B by omega)
    rw [← hZdef] at h2
    have h3 := (Nat.cast_lt (α := ℝ)).mpr h2
    push_cast at h3
    rw [hsub] at h3
    rw [le_div_iff₀ hE, hzdef, div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    push_cast
    linarith
  have hlow := logPolynomial_le_log hq1 nLog
  have hrem := logPolynomial_remainder hqpos nLog
  rw [logPolynomial_cast, hzc, hqR] at hlow hrem
  have hremU := (abs_le.mp hrem).2
  have hR : ((logRemainder q nLog : ℚ) : ℝ) ≤ ((remHi (Z + 1) a B : ℕ) : ℝ) / twoE := by
    unfold logRemainder
    push_cast
    rw [hzc, abs_of_nonneg hz0]
    exact remainder_le hB ha hz0 hZhi hz1
  have hsl := serLo_le hZlo nLog
  have hsh := le_serHi hz0 hZhi nLog
  have hk : (0 : ℝ) ≤ k := by positivity
  have hl1 := mul_le_mul_of_nonneg_left l2M_lo hk
  have hl2 := mul_le_mul_of_nonneg_left l2M_hi hk
  unfold logCore
  rw [← hZdef]
  push_cast at hl1 hl2 ⊢
  constructor
  · have : ((2 * (serLo Z nLog : ℝ) + k * 799144290324076111) / twoE) =
        2 * ((serLo Z nLog : ℝ) / twoE) + k * ((799144290324076111 : ℝ) / twoE) := by ring
    rw [this]
    linarith
  · have : ((2 * (serHi (Z + 1) nLog : ℝ) + (remHi (Z + 1) a B : ℝ) + k * 799144290325229033) / twoE) =
        2 * ((serHi (Z + 1) nLog : ℝ) / twoE) + (remHi (Z + 1) a B : ℝ) / twoE +
          k * ((799144290325229033 : ℝ) / twoE) := by ring
    rw [this]
    linarith

theorem logMantGe_sound {a b : ℕ} (hb : 0 < b) (hba : b ≤ a) :
    ((logMantGe a b).1 : ℝ) / twoE ≤ Real.log ((a : ℝ) / b) ∧
      Real.log ((a : ℝ) / b) ≤ ((logMantGe a b).2 : ℝ) / twoE := by
  obtain ⟨h1, h2, _⟩ := dblLoop_spec 64 a b 0 hba
  set B := (dblLoop 64 a b 0).1
  set k := (dblLoop 64 a b 0).2
  have hbR : (0 : ℝ) < b := by exact_mod_cast hb
  have hB : 0 < B := by rw [h2]; positivity
  have hs := logCore_sound (k := k) hB h1
  have hlog : Real.log ((a : ℝ) / b) = Real.log ((a : ℝ) / B) + k * Real.log 2 := by
    have haR : (0 : ℝ) < a := by
      have : 0 < a := lt_of_lt_of_le hb hba
      exact_mod_cast this
    rw [h2, Nat.sub_zero]
    push_cast
    rw [Real.log_div haR.ne' hbR.ne', Real.log_div haR.ne' (by positivity),
      Real.log_mul hbR.ne' (by positivity), Real.log_pow]
    ring
  unfold logMantGe
  rw [hlog]
  exact hs

theorem logMant_sound {a b : ℕ} (ha : 0 < a) (hb : 0 < b) :
    ((logMant a b).1 : ℝ) / twoE ≤ Real.log ((a : ℝ) / b) ∧
      Real.log ((a : ℝ) / b) ≤ ((logMant a b).2 : ℝ) / twoE := by
  unfold logMant
  split_ifs with h
  · have := logMantGe_sound hb h
    push_cast
    exact this
  · have h' : a ≤ b := by omega
    obtain ⟨h1, h2⟩ := logMantGe_sound ha h'
    have hl : Real.log ((a : ℝ) / b) = -Real.log ((b : ℝ) / a) := by
      rw [← Real.log_inv, inv_div]
    rw [hl]
    push_cast
    constructor
    · rw [neg_div]; linarith
    · rw [neg_div]; linarith

end Li2Lean.P0.CA.Frequency
