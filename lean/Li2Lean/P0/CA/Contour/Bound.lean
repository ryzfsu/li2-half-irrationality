/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.FourierConst
import Li2Lean.P0.ConfigLogEnclosures
import Li2Lean.P0.MixedCellClearanceFull

/-!
# A crude global bound for the second derivative

For every `θ`, `|W2 θ| ≤ 2200`.  The proof uses only the
proved clearance of the ellipse from the real sources
(`mixedCellClearance_full`), the trivial bounds on `cos`, `sin`, `arctan`,
the reference masses, and `|moment| ≤ contour mass`.
-/

namespace Li2Lean.P0.CA.Contour

noncomputable section

open Li2Lean.P0.ConfigSegment
open Li2Lean.P0.ConfigContourSelfPotential
open Li2Lean.P0.ConfigContourKernel
open Li2Lean.P0.ConfigContourReference

/-- Shifts `κ` used by the closed form: either `-κ ∈ [0,2]` or `κ ∈ [1/2, 11/2]`. -/
def Shift (κ : ℝ) : Prop := (0 ≤ -κ ∧ -κ ≤ 2) ∨ (1 / 2 ≤ κ ∧ κ ≤ 11 / 2)

theorem norm_ellipse_add (θ κ : ℝ) :
    ‖Li2Lean.p0EllipsePoint 1 θ + (κ : ℂ)‖ =
      Real.sqrt ((ellX θ + κ) ^ 2 + ellY θ ^ 2) := by
  rw [ellipse_eq]
  have : ((ellX θ : ℂ) + (ellY θ : ℂ) * Complex.I) + (κ : ℂ) =
      ((ellX θ + κ : ℝ) : ℂ) + (ellY θ : ℂ) * Complex.I := by push_cast; ring
  rw [this, Complex.norm_add_mul_I]

theorem dist_lower (θ : ℝ) {κ : ℝ} (hκ : Shift κ) :
    (9 / 400 : ℝ) ≤ (ellX θ + κ) ^ 2 + ellY θ ^ 2 := by
  have hmem : Li2Lean.p0EllipsePoint 1 θ ∈ Config.baseEllipseSet := ⟨θ, rfl⟩
  have hsq : ∀ d : ℝ, 0 ≤ d → (9 / 400 : ℝ) ≤ d ^ 2 →
      d ≤ Real.sqrt ((ellX θ + κ) ^ 2 + ellY θ ^ 2) →
      (9 / 400 : ℝ) ≤ (ellX θ + κ) ^ 2 + ellY θ ^ 2 := by
    intro d hd0 hd2 hd
    have h2 := pow_le_pow_left₀ hd0 hd 2
    rw [Real.sq_sqrt (by positivity)] at h2
    linarith
  rcases hκ with ⟨h0, h2⟩ | ⟨h0, h2⟩
  · have h := Config.mixedCellClearance_full.1 _ hmem (-κ) ⟨h0, h2⟩
    rw [show Li2Lean.p0EllipsePoint 1 θ - ((-κ : ℝ) : ℂ) =
        Li2Lean.p0EllipsePoint 1 θ + (κ : ℂ) by push_cast; ring,
      norm_ellipse_add] at h
    exact hsq _ (by norm_num [Config.dPlus]) (by norm_num [Config.dPlus]) h
  · have h := Config.mixedCellClearance_full.2 _ hmem κ h0
    rw [norm_ellipse_add] at h
    exact hsq _ (by norm_num [Config.dMinus]) (by norm_num [Config.dMinus]) h

theorem dist_upper (θ : ℝ) {κ : ℝ} (hκ : Shift κ) :
    (ellX θ + κ) ^ 2 + ellY θ ^ 2 ≤ 64 := by
  have hc1 := Real.neg_one_le_cos θ
  have hc2 := Real.cos_le_one θ
  have hs := Real.sin_sq_le_one θ
  have hk : -2 ≤ κ ∧ κ ≤ 11 / 2 := by
    rcases hκ with ⟨h0, h2⟩ | ⟨h0, h2⟩ <;> constructor <;> linarith
  unfold ellX ellY
  nlinarith [hk.1, hk.2]

theorem log_two_lt : Real.log 2 < 6931471806 / 10000000000 := by
  have := ConfigLogEnclosures.logTwo_strict_upper_v10
  linarith

theorem abs_log_le {D : ℝ} (h1 : (9 / 400 : ℝ) ≤ D) (h2 : D ≤ 64) :
    |Real.log D| ≤ 6 * (6931471806 / 10000000000) := by
  have h64 : Real.log 64 = 6 * Real.log 2 := by
    rw [show (64 : ℝ) = 2 ^ 6 by norm_num, Real.log_pow]; norm_num
  have hD : 0 < D := by linarith
  have hup : Real.log D ≤ Real.log 64 := Real.log_le_log hD h2
  have hlo : Real.log (400 / 9) ≤ Real.log 64 := Real.log_le_log (by norm_num) (by norm_num)
  have hinv : Real.log (9 / 400) = -Real.log (400 / 9) := by
    rw [show (9 / 400 : ℝ) = (400 / 9)⁻¹ by norm_num, Real.log_inv]
  have hlo2 : Real.log (9 / 400) ≤ Real.log D := Real.log_le_log (by norm_num) h1
  have := log_two_lt
  rw [abs_le]
  constructor <;> linarith

theorem d2Gr_bound {u v a b a2 b2 δ : ℝ} (hδ : 0 < δ)
    (hδ2 : δ ^ 2 ≤ u ^ 2 + v ^ 2)
    (hD1 : (9 / 400 : ℝ) ≤ u ^ 2 + v ^ 2) (hD2 : u ^ 2 + v ^ 2 ≤ 64)
    (hS : a ^ 2 + b ^ 2 ≤ (12783 / 10000) ^ 2)
    (ha2 : |a2| ≤ 12783 / 10000) (hb2 : |b2| ≤ 229 / 200) :
    |d2Gr u v a b a2 b2| ≤ 2 * (12783 / 10000) ^ 2 / δ +
      6 * (6931471806 / 10000000000) / 2 * (12783 / 10000) +
      3141593 / 2000000 * (229 / 200) := by
  set D := u ^ 2 + v ^ 2 with hDdef
  have hDpos : 0 < D := by linarith
  have hT1eq : (u * a + v * b) / D * a + (a * v - u * b) / D * b =
      (u * (a ^ 2 - b ^ 2) + 2 * v * a * b) / D := by
    field_simp; ring
  have hu : |u| * δ ≤ D := by
    by_cases h : |u| ≤ δ
    · nlinarith [abs_nonneg u, sq_nonneg v]
    · push Not at h
      have : |u| * δ ≤ |u| * |u| := by nlinarith [abs_nonneg u]
      have hu2 : |u| * |u| = u ^ 2 := by rw [← sq, sq_abs]
      nlinarith [sq_nonneg v]
  have hv : |v| * δ ≤ D := by
    by_cases h : |v| ≤ δ
    · nlinarith [abs_nonneg v, sq_nonneg u]
    · push Not at h
      have : |v| * δ ≤ |v| * |v| := by nlinarith [abs_nonneg v]
      have hv2 : |v| * |v| = v ^ 2 := by rw [← sq, sq_abs]
      nlinarith [sq_nonneg u]
  have hS0 : 0 ≤ a ^ 2 + b ^ 2 := by positivity
  have hnum : |u * (a ^ 2 - b ^ 2) + 2 * v * a * b| ≤ (|u| + |v|) * (a ^ 2 + b ^ 2) := by
    have h1 : |u * (a ^ 2 - b ^ 2)| ≤ |u| * (a ^ 2 + b ^ 2) := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg u)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg a, sq_nonneg b]
    have h2 : |2 * v * a * b| ≤ |v| * (a ^ 2 + b ^ 2) := by
      rw [show 2 * v * a * b = v * (2 * a * b) by ring, abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg v)
      rw [abs_le]; constructor <;> nlinarith [sq_nonneg (a + b), sq_nonneg (a - b)]
    calc _ ≤ |u * (a ^ 2 - b ^ 2)| + |2 * v * a * b| := abs_add_le _ _
      _ ≤ _ := by nlinarith
  have hT1 : |(u * a + v * b) / D * a + (a * v - u * b) / D * b| ≤
      2 * (12783 / 10000) ^ 2 / δ := by
    rw [hT1eq, abs_div, abs_of_pos hDpos, div_le_div_iff₀ hDpos hδ]
    have : (|u| + |v|) * (a ^ 2 + b ^ 2) * δ ≤ 2 * D * (a ^ 2 + b ^ 2) := by
      nlinarith
    nlinarith
  have hlog := abs_log_le hD1 hD2
  have hT2 : |Real.log D / 2 * a2| ≤ 6 * (6931471806 / 10000000000) / 2 * (12783 / 10000) := by
    rw [abs_mul, abs_div, abs_two]
    apply mul_le_mul (by linarith) ha2 (abs_nonneg _) (by positivity)
  have hat : |Real.arctan (u / v)| ≤ 3141593 / 2000000 := by
    have h1 := Real.arctan_lt_pi_div_two (u / v)
    have h2 := Real.neg_pi_div_two_lt_arctan (u / v)
    have hp := Real.pi_lt_d6
    rw [abs_le]; constructor <;> linarith
  have hT3 : |Real.arctan (u / v) * b2| ≤ 3141593 / 2000000 * (229 / 200) := by
    rw [abs_mul]
    exact mul_le_mul hat hb2 (abs_nonneg _) (by positivity)
  have hsplit : d2Gr u v a b a2 b2 =
      ((u * a + v * b) / D * a + (a * v - u * b) / D * b) +
        Real.log D / 2 * a2 + Real.arctan (u / v) * b2 := by
    unfold d2Gr; ring
  rw [hsplit]
  have e1 := abs_add_le ((u * a + v * b) / D * a + (a * v - u * b) / D * b +
    Real.log D / 2 * a2) (Real.arctan (u / v) * b2)
  have e2 := abs_add_le ((u * a + v * b) / D * a + (a * v - u * b) / D * b)
    (Real.log D / 2 * a2)
  linarith

/-- The pinned sources `x ∈ [1/4, 5/4]` stay at distance `≥ 2/5` from the contour. -/
theorem dist_lower_P (θ : ℝ) {x : ℝ} (h1 : 1 / 4 ≤ x) (h2 : x ≤ 5 / 4) :
    (4 / 25 : ℝ) ≤ (ellX θ - x) ^ 2 + ellY θ ^ 2 := by
  have hc1 := Real.neg_one_le_cos θ
  have hc2 := Real.cos_le_one θ
  have hs := Real.sin_sq_add_cos_sq θ
  unfold ellX ellY
  set C := Real.cos θ
  set y := (11281 / 10000 : ℝ) - x
  have hy1 : y ≤ 8781 / 10000 := by simp only [y]; linarith
  have hy2 : -(1219 / 10000) ≤ y := by simp only [y]; linarith
  have e : (11281 / 10000 + 12783 / 10000 * C - x) ^ 2 + (229 / 200 * Real.sin θ) ^ 2 =
      (12783 / 10000 * C + y) ^ 2 + (229 / 200) ^ 2 * (1 - C ^ 2) := by
    simp only [y]; nlinarith [hs]
  rw [e]
  by_cases hy : 3 / 10 ≤ y
  · have : (12783 / 10000 * C + y) ^ 2 + (229 / 200) ^ 2 * (1 - C ^ 2) -
        (12783 / 10000 - y) ^ 2 =
        (C + 1) * (((12783 / 10000) ^ 2 - (229 / 200) ^ 2) * (C - 1) +
          2 * (12783 / 10000) * y) := by ring
    have hpos : 0 ≤ (C + 1) * (((12783 / 10000) ^ 2 - (229 / 200) ^ 2) * (C - 1) +
        2 * (12783 / 10000) * y) := by
      apply mul_nonneg (by linarith)
      nlinarith
    nlinarith
  · push Not at hy
    nlinarith [sq_nonneg (((12783 / 10000) ^ 2 - (229 / 200) ^ 2) * C + 12783 / 10000 * y)]

/-! ## Sums of reference densities -/

theorem sum_getD_cast (l : List ℕ) :
    ∑ j ∈ Finset.range l.length, ((l.getD j 0 : ℕ) : ℝ) = (l.sum : ℝ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      rw [List.length_cons, Finset.sum_range_succ', List.sum_cons]
      simp only [List.getD_cons_succ, List.getD_cons_zero]
      rw [ih]; push_cast; ring

theorem sum_density (l : List ℕ) :
    ∑ j ∈ Finset.range l.length, referenceDensity l j =
      32 * (l.sum : ℝ) / (ConfigData.referenceDenominator : ℝ) := by
  unfold referenceDensity
  rw [← Finset.sum_div, ← Finset.mul_sum, sum_getD_cast]

theorem sum_ρp : ∑ j ∈ Finset.range 32, ρp j = 32 * 732114048060 / 1000000000000 := by
  have h := sum_density ConfigData.pinnedMassUnits
  rw [ConfigData.pinnedMassUnits_length, ConfigData.pinnedMassUnits_sum] at h
  unfold ρp; rw [h]; norm_num [ConfigData.referenceDenominator]

theorem sum_ρf : ∑ j ∈ Finset.range 160, ρf j = 32 := by
  have h := sum_density ConfigData.frequencyMassUnits
  rw [ConfigData.frequencyMassUnits_length, ConfigData.frequencyMassUnits_sum] at h
  unfold ρf; rw [h]; norm_num [ConfigData.referenceDenominator]

theorem shift_pL {j : ℕ} (hj : j ∈ Finset.range 32) : Shift (-pL j) := by
  have : (j : ℝ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  left; unfold pL referenceCellLeft; constructor <;>
    · simp only [neg_neg]; have : (0 : ℝ) ≤ j := by positivity
      linarith

theorem shift_pR {j : ℕ} (hj : j ∈ Finset.range 32) : Shift (-pR j) := by
  have : (j : ℝ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  left; unfold pR referenceCellRight; push_cast; constructor <;>
    · simp only [neg_neg]; have : (0 : ℝ) ≤ j := by positivity
      linarith

theorem shift_fL {j : ℕ} (hj : j ∈ Finset.range 160) : Shift (fL j) := by
  have : (j : ℝ) ≤ 159 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  right; unfold fL referenceCellLeft; constructor <;>
    · have : (0 : ℝ) ≤ j := by positivity
      linarith

theorem shift_fR {j : ℕ} (hj : j ∈ Finset.range 160) : Shift (fR j) := by
  have : (j : ℝ) ≤ 159 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  right; unfold fR referenceCellRight; push_cast; constructor <;>
    · have : (0 : ℝ) ≤ j := by positivity
      linarith

theorem ρp_nonneg (j : ℕ) : 0 ≤ ρp j := referenceDensity_nonneg _ _
theorem ρf_nonneg (j : ℕ) : 0 ≤ ρf j := referenceDensity_nonneg _ _

def ShiftA (κ : ℝ) : Prop := 0 ≤ -κ ∧ -κ ≤ 2
def ShiftP (κ : ℝ) : Prop := 1 / 4 ≤ -κ ∧ -κ ≤ 5 / 4
def ShiftF (κ : ℝ) : Prop := 1 / 2 ≤ κ ∧ κ ≤ 11 / 2

theorem shiftP_pL {j : ℕ} (hj : j ∈ Finset.range 32) : ShiftP (-pL j) := by
  have : (j : ℝ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have : (0 : ℝ) ≤ j := by positivity
  unfold ShiftP pL referenceCellLeft; simp only [neg_neg]; constructor <;> linarith

theorem shiftP_pR {j : ℕ} (hj : j ∈ Finset.range 32) : ShiftP (-pR j) := by
  have : (j : ℝ) ≤ 31 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have : (0 : ℝ) ≤ j := by positivity
  unfold ShiftP pR referenceCellRight; push_cast; simp only [neg_neg]; constructor <;> linarith

theorem shiftF_fL {j : ℕ} (hj : j ∈ Finset.range 160) : ShiftF (fL j) := by
  have : (j : ℝ) ≤ 159 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have : (0 : ℝ) ≤ j := by positivity
  unfold ShiftF fL referenceCellLeft; constructor <;> linarith

theorem shiftF_fR {j : ℕ} (hj : j ∈ Finset.range 160) : ShiftF (fR j) := by
  have : (j : ℝ) ≤ 159 := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have : (0 : ℝ) ≤ j := by positivity
  unfold ShiftF fR referenceCellRight; push_cast; constructor <;> linarith

theorem segComb_abs_le {g : ℝ → ℝ} {KA KP KF lin : ℝ}
    (hA : ∀ κ, ShiftA κ → |g κ| ≤ KA) (hP : ∀ κ, ShiftP κ → |g κ| ≤ KP)
    (hF : ∀ κ, ShiftF κ → |g κ| ≤ KF) :
    |segComb g lin 0| ≤ (2 + 4 * (32 * 732114048060 / 1000000000000)) * KP + 3 * KA +
      (1 + 2 * 32) * KF + |lin| := by
  have hs1 : |∑ j ∈ Finset.range 32, ρp j * (g (-pL j) - g (-pR j))| ≤
      (32 * 732114048060 / 1000000000000) * (2 * KP) := by
    calc _ ≤ ∑ j ∈ Finset.range 32, |ρp j * (g (-pL j) - g (-pR j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range 32, ρp j * (2 * KP) := by
          apply Finset.sum_le_sum; intro j hj
          rw [abs_mul, abs_of_nonneg (ρp_nonneg j)]
          apply mul_le_mul_of_nonneg_left _ (ρp_nonneg j)
          have := hP _ (shiftP_pL hj); have := hP _ (shiftP_pR hj)
          calc |g (-pL j) - g (-pR j)| ≤ |g (-pL j)| + |g (-pR j)| := abs_sub _ _
            _ ≤ 2 * KP := by linarith
      _ = _ := by rw [← Finset.sum_mul, sum_ρp]
  have hs2 : |∑ j ∈ Finset.range 160, ρf j * (g (fR j) - g (fL j))| ≤ 32 * (2 * KF) := by
    calc _ ≤ ∑ j ∈ Finset.range 160, |ρf j * (g (fR j) - g (fL j))| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j ∈ Finset.range 160, ρf j * (2 * KF) := by
          apply Finset.sum_le_sum; intro j hj
          rw [abs_mul, abs_of_nonneg (ρf_nonneg j)]
          apply mul_le_mul_of_nonneg_left _ (ρf_nonneg j)
          have := hF _ (shiftF_fR hj); have := hF _ (shiftF_fL hj)
          calc |g (fR j) - g (fL j)| ≤ |g (fR j)| + |g (fL j)| := abs_sub _ _
            _ ≤ 2 * KF := by linarith
      _ = _ := by rw [← Finset.sum_mul, sum_ρf]
  have p1 := hP (-(1 / 4)) ⟨by norm_num, by norm_num⟩
  have p2 := hP (-(5 / 4)) ⟨by norm_num, by norm_num⟩
  have a0 := hA 0 ⟨by norm_num, by norm_num⟩
  have a2 := hA (-2) ⟨by norm_num, by norm_num⟩
  have f0 := hF (1 / 2) ⟨by norm_num, by norm_num⟩
  unfold segComb
  set S1 := ∑ j ∈ Finset.range 32, ρp j * (g (-pL j) - g (-pR j))
  set S2 := ∑ j ∈ Finset.range 160, ρf j * (g (fR j) - g (fL j))
  have e : (g (-(1 / 4)) - g (-(5 / 4)) + (g 0 - g (-2))) - (lin + (g (1 / 2) - g 0) + 0) -
      2 * S1 - S2 = g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0 -
      lin - 2 * S1 - S2 := by ring
  rw [e]
  have t6 : |2 * S1| = 2 * |S1| := by rw [abs_mul]; norm_num
  have tri : ∀ a b : ℝ, |a - b| ≤ |a| + |b| := fun a b => abs_sub a b
  have tri2 : ∀ a b : ℝ, |a + b| ≤ |a| + |b| := fun a b => abs_add_le a b
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0 - lin - 2 * S1) S2
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0 - lin) (2 * S1)
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2) + g 0) lin
  have := tri2 (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2) - g (1 / 2)) (g 0)
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0 - g (-2)) (g (1 / 2))
  have := tri (g (-(1 / 4)) - g (-(5 / 4)) + g 0) (g (-2))
  have := tri2 (g (-(1 / 4)) - g (-(5 / 4))) (g 0)
  have := tri (g (-(1 / 4))) (g (-(5 / 4)))
  linarith

/-! ## The Fourier part -/

def bAbs (n : ℕ) : ℚ := max |(bLit.getD n ⟨0, 0⟩).lo| |(bLit.getD n ⟨0, 0⟩).hi|

theorem bR_abs_le {n : ℕ} (hn : n < 48) : |bR n| ≤ (bAbs n : ℝ) := by
  have h := bLit_mem hn
  unfold bAbs
  push_cast
  rw [abs_le]
  constructor
  · have := neg_abs_le ((bLit.getD n ⟨0, 0⟩).lo : ℝ)
    have := le_max_left |((bLit.getD n ⟨0, 0⟩).lo : ℝ)| |((bLit.getD n ⟨0, 0⟩).hi : ℝ)|
    linarith [h.1]
  · have := le_abs_self ((bLit.getD n ⟨0, 0⟩).hi : ℝ)
    have := le_max_right |((bLit.getD n ⟨0, 0⟩).lo : ℝ)| |((bLit.getD n ⟨0, 0⟩).hi : ℝ)|
    linarith [h.2]

def bSum2 : ℕ → ℚ
  | 0 => 0
  | n + 1 => bSum2 n + bAbs n * (n + 1) ^ 2

theorem bSum2_le : bSum2 48 ≤ 23 / 10 := by decide +kernel

theorem bSum2_eq (n : ℕ) : ((bSum2 n : ℚ) : ℝ) =
    ∑ k ∈ Finset.range n, (bAbs k : ℝ) * ((k : ℝ) + 1) ^ 2 := by
  induction n with
  | zero => simp [bSum2]
  | succ n ih => rw [bSum2, Finset.sum_range_succ]; push_cast; rw [ih]

theorem F2_abs_le (θ : ℝ) : |F2 θ| ≤ 23 / 10 := by
  unfold F2
  calc _ ≤ ∑ n ∈ Finset.range 48,
        |bR n * ((n + 1 : ℝ) ^ 2 * Real.cos ((n + 1 : ℝ) * θ))| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ n ∈ Finset.range 48, (bAbs n : ℝ) * ((n : ℝ) + 1) ^ 2 := by
        apply Finset.sum_le_sum; intro n hn
        have hb := bR_abs_le (Finset.mem_range.mp hn)
        have hc := Real.abs_cos_le_one ((n + 1 : ℝ) * θ)
        rw [abs_mul, abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ (n + 1 : ℝ) ^ 2)]
        calc |bR n| * ((n + 1 : ℝ) ^ 2 * |Real.cos ((n + 1 : ℝ) * θ)|)
            ≤ |bR n| * ((n + 1 : ℝ) ^ 2 * 1) := by gcongr
          _ ≤ (bAbs n : ℝ) * ((n : ℝ) + 1) ^ 2 := by
              rw [mul_one]; exact mul_le_mul_of_nonneg_right hb (by positivity)
    _ = ((bSum2 48 : ℚ) : ℝ) := (bSum2_eq 48).symm
    _ ≤ 23 / 10 := by
        have h : ((bSum2 48 : ℚ) : ℝ) ≤ ((23 / 10 : ℚ) : ℝ) := by exact_mod_cast bSum2_le
        simpa using h

/-- Global second-derivative bound for the contour closed form. -/
theorem W2_abs_le {θ : ℝ} : |W2 θ| ≤ 2200 := by
  have hS : ellX1 θ ^ 2 + ellY1 θ ^ 2 ≤ (12783 / 10000) ^ 2 := by
    unfold ellX1 ellY1
    nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg (Real.cos θ)]
  have ha2 : |ellX2 θ| ≤ 12783 / 10000 := by
    unfold ellX2; rw [abs_mul]
    have := Real.abs_cos_le_one θ
    norm_num; nlinarith [abs_nonneg (Real.cos θ)]
  have hb2 : |ellY2 θ| ≤ 229 / 200 := by
    unfold ellY2; rw [abs_mul]
    have := Real.abs_sin_le_one θ
    norm_num; nlinarith [abs_nonneg (Real.sin θ)]
  have hA : ∀ κ, ShiftA κ →
      |d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ)| ≤ 2625 / 100 := by
    intro κ hκ
    have hs : Shift κ := Or.inl hκ
    have := d2Gr_bound (δ := 3 / 20) (by norm_num) (by have := dist_lower θ hs; nlinarith)
      (dist_lower θ hs) (dist_upper θ hs) hS ha2 hb2
    linarith
  have hP : ∀ κ, ShiftP κ →
      |d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ)| ≤ 1263 / 100 := by
    intro κ hκ
    have hs : Shift κ := Or.inl ⟨by linarith [hκ.1], by linarith [hκ.2]⟩
    have hd := dist_lower_P θ (x := -κ) hκ.1 hκ.2
    rw [sub_neg_eq_add] at hd
    have := d2Gr_bound (δ := 2 / 5) (by norm_num) (by nlinarith)
      (dist_lower θ hs) (dist_upper θ hs) hS ha2 hb2
    linarith
  have hF : ∀ κ, ShiftF κ →
      |d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ) (ellY2 θ)| ≤ 138 / 10 := by
    intro κ hκ
    have hs : Shift κ := Or.inr hκ
    have hmem : Li2Lean.p0EllipsePoint 1 θ ∈ Config.baseEllipseSet := ⟨θ, rfl⟩
    have h := Config.mixedCellClearance_full.2 _ hmem κ hκ.1
    rw [norm_ellipse_add] at h
    have h2 := pow_le_pow_left₀ (by norm_num [Config.dMinus]) h 2
    rw [Real.sq_sqrt (by positivity)] at h2
    have := d2Gr_bound (δ := 1749 / 5000) (by norm_num) (by norm_num [Config.dMinus] at h2 ⊢; linarith)
      (dist_lower θ hs) (dist_upper θ hs) hS ha2 hb2
    linarith
  have hseg := segComb_abs_le (lin := ellX2 θ * Real.log 2) hA hP hF
  have hlin : |ellX2 θ * Real.log 2| ≤ 1 := by
    rw [abs_mul]
    have h2 : |Real.log 2| ≤ 7 / 10 := by
      rw [abs_of_pos (Real.log_pos (by norm_num))]; linarith [log_two_lt]
    nlinarith [abs_nonneg (ellX2 θ), abs_nonneg (Real.log 2)]
  have hF2 := F2_abs_le θ
  unfold W2
  calc _ ≤ |segComb (fun κ => d2Gr (ellX θ + κ) (ellY θ) (ellX1 θ) (ellY1 θ) (ellX2 θ)
        (ellY2 θ)) (ellX2 θ * Real.log 2) 0| + |2 * F2 θ| := abs_sub _ _
    _ ≤ 2200 := by
        rw [abs_mul, abs_two]
        linarith

end

end Li2Lean.P0.CA.Contour
