/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.Arith
import Li2Lean.P0.ConfigFejerLog

/-!
# CA-F: rational enclosures of the actual Fejer cosine moments

`ConfigFejerLog.contourMoment n` is the literal v10 moment
`(1 - n/49) * sum_j w_j cos(n * pi * (2 j + 1) / 64)` with the Appendix A
weights.  The cosines are enclosed by an exact rotation recurrence started
from `cos(pi/64) = sqrtTwoAddSeries 0 5 / 2` (Mathlib) and
`sin(pi/64) = sqrt(1 - cos(pi/64)^2)`.  All arithmetic is rational with
outward rounding to `2^-120`; the final table is checked by the kernel.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.P0.ConfigContourReference Li2Lean.P0.ConfigFejerLog

/-- Constant precision `2^120`. -/
def cScale : ℚ := 1329227995784915872903807060280344576

theorem cScale_pos : (0 : ℚ) < cScale := by norm_num [cScale]

/-- Interval for `sqrtTwoAddSeries 0 n`. -/
def seriesIv : ℕ → ℚ × ℚ
  | 0 => (0, 0)
  | n + 1 => (sqrtLoAt cScale (2 + (seriesIv n).1), sqrtHiAt cScale (2 + (seriesIv n).2))

theorem seriesIv_sound (n : ℕ) :
    0 ≤ (seriesIv n).1 ∧ ((seriesIv n).1 : ℝ) ≤ Real.sqrtTwoAddSeries 0 n ∧
      Real.sqrtTwoAddSeries 0 n ≤ ((seriesIv n).2 : ℝ) := by
  induction n with
  | zero => simp [seriesIv]
  | succ n ih =>
      obtain ⟨h0, h1, h2⟩ := ih
      have hs := Real.sqrtTwoAddSeries_zero_nonneg n
      have hdef : Real.sqrtTwoAddSeries 0 (n + 1) =
          Real.sqrt (2 + Real.sqrtTwoAddSeries 0 n) := rfl
      rw [hdef]
      refine ⟨sqrtLoAt_nonneg cScale_pos _, ?_, ?_⟩
      · simp only [seriesIv]
        refine le_trans (sqrtLoAt_le cScale_pos (by linarith)) ?_
        apply Real.sqrt_le_sqrt
        push_cast
        linarith
      · simp only [seriesIv]
        have h0' : (0 : ℝ) ≤ (seriesIv n).1 := by exact_mod_cast h0
        have hq : (0 : ℚ) ≤ 2 + (seriesIv n).2 := by
          have : ((seriesIv n).1 : ℝ) ≤ (seriesIv n).2 := le_trans h1 h2
          have : (seriesIv n).1 ≤ (seriesIv n).2 := by exact_mod_cast this
          linarith
        refine le_trans ?_ (le_sqrtHiAt cScale_pos hq)
        apply Real.sqrt_le_sqrt
        push_cast
        linarith

/-- The basic angle `pi/64`. -/
noncomputable def theta : ℝ := Real.pi / 64

def c1lo : ℚ := (seriesIv 5).1 / 2
def c1hi : ℚ := (seriesIv 5).2 / 2

theorem cos_theta_bounds : (c1lo : ℝ) ≤ Real.cos theta ∧ Real.cos theta ≤ c1hi := by
  have h := Real.cos_pi_over_two_pow 5
  have ht : theta = Real.pi / 2 ^ (5 + 1) := by unfold theta; norm_num
  obtain ⟨_, h1, h2⟩ := seriesIv_sound 5
  rw [ht, h]
  unfold c1lo c1hi
  push_cast
  constructor <;> linarith

theorem c1lo_nonneg : 0 ≤ c1lo := by
  unfold c1lo
  have := (seriesIv_sound 5).1
  linarith

def s1lo : ℚ := sqrtLoAt cScale (1 - c1hi ^ 2)
def s1hi : ℚ := sqrtHiAt cScale (1 - c1lo ^ 2)

theorem c1hi_sq_le : c1hi ^ 2 ≤ 1 := by decide +kernel

theorem sin_theta_bounds : (s1lo : ℝ) ≤ Real.sin theta ∧ Real.sin theta ≤ s1hi := by
  have hpi := Real.pi_pos
  have h0 : 0 ≤ theta := by unfold theta; positivity
  have h1 : theta ≤ Real.pi := by unfold theta; linarith
  rw [Real.sin_eq_sqrt_one_sub_cos_sq h0 h1]
  obtain ⟨hc1, hc2⟩ := cos_theta_bounds
  have hlo : (0 : ℝ) ≤ c1lo := by exact_mod_cast c1lo_nonneg
  have hcos0 : 0 ≤ Real.cos theta := le_trans hlo hc1
  have hsq1 : Real.cos theta ^ 2 ≤ (c1hi : ℝ) ^ 2 := pow_le_pow_left₀ hcos0 hc2 2
  have hsq2 : (c1lo : ℝ) ^ 2 ≤ Real.cos theta ^ 2 := pow_le_pow_left₀ hlo hc1 2
  constructor
  · have hd : (0 : ℚ) ≤ 1 - c1hi ^ 2 := by linarith [c1hi_sq_le]
    refine le_trans (sqrtLoAt_le cScale_pos hd) (Real.sqrt_le_sqrt ?_)
    push_cast
    linarith
  · have hd : (0 : ℚ) ≤ 1 - c1lo ^ 2 := by
      have : c1lo ≤ c1hi := by
        have : (c1lo : ℝ) ≤ c1hi := le_trans hc1 hc2
        exact_mod_cast this
      nlinarith [c1hi_sq_le, c1lo_nonneg]
    refine le_trans (Real.sqrt_le_sqrt ?_) (le_sqrtHiAt cScale_pos hd)
    push_cast
    linarith

/-- One rotation step on the intervals for `(cos(k theta), sin(k theta))`. -/
def rotStep (st : (ℚ × ℚ) × (ℚ × ℚ)) : (ℚ × ℚ) × (ℚ × ℚ) :=
  ((rdnAt cScale (mulLo st.1.1 st.1.2 c1lo c1hi - mulHi st.2.1 st.2.2 s1lo s1hi),
    rupAt cScale (mulHi st.1.1 st.1.2 c1lo c1hi - mulLo st.2.1 st.2.2 s1lo s1hi)),
   (rdnAt cScale (mulLo st.2.1 st.2.2 c1lo c1hi + mulLo st.1.1 st.1.2 s1lo s1hi),
    rupAt cScale (mulHi st.2.1 st.2.2 c1lo c1hi + mulHi st.1.1 st.1.2 s1lo s1hi)))

/-- The rotation intervals at step `k`. -/
def rotIv : ℕ → (ℚ × ℚ) × (ℚ × ℚ)
  | 0 => ((1, 1), (0, 0))
  | k + 1 => rotStep (rotIv k)

/-- Containment of `cos(k theta)` and `sin(k theta)` in the step-`k` intervals. -/
def RotSound (k : ℕ) : Prop :=
  ((rotIv k).1.1 : ℝ) ≤ Real.cos (k * theta) ∧ Real.cos (k * theta) ≤ (rotIv k).1.2 ∧
    ((rotIv k).2.1 : ℝ) ≤ Real.sin (k * theta) ∧ Real.sin (k * theta) ≤ (rotIv k).2.2

theorem rotIv_sound (k : ℕ) : RotSound k := by
  induction k with
  | zero => simp [RotSound, rotIv]
  | succ k ih =>
      obtain ⟨hc1, hc2, hs1, hs2⟩ := ih
      obtain ⟨hC1, hC2⟩ := cos_theta_bounds
      obtain ⟨hS1, hS2⟩ := sin_theta_bounds
      have hang : ((k + 1 : ℕ) : ℝ) * theta = k * theta + theta := by push_cast; ring
      have m1 := mul_mem_bounds hc1 hc2 hC1 hC2
      have m2 := mul_mem_bounds hs1 hs2 hS1 hS2
      have m3 := mul_mem_bounds hs1 hs2 hC1 hC2
      have m4 := mul_mem_bounds hc1 hc2 hS1 hS2
      have r1 := rdnAt_le cScale_pos
      have r2 := le_rupAt cScale_pos
      unfold RotSound
      rw [hang, Real.cos_add, Real.sin_add]
      simp only [rotIv, rotStep]
      refine ⟨?_, ?_, ?_, ?_⟩
      · refine le_trans (Rat.cast_le.mpr (r1 _)) ?_
        push_cast
        linarith [m1.1, m2.2]
      · refine le_trans ?_ (Rat.cast_le.mpr (r2 _))
        push_cast
        linarith [m1.2, m2.1]
      · refine le_trans (Rat.cast_le.mpr (r1 _)) ?_
        push_cast
        linarith [m3.1, m4.1]
      · refine le_trans ?_ (Rat.cast_le.mpr (r2 _))
        push_cast
        linarith [m3.2, m4.2]

/-- Interval for `cos(k pi / 64)`. -/
def cosIv (k : ℕ) : ℚ × ℚ := (rotIv k).1

theorem cosIv_sound (k : ℕ) :
    ((cosIv k).1 : ℝ) ≤ Real.cos (k * theta) ∧ Real.cos (k * theta) ≤ ((cosIv k).2 : ℝ) :=
  ⟨(rotIv_sound k).1, (rotIv_sound k).2.1⟩

/-- Periodic reduction of the literal moment angles. -/
theorem cos_moment_angle (n : ℕ) (j : Fin 64) :
    Real.cos ((n : ℝ) * contourAngle j) =
      Real.cos (((n * (2 * j.val + 1) % 128 : ℕ) : ℝ) * theta) := by
  set K := n * (2 * j.val + 1) with hKdef
  have hK : (n : ℝ) * contourAngle j = (K : ℝ) * theta := by
    unfold contourAngle theta
    rw [hKdef]
    push_cast
    ring
  rw [hK]
  have hdiv : (K : ℝ) = ((K % 128 : ℕ) : ℝ) + ((K / 128 : ℕ) : ℝ) * 128 := by
    have := Nat.mod_add_div K 128
    exact_mod_cast (by omega : K = K % 128 + K / 128 * 128)
  rw [hdiv, add_mul]
  have : ((K / 128 : ℕ) : ℝ) * 128 * theta = ((K / 128 : ℕ) : ℝ) * (2 * Real.pi) := by
    unfold theta; ring
  rw [this, Real.cos_add_nat_mul_two_pi]

/-- The rational weight of the `j`th Fejer kernel. -/
def weightQ (j : ℕ) : ℚ :=
  (Li2Lean.P0.ConfigData.contourMassUnits.getD j 0 : ℚ) /
    (Li2Lean.P0.ConfigData.referenceDenominator : ℚ)

theorem contourWeight_eq (j : Fin 64) : contourWeight j = (weightQ j.val : ℝ) := by
  unfold contourWeight weightQ
  push_cast
  rfl

/-- Finite sum by structural recursion (kernel-friendly). -/
def sumTo (f : ℕ → ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => sumTo f n + f n

theorem sumTo_eq (f : ℕ → ℚ) (n : ℕ) : sumTo f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- Unrounded rational moment bounds. -/
def momentLoQ (n : ℕ) : ℚ :=
  (1 - (n : ℚ) / 49) *
    sumTo (fun j => weightQ j * (cosIv (n * (2 * j + 1) % 128)).1) 64

def momentHiQ (n : ℕ) : ℚ :=
  (1 - (n : ℚ) / 49) *
    sumTo (fun j => weightQ j * (cosIv (n * (2 * j + 1) % 128)).2) 64

theorem weightQ_nonneg (j : ℕ) : 0 ≤ weightQ j := by
  unfold weightQ
  positivity

theorem moment_sound {n : ℕ} (hn : n ≤ 49) :
    (momentLoQ n : ℝ) ≤ contourMoment n ∧ contourMoment n ≤ (momentHiQ n : ℝ) := by
  have hf : (0 : ℝ) ≤ 1 - (n : ℝ) / 49 := by
    have : (n : ℝ) ≤ 49 := by exact_mod_cast hn
    linarith
  have hsum (g : ℕ → ℚ) : ((sumTo g 64 : ℚ) : ℝ) = ∑ j : Fin 64, (g j.val : ℝ) := by
    rw [sumTo_eq]
    push_cast
    exact (Fin.sum_univ_eq_sum_range (fun j => (g j : ℝ)) 64).symm
  unfold momentLoQ momentHiQ contourMoment
  push_cast
  rw [hsum, hsum]
  constructor
  · apply mul_le_mul_of_nonneg_left _ hf
    apply Finset.sum_le_sum
    intro j _
    rw [contourWeight_eq, cos_moment_angle]
    push_cast
    exact mul_le_mul_of_nonneg_left (cosIv_sound _).1
      (by exact_mod_cast weightQ_nonneg j)
  · apply mul_le_mul_of_nonneg_left _ hf
    apply Finset.sum_le_sum
    intro j _
    rw [contourWeight_eq, cos_moment_angle]
    push_cast
    exact mul_le_mul_of_nonneg_left (cosIv_sound _).2
      (by exact_mod_cast weightQ_nonneg j)

end Li2Lean.P0.CA.Frequency
