/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Agents.F_L8.Types
import Li2Lean.P0.CA.Receipt.Checks

/-!
# Step majorants for the C-A penalties

For a row table, a threshold `h` and a row allowance `a`, the step function
`stepMajorant h a cells` is `∑ 1_[lo,hi] * max (h - (lower - a)) 0`. It is
nonnegative and integrable on every set, its integral is at most the rational
`penaltyMass h a cells`, and on a chain-covered interval it dominates
`h - f` as soon as each row satisfies the spent bound `lower - a ≤ f`.
-/

open MeasureTheory Set

namespace Li2Lean.P0.CA.Receipt

open Li2Lean.F_L8

noncomputable section

/-- The penalty weight of one row. -/
def stepWeight (h a : ℚ) (c : ReceiptCell) : ℝ :=
  ((max (h - (c.lower - a)) 0 : ℚ) : ℝ)

theorem stepWeight_nonneg (h a : ℚ) (c : ReceiptCell) : 0 ≤ stepWeight h a c := by
  unfold stepWeight
  exact_mod_cast le_max_right _ _

/-- The step majorant of a row table. -/
def stepMajorant (h a : ℚ) (cells : List ReceiptCell) (x : ℝ) : ℝ :=
  (cells.map fun c =>
    (Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c) x).sum

theorem stepMajorant_nil (h a : ℚ) (x : ℝ) : stepMajorant h a [] x = 0 := by
  simp [stepMajorant]

theorem stepMajorant_cons (h a : ℚ) (c : ReceiptCell) (cells : List ReceiptCell)
    (x : ℝ) :
    stepMajorant h a (c :: cells) x =
      (Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c) x +
        stepMajorant h a cells x := by
  simp [stepMajorant]

theorem indicator_stepWeight_nonneg (h a : ℚ) (c : ReceiptCell) (x : ℝ) :
    0 ≤ (Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c) x :=
  Set.indicator_nonneg (fun _ _ => stepWeight_nonneg h a c) x

theorem stepMajorant_nonneg (h a : ℚ) (cells : List ReceiptCell) (x : ℝ) :
    0 ≤ stepMajorant h a cells x := by
  induction cells with
  | nil => simp [stepMajorant_nil]
  | cons c cells ih =>
      rw [stepMajorant_cons]
      exact add_nonneg (indicator_stepWeight_nonneg h a c x) ih

theorem integrable_indicator_stepWeight (h a : ℚ) (c : ReceiptCell) (S : Set ℝ) :
    Integrable ((Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c))
      (volume.restrict S) := by
  rw [integrable_indicator_iff measurableSet_Icc]
  refine integrableOn_const ?_
  exact (lt_of_le_of_lt (Measure.restrict_apply_le _ _) measure_Icc_lt_top).ne

theorem stepMajorant_integrable (h a : ℚ) (cells : List ReceiptCell) (S : Set ℝ) :
    Integrable (stepMajorant h a cells) (volume.restrict S) := by
  induction cells with
  | nil =>
      have : stepMajorant h a [] = fun _ => 0 := funext (stepMajorant_nil h a)
      rw [this]
      exact integrable_zero _ _ _
  | cons c cells ih =>
      have : stepMajorant h a (c :: cells) = fun x =>
          (Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c) x +
            stepMajorant h a cells x := funext (stepMajorant_cons h a c cells)
      rw [this]
      exact (integrable_indicator_stepWeight h a c S).add ih

theorem stepMajorant_integrableOn (h a : ℚ) (cells : List ReceiptCell) (S : Set ℝ) :
    IntegrableOn (stepMajorant h a cells) S :=
  stepMajorant_integrable h a cells S

/-- The integral of the step majorant over any set is at most the rational
penalty mass, provided every row has nonnegative width. -/
theorem integral_stepMajorant_le (h a : ℚ) (S : Set ℝ) :
    ∀ cells : List ReceiptCell, (∀ c ∈ cells, c.lo ≤ c.hi) →
      ∫ x in S, stepMajorant h a cells x ≤ (penaltyMass h a cells : ℝ)
  | [], _ => by simp [stepMajorant_nil, penaltyMass]
  | c :: cells, hw => by
      have hc : c.lo ≤ c.hi := hw c (by simp)
      have hrest : ∀ d ∈ cells, d.lo ≤ d.hi := fun d hd => hw d (by simp [hd])
      have ih := integral_stepMajorant_le h a S cells hrest
      have hfun : stepMajorant h a (c :: cells) = fun x =>
          (Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c) x +
            stepMajorant h a cells x := funext (stepMajorant_cons h a c cells)
      rw [hfun, integral_add (integrable_indicator_stepWeight h a c S)
        (stepMajorant_integrable h a cells S),
        integral_indicator_const _ measurableSet_Icc]
      have hvol : (volume.restrict S).real (Icc (c.lo : ℝ) (c.hi : ℝ)) ≤
          (c.hi : ℝ) - c.lo := by
        have hle : (volume.restrict S) (Icc (c.lo : ℝ) (c.hi : ℝ)) ≤
            volume (Icc (c.lo : ℝ) (c.hi : ℝ)) := Measure.restrict_apply_le _ _
        have hhi : (c.lo : ℝ) ≤ c.hi := by exact_mod_cast hc
        rw [Real.volume_Icc] at hle
        rw [Measure.real]
        calc ((volume.restrict S) (Icc (c.lo : ℝ) (c.hi : ℝ))).toReal
            ≤ (ENNReal.ofReal ((c.hi : ℝ) - c.lo)).toReal :=
              ENNReal.toReal_mono ENNReal.ofReal_ne_top hle
          _ = (c.hi : ℝ) - c.lo := ENNReal.toReal_ofReal (by linarith)
      have hw0 := stepWeight_nonneg h a c
      have hterm : (volume.restrict S).real (Icc (c.lo : ℝ) (c.hi : ℝ)) •
            stepWeight h a c ≤ ((c.hi : ℝ) - c.lo) * stepWeight h a c := by
        rw [smul_eq_mul]
        exact mul_le_mul_of_nonneg_right hvol hw0
      have hcast : (penaltyMass h a (c :: cells) : ℝ) =
          ((c.hi : ℝ) - c.lo) * stepWeight h a c + (penaltyMass h a cells : ℝ) := by
        simp [penaltyMass, stepWeight]
      rw [hcast]
      linarith

/-- Domination of `h - f` by the step majorant on a chain-covered interval. -/
theorem sub_le_stepMajorant {cells : List ReceiptCell} {left right : ℚ}
    (hchain : ExactChain cells left right) (h a : ℚ) {f : ℝ → ℝ}
    (hrow : ∀ c ∈ cells, ∀ x : ℝ, (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) →
      ((c.lower : ℝ) - a) ≤ f x)
    {x : ℝ} (hl : (left : ℝ) ≤ x) (hr : x ≤ (right : ℝ)) :
    (h : ℝ) - f x ≤ stepMajorant h a cells x := by
  obtain ⟨c, hmem, _, hlo, hhi⟩ := exactChain_covers hchain x hl hr
  have hfx := hrow c hmem x hlo hhi
  have hterm : (h : ℝ) - f x ≤
      (Icc (c.lo : ℝ) (c.hi : ℝ)).indicator (fun _ => stepWeight h a c) x := by
    rw [Set.indicator_of_mem (show x ∈ Icc (c.lo : ℝ) (c.hi : ℝ) from ⟨hlo, hhi⟩)]
    unfold stepWeight
    push_cast
    exact le_trans (by linarith) (le_max_left _ _)
  refine le_trans hterm ?_
  unfold stepMajorant
  apply List.single_le_sum
  · intro y hy
    rcases List.mem_map.mp hy with ⟨d, _, rfl⟩
    exact indicator_stepWeight_nonneg h a d x
  · exact List.mem_map.mpr ⟨c, hmem, rfl⟩

/-- Every row of an exact chain has nonnegative width. -/
theorem exactChain_widths {cells : List ReceiptCell} {left right : ℚ}
    (hchain : ExactChain cells left right) : ∀ c ∈ cells, c.lo ≤ c.hi := by
  induction hchain with
  | one c _ _ _ _ hwidth =>
      intro d hd
      rw [List.mem_singleton.mp hd]
      exact hwidth
  | more c d rest _ _ _ _ hwidth _ ih =>
      intro e he
      rcases List.mem_cons.mp he with rfl | he
      · exact hwidth
      · exact ih e he

/-- A row-valid table gives the original pointwise lower bound on each row. -/
theorem row_lower_of_valid {f : ℝ → ℝ} {cells : List ReceiptCell}
    (hvalid : ∀ c ∈ cells, ∀ hw : c.lo ≤ c.hi, c.modelRemainderValid f hw)
    (hwidth : ∀ c ∈ cells, c.lo ≤ c.hi) :
    ∀ c ∈ cells, ∀ x : ℝ, (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) → (c.lower : ℝ) ≤ f x :=
  fun c hc _ hlo hhi =>
    c.sound (hwidth c hc) (hvalid c hc (hwidth c hc)) hlo hhi

/-- Original row bounds imply the spent row bounds for a nonnegative allowance. -/
theorem spent_of_original {f : ℝ → ℝ} {cells : List ReceiptCell} {a : ℚ}
    (ha : 0 ≤ a)
    (horig : ∀ c ∈ cells, ∀ x : ℝ, (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) →
      (c.lower : ℝ) ≤ f x) :
    ∀ c ∈ cells, ∀ x : ℝ, (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) →
      ((c.lower : ℝ) - a) ≤ f x := by
  intro c hc x hlo hhi
  have := horig c hc x hlo hhi
  have haR : (0 : ℝ) ≤ a := by exact_mod_cast ha
  linarith

end

end Li2Lean.P0.CA.Receipt
