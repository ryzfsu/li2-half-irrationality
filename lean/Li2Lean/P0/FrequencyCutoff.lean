/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

/-!
# Exact frequency cutoffs and monotone nonnegative sums

The tuple types are definitionally identical to those in `P0.Contour`.
The subset/tuple correspondence is bijective and introduces no factorial.
The last two lemmas are the nonnegative monotone-convergence engine used
for the literal envelope in v10 `sec-frequency-tail.tex`.
-/

open MeasureTheory Filter Topology

namespace Li2Lean.P0.FrequencyCutoff

noncomputable section

open scoped BigOperators ENNReal

/-- An increasing frequency tuple; definitionally the tuple type used in `Contour`. -/
def IncreasingTuple (g m : ℕ) :=
  {r : Fin m → ℕ // StrictMono r ∧ ∀ i, g < r i}

/-- A bounded increasing tuple; definitionally the finite tuple type used in `Contour`. -/
def TruncatedTuple (g m H : ℕ) :=
  {r : Fin m → Fin (H + 1) //
    StrictMono (fun i => (r i).val) ∧ ∀ i, g < (r i).val}

/-- The finite bounded tuple type has the canonical finite structure. -/
instance truncatedFintype (g m H : ℕ) : Fintype (TruncatedTuple g m H) :=
  Fintype.ofInjective Subtype.val Subtype.val_injective

/-- Forget only the finite bound on a frequency tuple. -/
def forgetCutoff {g m H : ℕ} (r : TruncatedTuple g m H) :
    IncreasingTuple g m :=
  ⟨fun i => (r.val i).val, r.property⟩

theorem forgetCutoff_injective (g m H : ℕ) :
    Function.Injective (@forgetCutoff g m H) := by
  intro r s h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrFun (congrArg Subtype.val h) i

/-- The exact cutoff `max R ≤ H` as a finite subset of all increasing tuples. -/
def cutoffTuples (g m H : ℕ) : Finset (IncreasingTuple g m) := by
  classical
  exact Finset.univ.image (@forgetCutoff g m H)

theorem mem_cutoffTuples {g m H : ℕ} (r : IncreasingTuple g m) :
    r ∈ cutoffTuples g m H ↔ ∀ i, r.val i ≤ H := by
  classical
  constructor
  · intro hr
    rcases Finset.mem_image.mp hr with ⟨s, _, rfl⟩
    intro i
    exact Nat.le_of_lt_succ (s.val i).isLt
  · intro hr
    let s : TruncatedTuple g m H :=
      ⟨fun i => ⟨r.val i, Nat.lt_succ_of_le (hr i)⟩, r.property⟩
    exact Finset.mem_image.mpr ⟨s, Finset.mem_univ s, rfl⟩

theorem cutoffTuples_mono (g m : ℕ) : Monotone (cutoffTuples g m) := by
  intro H K hHK r hr
  rw [mem_cutoffTuples] at hr ⊢
  exact fun i => (hr i).trans hHK

/-- Every finite family is contained in some literal maximum-frequency cutoff. -/
theorem cutoffTuples_exhaustive (g m : ℕ)
    (s : Finset (IncreasingTuple g m)) :
    ∃ H, s ⊆ cutoffTuples g m H := by
  classical
  refine ⟨s.sup (fun r => Finset.univ.sup r.val), ?_⟩
  intro r hr
  rw [mem_cutoffTuples]
  intro i
  exact (Finset.le_sup (s := Finset.univ) (f := r.val) (Finset.mem_univ i)).trans
    (Finset.le_sup (f := fun r : IncreasingTuple g m => Finset.univ.sup r.val) hr)

/-- Conversion from the existing finite tuple sum to the common infinite tuple domain. -/
theorem sum_cutoffTuples {A : Type*} [AddCommMonoid A] (g m H : ℕ)
    (f : IncreasingTuple g m → A) :
    (∑ r ∈ cutoffTuples g m H, f r) =
      ∑ r : TruncatedTuple g m H, f (forgetCutoff r) := by
  classical
  exact Finset.sum_image fun r _ s _ h => forgetCutoff_injective g m H h

/-- Exact exhaustion of the nonnegative series by the paper's cutoffs. -/
theorem tsum_eq_iSup_cutoff (g m : ℕ)
    (f : IncreasingTuple g m → ℝ≥0∞) :
    (∑' r, f r) = ⨆ H : ℕ, ∑ r ∈ cutoffTuples g m H, f r :=
  ENNReal.tsum_eq_iSup_sum' (cutoffTuples g m) (cutoffTuples_exhaustive g m)

/-- The subset represented by an increasing tuple, without a permutation multiplicity. -/
def tupleSet {g m : ℕ} (r : IncreasingTuple g m) : Finset ℕ := by
  classical
  exact Finset.univ.image r.val

theorem tupleSet_card {g m : ℕ} (r : IncreasingTuple g m) : (tupleSet r).card = m := by
  classical
  rw [tupleSet, Finset.card_image_of_injective _ r.property.1.injective]
  simp

theorem mem_tupleSet {g m : ℕ} (r : IncreasingTuple g m) (a : ℕ) :
    a ∈ tupleSet r ↔ ∃ i, r.val i = a := by
  classical
  simp [tupleSet]

theorem tupleSet_injective (g m : ℕ) : Function.Injective (@tupleSet g m) := by
  classical
  intro r s hrs
  apply Subtype.ext
  have hr := Finset.orderEmbOfFin_unique (tupleSet_card s)
    (fun i => hrs ▸ (mem_tupleSet r _).2 ⟨i, rfl⟩) r.property.1
  have hs := Finset.orderEmbOfFin_unique (tupleSet_card s)
    (fun i => (mem_tupleSet s _).2 ⟨i, rfl⟩) s.property.1
  exact hr.trans hs.symm

/-- The canonical increasing enumeration of an admissible finite subset. -/
def tupleOfSet (g m : ℕ) (R : Finset ℕ) (hcard : R.card = m)
    (hR : ∀ r ∈ R, g < r) : IncreasingTuple g m :=
  ⟨R.orderEmbOfFin hcard, (R.orderEmbOfFin hcard).strictMono,
    fun i => hR _ (R.orderEmbOfFin_mem hcard i)⟩

theorem tupleSet_tupleOfSet (g m : ℕ) (R : Finset ℕ) (hcard : R.card = m)
    (hR : ∀ r ∈ R, g < r) : tupleSet (tupleOfSet g m R hcard hR) = R := by
  classical
  apply Finset.eq_of_subset_of_card_le
  · intro a ha
    rcases (mem_tupleSet _ _).mp ha with ⟨i, rfl⟩
    exact R.orderEmbOfFin_mem hcard i
  · rw [tupleSet_card, hcard]

theorem tupleSet_mem_powersetCard {g m H : ℕ} (r : IncreasingTuple g m) :
    tupleSet r ∈ (Finset.Ioc g H).powersetCard m ↔ r ∈ cutoffTuples g m H := by
  classical
  rw [Finset.mem_powersetCard, mem_cutoffTuples]
  constructor
  · rintro ⟨hsub, _⟩ i
    exact (Finset.mem_Ioc.mp (hsub ((mem_tupleSet _ _).2 ⟨i, rfl⟩))).2
  · intro hr
    refine ⟨?_, tupleSet_card r⟩
    intro a ha
    rcases (mem_tupleSet r a).mp ha with ⟨i, rfl⟩
    exact Finset.mem_Ioc.mpr ⟨r.property.2 i, hr i⟩

/-- Exact subset/tuple bijection for every literal finite cutoff. -/
theorem image_tupleSet_cutoff (g m H : ℕ) :
    (cutoffTuples g m H).image tupleSet = (Finset.Ioc g H).powersetCard m := by
  classical
  ext R
  constructor
  · intro h
    rcases Finset.mem_image.mp h with ⟨r, hr, rfl⟩
    exact (tupleSet_mem_powersetCard r).mpr hr
  · intro h
    rcases Finset.mem_powersetCard.mp h with ⟨hsub, hcard⟩
    let r := tupleOfSet g m R hcard (fun a ha => (Finset.mem_Ioc.mp (hsub ha)).1)
    have heq : tupleSet r = R := tupleSet_tupleOfSet g m R hcard _
    refine Finset.mem_image.mpr ⟨r, ?_, heq⟩
    rw [← tupleSet_mem_powersetCard, heq]
    exact h

/-- Exact equality of the finite subset sum and increasing-tuple sum; no `m!` appears. -/
theorem sum_powersetCard_eq_sum_truncated {A : Type*} [AddCommMonoid A]
    (g m H : ℕ) (f : Finset ℕ → A) :
    (∑ R ∈ (Finset.Ioc g H).powersetCard m, f R) =
      ∑ r : TruncatedTuple g m H, f (tupleSet (forgetCutoff r)) := by
  classical
  rw [← image_tupleSet_cutoff]
  rw [Finset.sum_image (fun r _ s _ h => tupleSet_injective g m h)]
  exact sum_cutoffTuples g m H (fun r => f (tupleSet r))

/-- Monotone convergence for the exact maximum-frequency cutoffs. -/
theorem lintegral_tsum_eq_iSup_cutoff {α : Type*} [MeasurableSpace α]
    (μ : MeasureTheory.Measure α) (g m : ℕ)
    (f : IncreasingTuple g m → α → ℝ≥0∞) (hf : ∀ r, Measurable (f r)) :
    (∫⁻ x, ∑' r, f r x ∂μ) =
      ⨆ H : ℕ, ∫⁻ x, ∑ r ∈ cutoffTuples g m H, f r x ∂μ := by
  simp_rw [tsum_eq_iSup_cutoff]
  apply MeasureTheory.lintegral_iSup
  · intro H
    exact Finset.measurable_fun_sum _ (fun r _ => hf r)
  · intro H K hHK x
    exact Finset.sum_le_sum_of_subset (cutoffTuples_mono g m hHK)

/-- A finite sum of monotone nonnegative cutoff families commutes with the supremum. -/
theorem sum_iSup_of_monotone {ι : Type*} (s : Finset ι)
    (f : ι → ℕ → ℝ≥0∞) (hf : ∀ i ∈ s, Monotone (f i)) :
    (∑ i ∈ s, ⨆ H, f i H) = ⨆ H, ∑ i ∈ s, f i H := by
  apply tendsto_nhds_unique
    (tendsto_finsetSum s (fun i hi => tendsto_atTop_iSup (hf i hi)))
  exact tendsto_atTop_iSup (fun H K hHK => Finset.sum_le_sum (fun i hi => hf i hi hHK))

end

end Li2Lean.P0.FrequencyCutoff

