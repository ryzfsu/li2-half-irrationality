/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Config
import Li2Lean.P0.Contour

open MeasureTheory

namespace Li2Lean.P0.Config

noncomputable section

open Li2Lean.P0

private theorem pinned_subset_Iset (C : FiniteConfiguration) :
    C.pinned ⊆ Iset C.m := by
  rw [Iset_eq_paper_interval C.m C.four_dvd_m]
  simpa [pinnedUniverse] using C.pinned_subset

private theorem contour_count_eq (C : FiniteConfiguration) :
    C.contourCount = C.m - C.pinned.card := by
  have h := C.mass_balance
  omega

private def scaledContourPoint (C : FiniteConfiguration)
    (i : Fin C.contourCount) : ℂ :=
  Complex.ofReal (C.m : ℝ) * C.contour i

theorem scaledContourPoint_eq_p0EllipsePoint_of_mem
    (C : FiniteConfiguration) (i : Fin C.contourCount) (u : ℝ)
    (hu : C.contour i = baseEllipse u) :
    scaledContourPoint C i = p0EllipsePoint C.m u := by
  dsimp [scaledContourPoint]
  rw [hu]
  simp [baseEllipse, p0EllipsePoint]

theorem scaledContourPoint_mem (C : FiniteConfiguration)
    (i : Fin C.contourCount) :
    scaledContourPoint C i ∈ Set.range (p0EllipsePoint C.m) := by
  rcases C.contour_mem i with ⟨u, hu⟩
  refine ⟨u, ?_⟩
  dsimp [scaledContourPoint]
  rw [← hu]
  simp only [baseEllipse, p0EllipsePoint]
  norm_num

noncomputable def literalConfigQWeight (C : FiniteConfiguration) : ℝ :=
  contourQValue C.pinned C.four_dvd_m (pinned_subset_Iset C)
    (fun i : Fin C.m =>
      orderedElem C.frequency (Fin.cast C.frequency_card.symm i))
    (by
      intro i j hij
      exact (Finset.orderIsoOfFin C.frequency C.frequency_card).strictMono hij)
    (fun i : Fin (C.m - C.pinned.card) =>
      scaledContourPoint C (Fin.cast (contour_count_eq C).symm i))

/-! Public C-A final bound with the actual `Q_m` weight. There is no free
function argument and no conclusion field: the weight is reconstructed from
the configuration's literal pinned/frequency sets and contour tuple. -/
def ConfigFinalBoundLiteral (alpha : ℝ) : Prop :=
  ConfigFinalBound alpha literalConfigQWeight

theorem configFinalBoundLiteral_eq (alpha : ℝ) :
    ConfigFinalBoundLiteral alpha =
      ConfigFinalBound alpha literalConfigQWeight :=
  rfl

theorem literalConfigQWeight_is_literal_contourQValue (C : FiniteConfiguration) :
    literalConfigQWeight C =
      contourQValue C.pinned C.four_dvd_m (pinned_subset_Iset C)
        (fun i : Fin C.m =>
          orderedElem C.frequency (Fin.cast C.frequency_card.symm i))
        (by
          intro i j hij
          exact (Finset.orderIsoOfFin C.frequency C.frequency_card).strictMono hij)
        (fun i : Fin (C.m - C.pinned.card) =>
          scaledContourPoint C (Fin.cast (contour_count_eq C).symm i)) := by
  rfl

theorem literalConfigQWeight_eq_contourQValue_of_baseEllipse
    (C : FiniteConfiguration) (u : Fin C.contourCount → ℝ)
    (hu : ∀ i, C.contour i = baseEllipse (u i)) :
    literalConfigQWeight C =
      contourQValue C.pinned C.four_dvd_m (pinned_subset_Iset C)
        (fun i : Fin C.m =>
          orderedElem C.frequency (Fin.cast C.frequency_card.symm i))
        (by
          intro i j hij
          exact (Finset.orderIsoOfFin C.frequency C.frequency_card).strictMono hij)
        (fun i : Fin (C.m - C.pinned.card) =>
          p0EllipsePoint C.m (u (Fin.cast (contour_count_eq C).symm i))) := by
  rw [literalConfigQWeight_is_literal_contourQValue]
  congr 5
  funext i
  apply scaledContourPoint_eq_p0EllipsePoint_of_mem
  exact hu _

end

end Li2Lean.P0.Config
