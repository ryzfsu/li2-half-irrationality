/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.NonvanishingLiteralBridge

namespace Li2Lean

open Li2Lean.P0
open Li2Lean.P0.ControlledResidue

set_option maxHeartbeats 5000000
set_option maxRecDepth 100000

private theorem den_coprime_add {x y : ℚ}
    (hx : Nat.Coprime x.den 83) (hy : Nat.Coprime y.den 83) :
    Nat.Coprime (x + y).den 83 := by
  apply Nat.Coprime.of_dvd_left (Rat.add_den_dvd x y)
  exact Nat.Coprime.mul_left hx hy

private theorem den_coprime_mul {x y : ℚ}
    (hx : Nat.Coprime x.den 83) (hy : Nat.Coprime y.den 83) :
    Nat.Coprime (x * y).den 83 := by
  apply Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y)
  exact Nat.Coprime.mul_left hx hy

private theorem den_coprime_int (z : ℤ) :
    Nat.Coprime (z : ℚ).den 83 := by
  simp [Rat.den_intCast]

private theorem den_coprime_sum {ι : Type} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, Nat.Coprime (f i).den 83) :
    Nat.Coprime (∑ i ∈ s, f i).den 83 := by
  apply Finset.sum_induction f (fun q => Nat.Coprime q.den 83)
  · intro a b ha hb
    exact den_coprime_add ha hb
  · simp
  · intro i hi
    exact h i hi

private theorem den_coprime_prod {ι : Type} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, Nat.Coprime (f i).den 83) :
    Nat.Coprime (∏ i ∈ s, f i).den 83 := by
  apply Finset.prod_induction f (fun q => Nat.Coprime q.den 83)
  · intro a b ha hb
    exact den_coprime_mul ha hb
  · simp
  · intro i hi
    exact h i hi

private theorem cast_sum_den_coprime {ι : Type} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, Nat.Coprime (f i).den 83) :
    ((∑ i ∈ s, f i : ℚ) : F83) =
      ∑ i ∈ s, (f i : F83) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha' : Nat.Coprime (f a).den 83 := h a (by simp)
      have hs' : ∀ i ∈ s, Nat.Coprime (f i).den 83 := by
        intro i hi
        exact h i (by simp [hi])
      rw [Finset.sum_insert ha, Finset.sum_insert ha]
      rw [Rat.cast_add_of_ne_zero
        (natCast_ne_zero_of_coprime ha')
        (natCast_ne_zero_of_coprime (den_coprime_sum s f hs')),
        ih hs']

private theorem cast_prod_den_coprime {ι : Type} (s : Finset ι)
    (f : ι → ℚ) (h : ∀ i ∈ s, Nat.Coprime (f i).den 83) :
    ((∏ i ∈ s, f i : ℚ) : F83) =
      ∏ i ∈ s, (f i : F83) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
      have ha' : Nat.Coprime (f a).den 83 := h a (by simp)
      have hs' : ∀ i ∈ s, Nat.Coprime (f i).den 83 := by
        intro i hi
        exact h i (by simp [hi])
      rw [Finset.prod_insert ha, Finset.prod_insert ha]
      rw [Rat.cast_mul_of_ne_zero
        (natCast_ne_zero_of_coprime ha')
        (natCast_ne_zero_of_coprime (den_coprime_prod s f hs')),
        ih hs']

theorem cast_det_of_entries_83 {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ)
    (N : Matrix (Fin n) (Fin n) F83)
    (hden : ∀ i j, Nat.Coprime (M i j).den 83)
    (hentry : ∀ i j, (M i j : F83) = N i j) :
    ((M.det : ℚ) : F83) = N.det := by
  rw [Matrix.det_apply']
  rw [cast_sum_den_coprime (s := Finset.univ) _ (fun σ _ => by
    apply den_coprime_mul
    · exact den_coprime_int _
    · apply den_coprime_prod
      intro i hi
      exact hden (σ i) i)]
  rw [Matrix.det_apply' N]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [Rat.cast_mul_of_ne_zero
      (natCast_ne_zero_of_coprime (den_coprime_int _))
      (natCast_ne_zero_of_coprime (den_coprime_prod _ _ (fun i hi =>
        hden (σ i) i)))]
  rw [Rat.cast_intCast]
  rw [cast_prod_den_coprime (s := Finset.univ) _ (fun i _ =>
    hden (σ i) i)]
  congr 1
  apply Finset.prod_congr rfl
  intro i hi
  exact hentry (σ i) i

#print axioms cast_det_of_entries_83

end Li2Lean
