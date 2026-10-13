/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateDetValuation
import Li2Lean.P0.RateResidueCount

/-!
# Low-ratio assignment bounds (v13, equation `p0-low-W`)

For an odd prime `p ≤ g = m/2`, every negated source entry bound is at most
`[lower row] + [same residue] - min(κ_i, κ_j)`.  Summed along any permutation
this gives the two feasible assignment bounds of v13:

* `m + S_U`, and
* `m + Σ_{unkilled} c_J - Σ_{killed} 2 c_I + S_K = 3m - 2K_I - K_J + S_K`,

where the residue counts are the literal row and column counts of the actual
matrix.  The proof is a direct matching count; no table enters.
-/

namespace Li2Lean.P0.Integerization

open Finset

theorem p0PrimeCarry_mod (p g n : ℕ) : p0PrimeCarry p g (n % p) = p0PrimeCarry p g n := by
  simp [p0PrimeCarry]

theorem p0PrimeCarry_eq_of_mod {p g i j : ℕ} (h : i % p = j % p) :
    p0PrimeCarry p g i = p0PrimeCarry p g j := by
  rw [← p0PrimeCarry_mod p g i, h, p0PrimeCarry_mod]

/-- Residue-level part of the low-range entry weight. -/
def p0LowE (p g i j : ℕ) : ℤ :=
  (if i % p = j % p then 1 else 0) - min (p0PrimeCarry p g i : ℤ) (p0PrimeCarry p g j)

theorem p0PrimeDiagBLower_ge (p g n : ℕ) :
    (p0PrimeCarry p g n : ℤ) - 2 ≤ p0PrimeDiagBLower p g n := by
  have hκ := p0PrimeCarry_le_one p g n
  unfold p0PrimeDiagBLower
  split
  · omega
  · split <;> omega

theorem p0RateWeight_le_low (p m : ℕ) (hpg : p ≤ m / 2) (r c : Fin (2 * m)) :
    p0RateWeight p m r c ≤
      (if r.val < m then 0 else 1) + p0LowE p (m / 2) (p0SourceRowIndex m r) c.val := by
  have hθ : ∀ n, p0PrimeTheta p (m / 2) n = (p0PrimeCarry p (m / 2) n : ℤ) - 1 := by
    intro n; simp [p0PrimeTheta, hpg]
  have hdiag := p0PrimeDiagBLower_ge p (m / 2) (p0SourceRowIndex m r)
  have hκi := p0PrimeCarry_le_one p (m / 2) (p0SourceRowIndex m r)
  have hκj := p0PrimeCarry_le_one p (m / 2) c.val
  unfold p0RateWeight p0PrimeEntryLower p0LowE
  simp only [hθ]
  generalize p0SourceRowIndex m r = i at *
  generalize c.val = j at *
  generalize hdi : p0PrimeDiagBLower p (m / 2) i = di at *
  generalize hki : p0PrimeCarry p (m / 2) i = ki at *
  generalize hkj : p0PrimeCarry p (m / 2) j = kj at *
  by_cases hij : i = j
  · subst hij
    rw [hkj] at hki
    subst hki
    by_cases hr : r.val < m
    · simp only [hr, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hpg,
        min_self]
      omega
    · simp only [hr, not_false_eq_true, decide_true, ↓reduceIte, min_self]
      omega
  · have hpgz : p ≤ m / 2 := hpg
    by_cases hr : r.val < m
    · simp only [hr, not_true_eq_false, decide_false, Bool.false_eq_true, ↓reduceIte, hij]
      simp only [min_def]
      split_ifs <;> omega
    · simp only [hr, not_false_eq_true, decide_true, ↓reduceIte, hij]
      simp only [min_def]
      split_ifs <;> omega

theorem p0LowE_le_A (p g i j : ℕ) :
    p0LowE p g i j ≤ if i % p = j % p ∧ p0PrimeCarry p g i = 0 then 1 else 0 := by
  have hκi := p0PrimeCarry_le_one p g i
  have hκj := p0PrimeCarry_le_one p g j
  unfold p0LowE
  by_cases hs : i % p = j % p
  · have he := p0PrimeCarry_eq_of_mod (g := g) hs
    rw [if_pos hs, he]
    simp only [min_self, true_and]
    split <;> omega
  · rw [if_neg hs]
    simp only [hs, false_and, ↓reduceIte]
    omega

theorem p0LowE_le_B (p g i j : ℕ) :
    p0LowE p g i j ≤
      (if p0PrimeCarry p g j = 0 then 1 else 0) - (if p0PrimeCarry p g i = 1 then 1 else 0) +
        (if i % p = j % p ∧ p0PrimeCarry p g i = 1 then 1 else 0) := by
  have hκi := p0PrimeCarry_le_one p g i
  have hκj := p0PrimeCarry_le_one p g j
  unfold p0LowE
  by_cases hs : i % p = j % p
  · have he := p0PrimeCarry_eq_of_mod (g := g) hs
    rw [if_pos hs, he]
    simp only [min_self, true_and]
    split_ifs <;> omega
  · rw [if_neg hs]
    simp only [hs, false_and, ↓reduceIte]
    split_ifs <;> omega

/-- Residue fibers of a bounded labelling. -/
theorem p0_sum_fiber {n p : ℕ} (f : Fin n → ℕ) (hf : ∀ x, f x < p) (φ : ℕ → ℤ) :
    ∑ x, φ (f x) =
      ∑ v ∈ range p, φ v * ((univ.filter (fun x => f x = v)).card : ℤ) := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range p) (g := f)
    (fun x _ => Finset.mem_range.mpr (hf x)) (fun x => φ (f x))]
  apply Finset.sum_congr rfl
  intro v _
  rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
  simp [Finset.sum_const, mul_comm]

/-- A permutation matches at most `min(#rows, #cols)` pairs inside one class. -/
theorem p0_match_card_le {n : ℕ} (σ : Equiv.Perm (Fin n)) (f g : Fin n → ℕ) (v : ℕ) :
    (univ.filter (fun i => g i = v ∧ f (σ i) = v)).card ≤
      min (univ.filter (fun r => f r = v)).card (univ.filter (fun c => g c = v)).card := by
  apply le_min
  · apply Finset.card_le_card_of_injOn σ
    · intro i hi
      simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hi ⊢
      exact hi.2
    · intro a _ b _ h
      exact σ.injective h
  · apply Finset.card_le_card
    intro i hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢
    exact hi.1

theorem p0_sum_match_le {n p : ℕ} (σ : Equiv.Perm (Fin n)) (f g : Fin n → ℕ)
    (hg : ∀ x, g x < p) (P : ℕ → Prop) [DecidablePred P] :
    ∑ i, (if g i = f (σ i) ∧ P (g i) then (1 : ℤ) else 0) ≤
      ∑ v ∈ range p, if P v then
        (min (univ.filter (fun r => f r = v)).card (univ.filter (fun c => g c = v)).card : ℤ)
        else 0 := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := univ) (t := range p) (g := g)
    (fun x _ => Finset.mem_range.mpr (hg x))]
  apply Finset.sum_le_sum
  intro v _
  have hrw : ∀ i ∈ univ.filter (fun x => g x = v),
      (if g i = f (σ i) ∧ P (g i) then (1 : ℤ) else 0) =
        if P v then (if f (σ i) = v then 1 else 0) else 0 := by
    intro i hi
    have hgi := (Finset.mem_filter.mp hi).2
    rw [hgi]
    by_cases hP : P v
    · simp only [hP, and_true, ↓reduceIte]
      by_cases hf : f (σ i) = v
      · simp [hf]
      · have : ¬ v = f (σ i) := fun h => hf h.symm
        simp [hf, this]
    · simp [hP]
  rw [Finset.sum_congr rfl hrw]
  by_cases hP : P v
  · simp only [hP, ↓reduceIte]
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one, Finset.filter_filter]
    have h := p0_match_card_le σ f g v
    exact_mod_cast h
  · simp [hP]

/-- Literal row and column residue counts of the actual matrix. -/
def p0RowRes (p m v : ℕ) : ℕ :=
  (univ.filter (fun r : Fin (2 * m) => p0SourceRowIndex m r % p = v)).card

def p0ColRes (p m v : ℕ) : ℕ :=
  (univ.filter (fun c : Fin (2 * m) => c.val % p = v)).card

theorem p0_sum_lower_rows (m : ℕ) :
    ∑ r : Fin (2 * m), (if r.val < m then (0 : ℤ) else 1) = m := by
  rw [Fin.sum_univ_eq_sum_range (fun x => if x < m then (0 : ℤ) else 1), two_mul,
    Finset.sum_range_add]
  have h1 : ∑ x ∈ range m, (if x < m then (0 : ℤ) else 1) = 0 :=
    Finset.sum_eq_zero (fun x hx => by simp [Finset.mem_range.mp hx])
  have h2 : ∑ x ∈ range m, (if m + x < m then (0 : ℤ) else 1) = m := by
    simp
  rw [h1, h2, zero_add]

/-- Pointwise residue sum of the low weight along a permutation. -/
theorem p0Low_weight_sum_le (p m : ℕ) (hpg : p ≤ m / 2) (σ : Equiv.Perm (Fin (2 * m))) :
    ∑ i, p0RateWeight p m (σ i) i ≤
      m + ∑ i, p0LowE p (m / 2) (p0SourceRowIndex m (σ i)) i.val := by
  calc ∑ i, p0RateWeight p m (σ i) i
      ≤ ∑ i, ((if (σ i).val < m then (0 : ℤ) else 1) +
          p0LowE p (m / 2) (p0SourceRowIndex m (σ i)) i.val) :=
        Finset.sum_le_sum (fun i _ => p0RateWeight_le_low p m hpg (σ i) i)
    _ = m + ∑ i, p0LowE p (m / 2) (p0SourceRowIndex m (σ i)) i.val := by
        rw [Finset.sum_add_distrib]
        congr 1
        rw [Equiv.sum_comp σ (fun r => if r.val < m then (0 : ℤ) else 1)]
        exact p0_sum_lower_rows m

/-- First v13 low assignment bound: `m + S_U`. -/
theorem p0Low_assign_bound1 (p m : ℕ) (hp : 0 < p) (hpg : p ≤ m / 2)
    (σ : Equiv.Perm (Fin (2 * m))) :
    ∑ i, p0RateWeight p m (σ i) i ≤
      m + ∑ v ∈ range p, if p0PrimeCarry p (m / 2) v = 0 then
        (min (p0RowRes p m v) (p0ColRes p m v) : ℤ) else 0 := by
  refine (p0Low_weight_sum_le p m hpg σ).trans ?_
  refine add_le_add le_rfl ?_
  have hA : ∀ i : Fin (2 * m), p0LowE p (m / 2) (p0SourceRowIndex m (σ i)) i.val ≤
      if i.val % p = p0SourceRowIndex m (σ i) % p ∧
        p0PrimeCarry p (m / 2) (i.val % p) = 0 then 1 else 0 := by
    intro i
    have h := p0LowE_le_A p (m / 2) (p0SourceRowIndex m (σ i)) i.val
    have hm1 := p0PrimeCarry_mod p (m / 2) i.val
    have hk1 := p0PrimeCarry_le_one p (m / 2) i.val
    have hk2 := p0PrimeCarry_le_one p (m / 2) (p0SourceRowIndex m (σ i))
    by_cases hs : p0SourceRowIndex m (σ i) % p = i.val % p
    · have he := p0PrimeCarry_eq_of_mod (g := m / 2) hs
      split_ifs at h ⊢ <;> omega
    · split_ifs at h ⊢ <;> omega
  refine (Finset.sum_le_sum (fun i _ => hA i)).trans ?_
  exact p0_sum_match_le σ (fun r => p0SourceRowIndex m r % p) (fun c => c.val % p)
    (fun x => Nat.mod_lt _ hp) (fun v => p0PrimeCarry p (m / 2) v = 0)

/-- Second v13 low assignment bound:
`m + Σ_{unkilled} c_J - Σ_{killed} (rows) + S_K`. -/
theorem p0Low_assign_bound2 (p m : ℕ) (hp : 0 < p) (hpg : p ≤ m / 2)
    (σ : Equiv.Perm (Fin (2 * m))) :
    ∑ i, p0RateWeight p m (σ i) i ≤
      m + ∑ v ∈ range p,
        ((if p0PrimeCarry p (m / 2) v = 0 then (p0ColRes p m v : ℤ) else 0) -
          (if p0PrimeCarry p (m / 2) v = 1 then (p0RowRes p m v : ℤ) else 0) +
          (if p0PrimeCarry p (m / 2) v = 1 then
            (min (p0RowRes p m v) (p0ColRes p m v) : ℤ) else 0)) := by
  refine (p0Low_weight_sum_le p m hpg σ).trans ?_
  refine add_le_add le_rfl ?_
  set κ := fun n => p0PrimeCarry p (m / 2) n
  have hB : ∀ i : Fin (2 * m), p0LowE p (m / 2) (p0SourceRowIndex m (σ i)) i.val ≤
      ((if κ (i.val % p) = 0 then (1 : ℤ) else 0) -
        (if κ (p0SourceRowIndex m (σ i) % p) = 1 then 1 else 0)) +
      (if i.val % p = p0SourceRowIndex m (σ i) % p ∧ κ (i.val % p) = 1 then 1 else 0) := by
    intro i
    have h := p0LowE_le_B p (m / 2) (p0SourceRowIndex m (σ i)) i.val
    have hm1 := p0PrimeCarry_mod p (m / 2) i.val
    have hm2 := p0PrimeCarry_mod p (m / 2) (p0SourceRowIndex m (σ i))
    have hk1 := p0PrimeCarry_le_one p (m / 2) i.val
    have hk2 := p0PrimeCarry_le_one p (m / 2) (p0SourceRowIndex m (σ i))
    simp only [κ]
    by_cases hs : p0SourceRowIndex m (σ i) % p = i.val % p
    · have he := p0PrimeCarry_eq_of_mod (g := m / 2) hs
      split_ifs at h ⊢ <;> omega
    · split_ifs at h ⊢ <;> omega
  refine (Finset.sum_le_sum (fun i _ => hB i)).trans ?_
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib]
  have hcol : ∑ i : Fin (2 * m), (if κ (i.val % p) = 0 then (1 : ℤ) else 0) =
      ∑ v ∈ range p, (if κ v = 0 then (p0ColRes p m v : ℤ) else 0) := by
    rw [p0_sum_fiber (fun c : Fin (2 * m) => c.val % p) (fun x => Nat.mod_lt _ hp)
      (fun v => if κ v = 0 then (1 : ℤ) else 0)]
    apply Finset.sum_congr rfl
    intro v _
    simp only [p0ColRes]
    split <;> simp
  have hrow : ∑ i : Fin (2 * m), (if κ (p0SourceRowIndex m (σ i) % p) = 1 then (1 : ℤ) else 0) =
      ∑ v ∈ range p, (if κ v = 1 then (p0RowRes p m v : ℤ) else 0) := by
    rw [Equiv.sum_comp σ (fun r => if κ (p0SourceRowIndex m r % p) = 1 then (1 : ℤ) else 0)]
    rw [p0_sum_fiber (fun r : Fin (2 * m) => p0SourceRowIndex m r % p)
      (fun x => Nat.mod_lt _ hp) (fun v => if κ v = 1 then (1 : ℤ) else 0)]
    apply Finset.sum_congr rfl
    intro v _
    simp only [p0RowRes]
    split <;> simp
  have hmatch := p0_sum_match_le σ (fun r => p0SourceRowIndex m r % p) (fun c => c.val % p)
    (fun x => Nat.mod_lt _ hp) (fun v => κ v = 1)
  rw [hcol, hrow, Finset.sum_add_distrib, Finset.sum_sub_distrib]
  simp only [p0RowRes, p0ColRes] at hmatch ⊢
  linarith

end Li2Lean.P0.Integerization
