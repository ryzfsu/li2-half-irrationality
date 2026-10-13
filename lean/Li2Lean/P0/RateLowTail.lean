/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateLowAssign

/-!
# Literal residue counts and the small-ratio tail bound

The row count of residue `v` in the actual matrix is twice the number of
`i ∈ [m/4, m/4 + m)` with `i ≡ v`, and the column count is the number of
`j < 2m` with `j ≡ v`.  From the second low assignment bound this gives the
v13 tail estimate `W ≤ 3m - 2⌊m/p⌋ (g mod p)` used for `p/m < 1/128`.
-/

namespace Li2Lean.P0.Integerization

open Finset

theorem p0RowRes_eq (p m v : ℕ) (hp : 0 < p) (hv : v < p) :
    (p0RowRes p m v : ℤ) =
      2 * ((p0ResCnt p (m / 4 + m) v : ℤ) - p0ResCnt p (m / 4) v) := by
  unfold p0RowRes p0SourceRowIndex
  rw [Finset.card_filter]
  push_cast
  rw [Fin.sum_univ_eq_sum_range
    (fun x => if (m / 4 + if x < m then x else x - m) % p = v then (1 : ℤ) else 0),
    two_mul, Finset.sum_range_add]
  have h1 : ∑ x ∈ range m, (if (m / 4 + if x < m then x else x - m) % p = v then (1 : ℤ) else 0) =
      ∑ x ∈ range m, (if (m / 4 + x) % p = v then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro x hx
    simp [Finset.mem_range.mp hx]
  have h2 : ∑ x ∈ range m,
      (if (m / 4 + if m + x < m then m + x else m + x - m) % p = v then (1 : ℤ) else 0) =
      ∑ x ∈ range m, (if (m / 4 + x) % p = v then (1 : ℤ) else 0) := by
    apply Finset.sum_congr rfl
    intro x _
    simp
  have hw := p0_card_window_res hp (m / 4) m v hv
  rw [Finset.card_filter] at hw
  push_cast at hw
  rw [h1, h2, hw]
  ring

theorem p0ColRes_eq (p m v : ℕ) :
    (p0ColRes p m v : ℤ) = p0ResCnt p (2 * m) v := by
  unfold p0ColRes p0ResCnt
  rw [Finset.card_filter, Finset.card_filter]
  push_cast
  exact Fin.sum_univ_eq_sum_range (fun x => if x % p = v then (1 : ℤ) else 0) (2 * m)

theorem p0ResCnt_add_p {p : ℕ} (hp : 0 < p) (N v : ℕ) (hv : v < p) :
    p0ResCnt p (N + p) v = p0ResCnt p N v + 1 := by
  rw [p0ResCnt_eq hp hv, p0ResCnt_eq hp hv, Nat.add_mod_right, Nat.add_div_right _ hp]
  ring

theorem p0ResCnt_add_mul {p : ℕ} (hp : 0 < p) (N v : ℕ) (hv : v < p) (k : ℕ) :
    p0ResCnt p (N + k * p) v = p0ResCnt p N v + k := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Nat.succ_mul, ← add_assoc, p0ResCnt_add_p hp _ v hv, ih]
    ring

theorem p0ResCnt_window_ge {p : ℕ} (hp : 0 < p) (a n v : ℕ) (hv : v < p) :
    p0ResCnt p a v + n / p ≤ p0ResCnt p (a + n) v := by
  rw [← p0ResCnt_add_mul hp a v hv (n / p)]
  apply p0ResCnt_mono
  have := Nat.div_mul_le_self n p
  omega

theorem p0_card_killed (p g : ℕ) (hp : 0 < p) :
    ((range p).filter (fun v => p0PrimeCarry p g v = 1)).card = g % p := by
  have hr : g % p < p := Nat.mod_lt g hp
  have hset : (range p).filter (fun v => p0PrimeCarry p g v = 1) = Ico (p - g % p) p := by
    ext v
    rw [Finset.mem_filter, Finset.mem_range, Finset.mem_Ico]
    unfold p0PrimeCarry
    constructor
    · rintro ⟨hv, hk⟩
      rw [Nat.mod_eq_of_lt hv] at hk
      by_cases h : p - g % p ≤ v
      · exact ⟨h, hv⟩
      · rw [if_neg h] at hk; exact absurd hk (by decide)
    · rintro ⟨h1, h2⟩
      refine ⟨h2, ?_⟩
      rw [Nat.mod_eq_of_lt h2, if_pos h1]
  rw [hset, Nat.card_Ico]
  omega

theorem p0_sum_colRes (p m : ℕ) (hp : 0 < p) :
    ∑ v ∈ range p, (p0ColRes p m v : ℤ) = 2 * m := by
  have h := p0_sum_fiber (fun c : Fin (2 * m) => c.val % p) (fun x => Nat.mod_lt _ hp)
    (fun _ => (1 : ℤ))
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, one_mul] at h
  unfold p0ColRes
  rw [← h]
  push_cast
  ring

/-- The v13 tail estimate: `W ≤ 3m - 2 ⌊m/p⌋ (g mod p)`. -/
theorem p0Tail_assign (p m : ℕ) (hp : 0 < p) (hpg : p ≤ m / 2)
    (σ : Equiv.Perm (Fin (2 * m))) :
    ∑ i, p0RateWeight p m (σ i) i ≤
      3 * (m : ℤ) - 2 * ((m / p : ℕ) : ℤ) * ((m / 2 % p : ℕ) : ℤ) := by
  refine (p0Low_assign_bound2 p m hp hpg σ).trans ?_
  set κ := fun v => p0PrimeCarry p (m / 2) v
  have hterm : ∀ v ∈ range p,
      ((if κ v = 0 then (p0ColRes p m v : ℤ) else 0) -
          (if κ v = 1 then (p0RowRes p m v : ℤ) else 0) +
          (if κ v = 1 then (min (p0RowRes p m v) (p0ColRes p m v) : ℤ) else 0)) ≤
        (p0ColRes p m v : ℤ) - (if κ v = 1 then 2 * ((m / p : ℕ) : ℤ) else 0) := by
    intro v hv
    have hvp := Finset.mem_range.mp hv
    have hκ := p0PrimeCarry_le_one p (m / 2) v
    have hrow := p0RowRes_eq p m v hp hvp
    have hwin := p0ResCnt_window_ge hp (m / 4) m v hvp
    have hmin1 : (min (p0RowRes p m v) (p0ColRes p m v) : ℤ) ≤ p0ColRes p m v := by
      exact_mod_cast min_le_right _ _
    have hwinZ : ((p0ResCnt p (m / 4) v : ℕ) : ℤ) + ((m / p : ℕ) : ℤ) ≤
        (p0ResCnt p (m / 4 + m) v : ℤ) := by exact_mod_cast hwin
    simp only [κ] at *
    split_ifs <;> omega
  refine (add_le_add le_rfl (Finset.sum_le_sum hterm)).trans ?_
  rw [Finset.sum_sub_distrib, p0_sum_colRes p m hp]
  have hk : ∑ v ∈ range p, (if κ v = 1 then 2 * ((m / p : ℕ) : ℤ) else 0) =
      2 * ((m / p : ℕ) : ℤ) * ((m / 2 % p : ℕ) : ℤ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    rw [p0_card_killed p (m / 2) hp]
    ring
  rw [hk]
  ring_nf
  exact le_refl _

/-- The tail estimate for the maximal assignment weight. -/
theorem p0Tail_assignMax (p m : ℕ) (hp : 0 < p) (hpg : p ≤ m / 2) :
    p0RateAssignMax p m ≤
      3 * (m : ℤ) - 2 * ((m / p : ℕ) : ℤ) * ((m / 2 % p : ℕ) : ℤ) :=
  p0RateAssignMax_le p m _ (fun σ => p0Tail_assign p m hp hpg σ)

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0Tail_assignMax
