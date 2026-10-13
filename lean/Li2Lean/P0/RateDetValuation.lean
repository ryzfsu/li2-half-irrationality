/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationOddPrimeLarge
import Li2Lean.P0.IntegerizationActualOddPrimeRate
import Li2Lean.P0.IntegerizationSmallPrimeTail

/-!
# Determinant valuation from entry valuations (actual `a = 2` P0 matrix)

Leibniz expansion with zero-safe lower valuations: every coefficient of the
determinant has valuation at least the minimum, over permutations, of the
summed entry lower bounds.  For the literal matrix `p0MatrixQ 2 m` and an odd
prime with `p^2 > U + g`, the entry bounds are the proved source bounds
`p0LargePrime_matrix_coeff`.  The moving-prime exponent is the exact maximal
assignment weight `p0RateAssignMax`; the coarse row-scale exponent is used
for the remaining primes.  No table or rate statement is an input here.
-/

namespace Li2Lean.P0.Integerization

noncomputable section

open Polynomial

theorem p0PolyVal_mul {p : ℕ} [Fact p.Prime] {a b : ℤ} {P Q : ℚ[X]}
    (hP : ∀ n, p0ValAtLeast p a (P.coeff n))
    (hQ : ∀ n, p0ValAtLeast p b (Q.coeff n)) :
    ∀ n, p0ValAtLeast p (a + b) ((P * Q).coeff n) := by
  intro n
  rw [Polynomial.coeff_mul]
  exact p0ValAtLeast.sum _ _ (fun x _ => (hP x.1).mul (hQ x.2))

theorem p0PolyVal_one (p : ℕ) : ∀ n, p0ValAtLeast p 0 ((1 : ℚ[X]).coeff n) := by
  intro n
  rw [Polynomial.coeff_one]
  split
  · exact Or.inr (by simp)
  · exact p0ValAtLeast.zero _ _

theorem p0PolyVal_prod {p : ℕ} [Fact p.Prime] {ι : Type*} (s : Finset ι)
    (f : ι → ℚ[X]) (a : ι → ℤ)
    (h : ∀ i ∈ s, ∀ n, p0ValAtLeast p (a i) ((f i).coeff n)) :
    ∀ n, p0ValAtLeast p (∑ i ∈ s, a i) ((∏ i ∈ s, f i).coeff n) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using p0PolyVal_one p
  | @insert x s hx ih =>
    rw [Finset.prod_insert hx, Finset.sum_insert hx]
    exact p0PolyVal_mul (h x (Finset.mem_insert_self x s))
      (ih (fun i hi => h i (Finset.mem_insert_of_mem hi)))

/-- Leibniz bound for the determinant of a polynomial matrix. -/
theorem p0Det_coeff_valAtLeast {p : ℕ} [Fact p.Prime] {n : ℕ}
    (M : Matrix (Fin n) (Fin n) ℚ[X]) (ℓ : Fin n → Fin n → ℤ) (L : ℤ)
    (hM : ∀ r c k, p0ValAtLeast p (ℓ r c) ((M r c).coeff k))
    (hL : ∀ σ : Equiv.Perm (Fin n), L ≤ ∑ i, ℓ (σ i) i) :
    ∀ k, p0ValAtLeast p L ((M.det).coeff k) := by
  intro k
  rw [Matrix.det_apply, Polynomial.finsetSum_coeff]
  apply p0ValAtLeast.sum
  intro σ _
  have hprod := p0PolyVal_prod Finset.univ (fun i => M (σ i) i)
    (fun i => ℓ (σ i) i) (fun i _ n => hM _ _ n) k
  have hprod' := hprod.mono (hL σ)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with hs | hs
  · rw [hs, one_smul]
    exact hprod'
  · rw [hs, Units.neg_smul, one_smul, Polynomial.coeff_neg]
    exact hprod'.neg

/-- The negated source entry bound: the assignment weight of one entry. -/
def p0RateWeight (p m : ℕ) (r c : Fin (2 * m)) : ℤ :=
  -p0PrimeEntryLower p (m / 2) (p0SourceRowIndex m r) c.val (decide (¬ r.val < m))

/-- The exact maximal assignment weight of the literal source entry bounds. -/
def p0RateAssignMax (p m : ℕ) : ℤ :=
  Finset.univ.sup' Finset.univ_nonempty
    (fun σ : Equiv.Perm (Fin (2 * m)) => ∑ i, p0RateWeight p m (σ i) i)

theorem p0RateAssign_le_max (p m : ℕ) (σ : Equiv.Perm (Fin (2 * m))) :
    ∑ i, p0RateWeight p m (σ i) i ≤ p0RateAssignMax p m :=
  Finset.le_sup' (fun σ : Equiv.Perm (Fin (2 * m)) => ∑ i, p0RateWeight p m (σ i) i)
    (Finset.mem_univ σ)

/-- Any uniform assignment bound bounds the maximal weight. -/
theorem p0RateAssignMax_le (p m : ℕ) (W : ℤ)
    (hW : ∀ σ : Equiv.Perm (Fin (2 * m)), ∑ i, p0RateWeight p m (σ i) i ≤ W) :
    p0RateAssignMax p m ≤ W :=
  Finset.sup'_le _ _ (fun σ _ => hW σ)

theorem p0CanonicalPolynomial_two_eq_det (m : ℕ) (h4 : 4 ∣ m) :
    p0CanonicalPolynomial 2 m = Matrix.det (p0MatrixQ 2 m) := by
  simp [p0CanonicalPolynomial, h4]

/-- Moving-prime coefficient valuation of the actual determinant. -/
theorem p0Rate_canonical_coeff_val (p m : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (h4 : 4 ∣ m) (hlarge : 2 * m - 1 + m / 2 < p ^ 2) (n : ℕ) :
    p0ValAtLeast p (-(p0RateAssignMax p m)) ((p0CanonicalPolynomial 2 m).coeff n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [p0CanonicalPolynomial_two_eq_det m h4]
  apply p0Det_coeff_valAtLeast (p0MatrixQ 2 m)
    (fun r c => p0PrimeEntryLower p (m / 2) (p0SourceRowIndex m r) c.val
      (decide (¬ r.val < m)))
  · intro r c k
    exact p0LargePrime_matrix_coeff p m k r c hp hpodd hlarge
  · intro σ
    have h := p0RateAssign_le_max p m σ
    simp only [p0RateWeight, Finset.sum_neg_distrib] at h
    linarith

/-- The concrete moving-prime exponent: the maximal source assignment weight
when `p^2` exceeds every source upper index, and the row-scale exponent
otherwise. -/
def p0RateW (m p : ℕ) : ℤ :=
  if p0SquarefullCutoff m < p ^ 2 then p0RateAssignMax p m
  else ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℤ)

/-- The odd-prime coefficient input of the settled integerizer, for every
`m` divisible by four, with no rate or table premise. -/
theorem p0Rate_odd_valuation (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    P0A2ActualOddPrimeValuationBound m p0RateW := by
  intro p hp hp2 _ n
  by_cases hlarge : p0SquarefullCutoff m < p ^ 2
  · have hpodd : 2 < p := lt_of_le_of_ne hp.two_le (Ne.symm hp2)
    have hl : 2 * m - 1 + m / 2 < p ^ 2 := by
      simpa [p0SquarefullCutoff, p0DenominatorU] using hlarge
    have h := p0Rate_canonical_coeff_val p m hp hpodd h4 hl n
    simp only [p0RateW, if_pos hlarge]
    exact h
  · simp only [p0RateW, if_neg hlarge]
    exact p0A2_baseline_coeff_valuation_lower m hm h4 n p hp

end

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0Det_coeff_valAtLeast
#print axioms Li2Lean.P0.Integerization.p0Rate_canonical_coeff_val
#print axioms Li2Lean.P0.Integerization.p0Rate_odd_valuation
