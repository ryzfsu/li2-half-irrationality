/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Contour
import Li2Lean.P0.IntegerizationS08Combinatorics

/-!
# The base-2 source bank of the P0 determinant (paper v13, `p0-arithmetic.tex` ll. 79-115)

For `g, i, j : ℕ`, with `w_r = binom(r-1,g) 2^{-r}`,

  `B_ij - β A_ij - log 2 · C_ij = (-1)^{g+1} Σ_{r>g} w_r / ((i+r)(j+r))`,

where `A, B, C` are the literal rational P0 bank entries `p0AQ 2, p0BQ 2, p0CQ 2` and
`β = Li₂(1/2) = li2InvValue 2` (paper `eq:p0-source-Dg` combined with
`eq:p0-source-identity` at `a = 2`, where `L(2) = -log 2`).

The paper obtains it by applying `D_g` to the Mellin identity.  Here the same identity is
proved by expanding both sides in powers of `x = 1/2` (`x = 1/a`) and comparing
coefficients: every coefficient identity is the Chu-Vandermonde identity
`binom(i+g-n, g) = Σ_s binom(i+g, g-s) binom(-n, s)` in the binomial ring `ℤ`, plus
(diagonal) the harmonic identity `harmonic_binomial` and the hockey-stick telescoping
`second_telescope`.  No derivative of a series is needed.
-/

open Finset

namespace Li2Lean.P0.Env

noncomputable section



theorem vandermonde_core (i g n : ℕ) (hn : 1 ≤ n) :
    (∑ s ∈ range (g + 1), (-1 : ℤ) ^ s * ((i + g).choose (g - s) : ℤ) *
        ((n + s - 1).choose s : ℤ)) =
      (if n ≤ i then ((i - n + g).choose g : ℤ) else 0) +
      (if i + g < n then (-1 : ℤ) ^ g * ((n - i - 1).choose g : ℤ) else 0) := by
  have hV := Ring.add_choose_eq (R := ℤ) (r := ((i + g : ℕ) : ℤ)) (s := -(n : ℤ)) g
    (Commute.all _ _)
  rw [← Finset.Nat.sum_antidiagonal_swap] at hV
  simp only [Prod.fst_swap, Prod.snd_swap] at hV
  rw [Finset.Nat.sum_antidiagonal_eq_sum_range_succ
      (fun a b => Ring.choose ((i + g : ℕ) : ℤ) b * Ring.choose (-(n : ℤ)) a)] at hV
  have hterm : ∀ s ∈ range (g + 1),
      Ring.choose ((i + g : ℕ) : ℤ) (g - s) * Ring.choose (-(n : ℤ)) s =
        (-1 : ℤ) ^ s * ((i + g).choose (g - s) : ℤ) * ((n + s - 1).choose s : ℤ) := by
    intro s hs
    rw [Ring.choose_natCast, Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast]
    have : ((n : ℤ) + s - 1) = ((n + s - 1 : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub (by omega : 1 ≤ n + s)]; ring
    rw [this, Ring.choose_natCast]
    simp only [smul_eq_mul]
    ring
  rw [Finset.sum_congr rfl hterm] at hV
  rw [← hV]
  rcases le_or_gt n i with h1 | h1
  · have : ((i + g : ℕ) : ℤ) + -(n : ℤ) = ((i - n + g : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h1]; ring
    have h2 : ¬ (i + g < n) := by omega
    rw [this, Ring.choose_natCast]
    simp [h1, h2]
  rcases le_or_gt n (i + g) with h2 | h2
  · have : ((i + g : ℕ) : ℤ) + -(n : ℤ) = ((i + g - n : ℕ) : ℤ) := by
      push_cast [Nat.cast_sub h2]; ring
    have h1' : ¬ (n ≤ i) := by omega
    have h2' : ¬ (i + g < n) := by omega
    rw [this, Ring.choose_natCast, Nat.choose_eq_zero_of_lt (by omega)]
    simp [h1', h2']
  · have e1 : n - i - g = n - (i + g) := by omega
    have e2 : n - i - 1 = n - (i + 1) := by omega
    have : ((i + g : ℕ) : ℤ) + -(n : ℤ) = -((n - i - g : ℕ) : ℤ) := by
      rw [e1]; push_cast [Nat.cast_sub h2.le]; ring
    have h3 : ((n - i - g : ℕ) : ℤ) + g - 1 = ((n - i - 1 : ℕ) : ℤ) := by
      rw [e1, e2]
      push_cast [Nat.cast_sub h2.le, Nat.cast_sub (by omega : i + 1 ≤ n)]
      ring
    have h1' : ¬ (n ≤ i) := by omega
    rw [this, Ring.choose_neg, Units.smul_def, Int.coe_negOnePow_natCast, h3,
      Ring.choose_natCast]
    simp [h1', h2]

/-- The common real core of both coefficient identities. -/
theorem coeff_core (i g n : ℕ) (hn : 1 ≤ n) :
    (if n ≤ i then ((i - n + g).choose g : ℝ) else 0) +
      (∑ t ∈ range g, (-1 : ℝ) ^ t * ((i + g).choose (g - (t + 1)) : ℝ) *
        ((n + t).choose (t + 1) : ℝ)) - ((i + g).choose g : ℝ) =
      -((-1 : ℝ) ^ g * (if i + g < n then ((n - i - 1).choose g : ℝ) else 0)) := by
  have hV := congrArg (fun z : ℤ => (z : ℝ)) (vandermonde_core i g n hn)
  push_cast at hV
  rw [Finset.sum_range_succ'] at hV
  simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one,
    mul_one] at hV
  have hsh : ∀ t, n + (t + 1) - 1 = n + t := fun t => by omega
  simp only [hsh] at hV
  have hs : (∑ t ∈ range g, (-1 : ℝ) ^ (t + 1) * ((i + g).choose (g - (t + 1)) : ℝ) *
      ((n + t).choose (t + 1) : ℝ)) =
      -(∑ t ∈ range g, (-1 : ℝ) ^ t * ((i + g).choose (g - (t + 1)) : ℝ) *
        ((n + t).choose (t + 1) : ℝ)) := by
    rw [← Finset.sum_neg_distrib]
    apply Finset.sum_congr rfl
    intro t _
    ring
  rw [hs] at hV
  split_ifs at hV ⊢ <;> linarith

/-- `n C(n+t,t)/(t+1) = C(n+t,t+1)`. -/
theorem choose_succ_real (n t : ℕ) :
    ((n + t).choose (t + 1) : ℝ) = ((n + t).choose t : ℝ) * n / (t + 1) := by
  have h := Nat.choose_succ_right_eq (n + t) t
  rw [show n + t - t = n by omega] at h
  have h' : ((n + t).choose (t + 1) : ℝ) * ((t : ℝ) + 1) = ((n + t).choose t : ℝ) * n := by
    exact_mod_cast h
  field_simp
  linarith

/-- Second-moment telescoping: `(k+1) C(n+k,k+1) - n = n^2 Σ_{r<k} C(n+r,r)/(r+1)`. -/
theorem second_telescope (n k : ℕ) :
    ((k : ℝ) + 1) * ((n + k).choose (k + 1) : ℝ) - n =
      (n : ℝ) ^ 2 * ∑ r ∈ range k, ((n + r).choose r : ℝ) / ((r : ℝ) + 1) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, mul_add, ← ih]
    have h1 := choose_succ_real n (k + 1)
    have h2 := choose_succ_real n k
    have hp : ((n + (k + 1)).choose (k + 1) : ℝ) =
        ((n + k).choose k : ℝ) + ((n + k).choose (k + 1) : ℝ) := by
      rw [show n + (k + 1) = (n + k) + 1 by omega]
      exact_mod_cast Nat.choose_succ_succ (n + k) k
    rw [show n + (k + 1) = n + k + 1 by omega] at h1 hp ⊢
    push_cast at h1 ⊢
    rw [h1, hp, h2]
    field_simp
    ring

/-- Coefficient identity of the first moment. -/
theorem coeff_first (i g n : ℕ) (hn : 1 ≤ n) :
    (if i + g < n then ((n - i - 1).choose g : ℝ) / n else 0) =
      (-1 : ℝ) ^ (g + 1) *
        ((if n ≤ i then ((i - n + g).choose g : ℝ) / n else 0) +
          (∑ s ∈ range g, ((-1 : ℝ) ^ s / ((s : ℝ) + 1) *
            ((i + g).choose (g - (s + 1)) : ℝ)) * ((n + s).choose s : ℝ)) -
          ((i + g).choose g : ℝ) / n) := by
  have hc := coeff_core i g n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hsum : (∑ s ∈ range g, ((-1 : ℝ) ^ s / ((s : ℝ) + 1) *
      ((i + g).choose (g - (s + 1)) : ℝ)) * ((n + s).choose s : ℝ)) =
      (∑ t ∈ range g, (-1 : ℝ) ^ t * ((i + g).choose (g - (t + 1)) : ℝ) *
        ((n + t).choose (t + 1) : ℝ)) / n := by
    rw [Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    rw [choose_succ_real]
    field_simp
  rw [hsum]
  have hg : ((-1 : ℝ) ^ (g + 1)) * (-1) ^ g = -1 := by
    rw [← pow_add, show g + 1 + g = 2 * g + 1 by ring, pow_succ, pow_mul]; norm_num
  set X := ∑ t ∈ range g, (-1 : ℝ) ^ t * ((i + g).choose (g - (t + 1)) : ℝ) *
        ((n + t).choose (t + 1) : ℝ)
  set A : ℝ := if n ≤ i then ((i - n + g).choose g : ℝ) else 0
  set B : ℝ := if i + g < n then ((n - i - 1).choose g : ℝ) else 0
  have key : (-1 : ℝ) ^ (g + 1) *
        ((if n ≤ i then ((i - n + g).choose g : ℝ) / n else 0) + X / n -
          ((i + g).choose g : ℝ) / n) =
      (-1 : ℝ) ^ (g + 1) * ((A + X - ((i + g).choose g : ℝ)) / n) := by
    simp only [A]; split_ifs <;> field_simp <;> ring
  have hB : (if i + g < n then ((n - i - 1).choose g : ℝ) / n else 0) = B / n := by
    simp only [B]; split_ifs <;> simp
  rw [key, hc, hB]
  rw [show (-1 : ℝ) ^ (g + 1) * (-((-1) ^ g * B) / n) =
    -((-1 : ℝ) ^ (g + 1) * (-1) ^ g) * B / n by ring, hg]
  ring

/-- Reindexing `Σ_{s ∈ [2,g]}` to `Σ_{t<g}` with `s = t+1` (the `s = 1` term is empty). -/
theorem sum_Icc_two_eq_range (g : ℕ) (b : ℕ → ℝ) (c : ℕ → ℝ) :
    (∑ s ∈ Icc 2 g, b s * ∑ r ∈ range (s - 1), c r) =
      ∑ t ∈ range g, b (t + 1) * ∑ r ∈ range t, c r := by
  have h1 : (∑ s ∈ Icc 2 g, b s * ∑ r ∈ range (s - 1), c r) =
      ∑ s ∈ Icc 1 g, b s * ∑ r ∈ range (s - 1), c r := by
    apply Finset.sum_subset
    · intro x hx; simp only [Finset.mem_Icc] at hx ⊢; omega
    · intro x hx hx'
      simp only [Finset.mem_Icc] at hx hx'
      have : x = 1 := by omega
      subst this; simp
  have hI : Icc 1 g = Ico 1 (g + 1) := by ext x; simp only [Finset.mem_Icc, Finset.mem_Ico]; omega
  rw [h1, hI, Finset.sum_Ico_eq_sum_range]
  simp only [show g + 1 - 1 = g by omega]
  apply Finset.sum_congr rfl
  intro t _
  simp only [show 1 + t = t + 1 by ring, Nat.add_sub_cancel]

/-- Coefficient identity of the diagonal second moment. -/
theorem coeff_second (i g n : ℕ) (hn : 1 ≤ n) :
    (if i + g < n then ((n - i - 1).choose g : ℝ) / (n : ℝ) ^ 2 else 0) =
      (-1 : ℝ) ^ (g + 1) *
        ((if n ≤ i then ((i - n + g).choose g : ℝ) / (n : ℝ) ^ 2 else 0) -
          (∑ s ∈ Icc 2 g, ((-1 : ℝ) ^ s / (s : ℝ) * ((i + g).choose (g - s) : ℝ)) *
            ∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) -
          ((i + g).choose g : ℝ) / (n : ℝ) ^ 2 +
          ((i + g).choose g : ℝ) * (∑ s ∈ range g, ((i : ℝ) + s + 1)⁻¹) / n) := by
  have hc := coeff_core i g n hn
  have hnR : (n : ℝ) ≠ 0 := by exact_mod_cast (show n ≠ 0 by omega)
  have hh : ((i + g).choose g : ℝ) * (∑ s ∈ range g, ((i : ℝ) + s + 1)⁻¹) =
      ∑ t ∈ range g, (-1 : ℝ) ^ t / ((t : ℝ) + 1) * ((i + g).choose (g - (t + 1)) : ℝ) := by
    have h := Li2Lean.P0.Integerization.S08.harmonic_binomial i g
    have h' := congrArg (fun q : ℚ => (q : ℝ)) h
    push_cast at h'
    rw [← h']
  rw [sum_Icc_two_eq_range g (fun s => (-1 : ℝ) ^ s / (s : ℝ) * ((i + g).choose (g - s) : ℝ))
    (fun r => ((n + r).choose r : ℝ) / ((r : ℝ) + 1)), hh]
  set X := ∑ t ∈ range g, (-1 : ℝ) ^ t * ((i + g).choose (g - (t + 1)) : ℝ) *
        ((n + t).choose (t + 1) : ℝ)
  have hsum : (∑ t ∈ range g, (-1 : ℝ) ^ (t + 1) / ((t + 1 : ℕ) : ℝ) *
        ((i + g).choose (g - (t + 1)) : ℝ) *
        ∑ r ∈ range t, ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) =
      (-X + n * ∑ t ∈ range g, (-1 : ℝ) ^ t / ((t : ℝ) + 1) *
        ((i + g).choose (g - (t + 1)) : ℝ)) / (n : ℝ) ^ 2 := by
    simp only [X]
    rw [Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib, Finset.sum_div]
    apply Finset.sum_congr rfl
    intro t _
    have hE := second_telescope n t
    have ht : ((t : ℝ) + 1) ≠ 0 := by positivity
    rw [show (∑ r ∈ range t, ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) =
      (((t : ℝ) + 1) * ((n + t).choose (t + 1) : ℝ) - n) / (n : ℝ) ^ 2 by
        rw [hE]; field_simp]
    push_cast
    field_simp
    ring
  rw [hsum]
  have hg : ((-1 : ℝ) ^ (g + 1)) * (-1) ^ g = -1 := by
    rw [← pow_add, show g + 1 + g = 2 * g + 1 by ring, pow_succ, pow_mul]; norm_num
  set A : ℝ := if n ≤ i then ((i - n + g).choose g : ℝ) else 0
  set B : ℝ := if i + g < n then ((n - i - 1).choose g : ℝ) else 0
  set Y := ∑ t ∈ range g, (-1 : ℝ) ^ t / ((t : ℝ) + 1) * ((i + g).choose (g - (t + 1)) : ℝ)
  have key : (-1 : ℝ) ^ (g + 1) *
        ((if n ≤ i then ((i - n + g).choose g : ℝ) / (n : ℝ) ^ 2 else 0) -
          (-X + n * Y) / (n : ℝ) ^ 2 - ((i + g).choose g : ℝ) / (n : ℝ) ^ 2 + Y / n) =
      (-1 : ℝ) ^ (g + 1) * ((A + X - ((i + g).choose g : ℝ)) / (n : ℝ) ^ 2) := by
    simp only [A]; split_ifs <;> field_simp <;> ring
  have hB : (if i + g < n then ((n - i - 1).choose g : ℝ) / (n : ℝ) ^ 2 else 0) =
      B / (n : ℝ) ^ 2 := by
    simp only [B]; split_ifs <;> simp
  rw [key, hc, hB]
  rw [show (-1 : ℝ) ^ (g + 1) * (-((-1) ^ g * B) / (n : ℝ) ^ 2) =
    -((-1 : ℝ) ^ (g + 1) * (-1) ^ g) * B / (n : ℝ) ^ 2 by ring, hg]
  ring


theorem hasSum_log_two :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else (2 : ℝ)⁻¹ ^ n / n) (Real.log 2) := by
  have h := Real.hasSum_pow_div_log_of_abs_lt_one (x := (2 : ℝ)⁻¹) (by norm_num [abs_of_pos])
  have hv : -Real.log (1 - (2 : ℝ)⁻¹) = Real.log 2 := by
    rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, Real.log_inv, neg_neg]
  rw [hv] at h
  rw [← hasSum_nat_add_iff' 1]
  simpa using h

theorem summable_li2_terms :
    Summable (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1) / ((k : ℝ) + 1) ^ 2) := by
  apply Summable.of_nonneg_of_le (fun k => by positivity)
  · intro k
    have h1 : (1 : ℝ) ≤ ((k : ℝ) + 1) ^ 2 := by nlinarith [(Nat.cast_nonneg k : (0 : ℝ) ≤ k)]
    exact div_le_self (by positivity) h1
  · have hg := (summable_geometric_of_lt_one (r := (2 : ℝ)⁻¹) (by norm_num)
      (by norm_num)).mul_left (2 : ℝ)⁻¹
    exact hg.congr (fun k => by ring)

theorem hasSum_li2_two :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else (2 : ℝ)⁻¹ ^ n / (n : ℝ) ^ 2)
      (li2InvValue 2) := by
  have h : HasSum (fun k : ℕ => (2 : ℝ)⁻¹ ^ (k + 1) / ((k : ℝ) + 1) ^ 2) (li2InvValue 2) := by
    unfold li2InvValue
    push_cast
    exact summable_li2_terms.hasSum
  rw [← hasSum_nat_add_iff' 1]
  simpa using h

theorem hasSum_geo_tail (s : ℕ) :
    HasSum (fun n : ℕ => if n = 0 then (0 : ℝ) else ((n + s).choose s : ℝ) * (2 : ℝ)⁻¹ ^ n)
      ((2 : ℝ) ^ (s + 1) - 1) := by
  have h := hasSum_choose_mul_geometric_of_norm_lt_one (𝕜 := ℝ) s (r := (2 : ℝ)⁻¹)
    (by norm_num [abs_of_pos])
  have hv : (1 : ℝ) / (1 - 2⁻¹) ^ (s + 1) = 2 ^ (s + 1) := by
    rw [show (1 : ℝ) - 2⁻¹ = 2⁻¹ by norm_num, inv_pow, one_div, inv_inv]
  rw [hv] at h
  rw [← hasSum_nat_add_iff' 1]
  have h' := (hasSum_nat_add_iff' 1).mpr h
  simpa using h'


/-- The finite head `Σ_{r<i} U_{i-r-1}/(r+1)`, scaled by `2^{-i}`, as a series. -/
def headFirst (g i n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n ≤ i then ((i - n + g).choose g : ℝ) / n * (2 : ℝ)⁻¹ ^ n else 0

theorem hasSum_headFirst (g i : ℕ) :
    HasSum (headFirst g i)
      (∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
        (2 : ℝ)⁻¹ ^ (r + 1)) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := range (i + 1)) (f := headFirst g i) (by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp only [headFirst]
    simp only [show ¬ (1 ≤ n ∧ n ≤ i) by omega, if_false])
  convert h using 1
  rw [Finset.sum_range_succ']
  simp only [headFirst, show ¬ (1 ≤ 0 ∧ 0 ≤ i) by omega, if_false, add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_range] at hr
  rw [if_pos (by omega)]
  push_cast
  ring

def geoTail (s n : ℕ) : ℝ :=
  if n = 0 then 0 else ((n + s).choose s : ℝ) * (2 : ℝ)⁻¹ ^ n

def logTail (n : ℕ) : ℝ := if n = 0 then 0 else (2 : ℝ)⁻¹ ^ n / n

def tailFirst (g i n : ℕ) : ℝ :=
  if i + g < n then ((n - i - 1).choose g : ℝ) / n * (2 : ℝ)⁻¹ ^ n else 0

def aFirst (g i s : ℕ) : ℝ :=
  (-1 : ℝ) ^ s / ((s : ℝ) + 1) * ((i + g).choose (g - (s + 1)) : ℝ)

theorem tailFirst_eq (g i n : ℕ) :
    tailFirst g i n = (-1 : ℝ) ^ (g + 1) *
      (headFirst g i n + ∑ s ∈ range g, aFirst g i s * geoTail s n -
        ((i + g).choose g : ℝ) * logTail n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tailFirst, headFirst, geoTail, logTail]
  have hc := coeff_first i g n hn
  have hn0 : n ≠ 0 := by omega
  have hT : tailFirst g i n =
      (if i + g < n then ((n - i - 1).choose g : ℝ) / n else 0) * (2 : ℝ)⁻¹ ^ n := by
    unfold tailFirst; split_ifs <;> simp
  have hH : headFirst g i n =
      (if n ≤ i then ((i - n + g).choose g : ℝ) / n else 0) * (2 : ℝ)⁻¹ ^ n := by
    by_cases h : n ≤ i
    · simp [headFirst, h, show 1 ≤ n by omega]
    · simp [headFirst, h]
  have hG : ∀ s, geoTail s n = ((n + s).choose s : ℝ) * (2 : ℝ)⁻¹ ^ n := fun s => by
    simp [geoTail, hn0]
  have hL : logTail n = (2 : ℝ)⁻¹ ^ n / n := by simp [logTail, hn0]
  rw [hT, hc, hH, hL]
  simp only [hG, aFirst]
  rw [show (∑ s ∈ range g, (-1 : ℝ) ^ s / ((s : ℝ) + 1) * ((i + g).choose (g - (s + 1)) : ℝ) *
      (((n + s).choose s : ℝ) * (2 : ℝ)⁻¹ ^ n)) =
      (∑ s ∈ range g, (-1 : ℝ) ^ s / ((s : ℝ) + 1) * ((i + g).choose (g - (s + 1)) : ℝ) *
      ((n + s).choose s : ℝ)) * (2 : ℝ)⁻¹ ^ n by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring]
  ring

/-- The first moment of the frequency weights, in scaled form. -/
theorem hasSum_tailFirst (g i : ℕ) :
    HasSum (tailFirst g i) ((-1 : ℝ) ^ (g + 1) *
      ((∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
          (2 : ℝ)⁻¹ ^ (r + 1)) +
        ∑ s ∈ range g, aFirst g i s * ((2 : ℝ) ^ (s + 1) - 1) -
        ((i + g).choose g : ℝ) * Real.log 2)) := by
  have hcomb := (((hasSum_headFirst g i).add (hasSum_sum (s := range g) (fun s _ =>
      (hasSum_geo_tail s).mul_left (aFirst g i s)))).sub
      (hasSum_log_two.mul_left ((i + g).choose g : ℝ))).mul_left ((-1 : ℝ) ^ (g + 1))
  convert hcomb using 1
  funext n
  rw [tailFirst_eq]
  simp only [geoTail, logTail]


def headSecond (g i n : ℕ) : ℝ :=
  if 1 ≤ n ∧ n ≤ i then ((i - n + g).choose g : ℝ) / (n : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ n else 0

theorem hasSum_headSecond (g i : ℕ) :
    HasSum (headSecond g i)
      (∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
        (2 : ℝ)⁻¹ ^ (r + 1)) := by
  have h := hasSum_sum_of_ne_finset_zero (L := SummationFilter.unconditional ℕ)
    (s := range (i + 1)) (f := headSecond g i) (by
    intro n hn
    simp only [Finset.mem_range, not_lt] at hn
    simp [headSecond, show ¬ (1 ≤ n ∧ n ≤ i) by omega])
  convert h using 1
  rw [Finset.sum_range_succ']
  simp only [headSecond, show ¬ (1 ≤ 0 ∧ 0 ≤ i) by omega, ite_false, add_zero]
  apply Finset.sum_congr rfl
  intro r hr
  simp only [Finset.mem_range] at hr
  rw [if_pos (show 1 ≤ r + 1 ∧ r + 1 ≤ i by omega)]
  push_cast
  ring

def li2Tail (n : ℕ) : ℝ := if n = 0 then 0 else (2 : ℝ)⁻¹ ^ n / (n : ℝ) ^ 2

def tailSecond (g i n : ℕ) : ℝ :=
  if i + g < n then ((n - i - 1).choose g : ℝ) / (n : ℝ) ^ 2 * (2 : ℝ)⁻¹ ^ n else 0

def bSecond (g i s : ℕ) : ℝ := (-1 : ℝ) ^ s / (s : ℝ) * ((i + g).choose (g - s) : ℝ)

def harm (g i : ℕ) : ℝ := ∑ s ∈ range g, ((i : ℝ) + s + 1)⁻¹

theorem tailSecond_eq (g i n : ℕ) :
    tailSecond g i n = (-1 : ℝ) ^ (g + 1) *
      (headSecond g i n -
        ∑ s ∈ Icc 2 g, bSecond g i s *
          ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * geoTail r n -
        ((i + g).choose g : ℝ) * li2Tail n +
        ((i + g).choose g : ℝ) * harm g i * logTail n) := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [tailSecond, headSecond, geoTail, logTail, li2Tail]
  have hc := coeff_second i g n hn
  have hn0 : n ≠ 0 := by omega
  have hT : tailSecond g i n =
      (if i + g < n then ((n - i - 1).choose g : ℝ) / (n : ℝ) ^ 2 else 0) *
        (2 : ℝ)⁻¹ ^ n := by
    unfold tailSecond; split_ifs <;> simp
  have hH : headSecond g i n =
      (if n ≤ i then ((i - n + g).choose g : ℝ) / (n : ℝ) ^ 2 else 0) * (2 : ℝ)⁻¹ ^ n := by
    by_cases h : n ≤ i
    · simp [headSecond, h, show 1 ≤ n by omega]
    · simp [headSecond, h]
  have hG : ∀ s, geoTail s n = ((n + s).choose s : ℝ) * (2 : ℝ)⁻¹ ^ n := fun s => by
    simp [geoTail, hn0]
  have hL : logTail n = (2 : ℝ)⁻¹ ^ n / n := by simp [logTail, hn0]
  have hL2 : li2Tail n = (2 : ℝ)⁻¹ ^ n / (n : ℝ) ^ 2 := by simp [li2Tail, hn0]
  rw [hT, hc, hH, hL, hL2]
  simp only [hG, bSecond, harm]
  have hin : ∀ s, (∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ *
      (((n + r).choose r : ℝ) * (2 : ℝ)⁻¹ ^ n)) =
      (∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) * (2 : ℝ)⁻¹ ^ n := by
    intro s; rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro r _; ring
  simp only [hin]
  rw [show (∑ s ∈ Icc 2 g, (-1 : ℝ) ^ s / (s : ℝ) * ((i + g).choose (g - s) : ℝ) *
      ((∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1)) * (2 : ℝ)⁻¹ ^ n)) =
      (∑ s ∈ Icc 2 g, (-1 : ℝ) ^ s / (s : ℝ) * ((i + g).choose (g - s) : ℝ) *
      (∑ r ∈ range (s - 1), ((n + r).choose r : ℝ) / ((r : ℝ) + 1))) * (2 : ℝ)⁻¹ ^ n by
    rw [Finset.sum_mul]; apply Finset.sum_congr rfl; intro s _; ring]
  ring

theorem hasSum_tailSecond (g i : ℕ) :
    HasSum (tailSecond g i) ((-1 : ℝ) ^ (g + 1) *
      ((∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
          (2 : ℝ)⁻¹ ^ (r + 1)) -
        ∑ s ∈ Icc 2 g, bSecond g i s *
          ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * ((2 : ℝ) ^ (r + 1) - 1) -
        ((i + g).choose g : ℝ) * li2InvValue 2 +
        ((i + g).choose g : ℝ) * harm g i * Real.log 2)) := by
  have hinner : ∀ s, HasSum (fun n => ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * geoTail r n)
      (∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * ((2 : ℝ) ^ (r + 1) - 1)) := fun s =>
    hasSum_sum (s := range (s - 1)) (fun r _ => (hasSum_geo_tail r).mul_left _)
  have hcomb := ((((hasSum_headSecond g i).sub (hasSum_sum (s := Icc 2 g) (fun s _ =>
      (hinner s).mul_left (bSecond g i s)))).sub
      (hasSum_li2_two.mul_left ((i + g).choose g : ℝ))).add
      (hasSum_log_two.mul_left (((i + g).choose g : ℝ) * harm g i))).mul_left
        ((-1 : ℝ) ^ (g + 1))
  convert hcomb using 1
  funext n
  rw [tailSecond_eq]
  simp only [geoTail, logTail, li2Tail]

/-- Dropping an initial block of zero terms. -/
theorem hasSum_shift_of_zero {f : ℕ → ℝ} {V : ℝ} (k : ℕ) (hz : ∀ n < k, f n = 0)
    (h : HasSum f V) : HasSum (fun r => f (r + k)) V := by
  have := (hasSum_nat_add_iff' k).mpr h
  simpa [Finset.sum_eq_zero (fun n hn => hz n (Finset.mem_range.mp hn))] using this

theorem frequencyWeightReal_eq (g r : ℕ) :
    frequencyWeightReal g r = ((r - 1).choose g : ℝ) * (2 : ℝ)⁻¹ ^ r := by
  simp [frequencyWeightReal, div_eq_mul_inv, inv_pow]

theorem tailFirst_shift (g i r : ℕ) :
    tailFirst g i (r + i) = (2 : ℝ)⁻¹ ^ i *
      (if g < r then frequencyWeightReal g r / ((i : ℝ) + r) else 0) := by
  unfold tailFirst
  by_cases h : g < r
  · rw [if_pos (by omega), if_pos h, frequencyWeightReal_eq,
      show r + i - i - 1 = r - 1 by omega, pow_add]
    push_cast; ring
  · rw [if_neg (by omega), if_neg h]; ring

theorem tailSecond_shift (g i r : ℕ) :
    tailSecond g i (r + i) = (2 : ℝ)⁻¹ ^ i *
      (if g < r then frequencyWeightReal g r / ((i : ℝ) + r) ^ 2 else 0) := by
  unfold tailSecond
  by_cases h : g < r
  · rw [if_pos (by omega), if_pos h, frequencyWeightReal_eq,
      show r + i - i - 1 = r - 1 by omega, pow_add]
    push_cast; ring
  · rw [if_neg (by omega), if_neg h]; ring


theorem p0UQ_two_cast (g i : ℕ) :
    ((p0UQ 2 g i : ℚ) : ℝ) = (2 : ℝ) ^ i * ((i + g).choose g : ℝ) := by
  simp [p0UQ]

theorem p0Q_two_cast (s : ℕ) : ((p0Q 2 s : ℚ) : ℝ) = (2 : ℝ) ^ s - 1 := by
  simp [p0Q]; norm_num

theorem headFirst_scale (g i : ℕ) :
    (2 : ℝ) ^ i * (∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
        (2 : ℝ)⁻¹ ^ (r + 1)) =
      ∑ r ∈ range i, ((p0UQ 2 g (i - (r + 1)) : ℚ) : ℝ) / ((r : ℝ) + 1) := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r + 1 ≤ i := by simp at hr; omega
  rw [p0UQ_two_cast, show i - (r + 1) + g = i - (r + 1) + g from rfl]
  have hp : (2 : ℝ) ^ i * (2 : ℝ)⁻¹ ^ (r + 1) = (2 : ℝ) ^ (i - (r + 1)) := by
    rw [inv_pow, pow_sub₀ _ (by norm_num : (2 : ℝ) ≠ 0) hr']
  calc (2 : ℝ) ^ i * (((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) * (2 : ℝ)⁻¹ ^ (r + 1))
      = ((2 : ℝ) ^ i * (2 : ℝ)⁻¹ ^ (r + 1)) * ((i - (r + 1) + g).choose g : ℝ) /
          ((r : ℝ) + 1) := by ring
    _ = _ := by rw [hp]

theorem headSecond_scale (g i : ℕ) :
    (2 : ℝ) ^ i * (∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
        (2 : ℝ)⁻¹ ^ (r + 1)) =
      ∑ r ∈ range i, ((p0UQ 2 g (i - (r + 1)) : ℚ) : ℝ) / ((r : ℝ) + 1) ^ 2 := by
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hr' : r + 1 ≤ i := by simp at hr; omega
  rw [p0UQ_two_cast]
  have hp : (2 : ℝ) ^ i * (2 : ℝ)⁻¹ ^ (r + 1) = (2 : ℝ) ^ (i - (r + 1)) := by
    rw [inv_pow, pow_sub₀ _ (by norm_num : (2 : ℝ) ≠ 0) hr']
  calc (2 : ℝ) ^ i * (((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
        (2 : ℝ)⁻¹ ^ (r + 1))
      = ((2 : ℝ) ^ i * (2 : ℝ)⁻¹ ^ (r + 1)) * ((i - (r + 1) + g).choose g : ℝ) /
          ((r : ℝ) + 1) ^ 2 := by ring
    _ = _ := by rw [hp]

theorem p0TQ_two_cast (g i : ℕ) :
    ((p0TQ 2 g i : ℚ) : ℝ) = (2 : ℝ) ^ i *
      ((∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) *
          (2 : ℝ)⁻¹ ^ (r + 1)) +
        ∑ s ∈ range g, aFirst g i s * ((2 : ℝ) ^ (s + 1) - 1)) := by
  rw [mul_add, headFirst_scale]
  unfold p0TQ
  push_cast
  congr 1 <;> first
    | rfl
    | (congr 1
       apply Finset.sum_congr rfl
       intro s _
       rw [p0Q_two_cast, aFirst])

theorem p0BQQ_two_cast (g i : ℕ) :
    ((p0BQQ 2 g i : ℚ) : ℝ) = (2 : ℝ) ^ i *
      ((∑ r ∈ range i, ((i - (r + 1) + g).choose g : ℝ) / ((r : ℝ) + 1) ^ 2 *
          (2 : ℝ)⁻¹ ^ (r + 1)) -
        ∑ s ∈ Icc 2 g, bSecond g i s *
          ∑ r ∈ range (s - 1), ((r : ℝ) + 1)⁻¹ * ((2 : ℝ) ^ (r + 1) - 1)) := by
  rw [mul_sub, headSecond_scale]
  unfold p0BQQ
  push_cast
  congr 1 <;> first
    | rfl
    | (congr 1
       apply Finset.sum_congr rfl
       intro s _
       rw [bSecond, Finset.mul_sum, Finset.mul_sum]
       apply Finset.sum_congr rfl
       intro r _
       rw [p0Q_two_cast]
       ring)

/-- First frequency moment at base `2`: `Σ_{r>g} w_r/(i+r) = (-1)^{g+1}(t_i - log 2 U_i)`. -/
theorem hasSum_first (g i : ℕ) :
    HasSum (fun r : ℕ => if g < r then frequencyWeightReal g r / ((i : ℝ) + r) else 0)
      ((-1 : ℝ) ^ (g + 1) *
        (((p0TQ 2 g i : ℚ) : ℝ) - Real.log 2 * ((p0UQ 2 g i : ℚ) : ℝ))) := by
  have h := (hasSum_shift_of_zero i (fun n hn => by
    unfold tailFirst; rw [if_neg (by omega)]) (hasSum_tailFirst g i)).mul_left ((2 : ℝ) ^ i)
  convert h using 1
  · funext r
    rw [tailFirst_shift, ← mul_assoc, ← mul_pow, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_pow,
      one_mul]
  · rw [p0TQ_two_cast, p0UQ_two_cast]; ring

/-- Diagonal second frequency moment at base `2`. -/
theorem hasSum_second (g i : ℕ) :
    HasSum (fun r : ℕ => if g < r then frequencyWeightReal g r / ((i : ℝ) + r) ^ 2 else 0)
      ((-1 : ℝ) ^ (g + 1) *
        (((p0BQQ 2 g i : ℚ) : ℝ) - li2InvValue 2 * ((p0UQ 2 g i : ℚ) : ℝ) -
          Real.log 2 * ((p0CQ 2 g i i : ℚ) : ℝ))) := by
  have h := (hasSum_shift_of_zero i (fun n hn => by
    unfold tailSecond; rw [if_neg (by omega)]) (hasSum_tailSecond g i)).mul_left ((2 : ℝ) ^ i)
  convert h using 1
  · funext r
    rw [tailSecond_shift, ← mul_assoc, ← mul_pow, show (2 : ℝ) * 2⁻¹ = 1 by norm_num, one_pow,
      one_mul]
  · rw [p0BQQ_two_cast, p0UQ_two_cast]
    have hC : ((p0CQ 2 g i i : ℚ) : ℝ) = -((2 : ℝ) ^ i * ((i + g).choose g : ℝ)) * harm g i := by
      simp only [p0CQ, if_true]
      push_cast
      rw [← p0UQ_two_cast]
      simp [harm, p0UQ]
    rw [hC]; ring

/-- The base-`2` source bank (paper v13 `eq:p0-source-Dg`, `eq:p0-source-identity`):
`B_ij - β A_ij - log 2 · C_ij = (-1)^{g+1} Σ_{r>g} w_r /((i+r)(j+r))`. -/
theorem bank_hasSum (g i j : ℕ) :
    HasSum (fun r : ℕ =>
        if g < r then frequencyWeightReal g r / (((i : ℝ) + r) * ((j : ℝ) + r)) else 0)
      ((-1 : ℝ) ^ (g + 1) *
        (((p0BQ 2 g i j : ℚ) : ℝ) - li2InvValue 2 * ((p0AQ 2 g i j : ℚ) : ℝ) -
          Real.log 2 * ((p0CQ 2 g i j : ℚ) : ℝ))) := by
  by_cases hij : i = j
  · subst hij
    convert hasSum_second g i using 1
    · funext r; split_ifs <;> ring
    · simp [p0BQ, p0AQ]
  · have hji : (j : ℝ) - i ≠ 0 := sub_ne_zero.mpr (by exact_mod_cast (Ne.symm hij))
    have h := ((hasSum_first g i).sub (hasSum_first g j)).div_const ((j : ℝ) - i)
    convert h using 1
    · funext r
      split_ifs with hr
      · have hjr : (j : ℝ) + r ≠ 0 := by
          have : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
          positivity
        have hir' : (i : ℝ) + r ≠ 0 := by
          have : (0 : ℝ) < r := by exact_mod_cast (show 0 < r by omega)
          positivity
        field_simp
        ring
      · simp
    · simp only [p0BQ, p0AQ, p0CQ, if_neg hij]
      push_cast
      field_simp
      ring

end

end Li2Lean.P0.Env
