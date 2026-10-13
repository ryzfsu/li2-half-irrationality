/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Mathlib.NumberTheory.Padics.PadicVal.Basic

namespace Li2Lean.P0.Integerization

noncomputable section

set_option linter.style.haveILetI false

/-- The units-digit carry in the paper's moving-prime argument. The zero
remainder convention is automatic, since the units digit is always below `p`. -/
def p0PrimeCarry (p g n : ℕ) : ℕ :=
  if p - g % p ≤ n % p then 1 else 0

/-- Legendre's factorial formula when only its first floor term can occur. -/
theorem p0LargePrime_factorial (p N : ℕ) (hp : p.Prime)
    (hN : N < p ^ 2) : padicValNat p N.factorial = N / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p N < 2 :=
    Nat.log_lt_of_lt_pow' (by decide) hN
  rw [padicValNat_factorial hlog]
  norm_num

/-- Kummer's one-carry formula, valid for every actual source upper index
strictly below `p²`, including the case `g % p = 0`. -/
theorem p0LargePrime_choose_carry (p g n : ℕ) (hp : p.Prime)
    (hN : n + g < p ^ 2) :
    padicValNat p ((n + g).choose g) = p0PrimeCarry p g n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (n + g) < 2 :=
    Nat.log_lt_of_lt_pow' (by decide) hN
  rw [padicValNat_choose' hlog]
  have hg : g % p < p := Nat.mod_lt _ hp.pos
  have hn : n % p < p := Nat.mod_lt _ hp.pos
  have hequiv : p ≤ g % p + n % p ↔ p - g % p ≤ n % p := by omega
  have hset : Finset.Ico 1 2 = {1} := by decide
  rw [hset]
  simp only [Finset.filter_singleton, pow_one]
  by_cases hc : p ≤ g % p + n % p
  · have hk := hequiv.mp hc
    simp [hc, hk, p0PrimeCarry]
  · have hk : ¬ p - g % p ≤ n % p := fun h => hc (hequiv.mpr h)
    simp [hc, hk, p0PrimeCarry]

/-- Exact Legendre floor difference for the same binomial coefficient. -/
theorem p0LargePrime_choose_floor (p g n : ℕ) (hp : p.Prime)
    (hN : n + g < p ^ 2) :
    padicValNat p ((n + g).choose g) =
      (n + g) / p - n / p - g / p := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Nat.choose_eq_factorial_div_factorial (Nat.le_add_left g n)]
  rw [padicValNat.div_of_dvd (Nat.factorial_mul_factorial_dvd_factorial
      (Nat.le_add_left g n))]
  rw [padicValNat.mul (Nat.factorial_ne_zero _) (Nat.factorial_ne_zero _)]
  rw [Nat.add_sub_cancel]
  rw [p0LargePrime_factorial p (n + g) hp hN,
    p0LargePrime_factorial p g hp (by omega),
    p0LargePrime_factorial p n hp (by omega)]
  omega

/-- The carry flag is in `{0,1}` without any parity or generic-position input. -/
theorem p0PrimeCarry_le_one (p g n : ℕ) : p0PrimeCarry p g n ≤ 1 := by
  unfold p0PrimeCarry
  split <;> omega

/-- Multiples of `p` preserve the carry flag on the first-source shifted
binomial, exactly as required by the rational summand denominators. -/
theorem p0LargePrime_shifted_choose_carry (p g n s : ℕ) (hp : p.Prime)
    (hN : n + g < p ^ 2) (hs : s ≤ n) (hps : p ∣ s) :
    padicValNat p ((n - s + g).choose g) = p0PrimeCarry p g n := by
  rw [p0LargePrime_choose_carry p g (n - s) hp (by omega)]
  have hmod : (n - s) % p = n % p := by
    obtain ⟨t, ht⟩ := hps
    have hEq : n = (n - s) + s := by omega
    rw [hEq, ht, Nat.add_mod]
    simp
  simp [p0PrimeCarry, hmod]

/-- A positive denominator below `p²` contains at most one factor of `p`. -/
theorem p0LargePrime_denominator_le_one (p d : ℕ) (hp : p.Prime)
    (hd : 0 < d) (hlarge : d < p ^ 2) : padicValNat p d ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hnot : ¬ p ^ 2 ∣ d := Nat.not_dvd_of_pos_of_lt hd hlarge
  have hlt : ¬ 2 ≤ padicValNat p d := by
    intro h
    exact hnot ((padicValNat_dvd_iff_le (Nat.ne_of_gt hd)).2 h)
  omega

/-- Zero-safe lower valuation bound. This treats a zero coefficient as
having arbitrarily high valuation, unlike `padicValRat`'s default at zero. -/
def p0ValAtLeast (p : ℕ) (k : ℤ) (q : ℚ) : Prop :=
  q = 0 ∨ k ≤ padicValRat p q

namespace p0ValAtLeast

variable {p : ℕ} {k l : ℤ} {q r : ℚ}

@[simp] theorem zero (p : ℕ) (k : ℤ) : p0ValAtLeast p k 0 := Or.inl rfl

theorem mono (h : p0ValAtLeast p k q) (hl : l ≤ k) :
    p0ValAtLeast p l q := h.imp id (hl.trans ·)

theorem neg (h : p0ValAtLeast p k q) : p0ValAtLeast p k (-q) := by
  rcases h with h | h
  · simp [h]
  · exact Or.inr (by simpa using h)

theorem add [Fact p.Prime] (hq : p0ValAtLeast p k q)
    (hr : p0ValAtLeast p k r) : p0ValAtLeast p k (q + r) := by
  rcases hq with rfl | hq
  · simpa using hr
  rcases hr with rfl | hr
  · simpa [p0ValAtLeast] using (Or.inr hq : p0ValAtLeast p k q)
  by_cases hqr : q + r = 0
  · exact Or.inl hqr
  · exact Or.inr ((le_min hq hr).trans (padicValRat.min_le_padicValRat_add hqr))

theorem sub [Fact p.Prime] (hq : p0ValAtLeast p k q)
    (hr : p0ValAtLeast p k r) : p0ValAtLeast p k (q - r) := by
  simpa [sub_eq_add_neg] using hq.add hr.neg

theorem mul [Fact p.Prime] (hq : p0ValAtLeast p k q)
    (hr : p0ValAtLeast p l r) : p0ValAtLeast p (k + l) (q * r) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  by_cases hr0 : r = 0
  · simp [hr0]
  apply Or.inr
  rw [padicValRat.mul hq0 hr0]
  exact add_le_add (hq.resolve_left hq0) (hr.resolve_left hr0)

theorem div [Fact p.Prime] (hq : p0ValAtLeast p k q) (r : ℚ) :
    p0ValAtLeast p (k - padicValRat p r) (q / r) := by
  by_cases hq0 : q = 0
  · simp [hq0]
  by_cases hr0 : r = 0
  · simp [hr0]
  apply Or.inr
  rw [padicValRat.div hq0 hr0]
  exact sub_le_sub_right (hq.resolve_left hq0) _

theorem natCast (p n : ℕ) : p0ValAtLeast p 0 (n : ℚ) :=
  Or.inr (zero_le_padicValRat_of_nat n)

theorem intCast (p : ℕ) (z : ℤ) : p0ValAtLeast p 0 (z : ℚ) := by
  exact Or.inr (by rw [padicValRat.of_int]; exact Int.natCast_nonneg _)

theorem sum [Fact p.Prime] {α : Type*} (s : Finset α) (f : α → ℚ)
    (h : ∀ x ∈ s, p0ValAtLeast p k (f x)) :
    p0ValAtLeast p k (∑ x ∈ s, f x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert x s hx ih =>
      rw [Finset.sum_insert hx]
      exact (h x (Finset.mem_insert_self x s)).add
        (ih (fun y hy => h y (Finset.mem_insert_of_mem hy)))

end p0ValAtLeast

/-- Subtracting a `p`-multiple from the lower binomial index gives the same
single carry; this covers the correction sum of the literal first moment. -/
theorem p0LargePrime_correction_choose_carry (p g n s : ℕ) (hp : p.Prime)
    (hN : n + g < p ^ 2) (hs : s ≤ g) (hps : p ∣ s) :
    padicValNat p ((n + g).choose (g - s)) = p0PrimeCarry p g n := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hlog : Nat.log p (n + g) < 2 := Nat.log_lt_of_lt_pow' (by decide) hN
  rw [padicValNat_choose (by omega : g - s ≤ n + g) hlog]
  have hsub : n + g - (g - s) = n + s := by omega
  have hmodg : (g - s) % p = g % p := by
    obtain ⟨t, ht⟩ := hps
    have hEq : g = (g - s) + s := by omega
    rw [hEq, ht, Nat.add_mod]
    simp
  have hmodn : (n + s) % p = n % p := by
    obtain ⟨t, ht⟩ := hps
    rw [ht, Nat.add_mod]
    simp
  have hset : Finset.Ico 1 2 = {1} := by decide
  rw [hset]
  simp only [Finset.filter_singleton, pow_one, hsub, hmodg, hmodn]
  have hg : g % p < p := Nat.mod_lt _ hp.pos
  have hequiv : p ≤ g % p + n % p ↔ p - g % p ≤ n % p := by omega
  by_cases hc : p ≤ g % p + n % p
  · have hk := hequiv.mp hc
    simp [hc, hk, p0PrimeCarry]
  · have hk : ¬ p - g % p ≤ n % p := fun h => hc (hequiv.mpr h)
    simp [hc, hk, p0PrimeCarry]

/-- Actual `a=2` source coefficient valuation at an odd large prime. -/
theorem p0LargePrime_UQ (p g n : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hN : n + g < p ^ 2) :
    padicValRat p (p0UQ 2 g n) = (p0PrimeCarry p g n : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : ¬ p ∣ 2 := by
    intro hd
    have h := Nat.le_of_dvd (by decide : 0 < 2) hd
    omega
  have h2 : padicValRat p (2 : ℚ) = 0 := by
    rw [show (2 : ℚ) = ((2 : ℕ) : ℚ) by norm_num, padicValRat.of_nat,
      padicValNat.eq_zero_of_not_dvd hp2]
    rfl
  have hc : ((n + g).choose g : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (Nat.le_add_left g n)
  rw [p0UQ, padicValRat.mul (by positivity) hc, padicValRat.pow,
    h2, mul_zero, zero_add, padicValRat.of_nat,
    p0LargePrime_choose_carry p g n hp hN]

/-- The literal specialized Q-term is integral at every prime. -/
theorem p0Q_two_valAtLeast (p s : ℕ) : p0ValAtLeast p 0 (p0Q 2 s) := by
  have heq : p0Q 2 s = ((2 : ℤ) ^ s - 1 : ℤ) := by
    norm_num [p0Q]
  rw [heq]
  exact p0ValAtLeast.intCast _ _

/-- The first-moment source valuation, with the copy-index exception required
by the high-ratio potential table. -/
def p0PrimeTheta (p g n : ℕ) : ℤ :=
  if p ≤ n ∨ p ≤ g then (p0PrimeCarry p g n : ℤ) - 1 else 0

theorem p0PrimeTheta_nonpos (p g n : ℕ) : p0PrimeTheta p g n ≤ 0 := by
  have hκ := p0PrimeCarry_le_one p g n
  unfold p0PrimeTheta
  split <;> omega

theorem p0UQ_two_ne_zero (g n : ℕ) : p0UQ 2 g n ≠ 0 := by
  unfold p0UQ
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  exact_mod_cast Nat.choose_ne_zero (Nat.le_add_left g n)

/-- Exact denominator cost for a first-source summand. The valuation gain
uses the original source carry whenever the summation index is a `p`-multiple. -/
theorem p0LargePrime_UQ_div_pow (p g n s e : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hN : n + g < p ^ 2) (hs0 : 0 < s) (hs : s ≤ n) :
    p0ValAtLeast p (if p ∣ s then (p0PrimeCarry p g n : ℤ) - e else 0)
      (p0UQ 2 g (n - s) / (s : ℚ) ^ e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs0
  apply Or.inr
  rw [padicValRat.div (p0UQ_two_ne_zero _ _) (pow_ne_zero _ hsQ),
    padicValRat.pow, padicValRat.of_nat,
    p0LargePrime_UQ p g (n - s) hp hpodd (by omega)]
  by_cases hps : p ∣ s
  · rw [ite_eq_left hps]
    have hκ : p0PrimeCarry p g (n - s) = p0PrimeCarry p g n := by
      rw [← p0LargePrime_choose_carry p g (n - s) hp (by omega),
        p0LargePrime_shifted_choose_carry p g n s hp hN hs hps]
    rw [hκ]
    have hd := p0LargePrime_denominator_le_one p s hp hs0 (by omega)
    have he : 0 ≤ (e : ℤ) := by positivity
    have hdZ : (padicValNat p s : ℤ) ≤ 1 := by exact_mod_cast hd
    nlinarith
  · rw [ite_eq_right hps, padicValNat.eq_zero_of_not_dvd hps]
    simp

/-- Correction summands have the same carry gain for their outer
`p`-divisible summation index, without any formal-series assumptions. -/
theorem p0LargePrime_correction_div_pow (p g n s e : ℕ) (hp : p.Prime)
    (hN : n + g < p ^ 2) (hs0 : 0 < s) (hs : s ≤ g) :
    p0ValAtLeast p (if p ∣ s then (p0PrimeCarry p g n : ℤ) - e else 0)
      (((n + g).choose (g - s) : ℚ) / (s : ℚ) ^ e) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsQ : (s : ℚ) ≠ 0 := by exact_mod_cast Nat.ne_of_gt hs0
  have hcQ : ((n + g).choose (g - s) : ℚ) ≠ 0 := by
    exact_mod_cast Nat.choose_ne_zero (by omega : g - s ≤ n + g)
  apply Or.inr
  rw [padicValRat.div hcQ (pow_ne_zero _ hsQ),
    padicValRat.pow, padicValRat.of_nat, padicValRat.of_nat]
  by_cases hps : p ∣ s
  · rw [ite_eq_left hps, p0LargePrime_correction_choose_carry p g n s hp hN hs hps]
    have hd := p0LargePrime_denominator_le_one p s hp hs0 (by omega)
    have he : 0 ≤ (e : ℤ) := by positivity
    have hdZ : (padicValNat p s : ℤ) ≤ 1 := by exact_mod_cast hd
    nlinarith
  · rw [ite_eq_right hps, padicValNat.eq_zero_of_not_dvd hps]
    simp

/-- First-source sum bound on the exact `p0TQ` definition. -/
theorem p0LargePrime_TQ (p g n : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hN : n + g < p ^ 2) :
    p0ValAtLeast p (p0PrimeTheta p g n) (p0TQ 2 g n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold p0TQ
  apply p0ValAtLeast.add
  · apply p0ValAtLeast.sum
    intro r hr
    have hrs : r + 1 ≤ n := by simpa using Finset.mem_range.mp hr
    have hterm := p0LargePrime_UQ_div_pow p g n (r + 1) 1 hp hpodd hN
      (by omega) hrs
    simp only [pow_one, Nat.cast_add, Nat.cast_one] at hterm
    apply hterm.mono
    by_cases hpr : p ∣ r + 1
    · have hple : p ≤ r + 1 := Nat.le_of_dvd (by omega) hpr
      simp [p0PrimeTheta, show p ≤ n ∨ p ≤ g by omega, hpr]
    · simpa [hpr] using p0PrimeTheta_nonpos p g n
  · have ha : p0ValAtLeast p 0 ((2 : ℚ) ^ n) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using p0ValAtLeast.natCast p (2 ^ n)
    have hsum : p0ValAtLeast p (p0PrimeTheta p g n)
        (∑ s ∈ Finset.range g, ((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
          ((n + g).choose (g - (s + 1)) : ℚ) * p0Q 2 (s + 1)) := by
      apply p0ValAtLeast.sum
      intro s hs
      have hss : s + 1 ≤ g := by simpa using Finset.mem_range.mp hs
      have hc := p0LargePrime_correction_div_pow p g n (s + 1) 1 hp hN
        (by omega) hss
      simp only [pow_one, Nat.cast_one] at hc
      have hsval : p0ValAtLeast p 0 ((-1 : ℚ) ^ s) := by
        simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
          p0ValAtLeast.intCast p ((-1 : ℤ) ^ s)
      have hprod := (hsval.mul hc).mul (p0Q_two_valAtLeast p (s + 1))
      have heq : ((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
          ((n + g).choose (g - (s + 1)) : ℚ) * p0Q 2 (s + 1) =
          (-1 : ℚ) ^ s *
            (((n + g).choose (g - (s + 1)) : ℚ) / (s + 1 : ℚ)) *
            p0Q 2 (s + 1) := by ring
      rw [heq]
      simp only [Nat.cast_add, Nat.cast_one] at hprod
      apply hprod.mono
      by_cases hps : p ∣ s + 1
      · have hple : p ≤ s + 1 := Nat.le_of_dvd (by omega) hps
        simp [p0PrimeTheta, show p ≤ n ∨ p ≤ g by omega, hps]
      · simpa [hps] using p0PrimeTheta_nonpos p g n
    simpa only [zero_add] using ha.mul hsum

/-- Rational row/column difference denominators, with the exact residue
indicator used by the table. The sign of the difference is retained. -/
theorem p0LargePrime_difference (p i j : ℕ) (hp : p.Prime)
    (hi : i < p ^ 2) (hj : j < p ^ 2) (hne : i ≠ j) :
    padicValRat p ((j : ℚ) - (i : ℚ)) ≤
      (if i % p = j % p then 1 else 0 : ℤ) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hforward : ∀ a b : ℕ, a < b → b < p ^ 2 →
      padicValRat p ((b : ℚ) - (a : ℚ)) ≤
        (if a % p = b % p then 1 else 0 : ℤ) := by
    intro a b hab hb
    rw [← Nat.cast_sub (by omega : a ≤ b), padicValRat.of_nat]
    by_cases hmod : a % p = b % p
    · rw [ite_eq_left hmod]
      exact_mod_cast p0LargePrime_denominator_le_one p (b - a) hp
        (by omega) (by omega)
    · have hnot : ¬ p ∣ b - a := by
        intro hdiv
        have hEq : b = (b - a) + a := by omega
        apply hmod
        rw [hEq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hdiv, zero_add,
          Nat.mod_mod]
      rw [ite_eq_right hmod, padicValNat.eq_zero_of_not_dvd hnot]
      simp
  rcases lt_or_gt_of_ne hne with hlt | hlt
  · exact hforward i j hlt hj
  · have heq : (j : ℚ) - (i : ℚ) = -((i : ℚ) - (j : ℚ)) := by ring
    rw [heq, padicValRat.neg]
    simpa [eq_comm] using hforward j i hlt hi

/-- Actual off-diagonal C source bound, including equal-residue prime poles. -/
theorem p0LargePrime_CQ_offdiag (p g i j : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hi : i + g < p ^ 2) (hj : j + g < p ^ 2) (hne : i ≠ j) :
    p0ValAtLeast p
      (min (p0PrimeCarry p g i : ℤ) (p0PrimeCarry p g j : ℤ) -
        if i % p = j % p then 1 else 0) (p0CQ 2 g i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu : p0ValAtLeast p (p0PrimeCarry p g i : ℤ) (p0UQ 2 g i) :=
    Or.inr (p0LargePrime_UQ p g i hp hpodd hi).ge
  have hv : p0ValAtLeast p (p0PrimeCarry p g j : ℤ) (p0UQ 2 g j) :=
    Or.inr (p0LargePrime_UQ p g j hp hpodd hj).ge
  have hnum := (hu.mono (min_le_left _ _)).sub (hv.mono (min_le_right _ _))
  rw [p0CQ, ite_eq_right hne]
  apply (hnum.div ((j : ℚ) - (i : ℚ))).mono
  have hd := p0LargePrime_difference p i j hp (by omega) (by omega) hne
  omega

/-- Actual off-diagonal B source bound. Its first-moment input has already
been proved from the two finite sums in `p0TQ`. -/
theorem p0LargePrime_BQ_offdiag (p g i j : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hi : i + g < p ^ 2) (hj : j + g < p ^ 2) (hne : i ≠ j) :
    p0ValAtLeast p
      (min (p0PrimeTheta p g i) (p0PrimeTheta p g j) -
        if i % p = j % p then 1 else 0) (p0BQ 2 g i j) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu := p0LargePrime_TQ p g i hp hpodd hi
  have hv := p0LargePrime_TQ p g j hp hpodd hj
  have hnum := (hu.mono (min_le_left _ _)).sub (hv.mono (min_le_right _ _))
  rw [p0BQ, ite_eq_right hne]
  apply (hnum.div ((j : ℚ) - (i : ℚ))).mono
  have hd := p0LargePrime_difference p i j hp (by omega) (by omega) hne
  omega

/-- If `p>g`, a harmonic denominator divisible by `p` forces the source
binomial carry. This proves the diagonal C exception without an extra hypothesis. -/
theorem p0LargePrime_harmonic_carry (p g n s : ℕ) (_hp : p.Prime)
    (hgp : g < p) (hs0 : 0 < s) (hs : s ≤ g) (hdiv : p ∣ n + s) :
    p0PrimeCarry p g n = 1 := by
  have hdn : (n + s) % p = 0 := Nat.mod_eq_zero_of_dvd hdiv
  have hslt : s < p := by omega
  rw [Nat.add_mod, Nat.mod_eq_of_lt hslt] at hdn
  have hple : p ≤ n % p + s := by
    by_contra h
    have hlt : n % p + s < p := by omega
    rw [Nat.mod_eq_of_lt hlt] at hdn
    omega
  have hgmod : g % p = g := Nat.mod_eq_of_lt hgp
  have hk : p - g % p ≤ n % p := by rw [hgmod]; omega
  simp [p0PrimeCarry, hk]

/-- Actual C diagonal valuation, including the integral `p>g` case. -/
theorem p0LargePrime_CQ_diag (p g n : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hN : n + g < p ^ 2) :
    p0ValAtLeast p
      (if p ≤ g then (p0PrimeCarry p g n : ℤ) - 1 else 0)
      (p0CQ 2 g n n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hu0 : p0ValAtLeast p (p0PrimeCarry p g n : ℤ) (p0UQ 2 g n) :=
    Or.inr (p0LargePrime_UQ p g n hp hpodd hN).ge
  have hu := p0ValAtLeast.neg hu0
  rw [p0CQ, ite_eq_left rfl, Finset.mul_sum]
  apply p0ValAtLeast.sum
  intro s hs
  have hsle : s + 1 ≤ g := by simpa using Finset.mem_range.mp hs
  have hdpos : 0 < n + (s + 1) := by omega
  have hdlt : n + (s + 1) < p ^ 2 := by omega
  have hd := p0LargePrime_denominator_le_one p (n + (s + 1)) hp hdpos hdlt
  have hterm := hu.div ((n + (s + 1) : ℕ) : ℚ)
  simp only [Nat.cast_add, Nat.cast_one, div_eq_mul_inv] at hterm
  have heq : (n : ℚ) + (s + 1) = (n : ℚ) + s + 1 := by ring
  rw [heq] at hterm
  apply hterm.mono
  rw [show (n : ℚ) + s + 1 = ((n + (s + 1) : ℕ) : ℚ) by push_cast; ring,
    padicValRat.of_nat]
  by_cases hpg : p ≤ g
  · rw [ite_eq_left hpg]
    have hdZ : (padicValNat p (n + (s + 1)) : ℤ) ≤ 1 := by exact_mod_cast hd
    omega
  · rw [ite_eq_right hpg]
    by_cases hdiv : p ∣ n + (s + 1)
    · have hk := p0LargePrime_harmonic_carry p g n (s + 1) hp
        (by omega) (by omega) hsle hdiv
      rw [hk]
      have hdZ : (padicValNat p (n + (s + 1)) : ℤ) ≤ 1 := by exact_mod_cast hd
      omega
    · rw [padicValNat.eq_zero_of_not_dvd hdiv]
      simp

/-- Exact diagonal lower bound from the three cases of v13's source table. -/
def p0PrimeDiagBLower (p g n : ℕ) : ℤ :=
  if p ≤ n ∨ 2 * p ≤ g then (p0PrimeCarry p g n : ℤ) - 2
  else if p ≤ g then -1 else 0

theorem p0PrimeDiagBLower_nonpos (p g n : ℕ) : p0PrimeDiagBLower p g n ≤ 0 := by
  have hκ := p0PrimeCarry_le_one p g n
  unfold p0PrimeDiagBLower
  split
  · omega
  · split <;> omega

theorem p0PrimeDiagBLower_le_neg_one (p g n : ℕ) (hpg : p ≤ g) :
    p0PrimeDiagBLower p g n ≤ -1 := by
  have hκ := p0PrimeCarry_le_one p g n
  unfold p0PrimeDiagBLower
  split
  · omega
  · simp

/-- The literal double-denominator binomial in `p0BQQ`. Both divisible
indices force `2p≤g`, so the carry credit is used exactly in that branch. -/
theorem p0LargePrime_correction_double (p g n s r : ℕ) (hp : p.Prime)
    (hN : n + g < p ^ 2) (hr0 : 0 < r) (hrs : r < s) (hsg : s ≤ g) :
    p0ValAtLeast p (p0PrimeDiagBLower p g n)
      (((n + g).choose (g - s) : ℚ) / (s : ℚ) / (r : ℚ)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hs0 : 0 < s := by omega
  have hsval := p0LargePrime_denominator_le_one p s hp hs0 (by omega)
  have hrval := p0LargePrime_denominator_le_one p r hp hr0 (by omega)
  have hsZ : (padicValNat p s : ℤ) ≤ 1 := by exact_mod_cast hsval
  have hrZ : (padicValNat p r : ℤ) ≤ 1 := by exact_mod_cast hrval
  have hcs : p0ValAtLeast p 0 (((n + g).choose (g - s) : ℚ)) :=
    p0ValAtLeast.natCast _ _
  by_cases hps : p ∣ s
  · by_cases hpr : p ∣ r
    · have hprle : p ≤ r := Nat.le_of_dvd hr0 hpr
      have hds : p ∣ s - r := Nat.dvd_sub hps hpr
      have hpds : p ≤ s - r := Nat.le_of_dvd (by omega) hds
      have hp2g : 2 * p ≤ g := by omega
      have hck : p0ValAtLeast p (p0PrimeCarry p g n : ℤ)
          (((n + g).choose (g - s) : ℚ)) := by
        apply Or.inr
        rw [padicValRat.of_nat,
          p0LargePrime_correction_choose_carry p g n s hp hN hsg hps]
      apply ((hck.div (s : ℚ)).div (r : ℚ)).mono
      simp only [padicValRat.of_nat]
      rw [p0PrimeDiagBLower, ite_eq_left (Or.inr hp2g)]
      omega
    · apply ((hcs.div (s : ℚ)).div (r : ℚ)).mono
      simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hpr]
      have hple : p ≤ s := Nat.le_of_dvd hs0 hps
      have hle := p0PrimeDiagBLower_le_neg_one p g n (by omega)
      omega
  · by_cases hpr : p ∣ r
    · apply ((hcs.div (s : ℚ)).div (r : ℚ)).mono
      simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hps]
      have hple : p ≤ r := Nat.le_of_dvd hr0 hpr
      have hle := p0PrimeDiagBLower_le_neg_one p g n (by omega)
      omega
    · apply ((hcs.div (s : ℚ)).div (r : ℚ)).mono
      simp only [padicValRat.of_nat, padicValNat.eq_zero_of_not_dvd hps,
        padicValNat.eq_zero_of_not_dvd hpr]
      exact p0PrimeDiagBLower_nonpos p g n

/-- The actual diagonal second moment source bound, proved from both finite
sums; this supplies all three diagonal cases in v13 without an extra input. -/
theorem p0LargePrime_BQQ_diag (p g n : ℕ) (hp : p.Prime) (hpodd : 2 < p)
    (hN : n + g < p ^ 2) :
    p0ValAtLeast p (p0PrimeDiagBLower p g n) (p0BQQ 2 g n) := by
  haveI : Fact p.Prime := ⟨hp⟩
  unfold p0BQQ
  apply p0ValAtLeast.sub
  · apply p0ValAtLeast.sum
    intro r hr
    have hrs : r + 1 ≤ n := by simpa using Finset.mem_range.mp hr
    have hterm := p0LargePrime_UQ_div_pow p g n (r + 1) 2 hp hpodd hN
      (by omega) hrs
    simp only [Nat.cast_add, Nat.cast_one, Nat.cast_ofNat] at hterm
    apply hterm.mono
    by_cases hpr : p ∣ r + 1
    · have hple : p ≤ r + 1 := Nat.le_of_dvd (by omega) hpr
      simp [p0PrimeDiagBLower, show p ≤ n ∨ 2 * p ≤ g by omega, hpr]
    · simpa [hpr] using p0PrimeDiagBLower_nonpos p g n
  · have ha : p0ValAtLeast p 0 ((2 : ℚ) ^ n) := by
      simpa only [Nat.cast_pow, Nat.cast_ofNat] using p0ValAtLeast.natCast p (2 ^ n)
    have hsum : p0ValAtLeast p (p0PrimeDiagBLower p g n)
        (∑ s ∈ Finset.Icc 2 g,
          ((-1 : ℚ) ^ s / (s : ℚ)) * ((n + g).choose (g - s) : ℚ) *
          (∑ r ∈ Finset.range (s - 1), p0Q 2 (r + 1) / (r + 1 : ℚ))) := by
      apply p0ValAtLeast.sum
      intro s hs
      obtain ⟨hs0, hsg⟩ := Finset.mem_Icc.mp hs
      rw [Finset.mul_sum]
      apply p0ValAtLeast.sum
      intro r hr
      have hrs : r + 1 < s := by have := Finset.mem_range.mp hr; omega
      have hc := p0LargePrime_correction_double p g n s (r + 1) hp hN
        (by omega) hrs hsg
      have hsval : p0ValAtLeast p 0 ((-1 : ℚ) ^ s) := by
        simpa only [Int.cast_pow, Int.cast_neg, Int.cast_one] using
          p0ValAtLeast.intCast p ((-1 : ℤ) ^ s)
      have hprod := (hsval.mul hc).mul (p0Q_two_valAtLeast p (r + 1))
      have heq : ((-1 : ℚ) ^ s / (s : ℚ)) * ((n + g).choose (g - s) : ℚ) *
          (p0Q 2 (r + 1) / (r + 1 : ℚ)) =
        (-1 : ℚ) ^ s * (((n + g).choose (g - s) : ℚ) / (s : ℚ) /
          (r + 1 : ℚ)) * p0Q 2 (r + 1) := by ring
      rw [heq]
      simpa only [zero_add, add_zero, Nat.cast_add, Nat.cast_one] using hprod
    simpa only [zero_add] using ha.mul hsum

/-- The signed coefficient lower bound for the literal specialized pencil,
with the source's diagonal conventions. -/
def p0PrimeEntryLower (p g i j : ℕ) (lower : Bool) : ℤ :=
  if lower then
    if i = j then p0PrimeDiagBLower p g i
    else min (p0PrimeTheta p g i) (p0PrimeTheta p g j) -
      if i % p = j % p then 1 else 0
  else
    if i = j then (if p ≤ g then (p0PrimeCarry p g i : ℤ) - 1 else 0)
    else min (p0PrimeCarry p g i : ℤ) (p0PrimeCarry p g j : ℤ) -
      if i % p = j % p then 1 else 0

theorem p0PrimeEntryLower_lower_nonpos (p g i j : ℕ) :
    p0PrimeEntryLower p g i j true ≤ 0 := by
  simp only [p0PrimeEntryLower, ite_true]
  split
  · exact p0PrimeDiagBLower_nonpos p g i
  · have hθ := p0PrimeTheta_nonpos p g i
    have hmin := min_le_left (p0PrimeTheta p g i) (p0PrimeTheta p g j)
    split <;> omega

/-- The exact A source entry is integral at every prime. -/
theorem p0AQ_two_valAtLeast (p g i j : ℕ) : p0ValAtLeast p 0 (p0AQ 2 g i j) := by
  by_cases hij : i = j
  · rw [p0AQ, ite_eq_left hij, p0UQ]
    simpa only [Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat] using
      p0ValAtLeast.natCast p (2 ^ i * (i + g).choose g)
  · rw [p0AQ, ite_eq_right hij]
    exact p0ValAtLeast.zero _ _

/-- Every coefficient of the actual top or lower pencil entry has the
source lower valuation, including the diagonal `-T A` term. -/
theorem p0LargePrime_pencil_coeff (p g i j k : ℕ) (lower : Bool)
    (hp : p.Prime) (hpodd : 2 < p)
    (hi : i + g < p ^ 2) (hj : j + g < p ^ 2) :
    p0ValAtLeast p (p0PrimeEntryLower p g i j lower)
      ((if lower then Polynomial.C (p0BQ 2 g i j) -
          Polynomial.X * Polynomial.C (p0AQ 2 g i j)
        else Polynomial.C (p0CQ 2 g i j) : Polynomial ℚ).coeff k) := by
  haveI : Fact p.Prime := ⟨hp⟩
  cases lower with
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    have hc : p0ValAtLeast p (p0PrimeEntryLower p g i j false) (p0CQ 2 g i j) := by
      by_cases hij : i = j
      · subst j
        simpa only [p0PrimeEntryLower, Bool.false_eq_true, ite_false,
          ite_true] using p0LargePrime_CQ_diag p g i hp hpodd hi
      · simpa only [p0PrimeEntryLower, Bool.false_eq_true, ite_false,
          ite_eq_right hij] using p0LargePrime_CQ_offdiag p g i j hp hpodd hi hj hij
    by_cases hk : k = 0
    · subst k
      simpa using hc
    · simp [Polynomial.coeff_C, hk]
  | true =>
    simp only [ite_true]
    have hb : p0ValAtLeast p (p0PrimeEntryLower p g i j true) (p0BQ 2 g i j) := by
      by_cases hij : i = j
      · subst j
        simpa only [p0PrimeEntryLower, ite_true, p0BQ] using
          p0LargePrime_BQQ_diag p g i hp hpodd hi
      · simpa only [p0PrimeEntryLower, ite_true, ite_eq_right hij] using
          p0LargePrime_BQ_offdiag p g i j hp hpodd hi hj hij
    cases k with
    | zero => simpa using hb
    | succ k =>
      by_cases hk : k = 0
      · subst k
        have ha := p0ValAtLeast.neg (p0AQ_two_valAtLeast p g i j)
        have ha' := ha.mono (p0PrimeEntryLower_lower_nonpos p g i j)
        simpa using ha'
      · simp [Polynomial.coeff_C, hk]

/-- Actual P0 row index, named solely to make the source matrix bridge readable. -/
def p0SourceRowIndex (m : ℕ) (r : Fin (2 * m)) : ℕ :=
  m / 4 + if r.val < m then r.val else r.val - m

/-- Uniform coefficient bridge to the source-locked actual `a=2` matrix.
The sole size input is the paper's `p² > U+g`; the carry and denominator
claims above are proved rather than supplied as certificate fields. -/
theorem p0LargePrime_matrix_coeff (p m k : ℕ) (r c : Fin (2 * m))
    (hp : p.Prime) (hpodd : 2 < p)
    (hlarge : 2 * m - 1 + m / 2 < p ^ 2) :
    p0ValAtLeast p
      (p0PrimeEntryLower p (m / 2) (p0SourceRowIndex m r) c.val
        (decide (¬ r.val < m)))
      ((p0MatrixQ 2 m r c).coeff k) := by
  have hi : p0SourceRowIndex m r ≤ 2 * m - 1 := by
    have hr := r.isLt
    have hmdiv := Nat.div_le_self m 4
    unfold p0SourceRowIndex
    split <;> omega
  have hj : c.val ≤ 2 * m - 1 := by have := c.isLt; omega
  have hvi : p0SourceRowIndex m r + m / 2 < p ^ 2 := by omega
  have hvj : c.val + m / 2 < p ^ 2 := by omega
  have h := p0LargePrime_pencil_coeff p (m / 2) (p0SourceRowIndex m r) c.val k
    (decide (¬ r.val < m)) hp hpodd hvi hvj
  by_cases hr : r.val < m
  · simpa [p0MatrixQ, p0SourceRowIndex, hr] using h
  · simpa [p0MatrixQ, p0SourceRowIndex, hr] using h

/-- Integer equations for all twelve large-ratio table walls. They include
both endpoints; using equations avoids division at `m=0`. -/
def p0HighRatioWall (m p : ℕ) : Prop :=
  m = 2 * p ∨ 7 * m = 12 * p ∨ 5 * m = 8 * p ∨
    2 * m = 3 * p ∨ 3 * m = 4 * p ∨ 5 * m = 6 * p ∨
    7 * m = 8 * p ∨ m = p ∨ 5 * m = 4 * p ∨
    7 * m = 4 * p ∨ 2 * m = p ∨ 5 * m = 2 * p

private theorem p0PrimeRatioWall_small (a b m p : ℕ)
    (ha : a.Prime) (hp : p.Prime) (hab : ¬a ∣ b)
    (hbe : b ≤ 12) (heq : a * m = b * p) : m ≤ 12 := by
  have hadiv : a ∣ b * p := by rw [← heq]; exact dvd_mul_right a m
  have hap : a ∣ p := (ha.dvd_mul.mp hadiv).resolve_left hab
  have hae : a = p := (Nat.prime_dvd_prime_iff_eq ha hp).mp hap
  subst a
  have heq' : p * m = p * b := by simpa only [Nat.mul_comm b p] using heq
  have hmb : m = b := by
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · have hmul := Nat.mul_lt_mul_of_pos_left h hp.pos
      omega
    · have hmul := Nat.mul_lt_mul_of_pos_left h hp.pos
      omega
  omega

/-- At positive multiples of four beyond `m=12`, an odd prime cannot lie
on a high-profile wall. Thus the large-ratio wall cost has finite support
along the actual paper subsequence. -/
theorem p0HighRatioWall_impossible (m p : ℕ) (hp : p.Prime) (_hpodd : 2 < p)
    (h4 : 4 ∣ m) (hm : 16 ≤ m) : ¬ p0HighRatioWall m p := by
  intro hw
  rcases hw with h | h | h | h | h | h | h | h | h | h | h | h
  · obtain ⟨t, ht⟩ := h4
    have hpEq : p = 2 * t := by omega
    have hd : 2 ∣ p := ⟨t, hpEq⟩
    have he : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  · have := p0PrimeRatioWall_small 7 12 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 5 8 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 2 3 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 3 4 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 5 6 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 7 8 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · obtain ⟨t, ht⟩ := h4
    have hd : 2 ∣ p := ⟨2 * t, by omega⟩
    have he : 2 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp hd
    omega
  · have := p0PrimeRatioWall_small 5 4 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 7 4 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega
  · have := p0PrimeRatioWall_small 2 1 m p (by norm_num) hp (by norm_num)
      (by omega) (by simpa using h)
    omega
  · have := p0PrimeRatioWall_small 5 2 m p (by norm_num) hp (by norm_num)
      (by omega) h
    omega

/-- Above all source upper indices the entry profile is identically zero;
this is the finite-support clause of the actual prime product. -/
theorem p0PrimeEntryLower_eq_zero_of_small (p g i j : ℕ) (lower : Bool)
    (hi : i + g < p) (hj : j + g < p) :
    p0PrimeEntryLower p g i j lower = 0 := by
  have hip : i < p := by omega
  have hjp : j < p := by omega
  have hgp : g < p := by omega
  have hiκ : p0PrimeCarry p g i = 0 := by
    simp only [p0PrimeCarry, Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hgp]
    rw [ite_eq_right (by omega)]
  have hjκ : p0PrimeCarry p g j = 0 := by
    simp only [p0PrimeCarry, Nat.mod_eq_of_lt hjp, Nat.mod_eq_of_lt hgp]
    rw [ite_eq_right (by omega)]
  have hiθ : p0PrimeTheta p g i = 0 := by simp [p0PrimeTheta, not_le.mpr hip, not_le.mpr hgp]
  have hjθ : p0PrimeTheta p g j = 0 := by simp [p0PrimeTheta, not_le.mpr hjp, not_le.mpr hgp]
  have hdiag : p0PrimeDiagBLower p g i = 0 := by
    simp [p0PrimeDiagBLower, show ¬ (p ≤ i ∨ 2 * p ≤ g) by omega, not_le.mpr hgp]
  have hdiagj : p0PrimeDiagBLower p g j = 0 := by
    simp [p0PrimeDiagBLower, show ¬ (p ≤ j ∨ 2 * p ≤ g) by omega, not_le.mpr hgp]
  cases lower <;> by_cases hij : i = j <;>
    simp [p0PrimeEntryLower, hij, hiκ, hjκ, hiθ, hjθ, hdiag, hdiagj,
      not_le.mpr hgp, Nat.mod_eq_of_lt hip, Nat.mod_eq_of_lt hjp]

/-- Literal P0 entries have prime-integral coefficients outside the finite
source support. No declared profile or denominator conclusion is an input. -/
theorem p0LargePrime_matrix_coeff_integral (p m k : ℕ) (r c : Fin (2 * m))
    (hp : p.Prime) (hpodd : 2 < p)
    (hlarge : 2 * m - 1 + m / 2 < p) :
    p0ValAtLeast p 0 ((p0MatrixQ 2 m r c).coeff k) := by
  have hlarge2 : 2 * m - 1 + m / 2 < p ^ 2 := by nlinarith [hp.pos]
  have h := p0LargePrime_matrix_coeff p m k r c hp hpodd hlarge2
  have hi : p0SourceRowIndex m r ≤ 2 * m - 1 := by
    have hr := r.isLt
    have hmdiv := Nat.div_le_self m 4
    unfold p0SourceRowIndex
    split <;> omega
  have hj : c.val ≤ 2 * m - 1 := by have := c.isLt; omega
  rw [p0PrimeEntryLower_eq_zero_of_small _ _ _ _ _ (by omega) (by omega)] at h
  exact h

end
end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0LargePrime_factorial
#print axioms Li2Lean.P0.Integerization.p0LargePrime_choose_carry
#print axioms Li2Lean.P0.Integerization.p0LargePrime_choose_floor
#print axioms Li2Lean.P0.Integerization.p0LargePrime_shifted_choose_carry
#print axioms Li2Lean.P0.Integerization.p0LargePrime_denominator_le_one

#print axioms Li2Lean.P0.Integerization.p0LargePrime_UQ
#print axioms Li2Lean.P0.Integerization.p0LargePrime_TQ

#print axioms Li2Lean.P0.Integerization.p0LargePrime_CQ_offdiag
#print axioms Li2Lean.P0.Integerization.p0LargePrime_BQ_offdiag
#print axioms Li2Lean.P0.Integerization.p0LargePrime_CQ_diag

#print axioms Li2Lean.P0.Integerization.p0LargePrime_BQQ_diag

#print axioms Li2Lean.P0.Integerization.p0LargePrime_pencil_coeff
#print axioms Li2Lean.P0.Integerization.p0LargePrime_matrix_coeff

#print axioms Li2Lean.P0.Integerization.p0HighRatioWall_impossible

#print axioms Li2Lean.P0.Integerization.p0LargePrime_matrix_coeff_integral
