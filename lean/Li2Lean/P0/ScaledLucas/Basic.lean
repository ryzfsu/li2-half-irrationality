/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.NonvanishingTowerProducer
import Li2Lean.P0.SeedTransport

/-!
# Entrywise Lucas transport for the scaled `a = 2` P0 pencil: basic layer

Good83 cast algebra, valuation of the scaled denominators, block sums,
Lucas/Frobenius reductions, and the reduced first moment `q T_i`.  Together
with `ScaledLucas/Entries.lean` and `NonvanishingScaledLucas.lean` this proves
`p0A2ScaledMatrixLucasObligation` for every `k > 0` and every rational
argument with `r.den < 83^k`.  The proof follows `eq:nv-lucas` and `eq:nv-pencil` of
`sec-nonvanishing.tex` (paper v10) over the full row and column ranges:

* every row index `R < 64 q` and column index `C < 64 q` (with `q = 83^k`) is
  written as `a q + v`, `b q + w` with `a, b < 64`, `v, w < q`;
* the C rows use `i = (8 + a) q + v < 40 q`, the B rows (lower bank, `R ≥ 32 q`)
  use `i = (8 + (a - 32)) q + v < 40 q`, and the columns run up to `64 q`;
* the scaled entries `q C_ij` and `q² B_ij` lie in `Good83` (integrality before
  reduction), and only the denominators that are exact multiples `c q` with
  `0 < c < 83` survive reduction modulo `83`; all other denominators carry a
  positive power of `83` in the numerator;
* the inner sums with `S = 1` are empty and contribute zero, and the shifted
  diagonal sum `∑_s q/(i+s+1)` keeps exactly one term per block of length `q`;
* signed divided differences use the integer `b - a ≠ 0` with `|b - a| < 83`.

The literal seed entries are recovered as the case `k = 0` of the same entry
formulas, so no separate seed computation is needed.
-/

namespace Li2Lean.P0
namespace ScaledLucas

noncomputable section

open ControlledResidue
open Finset

local instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

set_option hygiene false in
/-- `omega` after abstracting the block length `83 ^ k` to an atom. -/
local macro "qomega" : tactic => `(tactic| (generalize 83 ^ k = q at *; omega))

/-! ## Good83 cast algebra -/

theorem den_ne {x : ℚ} (hx : x ∈ Good83) : ((x.den : ℕ) : F83) ≠ 0 :=
  natCast_ne_zero_of_coprime hx

theorem cast_add' {x y : ℚ} (hx : x ∈ Good83) (hy : y ∈ Good83) :
    ((x + y : ℚ) : F83) = (x : F83) + (y : F83) :=
  Rat.cast_add_of_ne_zero (den_ne hx) (den_ne hy)

theorem cast_sub' {x y : ℚ} (hx : x ∈ Good83) (hy : y ∈ Good83) :
    ((x - y : ℚ) : F83) = (x : F83) - (y : F83) :=
  Rat.cast_sub_of_ne_zero (den_ne hx) (den_ne hy)

theorem cast_mul' {x y : ℚ} (hx : x ∈ Good83) (hy : y ∈ Good83) :
    ((x * y : ℚ) : F83) = (x : F83) * (y : F83) :=
  Rat.cast_mul_of_ne_zero (den_ne hx) (den_ne hy)

theorem cast_sum' {ι : Type*} (s : Finset ι) (f : ι → ℚ)
    (hf : ∀ i ∈ s, f i ∈ Good83) :
    ((∑ i ∈ s, f i : ℚ) : F83) = ∑ i ∈ s, (f i : F83) := by
  classical
  let g : ι → Good83 := fun i => if h : f i ∈ Good83 then ⟨f i, h⟩ else 0
  have hsum : (∑ i ∈ s, f i) = ((∑ i ∈ s, g i : Good83) : ℚ) := by
    rw [show ((∑ i ∈ s, g i : Good83) : ℚ) = Good83.subtype (∑ i ∈ s, g i)
      from rfl, map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    simp [g, hf i hi]
  rw [hsum]
  change residueHom (∑ i ∈ s, g i) = _
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [g, hf i hi, ↓reduceDIte]
  rfl

theorem mem_nat (n : ℕ) : (n : ℚ) ∈ Good83 := by
  change Nat.Coprime ((n : ℚ).den) 83
  simp

theorem mem_int (z : ℤ) : (z : ℚ) ∈ Good83 := by
  change Nat.Coprime ((z : ℚ).den) 83
  simp

theorem mem_ofNat (n : ℕ) [n.AtLeastTwo] : (OfNat.ofNat n : ℚ) ∈ Good83 := by
  have h := mem_nat n
  simpa using h

theorem coprime_of_pos_lt {n : ℕ} (h0 : 0 < n) (h : n < 83) :
    Nat.Coprime n 83 :=
  (Nat.coprime_of_lt_prime (Nat.ne_of_gt h0) h (by norm_num)).symm

theorem mem_inv_nat {n : ℕ} (hn : Nat.Coprime n 83) :
    ((n : ℚ)⁻¹) ∈ Good83 := by
  change Nat.Coprime (((n : ℚ)⁻¹).den) 83
  rw [Rat.inv_natCast_den]
  split_ifs
  · simp
  · exact hn

theorem mem_inv_int {z : ℤ} (h : z.natAbs < 83) :
    ((z : ℚ)⁻¹) ∈ Good83 := by
  change Nat.Coprime (((z : ℚ)⁻¹).den) 83
  rw [Rat.inv_intCast_den]
  split_ifs with hz
  · simp
  · exact coprime_of_pos_lt (Int.natAbs_pos.mpr hz) h

theorem cast_inv_nat {n : ℕ} (hn : Nat.Coprime n 83) :
    (((n : ℚ)⁻¹ : ℚ) : F83) = ((n : F83))⁻¹ := by
  have hn0 : n ≠ 0 := by
    rintro rfl
    norm_num at hn
  have hnQ : (n : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have h1 : ((n : ℚ)⁻¹ * (n : ℚ) : ℚ) = 1 := inv_mul_cancel₀ hnQ
  have h2 := congrArg (fun x : ℚ => (x : F83)) h1
  rw [cast_mul' (mem_inv_nat hn) (mem_nat n), Rat.cast_natCast,
    Rat.cast_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem intCast_ne_zero_of_small {z : ℤ} (h0 : z ≠ 0) (h : z.natAbs < 83) :
    (z : F83) ≠ 0 := by
  intro hz
  have hdvd : (83 : ℤ) ∣ z := (ZMod.intCast_zmod_eq_zero_iff_dvd z 83).mp hz
  have hdvd' : (83 : ℕ) ∣ z.natAbs := by
    have := Int.natAbs_dvd_natAbs.mpr hdvd
    simpa using this
  have hle := Nat.le_of_dvd (Int.natAbs_pos.mpr h0) hdvd'
  omega

theorem cast_inv_int {z : ℤ} (h0 : z ≠ 0) (h : z.natAbs < 83) :
    (((z : ℚ)⁻¹ : ℚ) : F83) = ((z : F83))⁻¹ := by
  have hzQ : (z : ℚ) ≠ 0 := Int.cast_ne_zero.mpr h0
  have h1 : ((z : ℚ)⁻¹ * (z : ℚ) : ℚ) = 1 := inv_mul_cancel₀ hzQ
  have h2 := congrArg (fun x : ℚ => (x : F83)) h1
  rw [cast_mul' (mem_inv_int h) (mem_int z), Rat.cast_intCast,
    Rat.cast_one] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem cast_mul5 {a b c d e : ℚ} (ha : a ∈ Good83) (hb : b ∈ Good83)
    (hc : c ∈ Good83) (hd : d ∈ Good83) (he : e ∈ Good83) :
    ((a * b * c * d * e : ℚ) : F83) =
      (a : F83) * (b : F83) * (c : F83) * (d : F83) * (e : F83) := by
  have hab := Good83.mul_mem ha hb
  have habc := Good83.mul_mem hab hc
  have habcd := Good83.mul_mem habc hd
  rw [cast_mul' habcd he, cast_mul' habc hd, cast_mul' hab hc, cast_mul' ha hb]

theorem mem_two_pow (n : ℕ) : ((2 : ℚ) ^ n) ∈ Good83 := by
  have h := mem_nat (2 ^ n)
  simpa using h

theorem cast_two_pow (n : ℕ) : (((2 : ℚ) ^ n : ℚ) : F83) = (2 : F83) ^ n := by
  rw [show ((2 : ℚ) ^ n) = ((2 ^ n : ℕ) : ℚ) by push_cast; ring,
    Rat.cast_natCast]
  push_cast
  ring

theorem mem_neg_one_pow (n : ℕ) : ((-1 : ℚ) ^ n) ∈ Good83 := by
  have h := mem_int ((-1) ^ n)
  simpa using h

theorem cast_neg_one_pow (n : ℕ) :
    (((-1 : ℚ) ^ n : ℚ) : F83) = (-1 : F83) ^ n := by
  rw [show ((-1 : ℚ) ^ n) = (((-1) ^ n : ℤ) : ℚ) by push_cast; ring,
    Rat.cast_intCast]
  push_cast
  ring

/-! ## Valuation of the scaled denominators -/

theorem qRat_eq (k : ℕ) : qRat k = ((83 ^ k : ℕ) : ℚ) := rfl

theorem qdiv_mem (k n : ℕ) (h0 : 0 < n) (hlt : n < 83 * 83 ^ k) :
    qRat k / (n : ℚ) ∈ Good83 :=
  pow83_div_den_coprime k n h0 hlt

/-- A denominator `c q` with `0 < c < 83` reduces to the unit `c⁻¹`. -/
theorem qdiv_cast_unit (k c : ℕ) (h0 : 0 < c) (hc : c < 83) :
    ((qRat k / ((c * 83 ^ k : ℕ) : ℚ) : ℚ) : F83) = ((c : F83))⁻¹ := by
  have hq : ((83 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  have hcQ : (c : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt h0)
  have hrat : qRat k / ((c * 83 ^ k : ℕ) : ℚ) = ((c : ℚ))⁻¹ := by
    rw [qRat_eq]
    push_cast
    field_simp
  rw [hrat, cast_inv_nat (coprime_of_pos_lt h0 hc)]

/-- A denominator not divisible by `q = 83^k` leaves a factor `83` in the
numerator of `q / n`; its reduction is zero. -/
theorem qdiv_cast_zero (k n : ℕ) (h0 : 0 < n) (hnd : ¬ 83 ^ k ∣ n) :
    ((qRat k / (n : ℚ) : ℚ) : F83) = 0 := by
  obtain ⟨e, n', hn', rfl⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (Nat.pos_iff_ne_zero.mp h0) 83
      (by norm_num)
  have hek : e < k := by
    by_contra hle
    push_neg at hle
    apply hnd
    exact Dvd.dvd.mul_right (Nat.pow_dvd_pow 83 hle) n'
  have hn'0 : n' ≠ 0 := by
    rintro rfl
    simp at h0
  have hcop : Nat.Coprime n' 83 :=
    Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd (by norm_num)).2 hn')
  obtain ⟨d, rfl⟩ : ∃ d, k = e + d + 1 := ⟨k - e - 1, by omega⟩
  have hy : ((83 ^ d : ℕ) : ℚ) * ((n' : ℚ))⁻¹ ∈ Good83 :=
    Good83.mul_mem (mem_nat _) (mem_inv_nat hcop)
  have hn'Q : (n' : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr hn'0
  have heq : qRat (e + d + 1) / ((83 ^ e * n' : ℕ) : ℚ) =
      (83 : ℚ) * (((83 ^ d : ℕ) : ℚ) * ((n' : ℚ))⁻¹) := by
    rw [qRat_eq]
    push_cast
    field_simp
    ring
  rw [heq, cast_mul' (mem_ofNat 83) hy]
  have h83 : (((83 : ℚ) : ℚ) : F83) = 0 := by
    rw [show ((83 : ℚ)) = ((83 : ℕ) : ℚ) by norm_num, Rat.cast_natCast]
    exact ZMod.natCast_self 83
  rw [h83, zero_mul]

theorem not_dvd_of_rem {q n m x : ℕ} (hn : n = m * q + x) (hx0 : 0 < x)
    (hxq : x < q) : ¬ q ∣ n := by
  intro hdvd
  have hx : q ∣ x := by
    have h' : q ∣ m * q + x := hn ▸ hdvd
    exact (Nat.dvd_add_right (Dvd.intro_left m rfl)).mp h'
  have := Nat.le_of_dvd hx0 hx
  omega

theorem mod_of_decomp {q a v : ℕ} (hv : v < q) : (a * q + v) % q = v := by
  rw [Nat.add_comm, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt hv]

theorem qdiff_cast_zero (k i j : ℕ) (hij : i ≠ j)
    (hmod : i % 83 ^ k ≠ j % 83 ^ k) :
    ((qRat k / ((j : ℚ) - (i : ℚ)) : ℚ) : F83) = 0 := by
  rcases Nat.lt_or_gt_of_ne hij with hlt | hlt
  · have hcast : ((j : ℚ) - (i : ℚ)) = ((j - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
    rw [hcast]
    apply qdiv_cast_zero k (j - i) (Nat.sub_pos_of_lt hlt)
    intro hdvd
    apply hmod
    exact (Nat.modEq_iff_dvd' hlt.le).mpr hdvd
  · have hcast : ((j : ℚ) - (i : ℚ)) = -((i - j : ℕ) : ℚ) := by
      rw [Nat.cast_sub hlt.le]
      ring
    rw [hcast, div_neg, Rat.cast_neg]
    rw [qdiv_cast_zero k (i - j) (Nat.sub_pos_of_lt hlt)]
    · simp
    intro hdvd
    apply hmod
    exact ((Nat.modEq_iff_dvd' hlt.le).mpr hdvd).symm

theorem qdiff_eq_unit (k A b v : ℕ) (hAb : A ≠ b) :
    qRat k / (((b * 83 ^ k + v : ℕ) : ℚ) - ((A * 83 ^ k + v : ℕ) : ℚ)) =
      ((((b : ℤ) - (A : ℤ) : ℤ) : ℚ))⁻¹ := by
  have hba : ((b : ℚ) - (A : ℚ)) ≠ 0 := by
    intro h
    apply hAb
    have : (b : ℚ) = (A : ℚ) := by linarith
    exact_mod_cast this.symm
  have hq : ((83 : ℚ) ^ k) ≠ 0 := pow_ne_zero _ (by norm_num)
  rw [qRat_eq]
  push_cast
  rw [show (b : ℚ) * 83 ^ k + v - (A * 83 ^ k + v) = (b - A) * 83 ^ k by ring]
  field_simp

theorem small_diff {A b : ℕ} (hA : A < 64) (hb : b < 64) :
    ((b : ℤ) - (A : ℤ)).natAbs < 83 := by
  omega

/-! ## Finite block sums -/

theorem block_sum_full {M' : Type*} [AddCommMonoid M'] (q t0 : ℕ)
    (f : ℕ → M') (ht0 : t0 < q) :
    ∀ M : ℕ, (∀ c < M, ∀ t < q, t ≠ t0 → f (c * q + t) = 0) →
      ∑ r ∈ range (M * q), f r = ∑ c ∈ range M, f (c * q + t0) := by
  intro M
  induction M with
  | zero => intro _; simp
  | succ M ih =>
      intro hblock
      rw [show (M + 1) * q = M * q + q by ring, Finset.sum_range_add,
        Finset.sum_range_succ,
        ih (fun c hc t ht htt => hblock c (by omega) t ht htt)]
      congr 1
      rw [Finset.sum_eq_single_of_mem t0 (Finset.mem_range.mpr ht0)]
      intro t ht htt
      exact hblock M (by omega) t (Finset.mem_range.mp ht) htt

theorem block_sum {M' : Type*} [AddCommMonoid M'] (q M v t0 : ℕ)
    (f : ℕ → M') (ht0 : t0 < q)
    (hblock : ∀ c < M, ∀ t < q, t ≠ t0 → f (c * q + t) = 0)
    (htail : ∀ t < v, f (M * q + t) = 0) :
    ∑ r ∈ range (M * q + v), f r = ∑ c ∈ range M, f (c * q + t0) := by
  rw [Finset.sum_range_add,
    Finset.sum_eq_zero (s := range v)
      (fun t ht => htail t (Finset.mem_range.mp ht)), add_zero]
  exact block_sum_full q t0 f ht0 M hblock

/-! ## Lucas and Frobenius reductions -/

theorem choose_pow_add_modEq {p A b k v : ℕ} [Fact p.Prime] (hv : v < p ^ k) :
    Nat.choose (A * p ^ k + v) (b * p ^ k) ≡ Nat.choose A b [MOD p] := by
  induction k generalizing A b v with
  | zero =>
      have hv1 : v < 1 := by simpa using hv
      have hv0 : v = 0 := by omega
      subst v
      simpa using (Nat.ModEq.refl (Nat.choose A b))
  | succ k ih =>
      have hpP : Nat.Prime p := Fact.out
      have hp : 0 < p := hpP.pos
      have hnmod : (A * p ^ k.succ + v) % p = v % p := by
        simp [pow_succ, Nat.add_mod, Nat.mul_mod]
      have hkmod : (b * p ^ k.succ) % p = 0 := by
        simp [pow_succ, Nat.mul_mod]
      have hndiv : (A * p ^ k.succ + v) / p = A * p ^ k + v / p := by
        calc
          (A * p ^ k.succ + v) / p = (v + p * (A * p ^ k)) / p := by
            rw [pow_succ]
            congr 1
            ring
          _ = v / p + A * p ^ k := Nat.add_mul_div_left v (A * p ^ k) hp
          _ = A * p ^ k + v / p := Nat.add_comm _ _
      have hkdiv : (b * p ^ k.succ) / p = b * p ^ k := by
        calc
          (b * p ^ k.succ) / p = (p * (b * p ^ k)) / p := by
            rw [pow_succ]
            congr 1
            ring
          _ = b * p ^ k := Nat.mul_div_right (b * p ^ k) hp
      have hvdiv : v / p < p ^ k := (Nat.div_lt_iff_lt_mul hp).2 (by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hv)
      have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := A * p ^ k.succ + v) (k := b * p ^ k.succ) (p := p)
      have hLucas' : Nat.choose (A * p ^ k.succ + v) (b * p ^ k.succ) ≡
          Nat.choose ((A * p ^ k.succ + v) / p)
            ((b * p ^ k.succ) / p) [MOD p] := by
        rw [hnmod, hkmod] at hLucas
        simpa using hLucas
      rw [hndiv, hkdiv] at hLucas'
      exact hLucas'.trans (ih hvdiv)

theorem cast_choose_lucas (k A b v : ℕ) (hv : v < 83 ^ k) :
    ((Nat.choose (A * 83 ^ k + v) (b * 83 ^ k) : ℕ) : F83) =
      ((Nat.choose A b : ℕ) : F83) :=
  (ZMod.natCast_eq_natCast_iff _ _ 83).mpr (choose_pow_add_modEq hv)

theorem two_pow_frob (k c : ℕ) :
    (2 : F83) ^ (c * 83 ^ k) = (2 : F83) ^ c := by
  rw [Nat.mul_comm, pow_mul, ZMod.pow_card_pow]

/-- The seed value of `U_A` reduced at `83`. -/
def YU (A : ℕ) : F83 := ((2 ^ A * Nat.choose (A + 16) 16 : ℕ) : F83)

theorem cast_U (k A v : ℕ) (hv : v < 83 ^ k) :
    ((p0UQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v) : ℚ) : F83) =
      (2 : F83) ^ v * YU A := by
  have hnat : p0UQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v) =
      ((2 ^ (A * 83 ^ k + v) *
        Nat.choose (A * 83 ^ k + v + 16 * 83 ^ k) (16 * 83 ^ k) : ℕ) : ℚ) := by
    simp [p0UQ]
  rw [hnat, Rat.cast_natCast]
  have hmod := Li2Lean.p0A2_U_lucas (k := k) (a := A) (h := 16) (v := v) hv
  have hz := (ZMod.natCast_eq_natCast_iff _ _ 83).mpr hmod
  rw [hz, YU, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]

theorem mem_U (g i : ℕ) : p0UQ (2 : ℚ) g i ∈ Good83 := p0U_good_general g i

theorem p0Q_two_eq (n : ℕ) : p0Q (2 : ℚ) n = ((2 ^ n - 1 : ℤ) : ℚ) := by
  simp [p0Q]
  norm_num

theorem mem_Q (n : ℕ) : p0Q (2 : ℚ) n ∈ Good83 := by
  rw [p0Q_two_eq]
  exact mem_int _

theorem cast_Q (n : ℕ) :
    ((p0Q (2 : ℚ) n : ℚ) : F83) = (2 : F83) ^ n - 1 := by
  rw [p0Q_two_eq, Rat.cast_intCast]
  push_cast
  ring

theorem cast_Q_scaled (k c : ℕ) :
    ((p0Q (2 : ℚ) (c * 83 ^ k) : ℚ) : F83) = (2 : F83) ^ c - 1 := by
  rw [cast_Q, two_pow_frob]

theorem q_odd (k : ℕ) : Odd (83 ^ k) := Odd.pow (by decide)

theorem neg_one_pow_frob (k c : ℕ) :
    (-1 : F83) ^ (c * 83 ^ k) = (-1 : F83) ^ c := by
  rw [Nat.mul_comm, pow_mul, Odd.neg_one_pow (q_odd k)]

/-! ## Index arithmetic over a block length `q` -/

theorem ar_last (c q : ℕ) (hq : 0 < q) : c * q + (q - 1) + 1 = (c + 1) * q := by
  have h : (c + 1) * q = c * q + q := by ring
  omega

theorem ar_shift (A c q v : ℕ) (hc : c < A) (hq : 0 < q) :
    A * q + v - (c * q + (q - 1) + 1) = (A - (c + 1)) * q + v := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_lt hc
  have h1 : (c + d + 1) * q = c * q + q + d * q := by ring
  rw [h1, show c + d + 1 - (c + 1) = d by omega]
  omega

theorem ar_lt (c t q N : ℕ) (hc : c < N) (ht : t < q) : c * q + t < N * q := by
  have h1 : (c + 1) * q ≤ N * q := Nat.mul_le_mul_right _ hc
  have h2 : (c + 1) * q = c * q + q := by ring
  omega

theorem ar_lt83 (n q N : ℕ) (hn : n < N * q) (hN : N ≤ 83) : n < 83 * q := by
  have : N * q ≤ 83 * q := Nat.mul_le_mul_right _ hN
  omega

theorem even_q_sub_one (k : ℕ) : Even (83 ^ k - 1) :=
  Nat.Odd.sub_odd (q_odd k) odd_one

/-! ## The first moment `q T_i` -/

/-- One summand of the second part of `T_i`, without the denominator. -/
def T2 (g i s : ℕ) : ℚ :=
  (2 : ℚ) ^ i * (-1 : ℚ) ^ s * (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
    p0Q (2 : ℚ) (s + 1)

theorem mem_T2 (g i s : ℕ) : T2 g i s ∈ Good83 :=
  Good83.mul_mem (Good83.mul_mem (Good83.mul_mem (mem_two_pow i)
    (mem_neg_one_pow s)) (mem_nat _)) (mem_Q _)

theorem qT_decomp (k g i : ℕ) :
    qRat k * p0TQ (2 : ℚ) g i =
      (∑ r ∈ range i,
        p0UQ (2 : ℚ) g (i - (r + 1)) * (qRat k / ((r + 1 : ℕ) : ℚ))) +
      ∑ s ∈ range g, T2 g i s * (qRat k / ((s + 1 : ℕ) : ℚ)) := by
  unfold p0TQ
  rw [mul_add]
  congr 1
  · rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro r hr
    push_cast
    ring
  · rw [← mul_assoc, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro s hs
    simp only [T2]
    push_cast
    ring

/-- The reduced seed value of `T_A`. -/
def YT (A : ℕ) : F83 :=
  (∑ c ∈ range A, YU (A - (c + 1)) * (((c + 1 : ℕ) : F83))⁻¹) +
    (2 : F83) ^ A * ∑ c ∈ range 16,
      (-1 : F83) ^ c * ((Nat.choose (A + 16) (16 - (c + 1)) : ℕ) : F83) *
        ((2 : F83) ^ (c + 1) - 1) * (((c + 1 : ℕ) : F83))⁻¹

theorem cast_two_pow_frob (k A v : ℕ) :
    (((2 : ℚ) ^ (A * 83 ^ k + v) : ℚ) : F83) = (2 : F83) ^ v * (2 : F83) ^ A := by
  rw [cast_two_pow, pow_add, two_pow_frob]
  ring

theorem cast_T2_block (k A v c : ℕ) (hv : v < 83 ^ k) (hc : c < 16) :
    ((T2 (16 * 83 ^ k) (A * 83 ^ k + v) (c * 83 ^ k + (83 ^ k - 1)) : ℚ) : F83) =
      (2 : F83) ^ v * ((2 : F83) ^ A * ((-1 : F83) ^ c *
        ((Nat.choose (A + 16) (16 - (c + 1)) : ℕ) : F83) *
        ((2 : F83) ^ (c + 1) - 1))) := by
  have hq : 0 < 83 ^ k := by positivity
  unfold T2
  rw [cast_mul' (Good83.mul_mem (Good83.mul_mem (mem_two_pow _)
      (mem_neg_one_pow _)) (mem_nat _)) (mem_Q _),
    cast_mul' (Good83.mul_mem (mem_two_pow _) (mem_neg_one_pow _)) (mem_nat _),
    cast_mul' (mem_two_pow _) (mem_neg_one_pow _),
    Rat.cast_natCast, cast_two_pow_frob, cast_neg_one_pow,
    ar_last c _ hq, cast_Q_scaled]
  have hsign : (-1 : F83) ^ (c * 83 ^ k + (83 ^ k - 1)) = (-1 : F83) ^ c := by
    rw [pow_add, neg_one_pow_frob, Even.neg_one_pow (even_q_sub_one k), mul_one]
  have hch : Nat.choose (A * 83 ^ k + v + 16 * 83 ^ k)
      (16 * 83 ^ k - (c + 1) * 83 ^ k) =
      Nat.choose ((A + 16) * 83 ^ k + v) ((16 - (c + 1)) * 83 ^ k) := by
    rw [Nat.sub_mul]
    congr 1
    ring
  rw [hsign, hch, cast_choose_lucas k (A + 16) (16 - (c + 1)) v hv]
  ring

theorem cast_qT (k A v : ℕ) (hA : A < 64) (hv : v < 83 ^ k) :
    ((qRat k * p0TQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v) : ℚ) : F83) =
      (2 : F83) ^ v * YT A := by
  have hq : 0 < 83 ^ k := by positivity
  have hiq : A * 83 ^ k + v < 64 * 83 ^ k := ar_lt A v _ 64 hA hv
  rw [qT_decomp]
  have hm1 : ∀ r ∈ range (A * 83 ^ k + v),
      p0UQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v - (r + 1)) *
        (qRat k / ((r + 1 : ℕ) : ℚ)) ∈ Good83 := by
    intro r hr
    have hr' := Finset.mem_range.mp hr
    exact Good83.mul_mem (mem_U _ _)
      (qdiv_mem k (r + 1) (by qomega) (ar_lt83 _ _ 64 (by qomega) (by norm_num)))
  have hm2 : ∀ s ∈ range (16 * 83 ^ k),
      T2 (16 * 83 ^ k) (A * 83 ^ k + v) s *
        (qRat k / ((s + 1 : ℕ) : ℚ)) ∈ Good83 := by
    intro s hs
    have hs' := Finset.mem_range.mp hs
    exact Good83.mul_mem (mem_T2 _ _ _)
      (qdiv_mem k (s + 1) (by qomega) (ar_lt83 _ _ 17 (by qomega) (by norm_num)))
  rw [cast_add' (Good83.sum_mem hm1) (Good83.sum_mem hm2),
    cast_sum' _ _ hm1, cast_sum' _ _ hm2]
  have hS1 : (∑ r ∈ range (A * 83 ^ k + v),
      ((p0UQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v - (r + 1)) *
        (qRat k / ((r + 1 : ℕ) : ℚ)) : ℚ) : F83)) =
      (2 : F83) ^ v * ∑ c ∈ range A,
        YU (A - (c + 1)) * (((c + 1 : ℕ) : F83))⁻¹ := by
    rw [block_sum (83 ^ k) A v (83 ^ k - 1) _ (by qomega)]
    · rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * 83 ^ k + (83 ^ k - 1) < A * 83 ^ k + v :=
        lt_of_lt_of_le (ar_lt c _ _ A hc' (by qomega)) (Nat.le_add_right _ _)
      rw [cast_mul' (mem_U _ _) (qdiv_mem k _ (by qomega)
          (ar_lt83 _ _ 64 (by qomega) (by norm_num))),
        ar_shift A c _ v hc' hq, ar_last c _ hq, cast_U k _ v hv,
        qdiv_cast_unit k (c + 1) (by qomega) (by qomega)]
      ring
    · intro c hc t ht htt
      have hlt : c * 83 ^ k + t < A * 83 ^ k := ar_lt c t _ A hc ht
      have ht1 : t + 1 < 83 ^ k := by qomega
      rw [cast_mul' (mem_U _ _) (qdiv_mem k _ (by qomega)
          (ar_lt83 _ _ 64 (by qomega) (by norm_num))),
        qdiv_cast_zero k _ (by qomega)
          (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by qomega) ht1),
        mul_zero]
    · intro t ht
      have ht1 : t + 1 < 83 ^ k := by qomega
      rw [cast_mul' (mem_U _ _) (qdiv_mem k _ (by qomega)
          (ar_lt83 _ _ 64 (by qomega) (by norm_num))),
        qdiv_cast_zero k _ (by qomega)
          (not_dvd_of_rem (m := A) (x := t + 1) (by ring) (by qomega) ht1),
        mul_zero]
  have hS2 : (∑ s ∈ range (16 * 83 ^ k),
      ((T2 (16 * 83 ^ k) (A * 83 ^ k + v) s *
        (qRat k / ((s + 1 : ℕ) : ℚ)) : ℚ) : F83)) =
      (2 : F83) ^ v * ((2 : F83) ^ A * ∑ c ∈ range 16,
        (-1 : F83) ^ c * ((Nat.choose (A + 16) (16 - (c + 1)) : ℕ) : F83) *
          ((2 : F83) ^ (c + 1) - 1) * (((c + 1 : ℕ) : F83))⁻¹) := by
    rw [block_sum_full (83 ^ k) (83 ^ k - 1) _ (by qomega) 16]
    · rw [Finset.mul_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro c hc
      have hc' := Finset.mem_range.mp hc
      have hlt : c * 83 ^ k + (83 ^ k - 1) < 16 * 83 ^ k := ar_lt c _ _ 16 hc' (by qomega)
      rw [cast_mul' (mem_T2 _ _ _) (qdiv_mem k _ (by qomega)
          (ar_lt83 _ _ 17 (by qomega) (by norm_num))),
        cast_T2_block k A v c hv hc', ar_last c _ hq,
        qdiv_cast_unit k (c + 1) (by qomega) (by qomega)]
      ring
    · intro c hc t ht htt
      have hlt : c * 83 ^ k + t < 16 * 83 ^ k := ar_lt c t _ 16 hc ht
      have ht1 : t + 1 < 83 ^ k := by qomega
      rw [cast_mul' (mem_T2 _ _ _) (qdiv_mem k _ (by qomega)
          (ar_lt83 _ _ 17 (by qomega) (by norm_num))),
        qdiv_cast_zero k _ (by qomega)
          (not_dvd_of_rem (m := c) (x := t + 1) (by ring) (by qomega) ht1),
        mul_zero]
  rw [hS1, hS2, YT]
  ring

theorem mem_qT (k A v : ℕ) (hA : A < 64) (hv : v < 83 ^ k) :
    qRat k * p0TQ (2 : ℚ) (16 * 83 ^ k) (A * 83 ^ k + v) ∈ Good83 := by
  have hq : 0 < 83 ^ k := by positivity
  have hg : 16 * 83 ^ k < 83 * 83 ^ k := by qomega
  exact q_mul_p0T_good k (16 * 83 ^ k) (A * 83 ^ k + v)
    (ar_lt83 _ _ 64 (ar_lt A v _ 64 hA hv) (by norm_num)) hg

end

end ScaledLucas
end Li2Lean.P0
