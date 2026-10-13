/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Frequency.Contour
import Li2Lean.P0.CA.Frequency.FixTerms

/-!
# CA-F fixed-point contour bound

Kernel-fast version of `nuHi`: the logarithm uses `logMant` and the Fejer
polynomial uses integer mantissas of the exact dyadic `sigma` bounds and a
literal mantissa table `betaM` checked against `betaLo`.  Soundness reduces
to `nu_core`.
-/

namespace Li2Lean.P0.CA.Frequency

open Li2Lean.P0.ConfigContourReference

/-- Mantissa lower bounds (scale `2^60`) for `betaLo n` (generated). -/
def betaM : List ℤ := [(0 : ℤ), (-291627479867345118 : ℤ), (101794703526430259 : ℤ), (-37952018835288981 : ℤ), (9043112808819918 : ℤ), (2377579353642375 : ℤ), (-4469740584162333 : ℤ), (2579895474316621 : ℤ), (-123369491483833 : ℤ), (-1252724151155096 : ℤ), (1307234462128684 : ℤ), (-595413619371649 : ℤ), (-165723470365093 : ℤ), (527847326605836 : ℤ), (-437909629047759 : ℤ), (116256098265731 : ℤ), (164435071391354 : ℤ), (-250952943377214 : ℤ), (156598788546094 : ℤ), (1948207334901 : ℤ), (-107375993897163 : ℤ), (112442639517970 : ℤ), (-46666765497941 : ℤ), (-25887097964219 : ℤ), (57466291928331 : ℤ), (-41897081252821 : ℤ), (5580108546066 : ℤ), (20170457636618 : ℤ), (-21862938361627 : ℤ), (7600434954406 : ℤ), (5552747783703 : ℤ), (-7210686939369 : ℤ), (-1 : ℤ), (6021044986408 : ℤ), (-3868013162023 : ℤ), (-4408252273556 : ℤ), (10526599951894 : ℤ), (-8028535963470 : ℤ), (-1825985176402 : ℤ), (11190459736330 : ℤ), (-12412719056520 : ℤ), (4468317097013 : ℤ), (6337461981201 : ℤ), (-11767252972811 : ℤ), (8415046543664 : ℤ), (-109676857373 : ℤ), (-5930108402167 : ℤ), (5673138347623 : ℤ), (-1660960317085 : ℤ)]

theorem betaM_check :
    (List.range 49).all (fun n => decide (((betaM.getD n 0 : ℤ) : ℚ) / twoE ≤ betaLo n)) = true := by
  decide +kernel

theorem betaM_le {n : ℕ} (hn : n < 49) : (((betaM.getD n 0 : ℤ) : ℝ)) / twoE ≤ (betaLo n : ℝ) := by
  have h := List.all_eq_true.mp betaM_check n (List.mem_range.mpr hn)
  simp only [decide_eq_true_eq] at h
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  exact h'

/-- The sigma scale `2^48`. -/
def sNat : ℕ := 281474976710656

theorem sNat_cast : ((sNat : ℕ) : ℚ) = roundScale := by norm_num [sNat, roundScale]

/-- Mantissa lower bound of the `n`th Fejer summand. -/
def sigM (Slo Shi : ℕ) (n : ℕ) : ℤ :=
  if n = 0 then 0
  else if 0 ≤ betaM.getD n 0 then fdiv (betaM.getD n 0 * ((Slo ^ n : ℕ) : ℤ)) (sNat ^ n)
  else fdiv (betaM.getD n 0 * ((Shi ^ n : ℕ) : ℤ)) (sNat ^ n)

def sumToI (f : ℕ → ℤ) : ℕ → ℤ
  | 0 => 0
  | n + 1 => sumToI f n + f n

theorem sumToI_eq (f : ℕ → ℤ) (n : ℕ) : sumToI f n = ∑ i ∈ Finset.range n, f i := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Finset.sum_range_succ, ← ih]; rfl

/-- Fixed-point upper bound for `contourReferencePotential (-t)`. -/
def nuHiF (t : ℚ) : ℚ :=
  massQ * (((logMant (rhiOf t).num.natAbs (rhiOf t).den).2 : ℤ) : ℚ) / twoE -
    ((sumToI (sigM (⌊cScaleQ / rhiOf t * roundScale⌋).natAbs
      (⌈cScaleQ / rloOf t * roundScale⌉).natAbs) 49 : ℤ) : ℚ) / twoE

theorem sigM_le {n : ℕ} (hn : n < 49) {Slo Shi : ℕ} {a b : ℝ}
    (ha : a = (Slo : ℝ) / sNat) (hb : b = (Shi : ℝ) / sNat) (hab : a ≤ b) :
    ((sigM Slo Shi n : ℤ) : ℝ) / twoE ≤
      min ((betaLo n : ℝ) * a ^ n) ((betaLo n : ℝ) * b ^ n) := by
  have hE := twoE_cast_pos
  have hS : (0 : ℝ) < sNat := by norm_num [sNat]
  have ha0 : 0 ≤ a := by rw [ha]; positivity
  have hpa : 0 ≤ a ^ n := pow_nonneg ha0 n
  have hpab : a ^ n ≤ b ^ n := pow_le_pow_left₀ ha0 hab n
  have hβ := betaM_le hn
  set β : ℝ := ((betaM.getD n 0 : ℤ) : ℝ) / twoE with hβdef
  unfold sigM
  split_ifs with h0 hpos
  · subst h0; simp [betaLo]
  · have hf := fdiv_le (betaM.getD n 0 * ((Slo ^ n : ℕ) : ℤ)) (pow_pos (by norm_num [sNat] : 0 < sNat) n)
    have e : ((betaM.getD n 0 * ((Slo ^ n : ℕ) : ℤ) : ℤ) : ℝ) / ((sNat ^ n : ℕ) : ℝ) / twoE =
        β * a ^ n := by
      rw [hβdef, ha, div_pow]; push_cast; field_simp
    have hb0 : (0 : ℝ) ≤ β := by
      rw [hβdef]; apply div_nonneg _ hE.le; exact_mod_cast hpos
    have h1 : ((sigM Slo Shi n : ℤ) : ℝ) / twoE ≤ β * a ^ n := by
      simp only [sigM, h0, hpos, ↓reduceIte]; rw [← e]
      exact div_le_div_of_nonneg_right hf hE.le
    simp only [sigM, h0, hpos, ↓reduceIte] at h1 ⊢
    have hblo : (0 : ℝ) ≤ betaLo n := le_trans hb0 hβ
    apply le_min
    · exact le_trans h1 (mul_le_mul_of_nonneg_right hβ hpa)
    · exact le_trans h1 (le_trans (mul_le_mul_of_nonneg_right hβ hpa)
        (mul_le_mul_of_nonneg_left hpab hblo))
  · have hf := fdiv_le (betaM.getD n 0 * ((Shi ^ n : ℕ) : ℤ)) (pow_pos (by norm_num [sNat] : 0 < sNat) n)
    have e : ((betaM.getD n 0 * ((Shi ^ n : ℕ) : ℤ) : ℤ) : ℝ) / ((sNat ^ n : ℕ) : ℝ) / twoE =
        β * b ^ n := by
      rw [hβdef, hb, div_pow]; push_cast; field_simp
    have hb0 : β ≤ 0 := by
      rw [hβdef]; apply div_nonpos_of_nonpos_of_nonneg _ hE.le
      exact_mod_cast (le_of_lt (lt_of_not_ge hpos))
    have h1 : ((sigM Slo Shi n : ℤ) : ℝ) / twoE ≤ β * b ^ n := by
      simp only [sigM, h0, hpos, ↓reduceIte]; rw [← e]
      exact div_le_div_of_nonneg_right hf hE.le
    simp only [sigM, h0, hpos, ↓reduceIte] at h1 ⊢
    have hpb : 0 ≤ b ^ n := le_trans hpa hpab
    apply le_min
    · exact le_trans h1 (le_trans (mul_le_mul_of_nonpos_left hpab hb0)
        (mul_le_mul_of_nonneg_right hβ hpa))
    · exact le_trans h1 (mul_le_mul_of_nonneg_right hβ hpb)

/-- The fixed-point contour bound is sound for every rational `t ≥ 1/2`. -/
theorem contourReferencePotential_neg_le_nuHiF {t : ℚ} (ht : (1 / 2 : ℚ) ≤ t) :
    contourReferencePotential (-((t : ℝ) : ℂ)) ≤ (nuHiF t : ℝ) := by
  obtain ⟨hpos, hs0, hs01, h⟩ := nu_core ht
  have hE := twoE_cast_pos
  have hS := roundScale_pos
  -- log part
  have hnum0 : 0 < (rhiOf t).num := Rat.num_pos.mpr hpos
  have hnum : 0 < (rhiOf t).num.natAbs := Int.natAbs_pos.mpr hnum0.ne'
  have hl := (logMant_sound hnum (rhiOf t).den_pos).2
  have hr : (((rhiOf t).num.natAbs : ℕ) : ℝ) / ((rhiOf t).den : ℝ) = ((rhiOf t : ℚ) : ℝ) := by
    rw [Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hnum0), Rat.cast_def]
  rw [hr] at hl
  -- sigma mantissas
  set x : ℚ := cScaleQ / rhiOf t * roundScale with hx
  set y : ℚ := cScaleQ / rloOf t * roundScale with hy
  have hfl : (0 : ℤ) ≤ ⌊x⌋ := by
    have h2 : sigLo t * roundScale = (⌊x⌋ : ℚ) := by
      unfold sigLo rdn rdnAt; rw [← hx]; field_simp
    have : (0 : ℚ) ≤ (⌊x⌋ : ℚ) := by rw [← h2]; exact mul_nonneg hs0 hS.le
    exact_mod_cast this
  have hcl : (0 : ℤ) ≤ ⌈y⌉ := by
    have h2 : sigHi t * roundScale = (⌈y⌉ : ℚ) := by
      unfold sigHi rup rupAt; rw [← hy]; field_simp
    have : (0 : ℚ) ≤ (⌈y⌉ : ℚ) := by rw [← h2]; exact mul_nonneg (le_trans hs0 hs01) hS.le
    exact_mod_cast this
  have hSR : ((sNat : ℕ) : ℝ) = ((roundScale : ℚ) : ℝ) := by
    rw [← sNat_cast]; push_cast; rfl
  have ha : ((sigLo t : ℚ) : ℝ) = (((⌊x⌋).natAbs : ℕ) : ℝ) / sNat := by
    rw [Nat.cast_natAbs, abs_of_nonneg hfl, hSR]
    unfold sigLo rdn rdnAt; rw [← hx]; push_cast; rfl
  have hb : ((sigHi t : ℚ) : ℝ) = (((⌈y⌉).natAbs : ℕ) : ℝ) / sNat := by
    rw [Nat.cast_natAbs, abs_of_nonneg hcl, hSR]
    unfold sigHi rup rupAt; rw [← hy]; push_cast; rfl
  have hab : ((sigLo t : ℚ) : ℝ) ≤ ((sigHi t : ℚ) : ℝ) := by exact_mod_cast hs01
  have hsum : ((sumToI (sigM (⌊x⌋).natAbs (⌈y⌉).natAbs) 49 : ℤ) : ℝ) / twoE ≤
      ((sumTo (termLoN (sigLo t) (sigHi t)) 49 : ℚ) : ℝ) := by
    rw [sumToI_eq, sumTo_eq]
    push_cast
    rw [Finset.sum_div]
    apply Finset.sum_le_sum
    intro n hn
    have hn49 := Finset.mem_range.mp hn
    have hm := sigM_le hn49 ha hb hab
    unfold termLoN
    split_ifs with h0
    · subst h0; simp [sigM]
    · push_cast
      exact hm
  have hmass : ((massQ : ℚ) : ℝ) = 267885951940 / 1000000000000 := by
    unfold massQ; push_cast; ring
  unfold nuHiF
  rw [← hx, ← hy]
  rw [Rat.cast_sub, Rat.cast_div, Rat.cast_mul, hmass, Rat.cast_div]
  have e1 : (((twoE : ℕ) : ℚ) : ℝ) = (twoE : ℝ) := by push_cast; rfl
  simp only [Rat.cast_intCast, e1]
  have := mul_le_mul_of_nonneg_left hl (by norm_num : (0 : ℝ) ≤ 267885951940 / 1000000000000)
  rw [mul_div_assoc]
  linarith

end Li2Lean.P0.CA.Frequency
