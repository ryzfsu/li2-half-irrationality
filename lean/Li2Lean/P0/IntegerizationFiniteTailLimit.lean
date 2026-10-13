/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationLowPrimeLimit

/-! A finite affine majorant for the low-ratio tail. The 64 tangent pieces
cover (1/256,1/128), and the unexpanded interval below 1/256 is charged
at the coarse height 3. This deliberately pays a slightly larger constant
than v13's infinite-tail calculation; its total is strictly below 1/50. -/
namespace Li2Lean.P0.Integerization
noncomputable section
open Filter Topology MeasureTheory

private def tailLeft (q : ℕ) : ℚ := 1 / (2 * ((q : ℚ) + 65))
private def tailRight (q : ℕ) : ℚ := 1 / (2 * ((q : ℚ) + 64))
private def tailCenter (q : ℕ) : ℚ := (tailLeft q + tailRight q) / 2

private theorem tailLeft_pos (q : ℕ) : 0 < tailLeft q := by
  unfold tailLeft
  positivity
private theorem tailRight_pos (q : ℕ) : 0 < tailRight q := by
  unfold tailRight
  positivity
private theorem tailCenter_pos (q : ℕ) : 0 < tailCenter q := by
  exact div_pos (add_pos (tailLeft_pos q) (tailRight_pos q)) (by norm_num)
private theorem tailLeft_lt_right (q : ℕ) : tailLeft q < tailRight q := by
  unfold tailLeft tailRight
  apply one_div_lt_one_div_of_lt
  · positivity
  · linarith

def p0FiniteTailPiece (q : ℕ) : PrimeAffinePiece where
  lo := tailLeft q
  hi := tailRight q
  intercept := 3 + 2 * ((q : ℚ) + 64) - 2 / tailCenter q
  slope := 2 + 1 / (tailCenter q) ^ 2
  lo_pos := tailLeft_pos q
  lo_lt_hi := tailLeft_lt_right q

def p0FiniteTailProfile : PrimeAffineProfile :=
  ⟨(List.range 64).map p0FiniteTailPiece⟩

def p0FiniteTailIntegral : ℚ :=
  ((List.range 64).map fun q =>
    let f := p0FiniteTailPiece q
    f.slope * (f.hi ^ 2 - f.lo ^ 2) / 2 + f.intercept * (f.hi - f.lo)).sum

/-- The tangent bound is a square divided by a positive denominator. -/
theorem reciprocal_tangent_majorant {x c : ℝ} (hx : 0 < x) (hc : 0 < c) :
    -(1 / x) ≤ x / c ^ 2 - 2 / c := by
  have heq : (x / c ^ 2 - 2 / c) - (-(1 / x)) =
      (x - c) ^ 2 / (x * c ^ 2) := by
    field_simp
    <;> ring
  apply sub_nonneg.mp
  rw [heq]
  positivity

/-- The paper's tail bound on the open cell associated to q+64.
Endpoints are intentionally excluded and must be paid as finite walls. -/
theorem p0FiniteTailPiece_majorizes (q : ℕ) (x : ℝ)
    (hxlo : ((p0FiniteTailPiece q).lo : ℝ) < x)
    (hxhi : x < ((p0FiniteTailPiece q).hi : ℝ)) :
    3 - 2 * Int.fract (1 / (2 * x)) + 2 * x ≤
      ((p0FiniteTailPiece q).slope : ℝ) * x +
        ((p0FiniteTailPiece q).intercept : ℝ) := by
  have hlo : 0 < ((tailLeft q : ℚ) : ℝ) := by exact_mod_cast tailLeft_pos q
  have hx : 0 < x := lt_trans hlo hxlo
  have hq : 0 < (q : ℝ) + 64 := by positivity
  have helo : ((p0FiniteTailPiece q).lo : ℝ) = 1 / (2 * ((q : ℝ) + 65)) := by
    simp [p0FiniteTailPiece, tailLeft]
  have hehi : ((p0FiniteTailPiece q).hi : ℝ) = 1 / (2 * ((q : ℝ) + 64)) := by
    simp [p0FiniteTailPiece, tailRight]
  rw [helo] at hxlo
  rw [hehi] at hxhi
  have hlow : (q : ℝ) + 64 ≤ 1 / (2 * x) := by
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2*x)).mpr
    have ht := (lt_div_iff₀ (by positivity : (0 : ℝ) < 2*((q : ℝ)+64))).mp hxhi
    nlinarith
  have hhigh : 1 / (2 * x) < (q : ℝ) + 65 := by
    apply (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*x)).mpr
    have ht := (div_lt_iff₀ (by positivity : (0 : ℝ) < 2*((q : ℝ)+65))).mp hxlo
    nlinarith
  have hfloor : ⌊1 / (2 * x)⌋ = (q : ℤ) + 64 := by
    apply Int.floor_eq_iff.mpr
    constructor <;> push_cast <;> linarith
  have hc : 0 < (tailCenter q : ℝ) := by exact_mod_cast tailCenter_pos q
  have htan := reciprocal_tangent_majorant hx hc
  unfold Int.fract
  rw [hfloor]
  simp only [p0FiniteTailPiece]
  push_cast
  have hmain := add_le_add_right htan (3 + 2 * ((q : ℝ) + 64) + 2 * x)
  convert hmain using 1 <;> field_simp <;> ring

private theorem finiteTail_integral_list (qs : List ℕ) :
    (∫ t : ℝ, (PrimeAffineProfile.mk (qs.map p0FiniteTailPiece)).eval t) =
      (((qs.map fun q => let f := p0FiniteTailPiece q
        f.slope * (f.hi ^ 2 - f.lo ^ 2) / 2 + f.intercept * (f.hi - f.lo)).sum : ℚ) : ℝ) := by
  rw [primeAffineProfile_integral_eq_sum_singletons]
  induction qs with
  | nil => simp
  | cons q qs ih =>
    simp only [List.map_cons, List.sum_cons, Rat.cast_add]
    rw [ih, singletonPrimeAffineProfile_integral]
    push_cast
    ring

theorem p0FiniteTailProfile_integral :
    (∫ t : ℝ, p0FiniteTailProfile.eval t) = (p0FiniteTailIntegral : ℝ) :=
  finiteTail_integral_list (List.range 64)

set_option maxRecDepth 10000 in
set_option maxHeartbeats 2000000 in
theorem p0FiniteTail_total_lt : p0FiniteTailIntegral + 3 / 256 < (1 / 50 : ℚ) := by
  norm_num [p0FiniteTailIntegral, p0FiniteTailPiece, tailLeft, tailRight,
    tailCenter, List.range, List.range.loop]

theorem p0FiniteTailProfile_weightedPrime_nat_limit :
    Tendsto (fun m : ℕ => weightedPrimeSum p0FiniteTailProfile m / (m : ℝ))
      atTop (𝓝 (p0FiniteTailIntegral : ℝ)) := by
  have h := l3WeightedPrimeLimit_unconditional p0FiniteTailProfile
  rw [p0FiniteTailProfile_integral] at h
  exact h.comp tendsto_natCast_atTop_atTop

/-- The complete paid tail budget: a literal finite weighted-prime sum and
one coarse Chebyshev cutoff. No infinite family of affine pieces is used. -/
def p0FiniteTailBudget (m : ℕ) : ℝ :=
  weightedPrimeSum p0FiniteTailProfile m / (m : ℝ) +
    3 * Chebyshev.theta ((1 / 256 : ℝ) * m) / (m : ℝ)

theorem p0FiniteTailBudget_tendsto :
    Tendsto p0FiniteTailBudget atTop
      (𝓝 ((p0FiniteTailIntegral : ℝ) + 3 / 256)) := by
  have ht := (hPNT_theta_scaled hPNT_of_primeNumberTheoremAnd (1/256) (by norm_num)).comp
    (tendsto_natCast_atTop_atTop : Tendsto (fun m : ℕ => (m : ℝ)) atTop atTop)
  have h3 := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (3 : ℝ)) atTop (𝓝 3)).mul ht
  have hsum := p0FiniteTailProfile_weightedPrime_nat_limit.add h3
  unfold p0FiniteTailBudget
  simpa only [div_eq_mul_inv, one_mul, mul_assoc,
    Function.comp_apply] using hsum


/-- The integer killed-residue estimate implies the paper's real tail
profile. This includes the exact half-index and fractional-part conversion. -/
theorem p0TailFloorBudget_le_profile (m p : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hp : 0 < p) (W : ℝ)
    (hW : W ≤ 3*(m : ℝ) - 2*((m / p : ℕ) : ℝ)*((m / 2 % p : ℕ) : ℝ)) :
    W / (m : ℝ) ≤ 3 - 2*Int.fract (1 / (2*((p : ℝ)/(m : ℝ)))) +
      2*((p : ℝ)/(m : ℝ)) := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hpR : 0 < (p : ℝ) := by exact_mod_cast hp
  have h2 : 2 ∣ m := dvd_trans (by decide : 2 ∣ 4) h4
  have hhalfN : m / 2 * 2 = m := Nat.div_mul_cancel h2
  have hhalf : ((m / 2 : ℕ) : ℝ)*2 = (m : ℝ) := by exact_mod_cast hhalfN
  have hratio : 1 / (2*((p : ℝ)/(m : ℝ))) = ((m / 2 : ℕ) : ℝ)/(p : ℝ) := by
    apply (div_eq_div_iff (mul_ne_zero (by norm_num) (div_ne_zero hpR.ne' hmR.ne')) hpR.ne').mpr
    field_simp
    nlinarith
  rw [hratio, Int.fract_div_natCast_eq_div_natCast_mod]
  have hmod : ((m % p : ℕ) : ℝ) < (p : ℝ) := by exact_mod_cast Nat.mod_lt m hp
  have hdiv : (p : ℝ)*((m / p : ℕ) : ℝ) + ((m % p : ℕ) : ℝ) = (m : ℝ) := by
    exact_mod_cast Nat.div_add_mod m p
  have hq : (m : ℝ)/(p : ℝ) ≤ ((m / p : ℕ) : ℝ)+1 := by
    apply (div_le_iff₀ hpR).mpr
    nlinarith
  have hr0 : (0 : ℝ) ≤ ((m / 2 % p : ℕ) : ℝ) := by positivity
  have hr : ((m / 2 % p : ℕ) : ℝ) ≤ (p : ℝ) := by
    exact_mod_cast (Nat.mod_lt (m/2) hp).le
  have hprod := mul_le_mul_of_nonneg_right hq hr0
  have hbound : W ≤ 3*(m : ℝ) -
      2*((m : ℝ)/(p : ℝ))*((m / 2 % p : ℕ) : ℝ)+2*(p : ℝ) := by
    nlinarith
  have hd := div_le_div_of_nonneg_right hbound hmR.le
  convert hd using 1 <;> field_simp <;> ring

end
end Li2Lean.P0.Integerization
#print axioms Li2Lean.P0.Integerization.p0FiniteTailPiece_majorizes
#print axioms Li2Lean.P0.Integerization.p0FiniteTail_total_lt
#print axioms Li2Lean.P0.Integerization.p0FiniteTailBudget_tendsto

#print axioms Li2Lean.P0.Integerization.p0TailFloorBudget_le_profile
