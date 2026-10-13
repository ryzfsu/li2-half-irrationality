/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace Li2Lean
namespace P0ContourLeaf

noncomputable section

/-- Centre of the v10 P0 ellipse in docs/6333, section 3. -/
def xi : ℝ := (11281 : ℝ) / 10000

/-- Horizontal semiaxis of the v10 P0 ellipse in docs/6333, section 3. -/
def axisA : ℝ := (12783 : ℝ) / 10000

/-- Vertical semiaxis of the v10 P0 ellipse in docs/6333, section 3. -/
def axisB : ℝ := (229 : ℝ) / 200

/-- Joukowski coefficients of the v10 ellipse, with no decimal rounding. -/
def alpha : ℝ := (axisA + axisB) / 2

def beta : ℝ := (axisA - axisB) / 2

/-- The quadratic whose roots are the Joukowski preimages of a real point. -/
def polePolynomial (t : ℝ) (z : ℂ) : ℂ :=
  (alpha : ℂ) * z ^ 2 + ((xi - t : ℝ) : ℂ) * z + (beta : ℂ)

/-- The v10 ellipse's Joukowski map, before scaling by `m`. -/
def joukowski (z : ℂ) : ℂ :=
  (xi : ℂ) + (alpha : ℂ) * z + (beta : ℂ) / z

/-- The scaled map taking the unit-circle parameter to `m Gamma`. -/
def scaledJoukowski (m : ℕ) (z : ℂ) : ℂ :=
  (m : ℂ) * joukowski z

/-- A quadratic preimage root is nonzero because the constant term is positive. -/
theorem pole_root_ne_zero {t : ℝ} {z : ℂ}
    (hz : polePolynomial t z = 0) : z ≠ 0 := by
  intro hz0
  have hbeta : 0 < beta := by norm_num [beta, axisA, axisB]
  have hbeta0 : (beta : ℂ) = 0 := by
    simpa [polePolynomial, hz0] using hz
  exact (ne_of_gt hbeta) (by exact_mod_cast hbeta0)

/-- The quadratic is exactly the equation `J(z)=t`, after multiplication by z. -/
theorem polePolynomial_eq_zero_iff_joukowski {t : ℝ} {z : ℂ} (hz : z ≠ 0) :
    polePolynomial t z = 0 ↔ joukowski z = Complex.ofReal t := by
  constructor
  · intro h
    dsimp [polePolynomial] at h
    dsimp [joukowski]
    field_simp [hz]
    push_cast at h ⊢
    linear_combination h
  · intro h
    dsimp [joukowski] at h
    field_simp [hz] at h
    dsimp [polePolynomial]
    push_cast at h ⊢
    linear_combination h

/--
For every real pole on the interval enclosed by the unscaled P0 ellipse,
every solution of its Joukowski preimage quadratic lies strictly in the unit
disk. The strict margin is `axisB - xi = 169/10000` at the left endpoint.
-/
theorem pole_preimage_mem_unitDisk {t : ℝ} (ht0 : 0 ≤ t) (ht2 : t ≤ 2)
    (z : ℂ) (hz : polePolynomial t z = 0) : ‖z‖ < 1 := by
  have halpha : 0 < alpha := by
    norm_num [alpha, axisA, axisB]
  have hbeta : 0 < beta := by
    norm_num [beta, axisA, axisB]
  have hmargin0 : xi + beta < alpha := by
    norm_num [xi, alpha, beta, axisA, axisB]
  have habs : |xi - t| ≤ xi := by
    rw [abs_le]
    constructor
    · have htwo : 2 ≤ 2 * xi := by norm_num [xi]
      nlinarith [ht2]
    · nlinarith [ht0]
  have hmargin : |xi - t| + beta < alpha := by
    linarith
  have heq : (alpha : ℂ) * z ^ 2 =
      -(((xi - t : ℝ) : ℂ) * z + (beta : ℂ)) := by
    dsimp [polePolynomial] at hz
    linear_combination hz
  have hnorm : alpha * ‖z‖ ^ 2 =
      ‖((xi - t : ℝ) : ℂ) * z + (beta : ℂ)‖ := by
    calc
      alpha * ‖z‖ ^ 2 = ‖(alpha : ℂ) * z ^ 2‖ := by
        simp only [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
          abs_of_pos halpha]
      _ = ‖((xi - t : ℝ) : ℂ) * z + (beta : ℂ)‖ := by
        rw [heq, norm_neg]
  have htriangle :
      ‖((xi - t : ℝ) : ℂ) * z + (beta : ℂ)‖ ≤
        ‖((xi - t : ℝ) : ℂ) * z‖ + ‖(beta : ℂ)‖ := norm_add_le _ _
  have hcmul : ‖((xi - t : ℝ) : ℂ) * z‖ = |xi - t| * ‖z‖ := by
    simp only [norm_mul, Complex.norm_real, Real.norm_eq_abs]
  have hbetaNorm : ‖(beta : ℂ)‖ = beta := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hbeta]
  have hbound : alpha * ‖z‖ ^ 2 ≤ |xi - t| * ‖z‖ + beta := by
    calc
      alpha * ‖z‖ ^ 2 =
          ‖((xi - t : ℝ) : ℂ) * z + (beta : ℂ)‖ := hnorm
      _ ≤ ‖((xi - t : ℝ) : ℂ) * z‖ + ‖(beta : ℂ)‖ := htriangle
      _ = |xi - t| * ‖z‖ + beta := by rw [hcmul, hbetaNorm]
  by_contra hnot
  have hr : 1 ≤ ‖z‖ := le_of_not_gt hnot
  have hrpos : 0 < ‖z‖ := lt_of_lt_of_le zero_lt_one hr
  have hsq : alpha * ‖z‖ ≤ alpha * ‖z‖ ^ 2 := by
    have hnonneg : 0 ≤ alpha * ‖z‖ * (‖z‖ - 1) :=
      mul_nonneg (mul_nonneg (le_of_lt halpha) (norm_nonneg z)) (by linarith)
    nlinarith
  have hbetaLe : beta ≤ beta * ‖z‖ := by
    have hnonneg : 0 ≤ beta * (‖z‖ - 1) :=
      mul_nonneg (le_of_lt hbeta) (by linarith)
    nlinarith
  have hmerge : |xi - t| * ‖z‖ + beta ≤
      (|xi - t| + beta) * ‖z‖ := by
    nlinarith [hbetaLe]
  have hstrict : (|xi - t| + beta) * ‖z‖ < alpha * ‖z‖ :=
    mul_lt_mul_of_pos_right hmargin hrpos
  nlinarith

/--
The exact scaled quadratic for a paper pole `i` on `m Gamma`. The paper's
indices satisfy `0 ≤ i ≤ 2m`; dividing by `m` recovers `polePolynomial`.
-/
def scaledPolePolynomial (m i : ℕ) (z : ℂ) : ℂ :=
  (((m : ℝ) * alpha : ℝ) : ℂ) * z ^ 2 +
    (((m : ℝ) * xi - (i : ℝ) : ℝ) : ℂ) * z +
    (((m : ℝ) * beta : ℝ) : ℂ)

/--
Paper-specific pole/preimage range condition for the contour `m Gamma`:
all preimages of every integer pole `i` in `[0,2m]` lie strictly inside the
unit circle. This is the root-range premise used by the Joukowski pullback.
-/
theorem scaled_pole_preimage_mem_unitDisk {m i : ℕ} (hm : 0 < m)
    (hi : i ≤ 2 * m) (z : ℂ) (hz : scaledPolePolynomial m i z = 0) :
    ‖z‖ < 1 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hmC : (m : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hiR : (i : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hi
  have ht0 : 0 ≤ (i : ℝ) / (m : ℝ) :=
    div_nonneg (Nat.cast_nonneg i) (le_of_lt hmR)
  have ht2 : (i : ℝ) / (m : ℝ) ≤ 2 :=
    (div_le_iff₀ hmR).2 hiR
  have hscale : scaledPolePolynomial m i z =
      (m : ℂ) * polePolynomial ((i : ℝ) / (m : ℝ)) z := by
    dsimp [scaledPolePolynomial, polePolynomial]
    push_cast
    field_simp [ne_of_gt hmR]
  rw [hscale] at hz
  have hbase : polePolynomial ((i : ℝ) / (m : ℝ)) z = 0 := by
    rcases mul_eq_zero.mp hz with hmzero | hbase
    · exact (hmC hmzero).elim
    · exact hbase
  exact pole_preimage_mem_unitDisk ht0 ht2 z hbase

/--
Paper-level form of the pole-range lemma: every nonzero preimage of a pole
`i ∈ [0,2m]` under the scaled v10 Joukowski map is in the open unit disk.
The parameter interval is exactly the pole interval for `m Gamma` in (3.1).
-/
theorem p0_joukowski_preimage_mem_unitDisk {m i : ℕ} (hm : 0 < m)
    (hi : i ≤ 2 * m) (z : ℂ) (hz : z ≠ 0)
    (hmap : scaledJoukowski m z = (i : ℂ)) : ‖z‖ < 1 := by
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have ht0 : 0 ≤ (i : ℝ) / (m : ℝ) :=
    div_nonneg (Nat.cast_nonneg i) (le_of_lt hmR)
  have hiR : (i : ℝ) ≤ 2 * (m : ℝ) := by exact_mod_cast hi
  have ht2 : (i : ℝ) / (m : ℝ) ≤ 2 :=
    (div_le_iff₀ hmR).2 hiR
  have hmap' : joukowski z = (i : ℂ) / (m : ℂ) := by
    dsimp [scaledJoukowski] at hmap
    field_simp [show (m : ℂ) ≠ 0 by exact_mod_cast (Nat.ne_of_gt hm)] at hmap ⊢
    exact hmap
  have hquot : Complex.ofReal ((i : ℝ) / (m : ℝ)) =
      (i : ℂ) / (m : ℂ) := by
    exact Complex.ofReal_div (i : ℝ) (m : ℝ)
  have hmapReal : joukowski z = Complex.ofReal ((i : ℝ) / (m : ℝ)) := by
    exact hmap'.trans hquot.symm
  exact pole_preimage_mem_unitDisk ht0 ht2 z
    ((polePolynomial_eq_zero_iff_joukowski hz).2 hmapReal)

end
end P0ContourLeaf
end Li2Lean
