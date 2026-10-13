/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib

namespace ContourKit

noncomputable section

/-- General finite-place representation of a rational value and its residue
modulo `p`; the denominator condition certifies a valid reduction. Used by
the P0 prime-power nonvanishing argument. -/
structure ReducedRational (p : ℕ) where
  value : ℚ
  numerator : ℤ
  denominator : ℤ
  denominator_ne_zero : denominator ≠ 0
  denominator_residue_ne_zero : (denominator : ZMod p) ≠ 0
  value_eq : value = (numerator : ℚ) / (denominator : ℚ)
  residue : ZMod p
  residue_eq : residue = (numerator : ZMod p) * (denominator : ZMod p)⁻¹

/-- If a rational value has nonzero residue, it is nonzero. This general
criterion extracts the rational-point conclusion from P0's `eq:nv-final`
residue in `output/li2-half-paper-v10/sec-nonvanishing.tex`.
-/
theorem ReducedRational.value_ne_zero {p : ℕ} (x : ReducedRational p)
    (h : x.residue ≠ 0) : x.value ≠ 0 := by
  intro hvalue
  have hnumQ : (x.numerator : ℚ) = 0 := by
    have hquot : (x.numerator : ℚ) / (x.denominator : ℚ) = 0 :=
      x.value_eq.symm.trans hvalue
    have hdenQ : (x.denominator : ℚ) ≠ 0 := by
      exact_mod_cast x.denominator_ne_zero
    field_simp [hdenQ] at hquot
    simpa using hquot
  have hnum : x.numerator = 0 := by exact_mod_cast hnumQ
  apply h
  rw [x.residue_eq, hnum]
  simp

end

end ContourKit
