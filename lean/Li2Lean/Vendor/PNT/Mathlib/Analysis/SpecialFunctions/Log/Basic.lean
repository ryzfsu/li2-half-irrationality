import Mathlib.Algebra.Order.Floor.Defs
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/-
Vendored from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
original path `PrimeNumberTheoremAnd/Mathlib/Analysis/SpecialFunctions/Log/Basic.lean`.
Licensed under the Apache License, Version 2.0; see `Li2Lean/Vendor/PNT/LICENSE` and `Li2Lean/Vendor/PNT/NOTICE`.
Modifications by the Li2Lean project:
- added this header; declaration names and proof content otherwise unchanged
-/

open Filter Real

/-- log^b x / x^a goes to zero at infinity if a is positive. -/
theorem Real.tendsto_pow_log_div_pow_atTop (a : ℝ) (b : ℝ) (ha : 0 < a) :
    Filter.Tendsto (fun x ↦ log x ^ b / x^a) Filter.atTop (nhds 0) := by
  apply Asymptotics.isLittleO_iff_tendsto' _|>.mp <| isLittleO_log_rpow_rpow_atTop _ ha
  filter_upwards [eventually_gt_atTop 0] with x hx
  intro h
  rw [rpow_eq_zero hx.le ha.ne.symm] at h
  exfalso
  linarith
