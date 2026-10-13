/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
theorem smoke_irrational_sqrt_two : Irrational (Real.sqrt 2) := irrational_sqrt_two
example : (2:ℕ)^64 % 1000003 = 2^64 % 1000003 := by decide +kernel
#print axioms smoke_irrational_sqrt_two
