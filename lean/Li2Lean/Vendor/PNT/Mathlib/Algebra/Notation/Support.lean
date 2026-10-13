import Mathlib.Algebra.Notation.Support

/-
Vendored from PrimeNumberTheoremAnd (https://github.com/AlexKontorovich/PrimeNumberTheoremAnd),
commit c39a751132c88b6e8080b74c74023fd95b3d8be0,
original path `PrimeNumberTheoremAnd/Mathlib/Algebra/Notation/Support.lean`.
Licensed under the Apache License, Version 2.0; see `Li2Lean/Vendor/PNT/LICENSE` and `Li2Lean/Vendor/PNT/NOTICE`.
Modifications by the Li2Lean project:
- added this header; declaration names and proof content otherwise unchanged
-/

namespace Function

variable {α : Type*} [Zero α]

theorem support_id : support (id : α → α) = {0}ᶜ := by
  ext; simp

theorem support_id' {α : Type*} [Zero α] : support (fun x : α ↦ x) = {0}ᶜ :=
  support_id

end Function
