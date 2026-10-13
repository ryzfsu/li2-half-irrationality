/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.Statement
import Li2Lean.LayerInterfaces
import Li2Lean.P0.Source

namespace Li2Lean

/--
S0 interface for the currently unformalized irrationality results. The exact
status of each field is recorded in `LEDGER.md`; this structure is an explicit
assumption, not an axiom or a proof of the unconditional target.
-/
structure Li2Bridges : Prop where
  /-- The source Mellin and derivative-bank identities, docs/6333 §2. -/
  p0_source : P0SourceBridge
  /-- The `n = 1` case, docs/6404 §1 and docs/6406 §2 (L0). -/
  pos_one : Irrational (li2InvValue (1 : ℤ))
  /-- The `n = -1` case, docs/6404 §1 and docs/6406 §2 (L0). -/
  neg_one : Irrational (li2InvValue (-1 : ℤ))
  /-- The `n = 2` endpoint input, consumed by the L1 criterion. -/
  pos_two : Nonempty (EndpointCertificate (li2InvValue (2 : ℤ)))
  /-- The `n = -2` case, docs/6404 §1 (family V; docs/6013). -/
  neg_two : Irrational (li2InvValue (-2 : ℤ))
  /-- The positive middle range, docs/6404 §§1, 3–4 (P0, 3 <= n <= 11). -/
  pos_middle : ∀ n : ℤ, (3 : ℤ) ≤ n → n ≤ 11 → n ≠ 0 →
    Irrational (li2InvValue n)
  /-- The negative middle range, docs/6404 §§1, 3–5 (P0, -7 <= n <= -3). -/
  neg_middle : ∀ n : ℤ, (-7 : ℤ) ≤ n → n ≤ -3 → n ≠ 0 →
    Irrational (li2InvValue n)
  /-- The positive tail, docs/6404 §§1, 5 (HP tail, threshold n >= 12). -/
  pos_tail : ∀ n : ℤ, (12 : ℤ) ≤ n → n ≠ 0 → Irrational (li2InvValue n)
  /-- The negative tail, docs/6404 §§1, 5 (HP tail, threshold n <= -8). -/
  neg_tail : ∀ n : ℤ, n ≤ (-8 : ℤ) → n ≠ 0 → Irrational (li2InvValue n)

end Li2Lean
