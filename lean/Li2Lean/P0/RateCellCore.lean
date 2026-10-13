/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateResidueCount

/-!
# Exact residue-cell geometry for a fixed prime-ratio interval

For `4 ∣ m`, a prime `p` and `ρ = p/m` in an open interval `(lo, hi)`, the
four residue thresholds of v13

* `α = (m/4) mod p`, `β = (5m/4) mod p`, `γ = (2m) mod p`,
* `τ = p - (m/2 mod p)` (the carry threshold),

are affine forms `c₀ m + c₁ p` once the four floors are fixed, and their order
is fixed.  A finite rational check (`RCell.ok`) certifies the floors and the
order from the interval endpoints alone.  Soundness turns every residue sum into
an exact sum over the five residue groups with affine integer widths.
-/

namespace Li2Lean.P0.Integerization

open Finset

/-- The affine form `c0 * m + c1 * p`. -/
structure RAff where
  c0 : ℚ
  c1 : ℚ
  deriving DecidableEq

namespace RAff

/-- Value at the ratio `ρ = p / m`, normalized by `m`. -/
def ev (L : RAff) (ρ : ℚ) : ℚ := L.c0 + L.c1 * ρ

/-- Value at `(m, p)`. -/
def val (L : RAff) (m p : ℚ) : ℚ := L.c0 * m + L.c1 * p

instance : Add RAff := ⟨fun a b => ⟨a.c0 + b.c0, a.c1 + b.c1⟩⟩
instance : Sub RAff := ⟨fun a b => ⟨a.c0 - b.c0, a.c1 - b.c1⟩⟩
instance : Zero RAff := ⟨⟨0, 0⟩⟩

/-- Scalar multiple. -/
def smul (z : ℚ) (a : RAff) : RAff := ⟨z * a.c0, z * a.c1⟩

@[simp] theorem val_add (a b : RAff) (m p : ℚ) : (a + b).val m p = a.val m p + b.val m p := by
  show (a.c0 + b.c0) * m + (a.c1 + b.c1) * p = _
  unfold val; ring

@[simp] theorem val_sub (a b : RAff) (m p : ℚ) : (a - b).val m p = a.val m p - b.val m p := by
  show (a.c0 - b.c0) * m + (a.c1 - b.c1) * p = _
  unfold val; ring

@[simp] theorem val_zero (m p : ℚ) : (0 : RAff).val m p = 0 := by
  show (0 : ℚ) * m + 0 * p = 0
  ring

@[simp] theorem val_smul (z : ℚ) (a : RAff) (m p : ℚ) : (smul z a).val m p = z * a.val m p := by
  unfold smul val; ring

theorem val_mk (c0 c1 m p : ℚ) : (⟨c0, c1⟩ : RAff).val m p = c0 * m + c1 * p := rfl

/-- Nonnegative at both interval endpoints. -/
def nonnegOn (L : RAff) (lo hi : ℚ) : Bool :=
  decide (0 ≤ L.ev lo) && decide (0 ≤ L.ev hi)

/-- Nonnegative at both endpoints and positive at one of them. -/
def posOpen (L : RAff) (lo hi : ℚ) : Bool :=
  L.nonnegOn lo hi && (decide (0 < L.ev lo) || decide (0 < L.ev hi))

theorem nonneg_of_nonnegOn (L : RAff) {lo hi m p : ℚ} (hm : 0 < m)
    (hlo : lo * m ≤ p) (hhi : p ≤ hi * m) (h : L.nonnegOn lo hi = true) :
    0 ≤ L.val m p := by
  simp only [nonnegOn, Bool.and_eq_true, ev] at h
  obtain ⟨h1, h2⟩ := h
  have h1 := of_decide_eq_true h1
  have h2 := of_decide_eq_true h2
  unfold val
  rcases le_or_gt 0 L.c1 with hc | hc
  · have := mul_le_mul_of_nonneg_left hlo hc
    nlinarith [mul_nonneg hm.le h1]
  · have := mul_le_mul_of_nonpos_left hhi hc.le
    nlinarith [mul_nonneg hm.le h2]

theorem pos_of_posOpen (L : RAff) {lo hi m p : ℚ} (hm : 0 < m)
    (hlo : lo * m < p) (hhi : p < hi * m) (h : L.posOpen lo hi = true) :
    0 < L.val m p := by
  simp only [posOpen, nonnegOn, Bool.and_eq_true, Bool.or_eq_true, ev] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have h1 := of_decide_eq_true h1
  have h2 := of_decide_eq_true h2
  have h3 : 0 < L.c0 + L.c1 * lo ∨ 0 < L.c0 + L.c1 * hi :=
    h3.imp of_decide_eq_true of_decide_eq_true
  unfold val
  rcases lt_trichotomy L.c1 0 with hc | hc | hc
  · have := mul_lt_mul_of_neg_left hhi hc
    nlinarith [mul_nonneg hm.le h2]
  · rw [hc] at h3 ⊢
    rcases h3 with h3 | h3
    · nlinarith [mul_pos hm h3]
    · nlinarith [mul_pos hm h3]
  · have := mul_lt_mul_of_pos_left hlo hc
    nlinarith [mul_nonneg hm.le h1]

end RAff

/-- The four affine thresholds `α, β, γ, τ` for the floors `A, B, C, Q`. -/
def p0ThrAff (A B C Q : ℕ) : Fin 4 → RAff :=
  ![⟨1 / 4, -(A : ℚ)⟩, ⟨5 / 4, -(B : ℚ)⟩, ⟨2, -(C : ℚ)⟩, ⟨-1 / 2, (Q : ℚ) + 1⟩]

/-- The actual integer thresholds. -/
def p0Thr (m p : ℕ) : Fin 4 → ℕ :=
  ![(m / 4) % p, (m / 4 + m) % p, (2 * m) % p, p - (m / 2) % p]

/-- A certified residue cell: an interval, its floors, and the sorted order of
its thresholds (`perm j` is the threshold in sorted position `j`). -/
structure RCell where
  lo : ℚ
  hi : ℚ
  A : ℕ
  B : ℕ
  C : ℕ
  Q : ℕ
  perm : Fin 4 → Fin 4
  deriving DecidableEq

namespace RCell

/-- Sorted cut points `0 = S₀ ≤ S₁ ≤ … ≤ S₄ ≤ S₅ = p`. -/
def S (c : RCell) : Fin 6 → RAff :=
  ![0, p0ThrAff c.A c.B c.C c.Q (c.perm 0), p0ThrAff c.A c.B c.C c.Q (c.perm 1),
    p0ThrAff c.A c.B c.C c.Q (c.perm 2), p0ThrAff c.A c.B c.C c.Q (c.perm 3), ⟨0, 1⟩]

/-- Width of residue group `g`. -/
def width (c : RCell) (g : Fin 5) : RAff := c.S g.succ - c.S g.castSucc

/-- Bit pattern of group `g`: threshold `k` lies above the group. -/
def pattern (c : RCell) (g : Fin 5) (k : Fin 4) : Bool :=
  decide (∃ j : Fin 4, g.val ≤ j.val ∧ c.perm j = k)

/-- Rational certificate for the floors and the threshold order. -/
def ok (c : RCell) : Bool :=
  decide (0 < c.lo) && decide (c.lo < c.hi) &&
  (⟨1 / 4, -(c.A : ℚ)⟩ : RAff).nonnegOn c.lo c.hi &&
  (⟨-(1 / 4), (c.A : ℚ) + 1⟩ : RAff).posOpen c.lo c.hi &&
  (⟨5 / 4, -(c.B : ℚ)⟩ : RAff).nonnegOn c.lo c.hi &&
  (⟨-(5 / 4), (c.B : ℚ) + 1⟩ : RAff).posOpen c.lo c.hi &&
  (⟨2, -(c.C : ℚ)⟩ : RAff).nonnegOn c.lo c.hi &&
  (⟨-2, (c.C : ℚ) + 1⟩ : RAff).posOpen c.lo c.hi &&
  (⟨1 / 2, -(c.Q : ℚ)⟩ : RAff).nonnegOn c.lo c.hi &&
  (⟨-(1 / 2), (c.Q : ℚ) + 1⟩ : RAff).posOpen c.lo c.hi &&
  decide (∀ k : Fin 4, ∃ j : Fin 4, c.perm j = k) &&
  decide (∀ a b : Fin 6, a ≤ b → (c.S b - c.S a).nonnegOn c.lo c.hi = true)

end RCell

/-- Actual sorted cut points. -/
def p0CutAct (c : RCell) (m p : ℕ) : Fin 6 → ℕ :=
  ![0, p0Thr m p (c.perm 0), p0Thr m p (c.perm 1), p0Thr m p (c.perm 2),
    p0Thr m p (c.perm 3), p]

section Sound

variable {c : RCell} {m p : ℕ}

theorem p0_floor_of_aff {N A : ℕ} {x lo hi : ℚ} {m p : ℕ}
    (hm : 0 < (m : ℚ)) (hlo : lo * m < p) (hhi : p < hi * m)
    (hN : (N : ℚ) = x * m)
    (h1 : (⟨x, -(A : ℚ)⟩ : RAff).nonnegOn lo hi = true)
    (h2 : (⟨-x, (A : ℚ) + 1⟩ : RAff).posOpen lo hi = true) :
    N / p = A := by
  have e1 := RAff.nonneg_of_nonnegOn _ hm hlo.le hhi.le h1
  have e2 := RAff.pos_of_posOpen _ hm hlo hhi h2
  simp only [RAff.val_mk] at e1 e2
  have hp : (0 : ℚ) < p := by
    rcases Nat.eq_zero_or_pos p with h | h
    · subst h
      have : (0 : ℚ) < ((A : ℚ) + 1) * 0 + -x * m := by simpa using e2
      nlinarith
    · exact_mod_cast h
  have hle : (A : ℚ) * p ≤ N := by rw [hN]; linarith
  have hlt : (N : ℚ) < ((A : ℚ) + 1) * p := by rw [hN]; linarith
  have hle' : A * p ≤ N := by exact_mod_cast hle
  have hlt' : N < (A + 1) * p := by exact_mod_cast hlt
  exact Nat.div_eq_of_lt_le hle' hlt'

theorem p0Cell_floors (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) :
    m / 4 / p = c.A ∧ (m / 4 + m) / p = c.B ∧ 2 * m / p = c.C ∧ m / 2 / p = c.Q := by
  simp only [RCell.ok, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, _⟩, hA1⟩, hA2⟩, hB1⟩, hB2⟩, hC1⟩, hC2⟩, hQ1⟩, hQ2⟩, _⟩, _⟩ := hc
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  obtain ⟨t, rfl⟩ := h4
  have e4 : 4 * t / 4 = t := by omega
  have e2 : 4 * t / 2 = 2 * t := by omega
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact p0_floor_of_aff hmQ hlo hhi (by rw [e4]; push_cast; ring) hA1 hA2
  · exact p0_floor_of_aff hmQ hlo hhi (by rw [e4]; push_cast; ring) hB1 hB2
  · exact p0_floor_of_aff hmQ hlo hhi (by push_cast; ring) hC1 hC2
  · exact p0_floor_of_aff hmQ hlo hhi (by rw [e2]; push_cast; ring) hQ1 hQ2

/-- The actual thresholds are the affine thresholds. -/
theorem p0Cell_thr_val (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (k : Fin 4) :
    ((p0Thr m p k : ℕ) : ℚ) = (p0ThrAff c.A c.B c.C c.Q k).val m p := by
  obtain ⟨hA, hB, hC, hQ⟩ := p0Cell_floors hc h4 hm hlo hhi
  obtain ⟨t, rfl⟩ := h4
  have e4 : 4 * t / 4 = t := by omega
  have e2 : 4 * t / 2 = 2 * t := by omega
  rw [e4] at hA hB
  rw [e2] at hQ
  have dA := Nat.div_add_mod t p
  have dB := Nat.div_add_mod (t + 4 * t) p
  have dC := Nat.div_add_mod (2 * (4 * t)) p
  have dQ := Nat.div_add_mod (2 * t) p
  rw [hA] at dA
  rw [hB] at dB
  rw [hC] at dC
  rw [hQ] at dQ
  have hlt : (2 * t) % p ≤ p := (Nat.mod_lt _ hp).le
  have qA : (((t % p : ℕ)) : ℚ) = t - c.A * p := by
    have : ((p * c.A + t % p : ℕ) : ℚ) = t := by exact_mod_cast dA
    push_cast at this; linarith
  have qB : (((t + 4 * t) % p : ℕ) : ℚ) = 5 * t - c.B * p := by
    have : ((p * c.B + (t + 4 * t) % p : ℕ) : ℚ) = (t + 4 * t : ℕ) := by exact_mod_cast dB
    push_cast at this; linarith
  have qC : (((2 * (4 * t)) % p : ℕ) : ℚ) = 8 * t - c.C * p := by
    have : ((p * c.C + (2 * (4 * t)) % p : ℕ) : ℚ) = (2 * (4 * t) : ℕ) := by exact_mod_cast dC
    push_cast at this; linarith
  have qQ : (((p - (2 * t) % p : ℕ)) : ℚ) = p - 2 * t + c.Q * p := by
    rw [Nat.cast_sub hlt]
    have : ((p * c.Q + (2 * t) % p : ℕ) : ℚ) = (2 * t : ℕ) := by exact_mod_cast dQ
    push_cast at this ⊢; linarith
  fin_cases k <;> simp [p0Thr, p0ThrAff, RAff.val, e4, e2, qA, qB, qC, qQ] <;> ring


theorem p0Cell_ok_parts (hc : c.ok = true) :
    0 < c.lo ∧ (∀ k : Fin 4, ∃ j : Fin 4, c.perm j = k) ∧
      (∀ a b : Fin 6, a ≤ b → (c.S b - c.S a).nonnegOn c.lo c.hi = true) := by
  simp only [RCell.ok, Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hperm⟩, hsort⟩ := hc
  exact ⟨of_decide_eq_true h0, of_decide_eq_true hperm, of_decide_eq_true hsort⟩

theorem p0CutAct_thr (c : RCell) (m p : ℕ) (j : Fin 4) :
    p0CutAct c m p ⟨j.val + 1, by omega⟩ = p0Thr m p (c.perm j) := by
  fin_cases j <;> rfl

theorem p0CutAct_zero (c : RCell) (m p : ℕ) : p0CutAct c m p 0 = 0 := rfl
theorem p0CutAct_last (c : RCell) (m p : ℕ) : p0CutAct c m p 5 = p := rfl

theorem p0Cell_cut_val (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (g : Fin 6) :
    ((p0CutAct c m p g : ℕ) : ℚ) = (c.S g).val m p := by
  have ht := p0Cell_thr_val hc h4 hm hp hlo hhi
  fin_cases g
  · simp [p0CutAct, RCell.S]
  · simpa [p0CutAct, RCell.S] using ht (c.perm 0)
  · simpa [p0CutAct, RCell.S] using ht (c.perm 1)
  · simpa [p0CutAct, RCell.S] using ht (c.perm 2)
  · simpa [p0CutAct, RCell.S] using ht (c.perm 3)
  · simp [p0CutAct, RCell.S, RAff.val]

theorem p0Cell_cut_mono (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) {a b : Fin 6} (hab : a ≤ b) :
    p0CutAct c m p a ≤ p0CutAct c m p b := by
  obtain ⟨_, _, hsort⟩ := p0Cell_ok_parts hc
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have h := RAff.nonneg_of_nonnegOn _ hmQ hlo.le hhi.le (hsort a b hab)
  rw [RAff.val_sub, ← p0Cell_cut_val hc h4 hm hp hlo hhi,
    ← p0Cell_cut_val hc h4 hm hp hlo hhi] at h
  have : ((p0CutAct c m p a : ℕ) : ℚ) ≤ p0CutAct c m p b := by linarith
  exact_mod_cast this

/-- Inside group `g` every residue has the bit pattern of `g`. -/
theorem p0Cell_bits (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (g : Fin 5) (v : ℕ)
    (hv1 : p0CutAct c m p g.castSucc ≤ v) (hv2 : v < p0CutAct c m p g.succ) (k : Fin 4) :
    decide (v < p0Thr m p k) = c.pattern g k := by
  obtain ⟨_, hperm, _⟩ := p0Cell_ok_parts hc
  have hsurj : Function.Surjective c.perm := hperm
  have hinj : Function.Injective c.perm := Finite.injective_iff_surjective.mpr hsurj
  obtain ⟨j, hj⟩ := hsurj k
  have hcut := p0CutAct_thr c m p j
  rw [hj] at hcut
  have mono := fun {a b : Fin 6} (h : a ≤ b) => p0Cell_cut_mono hc h4 hm hp hlo hhi h
  by_cases hgj : g.val ≤ j.val
  · have hle : g.succ ≤ (⟨j.val + 1, by omega⟩ : Fin 6) := by
      simp [Fin.le_def]; omega
    have h1 := mono hle
    rw [hcut] at h1
    have hlt : v < p0Thr m p k := lt_of_lt_of_le hv2 h1
    have hpat : c.pattern g k = true := by
      simp only [RCell.pattern, decide_eq_true_eq]
      exact ⟨j, hgj, hj⟩
    rw [hpat]
    simpa using hlt
  · have hle : (⟨j.val + 1, by omega⟩ : Fin 6) ≤ g.castSucc := by
      simp [Fin.le_def]; omega
    have h1 := mono hle
    rw [hcut] at h1
    have hge : ¬ v < p0Thr m p k := by omega
    have hpat : c.pattern g k = false := by
      simp only [RCell.pattern, decide_eq_false_iff_not, not_exists, not_and]
      intro j' hj' hj'k
      have : j' = j := hinj (hj'k.trans hj.symm)
      subst this
      exact hgj hj'
    rw [hpat]
    simpa using hge

/-- Exact group decomposition of a residue sum. -/
theorem p0Cell_group_sum (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (ψ : ℕ → ℤ) (Ψ : Fin 5 → ℤ)
    (h : ∀ g : Fin 5, ∀ v, p0CutAct c m p g.castSucc ≤ v → v < p0CutAct c m p g.succ →
      ψ v = Ψ g) :
    ∑ v ∈ range p, ψ v =
      ∑ g : Fin 5, (((p0CutAct c m p g.succ : ℕ) : ℤ) - p0CutAct c m p g.castSucc) * Ψ g := by
  have mono := fun {a b : Fin 6} (h : a ≤ b) => p0Cell_cut_mono hc h4 hm hp hlo hhi h
  set S := p0CutAct c m p
  have hgroup : ∀ g : Fin 5, ∑ v ∈ Ico (S g.castSucc) (S g.succ), ψ v =
      (((S g.succ : ℕ) : ℤ) - S g.castSucc) * Ψ g := by
    intro g
    rw [Finset.sum_congr rfl (fun v hv => h g v (Finset.mem_Ico.mp hv).1 (Finset.mem_Ico.mp hv).2),
      Finset.sum_const, Nat.card_Ico, nsmul_eq_mul]
    have hle : S g.castSucc ≤ S g.succ := mono (Fin.castSucc_le_succ g)
    push_cast [hle]
    ring
  have h01 : S 0 ≤ S 1 := mono (by decide)
  have h12 : S 1 ≤ S 2 := mono (by decide)
  have h23 : S 2 ≤ S 3 := mono (by decide)
  have h34 : S 3 ≤ S 4 := mono (by decide)
  have h45 : S 4 ≤ S 5 := mono (by decide)
  have hr : range p = Ico (S 0) (S 5) := by
    rw [Finset.range_eq_Ico]
    rfl
  have e0 : ∑ v ∈ Ico (S 0) (S 1), ψ v = (((S 1 : ℕ) : ℤ) - S 0) * Ψ 0 := hgroup 0
  have e1 : ∑ v ∈ Ico (S 1) (S 2), ψ v = (((S 2 : ℕ) : ℤ) - S 1) * Ψ 1 := hgroup 1
  have e2 : ∑ v ∈ Ico (S 2) (S 3), ψ v = (((S 3 : ℕ) : ℤ) - S 2) * Ψ 2 := hgroup 2
  have e3 : ∑ v ∈ Ico (S 3) (S 4), ψ v = (((S 4 : ℕ) : ℤ) - S 3) * Ψ 3 := hgroup 3
  have e4 : ∑ v ∈ Ico (S 4) (S 5), ψ v = (((S 5 : ℕ) : ℤ) - S 4) * Ψ 4 := hgroup 4
  rw [hr, ← Finset.sum_Ico_consecutive _ h01 (h12.trans (h23.trans (h34.trans h45))),
    ← Finset.sum_Ico_consecutive _ h12 (h23.trans (h34.trans h45)),
    ← Finset.sum_Ico_consecutive _ h23 (h34.trans h45),
    ← Finset.sum_Ico_consecutive _ h34 h45, Fin.sum_univ_five, e0, e1, e2, e3, e4]
  show _ = (((S 1 : ℕ) : ℤ) - S 0) * Ψ 0 + (((S 2 : ℕ) : ℤ) - S 1) * Ψ 1 +
    (((S 3 : ℕ) : ℤ) - S 2) * Ψ 2 + (((S 4 : ℕ) : ℤ) - S 3) * Ψ 3 +
    (((S 5 : ℕ) : ℤ) - S 4) * Ψ 4
  ring

/-- Each residue `v < p` lies in exactly one group. -/
theorem p0Cell_group_exists (hc : c.ok = true) (h4 : 4 ∣ m) (hm : 0 < m) (hp : 0 < p)
    (hlo : c.lo * m < p) (hhi : p < c.hi * m) (v : ℕ) (hv : v < p) :
    ∃ g : Fin 5, p0CutAct c m p g.castSucc ≤ v ∧ v < p0CutAct c m p g.succ := by
  have mono := fun {a b : Fin 6} (h : a ≤ b) => p0Cell_cut_mono hc h4 hm hp hlo hhi h
  set S := p0CutAct c m p
  have h5 : S 5 = p := rfl
  have h0 : S 0 = 0 := rfl
  by_cases g1 : v < S 1
  · exact ⟨0, by simp [h0], g1⟩
  by_cases g2 : v < S 2
  · exact ⟨1, by simpa using not_lt.mp g1, g2⟩
  by_cases g3 : v < S 3
  · exact ⟨2, by simpa using not_lt.mp g2, g3⟩
  by_cases g4 : v < S 4
  · exact ⟨3, by simpa using not_lt.mp g3, g4⟩
  · exact ⟨4, by simpa using not_lt.mp g4, by simpa [h5] using hv⟩

end Sound

end Li2Lean.P0.Integerization
