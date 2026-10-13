/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.ScaledLucas.Entries

/-!
# Seed-to-tower certificate for the `a = 2` P0 nonvanishing tower

The matrix-level Lucas transport `p0A2ScaledMatrixLucas` closes
`p0A2ScaledMatrixLucasObligation`; with the exact rational scaled determinant
identity and the seed residue `30` this fills every field of
`P0A2SeedToTowerCertificate`, giving `p0A2_nonvanishing` unconditionally.
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

/-! ## Matrix-level transport -/

theorem rbm_apply {n : ℕ} {R : Type*} [CommRing R]
    (S : Matrix (Fin n) (Fin n) R) (c : R) (q : ℕ)
    (a b : Fin n) (v w : Fin q) :
    residueBlockMatrix S c q (finProdFinEquiv (a, v)) (finProdFinEquiv (b, w)) =
      if v = w then c ^ v.val * S a b else 0 := by
  simp only [residueBlockMatrix, Matrix.reindex_apply, Matrix.submatrix_apply,
    Equiv.symm_apply_apply, Matrix.blockDiagonal_apply]
  split_ifs with h
  · subst h
    rfl
  · rfl

theorem scaledQ_apply (k : ℕ) (r : ℚ) (row col : Fin (2 * (32 * 83 ^ k))) :
    p0A2ScaledMatrixQ k r row col =
      if row.val < 32 * 83 ^ k then
        qRat k * p0CQ (2 : ℚ) (16 * 83 ^ k) (8 * 83 ^ k + row.val) col.val
      else
        (qRat k) ^ 2 * p0BQ (2 : ℚ) (16 * 83 ^ k)
            (8 * 83 ^ k + (row.val - 32 * 83 ^ k)) col.val -
          ((qRat k) ^ 2 * r) *
            p0AQ (2 : ℚ) (16 * 83 ^ k) (8 * 83 ^ k + (row.val - 32 * 83 ^ k))
              col.val := by
  unfold p0A2ScaledMatrixQ
  by_cases h : row.val < 32 * 83 ^ k
  · simp only [h, if_true]
  · simp only [h, if_false]

theorem cast_qRat_pos (k : ℕ) (hk : 0 < k) : ((qRat k : ℚ) : F83) = 0 := by
  rw [qRat_eq, Rat.cast_natCast, Nat.cast_pow]
  have h83 : ((83 : ℕ) : F83) = 0 := ZMod.natCast_self 83
  rw [h83, zero_pow (Nat.pos_iff_ne_zero.mp hk)]

theorem cast_scale_arg (k : ℕ) (r : ℚ) (hbound : r.den < 83 ^ k) (hk : 0 < k) :
    (((qRat k) ^ 2 * r : ℚ) : F83) = 0 := by
  rw [show (qRat k) ^ 2 * r = qRat k * (qRat k * r) by ring,
    cast_mul' (qRat_good k) (q_mul_rat_good k r hbound), cast_qRat_pos k hk,
    zero_mul]

theorem seed_entry (a b : Fin 64) :
    ((sourceSeedQ a b : ℚ) : F83) =
      if a.val < 32 then YC (8 + a.val) b.val else YB (8 + (a.val - 32)) b.val := by
  unfold sourceSeedQ
  by_cases h : a.val < 32
  · rw [if_pos h, if_pos h, seedC _ _ (by omega) b.isLt]
  · rw [if_neg h, if_neg h, seedB _ _ (by omega) b.isLt]

theorem scaled_entry (k : ℕ) (r : ℚ) (hbound : r.den < 83 ^ k) (hk : 0 < k)
    (a b : Fin 64) (v w : Fin (83 ^ k))
    (row col : Fin (2 * (32 * 83 ^ k)))
    (hrow : row.val = v.val + 83 ^ k * a.val)
    (hcol : col.val = w.val + 83 ^ k * b.val) :
    ((p0A2ScaledMatrixQ k r row col : ℚ) : F83) =
      if v = w then (2 : F83) ^ v.val * ((sourceSeedQ a b : ℚ) : F83) else 0 := by
  have hq : 0 < 83 ^ k := by positivity
  have hv := v.isLt
  have hw := w.isLt
  have ha := a.isLt
  have hb := b.isLt
  have hcol' : col.val = b.val * 83 ^ k + w.val := by rw [hcol]; ring
  have hvw : (v = w) ↔ (v.val = w.val) := Fin.val_inj.symm
  rw [scaledQ_apply, seed_entry, hcol']
  by_cases ha32 : a.val < 32
  · have hlt : row.val < 32 * 83 ^ k := by
      rw [hrow]
      have := ar_lt a.val v.val (83 ^ k) 32 ha32 hv
      have h' : a.val * 83 ^ k = 83 ^ k * a.val := by ring
      omega
    rw [if_pos hlt, if_pos ha32]
    have hidx : 8 * 83 ^ k + row.val = (8 + a.val) * 83 ^ k + v.val := by
      rw [hrow]; ring
    rw [hidx, EC k (8 + a.val) b.val v.val w.val (by omega) hb hv hw]
    by_cases h : v = w
    · rw [if_pos (hvw.mp h), if_pos h]
    · rw [if_neg (fun h' => h (hvw.mpr h')), if_neg h]
  · have hge : ¬ row.val < 32 * 83 ^ k := by
      rw [hrow]
      have h1 : 32 * 83 ^ k ≤ a.val * 83 ^ k := Nat.mul_le_mul_right _ (by omega)
      have h' : a.val * 83 ^ k = 83 ^ k * a.val := by ring
      omega
    rw [if_neg hge, if_neg ha32]
    have hidx : 8 * 83 ^ k + (row.val - 32 * 83 ^ k) =
        (8 + (a.val - 32)) * 83 ^ k + v.val := by
      rw [hrow]
      obtain ⟨a', ha'⟩ : ∃ a', a.val = a' + 32 := ⟨a.val - 32, by omega⟩
      rw [ha', show a' + 32 - 32 = a' by omega]
      have h1 : 83 ^ k * (a' + 32) = 83 ^ k * a' + 32 * 83 ^ k := by ring
      have h2 : (8 + a') * 83 ^ k = 8 * 83 ^ k + 83 ^ k * a' := by ring
      rw [h1, h2]
      omega
    have hA : 8 + (a.val - 32) < 40 := by omega
    have hiA : (8 + (a.val - 32)) * 83 ^ k + v.val < 83 * 83 ^ k :=
      ar_lt83 _ _ 40 (ar_lt _ _ _ 40 hA hv) (by norm_num)
    have hjb : b.val * 83 ^ k + w.val < 83 * 83 ^ k :=
      ar_lt83 _ _ 64 (ar_lt _ _ _ 64 hb hw) (by norm_num)
    have hg : 16 * 83 ^ k < 83 * 83 ^ k := by qomega
    rw [hidx,
      cast_sub' (q_sq_mul_p0BQ_good k _ _ _ hg hiA hjb)
        (Good83.mul_mem (q_sq_mul_rat_good k r hbound) (p0AQ_good _ _ _)),
      cast_mul' (q_sq_mul_rat_good k r hbound) (p0AQ_good _ _ _),
      cast_scale_arg k r hbound hk, zero_mul, sub_zero,
      EB k (8 + (a.val - 32)) b.val v.val w.val hA hb hv hw]
    by_cases h : v = w
    · rw [if_pos (hvw.mp h), if_pos h]
    · rw [if_neg (fun h' => h (hvw.mpr h')), if_neg h]

/-- The full-range entrywise Lucas transport of the scaled `a = 2` pencil:
the reduction of the actual Good83-scaled matrix is the residue block matrix
of the literal 64-by-64 source seed, for every `k > 0` and every rational
argument with `r.den < 83^k`. -/
theorem p0A2ScaledMatrixLucas (k : ℕ) (r : ℚ) (hbound : r.den < 83 ^ k)
    (hk : 0 < k) : p0A2ScaledMatrixLucasObligation k r hbound hk := by
  unfold p0A2ScaledMatrixLucasObligation
  ext row col
  obtain ⟨⟨a, v⟩, rfl⟩ := finProdFinEquiv.surjective row
  obtain ⟨⟨b, w⟩, rfl⟩ := finProdFinEquiv.surjective col
  rw [rbm_apply]
  unfold p0A2ScaledMatrixResidue
  rw [Matrix.reindex_apply, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
    Matrix.map_apply]
  change ((p0A2ScaledMatrixQ k r _ _ : ℚ) : F83) = _
  rw [scaled_entry k r hbound hk a b v w _ _
    (by simp [finProdFinEquiv_apply_val]) (by simp [finProdFinEquiv_apply_val])]
  by_cases h : v = w
  · rw [if_pos h, if_pos h]
    rfl
  · rw [if_neg h, if_neg h]

/-! ## Instantiating the seed-to-tower certificate -/

theorem cast_pow' {x : ℚ} (hx : x ∈ Good83) (n : ℕ) :
    ((x ^ n : ℚ) : F83) = (x : F83) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [pow_succ, cast_mul' (Good83.pow_mem hx n) hx, ih, pow_succ]

theorem p0A2_frobenius_field {F : P0Family} (hbase : F.a = 2) :
    ∀ r : ℚ, ∃ k₁, ∀ k : ℕ, k₁ ≤ k →
      ∃ lhs rhs : ContourKit.ReducedRational 83,
        lhs.value = (83 ^ k : ℚ) ^ (3 * 32 * 83 ^ k) *
          p0SourceEvalQ F (32 * 83 ^ k) r ∧
        rhs.value = (p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r)) ^ (83 ^ k) ∧
        lhs.residue = rhs.residue ∧
        (∀ s : ContourKit.ReducedRational 83,
          s.value = p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r) →
            rhs.residue = s.residue ^ (83 ^ k)) := by
  intro r
  refine ⟨r.den, fun k hk => ?_⟩
  have hbound : r.den < 83 ^ k :=
    lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 83))
      (Nat.pow_le_pow_right (by norm_num) hk)
  have hk0 : 0 < k := by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h
      have := Nat.pos_of_ne_zero r.den_nz
      simp at hbound
    · exact h
  let D : Good83 := Matrix.det (p0A2ScaledMatrixGood k r hbound)
  have hDval : (D : ℚ) = (83 ^ k : ℚ) ^ (3 * 32 * 83 ^ k) *
      p0SourceEvalQ F (32 * 83 ^ k) r := by
    change ((Matrix.det (p0A2ScaledMatrixGood k r hbound) : Good83) : ℚ) = _
    rw [p0A2ScaledMatrixGood_det_value, p0A2ScaledMatrix_det_eq_source_eval hbase,
      qRat_eq, show 3 * 32 * 83 ^ k = 3 * (32 * 83 ^ k) by ring]
    norm_num
  let x : ℚ := p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r)
  have hx : x ∈ Good83 :=
    Li2Lean.p0A2_source_eval_good hbase _ (p0ScaleArg_good r k hbound)
  have hxres : ((x : ℚ) : F83) = ((p0SourceEvalQ F 32 0 : ℚ) : F83) := by
    have hmod := Li2Lean.p0A2_eval_residue_zero hbase r k hbound
    change ((p0SourceEvalQ F 32 (p0ScaleArg r k) : ℚ) : F83) =
      ((p0SourceEvalQ F 32 0 : ℚ) : F83) at hmod
    exact hmod
  have hDc : Nat.Coprime (D : ℚ).den 83 := by
    have h := D.property
    change Nat.Coprime _ 83 at h
    exact h
  have hxc : Nat.Coprime (x ^ (83 ^ k)).den 83 := by
    have h := Good83.pow_mem hx (83 ^ k)
    change Nat.Coprime _ 83 at h
    exact h
  have hxc1 : Nat.Coprime x.den 83 := by
    have h := hx
    change Nat.Coprime _ 83 at h
    exact h
  let lhs := reducedOf (D : ℚ) hDc
  let rhs := reducedOf (x ^ (83 ^ k)) hxc
  have hrhs : rhs.residue = ((p0SourceEvalQ F 32 0 : ℚ) : F83) ^ (83 ^ k) := by
    change residueOf (x ^ (83 ^ k)) hxc = _
    rw [residueOf_eq_cast, cast_pow' hx, hxres]
  refine ⟨lhs, rhs, hDval, rfl, ?_, ?_⟩
  · have hlucas := p0A2ScaledMatrix_det_residue_of_lucas k r hbound hk0
      (p0A2ScaledMatrixLucas k r hbound hk0)
    have hseed : Matrix.det p0A2SourceSeedResidue =
        ((p0SourceEvalQ F 32 0 : ℚ) : F83) := by
      unfold p0A2SourceSeedResidue
      rw [← RingHom.map_det]
      change (((Matrix.det sourceSeedGood : Good83) : ℚ) : F83) = _
      rw [sourceSeedGood_det_coe, ← p0A2_sourceSeedQ_det_value hbase]
    change residueOf (D : ℚ) hDc = _
    rw [residueOf_eq_cast, hrhs]
    change residueHom D = _
    rw [hlucas, hseed]
  · intro s hs
    have hsx : s.residue = ((x : ℚ) : F83) := by
      have h := reducedRational_residue_eq_of_value_eq
        (x := s) (y := reducedOf x hxc1) hs
      rw [h]
      change residueOf x hxc1 = _
      rw [residueOf_eq_cast]
    rw [hsx, hrhs, hxres]

/-- The seed-to-tower certificate for every `a = 2` P0 family, with all
fields proved. -/
def p0A2SeedToTowerCertificateOfBase (F : P0Family) (hbase : F.a = 2) :
    P0A2SeedToTowerCertificate F where
  base_is_two := hbase
  seed := p0A2SourceEvalReduced F hbase
  seed_value := p0A2SourceEvalReduced_value F hbase
  seed_residue_eq_30 := p0A2SourceEvalReduced_residue_eq_30 F hbase
  frobenius := p0A2_frobenius_field hbase

/-- Unconditional fixed-base nonvanishing on the tower `m = 32 * 83^k`. -/
theorem p0A2_nonvanishing (F : P0Family) : P0A2NonvanishingStatement F :=
  fun ha => p0A2SeedToTower_nonvanishing
    (p0A2SeedToTowerCertificateOfBase F ha) ha

end

end ScaledLucas
end Li2Lean.P0
