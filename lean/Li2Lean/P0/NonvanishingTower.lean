/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Nonvanishing
import Li2Lean.P0.ControlledResidue
import Li2Lean.P0.NonvanishingLocalResidue

namespace Li2Lean

noncomputable section

/-- The concrete fixed-base index used by the `a=2`, `p=83` tower. -/
def p0A2TowerIndex (k : ℕ) : ℕ := 32 * 83 ^ k

theorem p0A2TowerIndex_eq (k : ℕ) :
    p0A2TowerIndex k = 32 * 83 ^ k := rfl

theorem p0A2TowerIndex_zero : p0A2TowerIndex 0 = 32 := by
  simp [p0A2TowerIndex]

theorem p0A2TowerIndex_succ (k : ℕ) :
    p0A2TowerIndex (k + 1) = 83 * p0A2TowerIndex k := by
  simp [p0A2TowerIndex, pow_succ]
  ring

theorem p0A2TowerIndex_pos (k : ℕ) : 0 < p0A2TowerIndex k := by
  simp [p0A2TowerIndex]

theorem p0A2TowerIndex_multiple_four (k : ℕ) :
    4 ∣ p0A2TowerIndex k := by
  refine ⟨8 * 83 ^ k, ?_⟩
  simp [p0A2TowerIndex]
  ring

theorem p0A2Tower_prime : Nat.Prime 83 := by norm_num

theorem p0A2SeedResidue30_ne_zero :
    (30 : P0.ControlledResidue.F83) ≠ 0 := by decide

theorem p0A2Tower_cutoff : 2 * 32 + 32 / 2 < 83 := by norm_num

theorem p0A2Tower_index_decompose {k i : ℕ}
    (hi : i < p0A2TowerIndex k) :
    ∃ a v : ℕ, a < 32 ∧ v < 83 ^ k ∧
      i = a * 83 ^ k + v := by
  let q := 83 ^ k
  have hq : 0 < q := by simp [q]
  have hi' : i < 32 * q := by simpa [p0A2TowerIndex, q] using hi
  refine ⟨i / q, i % q, ?_, Nat.mod_lt _ hq, ?_⟩
  · apply Nat.div_lt_of_lt_mul
    simpa [Nat.mul_comm] using hi'
  · calc
      i = q * (i / q) + i % q := (Nat.div_add_mod i q).symm
      _ = (i / q) * 83 ^ k + i % q := by simp [q, Nat.mul_comm]

theorem p0A2_U_lucas
    {k a h v : ℕ} (hv : v < 83 ^ k) :
    (2 ^ (a * 83 ^ k + v) *
      Nat.choose (a * 83 ^ k + v + h * 83 ^ k) (h * 83 ^ k))
      ≡ 2 ^ v * (2 ^ a * Nat.choose (a + h) h) [MOD 83] := by
  exact @p0U_nat_prime_power_modEq 83 a h k v
    ⟨p0A2Tower_prime⟩ hv

theorem p0A2_U_lucas_for_tower_index {k i h : ℕ}
    (hi : i < p0A2TowerIndex k) :
    ∃ a v : ℕ, a < 32 ∧ v < 83 ^ k ∧ i = a * 83 ^ k + v ∧
      (2 ^ i * Nat.choose (i + h * 83 ^ k) (h * 83 ^ k))
        ≡ 2 ^ v * (2 ^ a * Nat.choose (a + h) h) [MOD 83] := by
  obtain ⟨a, v, ha, hv, rfl⟩ := p0A2Tower_index_decompose hi
  refine ⟨a, v, ha, hv, rfl, ?_⟩
  convert p0A2_U_lucas (k := k) (a := a) (h := h) (v := v) hv using 1

/-- A seed-to-tower certificate with the fixed numerical parameters exposed.

The eventual entrywise Frobenius/Lucas transfer remains explicit. The seed
argument is derived below from the finite-place seed value, and the constructor
fills all numerical side conditions and derives seed nonvanishing from `30`. -/
structure P0A2SeedToTowerCertificate (F : P0Family) where
  base_is_two : F.a = 2
  seed : ContourKit.ReducedRational 83
  seed_value : seed.value = p0SourceEvalQ F 32 0
  seed_residue_eq_30 : seed.residue = (30 : ZMod 83)
  frobenius : ∀ r : ℚ, ∃ k₁, ∀ k : ℕ, k₁ ≤ k →
    ∃ lhs rhs : ContourKit.ReducedRational 83,
      lhs.value = (83 ^ k : ℚ) ^ (3 * 32 * 83 ^ k) *
        p0SourceEvalQ F (32 * 83 ^ k) r ∧
      rhs.value = (p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r)) ^ (83 ^ k) ∧
      lhs.residue = rhs.residue ∧
      (∀ s : ContourKit.ReducedRational 83,
        s.value = p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r) →
          rhs.residue = s.residue ^ (83 ^ k))

section P0A2SeedArgument

open P0
private lemma p0A2U_good (i : ℕ) : p0UQ (2 : ℚ) 16 i ∈
    P0.ControlledResidue.Good83 := by
  change (2 : ℚ) ^ i * (Nat.choose (i + 16) 16 : ℚ) ∈
    P0.ControlledResidue.Good83
  apply P0.ControlledResidue.Good83.mul_mem
  · change Nat.Coprime ((2 : ℚ) ^ i).den 83
    norm_num [Rat.den_mul]
  · change Nat.Coprime ((Nat.choose (i + 16) 16 : ℕ) : ℚ).den 83
    simp

private lemma p0A2AQ_good (i j : ℕ) : p0AQ (2 : ℚ) 16 i j ∈
    P0.ControlledResidue.Good83 := by
  unfold p0AQ
  split
  · exact p0A2U_good i
  · exact P0.ControlledResidue.Good83.zero_mem

private def p0A2MatrixGood :
    Matrix (Fin 64) (Fin 64)
      (Polynomial P0.ControlledResidue.Good83) := fun r c =>
  let i := 8 + (if r.val < 32 then r.val else r.val - 32)
  if hr : r.val < 32 then
    Polynomial.C ⟨p0CQ (2 : ℚ) 16 i c.val, by
      have h := P0.ControlledResidue.sourceSeedQ_mem
        (⟨r.val, by omega⟩ : Fin 64) c
      simpa [i, P0.ControlledResidue.sourceSeedQ, hr] using h⟩
  else
    Polynomial.C ⟨p0BQ (2 : ℚ) 16 i c.val, by
      have h := P0.ControlledResidue.sourceSeedQ_mem
        (⟨r.val, by omega⟩ : Fin 64) c
      simpa [i, P0.ControlledResidue.sourceSeedQ, hr] using h⟩ -
    Polynomial.X * Polynomial.C ⟨p0AQ (2 : ℚ) 16 i c.val,
      p0A2AQ_good i c.val⟩

private theorem p0A2MatrixGood_map :
    (Polynomial.mapRingHom P0.ControlledResidue.Good83.subtype).mapMatrix
      p0A2MatrixGood = p0MatrixQ (2 : ℚ) 32 := by
  ext r c
  by_cases hr : r.val < 32 <;>
    simp [p0A2MatrixGood, p0MatrixQ, hr]

private def p0A2PolynomialGood :
    Polynomial P0.ControlledResidue.Good83 := Matrix.det p0A2MatrixGood

private theorem p0A2PolynomialGood_map :
    Polynomial.mapRingHom P0.ControlledResidue.Good83.subtype
      p0A2PolynomialGood = p0CanonicalPolynomial 2 32 := by
  calc
    Polynomial.mapRingHom P0.ControlledResidue.Good83.subtype
        p0A2PolynomialGood =
        Matrix.det ((Polynomial.mapRingHom P0.ControlledResidue.Good83.subtype).mapMatrix
          p0A2MatrixGood) := RingHom.map_det _ _
    _ = (p0MatrixQ (2 : ℚ) 32).det := by rw [p0A2MatrixGood_map]
    _ = p0CanonicalPolynomial 2 32 := by
      simp [p0CanonicalPolynomial, show 4 ∣ (32 : ℕ) by norm_num]

def p0ScaleArg (r : ℚ) (k : ℕ) : ℚ :=
  ((83 ^ k : ℕ) : ℚ) ^ 2 * r

private theorem p0ScaleArg_cross (r : ℚ) (k : ℕ) :
    (p0ScaleArg r k).num.natAbs * r.den =
      83 ^ k * 83 ^ k * r.num.natAbs * (p0ScaleArg r k).den := by
  let z := p0ScaleArg r k
  have hrat : (z.num : ℚ) / (z.den : ℚ) =
      ((83 ^ k : ℕ) : ℚ) ^ 2 * ((r.num : ℚ) / (r.den : ℚ)) := by
    calc
      (z.num : ℚ) / (z.den : ℚ) = z := Rat.num_div_den z
      _ = ((83 ^ k : ℕ) : ℚ) ^ 2 * r := rfl
      _ = ((83 ^ k : ℕ) : ℚ) ^ 2 *
          ((r.num : ℚ) / (r.den : ℚ)) := by rw [Rat.num_div_den r]
  have hcrossQ : (z.num : ℚ) * (r.den : ℚ) =
      ((83 ^ k : ℕ) : ℚ) ^ 2 * (r.num : ℚ) * (z.den : ℚ) := by
    have h := hrat
    field_simp [Rat.den_nz z, Rat.den_nz r] at h
    nlinarith [h]
  have hcrossZ : (z.num : ℤ) * (r.den : ℤ) =
      ((83 ^ k : ℕ) : ℤ) ^ 2 * r.num * (z.den : ℤ) := by
    exact_mod_cast hcrossQ
  have habs := congrArg Int.natAbs hcrossZ
  simpa [z, p0ScaleArg, Int.natAbs_mul, Nat.pow_two, Nat.mul_assoc] using habs

lemma p0SingleScaleArg_good (r : ℚ) (k : ℕ)
    (hbound : r.den < 83 ^ k) :
    ((83 ^ k : ℕ) : ℚ) * r ∈ P0.ControlledResidue.Good83 := by
  let d := r.den
  let p : ℚ := ((83 ^ k : ℕ) : ℚ)
  let t : ℚ := p / (d : ℚ)
  let u : ℚ := (r.num : ℚ)
  have hdpos : 0 < d := by
    dsimp [d]
    exact Nat.pos_of_ne_zero r.den_nz
  have hb : d < 83 * 83 ^ k := by
    have hpow : 1 ≤ 83 ^ k := Nat.one_le_pow _ _ (by norm_num)
    dsimp [d] at *
    omega
  have ht : t ∈ P0.ControlledResidue.Good83 := by
    change Nat.Coprime t.den 83
    dsimp [t, p, d]
    exact P0.ControlledResidue.pow83_div_den_coprime k r.den hdpos hb
  have hu : u ∈ P0.ControlledResidue.Good83 := by
    change Nat.Coprime u.den 83
    simp [u, Rat.den_intCast]
  have hrrepr : r = (r.num : ℚ) / (r.den : ℚ) :=
    (Rat.num_div_den r).symm
  have hscale1 : p * r = t * u := by
    calc
      p * r = p * ((r.num : ℚ) / (r.den : ℚ)) :=
        congrArg (fun x : ℚ => p * x) hrrepr
      _ = t * u := by
        dsimp [t, u, d]
        field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hdpos)]
  have hpr : p * r ∈ P0.ControlledResidue.Good83 := by
    rw [hscale1]
    exact P0.ControlledResidue.Good83.mul_mem ht hu
  simpa [p] using hpr

lemma p0ScaleArg_good (r : ℚ) (k : ℕ)
    (hbound : r.den < 83 ^ k) :
    p0ScaleArg r k ∈ P0.ControlledResidue.Good83 := by
  let p : ℚ := ((83 ^ k : ℕ) : ℚ)
  have hp : p ∈ P0.ControlledResidue.Good83 := by
    change Nat.Coprime p.den 83
    simp [p]
  have hscale2 : p0ScaleArg r k = p * (p * r) := by
    dsimp [p0ScaleArg, p]
    ring
  rw [hscale2]
  exact P0.ControlledResidue.Good83.mul_mem hp
    (p0SingleScaleArg_good r k hbound)

lemma p0ScaleArg_residue_zero (r : ℚ) (k : ℕ)
    (hbound : r.den < 83 ^ k) :
    P0.ControlledResidue.residueHom
      ⟨p0ScaleArg r k, p0ScaleArg_good r k hbound⟩ = 0 := by
  let p : ℚ := ((83 ^ k : ℕ) : ℚ)
  let hp : P0.ControlledResidue.Good83 := ⟨p, by
    change Nat.Coprime p.den 83
    simp [p]⟩
  let b : P0.ControlledResidue.Good83 := ⟨(83 : ℚ), by norm_num⟩
  have hp_eq : hp = b ^ k := by
    apply Subtype.ext
    dsimp [hp, b, p]
    norm_num [Nat.cast_pow]
  let hy : P0.ControlledResidue.Good83 :=
    ⟨p * r, p0SingleScaleArg_good r k hbound⟩
  have hrepr :
      (⟨p0ScaleArg r k, p0ScaleArg_good r k hbound⟩ :
        P0.ControlledResidue.Good83) = hp * hy := by
    apply Subtype.ext
    change p0ScaleArg r k = p * (p * r)
    dsimp [p, p0ScaleArg]
    ring
  have hk : 0 < k := by
    by_contra hk
    have hk0 : k = 0 := Nat.eq_zero_of_not_pos hk
    subst k
    have hdpos : 0 < r.den := Nat.pos_of_ne_zero r.den_nz
    norm_num at hbound
  have hpres : P0.ControlledResidue.residueHom hp = 0 := by
    rw [hp_eq, map_pow]
    have hb : P0.ControlledResidue.residueHom b = 0 := by
      change ((83 : ℚ) : P0.ControlledResidue.F83) = 0
      simpa using (ZMod.natCast_self 83)
    rw [hb]
    simp [Nat.ne_of_gt hk]
  rw [hrepr, map_mul, hpres]
  exact zero_mul _

lemma p0A2_eval_residue_zero {F : P0Family} (hbase : F.a = 2)
    (r : ℚ) (k : ℕ) (hbound : r.den < 83 ^ k) :
    P0.ControlledResidue.residueHom
        ⟨p0SourceEvalQ F 32 (p0ScaleArg r k), by
          have hP := p0A2PolynomialGood_map
          let xg : P0.ControlledResidue.Good83 :=
            ⟨p0ScaleArg r k, p0ScaleArg_good r k hbound⟩
          have hx : p0SourceEvalQ F 32 (p0ScaleArg r k) =
              ((p0A2PolynomialGood.eval xg :
                P0.ControlledResidue.Good83) : ℚ) := by
            change (p0CanonicalPolynomial F.a 32).eval
                (p0ScaleArg r k) = _
            rw [hbase, ← hP]
            simpa [xg] using
              (Polynomial.eval_map_apply (p := p0A2PolynomialGood)
                P0.ControlledResidue.Good83.subtype xg)
          rw [hx]
          exact (p0A2PolynomialGood.eval xg).property⟩ =
      P0.ControlledResidue.residueHom
        ⟨p0SourceEvalQ F 32 0, by
          have hP := p0A2PolynomialGood_map
          let zg : P0.ControlledResidue.Good83 :=
            ⟨0, P0.ControlledResidue.Good83.zero_mem⟩
          have hz : p0SourceEvalQ F 32 0 =
              ((p0A2PolynomialGood.eval zg :
                P0.ControlledResidue.Good83) : ℚ) := by
            change (p0CanonicalPolynomial F.a 32).eval 0 = _
            rw [hbase, ← hP]
            simpa [zg] using
              (Polynomial.eval_map_apply (p := p0A2PolynomialGood)
                P0.ControlledResidue.Good83.subtype zg)
          rw [hz]
          exact (p0A2PolynomialGood.eval zg).property⟩ := by
  let P := p0A2PolynomialGood
  let xg : P0.ControlledResidue.Good83 :=
    ⟨p0ScaleArg r k, p0ScaleArg_good r k hbound⟩
  let zg : P0.ControlledResidue.Good83 :=
    ⟨0, P0.ControlledResidue.Good83.zero_mem⟩
  have hxzero : P0.ControlledResidue.residueHom xg = 0 := by
    exact p0ScaleArg_residue_zero r k hbound
  have hzzero : P0.ControlledResidue.residueHom zg = 0 := by
    dsimp [zg, P0.ControlledResidue.residueHom]
    simp
  have hpoly : P0.ControlledResidue.residueHom (P.eval xg) =
      P0.ControlledResidue.residueHom (P.eval zg) := by
    calc
      P0.ControlledResidue.residueHom (P.eval xg) =
          (P.map P0.ControlledResidue.residueHom).eval
            (P0.ControlledResidue.residueHom xg) :=
        (Polynomial.eval_map_apply (p := P)
          P0.ControlledResidue.residueHom xg).symm
      _ = (P.map P0.ControlledResidue.residueHom).eval 0 := by
        rw [hxzero]
      _ = (P.map P0.ControlledResidue.residueHom).eval
            (P0.ControlledResidue.residueHom zg) := by
        rw [hzzero]
      _ = P0.ControlledResidue.residueHom (P.eval zg) :=
        Polynomial.eval_map_apply (p := P)
          P0.ControlledResidue.residueHom zg
  change ((p0SourceEvalQ F 32 (p0ScaleArg r k) : ℚ) :
      P0.ControlledResidue.F83) =
    ((p0SourceEvalQ F 32 0 : ℚ) : P0.ControlledResidue.F83)
  have hx : p0SourceEvalQ F 32 (p0ScaleArg r k) =
      ((P.eval xg : P0.ControlledResidue.Good83) : ℚ) := by
    change (p0CanonicalPolynomial F.a 32).eval (p0ScaleArg r k) = _
    rw [hbase, ← p0A2PolynomialGood_map]
    simpa [P, xg] using
      (Polynomial.eval_map_apply (p := P)
        P0.ControlledResidue.Good83.subtype xg)
  have hz : p0SourceEvalQ F 32 0 =
      ((P.eval zg : P0.ControlledResidue.Good83) : ℚ) := by
    change (p0CanonicalPolynomial F.a 32).eval 0 = _
    rw [hbase, ← p0A2PolynomialGood_map]
    simpa [P, zg] using
      (Polynomial.eval_map_apply (p := P)
        P0.ControlledResidue.Good83.subtype zg)
  rw [hx, hz]
  exact hpoly

lemma p0A2_source_eval_good {F : P0Family} (hbase : F.a = 2)
    (x : ℚ) (hx : x ∈ P0.ControlledResidue.Good83) :
    p0SourceEvalQ F 32 x ∈ P0.ControlledResidue.Good83 := by
  let xg : P0.ControlledResidue.Good83 := ⟨x, hx⟩
  have hEval : p0SourceEvalQ F 32 x =
      ((p0A2PolynomialGood.eval xg : P0.ControlledResidue.Good83) : ℚ) := by
    change (p0CanonicalPolynomial F.a 32).eval x = _
    rw [hbase, ← p0A2PolynomialGood_map]
    simpa [xg] using
      (Polynomial.eval_map_apply (p := p0A2PolynomialGood)
        P0.ControlledResidue.Good83.subtype xg)
  change Nat.Coprime (p0SourceEvalQ F 32 x).den 83
  rw [hEval]
  exact (p0A2PolynomialGood.eval xg).property

private theorem reducedRational_residue_eq_of_value_eq_tower
    {p : ℕ} [Fact (Nat.Prime p)]
    {x y : ContourKit.ReducedRational p}
    (hvalue : x.value = y.value) : x.residue = y.residue := by
  have hxdenQ : (x.denominator : ℚ) ≠ 0 := by
    exact_mod_cast x.denominator_ne_zero
  have hydenQ : (y.denominator : ℚ) ≠ 0 := by
    exact_mod_cast y.denominator_ne_zero
  have hquot : (x.numerator : ℚ) / (x.denominator : ℚ) =
      (y.numerator : ℚ) / (y.denominator : ℚ) := by
    calc
      (x.numerator : ℚ) / (x.denominator : ℚ) = x.value := x.value_eq.symm
      _ = y.value := hvalue
      _ = (y.numerator : ℚ) / (y.denominator : ℚ) := y.value_eq
  have hcrossQ : (x.numerator : ℚ) * (y.denominator : ℚ) =
      (y.numerator : ℚ) * (x.denominator : ℚ) := by
    have h := hquot
    field_simp [hxdenQ, hydenQ] at h
    simpa [mul_comm, mul_left_comm, mul_assoc] using h
  have hcrossZ : x.numerator * y.denominator =
      y.numerator * x.denominator := by
    exact_mod_cast hcrossQ
  have hcross : (x.numerator : ZMod p) * (y.denominator : ZMod p) =
      (y.numerator : ZMod p) * (x.denominator : ZMod p) := by
    simpa only [Int.cast_mul] using congrArg (fun z : ℤ => (z : ZMod p)) hcrossZ
  rw [x.residue_eq, y.residue_eq]
  field_simp [x.denominator_residue_ne_zero, y.denominator_residue_ne_zero]
  simpa [mul_comm] using hcross

theorem p0A2_seed_argument_of_seed_value {F : P0Family}
    (hbase : F.a = 2) (seed : ContourKit.ReducedRational 83)
    (hseed_value : seed.value = p0SourceEvalQ F 32 0) :
    ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      ∃ s : ContourKit.ReducedRational 83,
        s.value = p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r) ∧
        s.residue = seed.residue := by
  intro r
  refine ⟨r.den, ?_⟩
  intro k hdk
  have hbound : r.den < 83 ^ k := by
    exact lt_of_lt_of_le (Nat.lt_pow_self (by norm_num : 1 < 83))
      (Nat.pow_le_pow_right (by norm_num : 0 < 83) hdk)
  let x := p0ScaleArg r k
  have hxgood : x ∈ P0.ControlledResidue.Good83 := by
    exact p0ScaleArg_good r k hbound
  have hsource : p0SourceEvalQ F 32 x ∈ P0.ControlledResidue.Good83 :=
    p0A2_source_eval_good hbase x hxgood
  have hzero : p0SourceEvalQ F 32 0 ∈ P0.ControlledResidue.Good83 :=
    p0A2_source_eval_good hbase 0 P0.ControlledResidue.Good83.zero_mem
  change Nat.Coprime (p0SourceEvalQ F 32 x).den 83 at hsource
  change Nat.Coprime (p0SourceEvalQ F 32 0).den 83 at hzero
  let s := P0.ControlledResidue.reducedOf
    (p0SourceEvalQ F 32 x) hsource
  let s₀ := P0.ControlledResidue.reducedOf
    (p0SourceEvalQ F 32 0) hzero
  refine ⟨s, ?_, ?_⟩
  · change p0SourceEvalQ F 32 x =
      p0SourceEvalQ F 32 ((83 ^ k : ℕ) ^ 2 * r)
    congr 1
  · have hres : s.residue = s₀.residue := by
      change P0.ControlledResidue.residueOf
          (p0SourceEvalQ F 32 x) hsource =
        P0.ControlledResidue.residueOf (p0SourceEvalQ F 32 0) hzero
      rw [P0.ControlledResidue.residueOf_eq_ratCast,
        P0.ControlledResidue.residueOf_eq_ratCast]
      have hmod := p0A2_eval_residue_zero hbase r k hbound
      change ((p0SourceEvalQ F 32 (p0ScaleArg r k) : ℚ) :
          P0.ControlledResidue.F83) =
        ((p0SourceEvalQ F 32 0 : ℚ) : P0.ControlledResidue.F83) at hmod
      simpa [x] using hmod
    have hseed : seed.residue = s₀.residue := by
      apply reducedRational_residue_eq_of_value_eq_tower
      simpa [s₀, P0.ControlledResidue.reducedOf] using hseed_value
    exact hres.trans hseed.symm



end P0A2SeedArgument

def P0A2SeedToTowerCertificate.to_frobenius
    {F : P0Family} (hcert : P0A2SeedToTowerCertificate F) :
    P0FrobeniusTowerCertificate F 32 83 := by
  have hseed_ne : hcert.seed.residue ≠ 0 := by
    rw [hcert.seed_residue_eq_30]
    exact p0A2SeedResidue30_ne_zero
  refine
    { M_pos := by norm_num
      M_multiple_four := by norm_num
      p_prime := p0A2Tower_prime
      p_gt_twoM_plus_h := p0A2Tower_cutoff
      seed := hcert.seed
      seed_value := hcert.seed_value
      seed_residue_nonzero := hseed_ne
      seed_argument := p0A2_seed_argument_of_seed_value
        hcert.base_is_two hcert.seed hcert.seed_value
      frobenius := hcert.frobenius }

theorem p0A2SeedToTower_source_nonzero {F : P0Family}
    (hcert : P0A2SeedToTowerCertificate F) :
    ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      p0SourceEvalQ F (p0A2TowerIndex k) r ≠ 0 := by
  intro r
  simpa [p0A2TowerIndex] using
    (p0FrobeniusTower_source_nonzero hcert.to_frobenius r)

theorem p0A2SeedToTower_nonvanishing {F : P0Family}
    (hcert : P0A2SeedToTowerCertificate F) :
    P0A2NonvanishingStatement F := by
  exact p0A2FrobeniusTower_nonvanishing
    ⟨hcert.base_is_two, hcert.to_frobenius,
      by simpa [P0A2SeedToTowerCertificate.to_frobenius] using
        hcert.seed_residue_eq_30⟩

end

end Li2Lean
