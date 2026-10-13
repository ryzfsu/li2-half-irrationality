/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.Kit.ReducedRational

namespace Li2Lean

noncomputable section

/-- Quotient coefficients for `H = X^2 + X + 1 + 5R` in docs/6393 §2. -/
def p0SeedRemainder : Polynomial ℤ :=
    Polynomial.monomial 0 (259 : ℤ)
  + Polynomial.monomial 1 (-8909296 : ℤ)
  + Polynomial.monomial 2 (951976521 : ℤ)
  + Polynomial.monomial 3 (84806809854 : ℤ)
  + Polynomial.monomial 4 (-1894747558258 : ℤ)
  + Polynomial.monomial 5 (18335224438387 : ℤ)
  + Polynomial.monomial 6 (-97325286222780 : ℤ)
  + Polynomial.monomial 7 (526889189446410 : ℤ)
  + Polynomial.monomial 8 (-3150733440920520 : ℤ)
  + Polynomial.monomial 9 (14288707666419480 : ℤ)
  + Polynomial.monomial 10 (-44073477632016000 : ℤ)
  + Polynomial.monomial 11 (93969532668060000 : ℤ)
  + Polynomial.monomial 12 (-141488586282960000 : ℤ)
  + Polynomial.monomial 13 (150921910271664000 : ℤ)
  + Polynomial.monomial 14 (-111821247014400000 : ℤ)
  + Polynomial.monomial 15 (54734402419200000 : ℤ)
  + Polynomial.monomial 16 (-15900588748800000 : ℤ)
  + Polynomial.monomial 17 (2073989836800000 : ℤ)

/-- The degree-17 seed factor `H` from docs/6393 §2. -/
def p0SeedH : Polynomial ℤ :=
  Polynomial.X ^ 2 + Polynomial.X + 1 + Polynomial.C (5 : ℤ) * p0SeedRemainder

/-- Coefficient identity from docs/6393 §2: `H mod 5 = X^2 + X + 1`. -/
structure P0SeedModFiveCertificate : Prop where
  mod_five : p0SeedH.map (Int.castRingHom (ZMod 5)) =
    (Polynomial.X : Polynomial (ZMod 5)) ^ 2 + Polynomial.X + 1

/-- Verifies the mod-five decomposition of the general-a seed in docs/6393 §2. -/
theorem p0SeedModFive_cert : P0SeedModFiveCertificate := by
  constructor
  simp [p0SeedH, Polynomial.map_add, Polynomial.map_mul,
    Polynomial.map_X]
  have hfive : (5 : Polynomial (ZMod 5)) = 0 := by
    change Polynomial.C (5 : ZMod 5) = 0
    simpa using congrArg (Polynomial.C : ZMod 5 → Polynomial (ZMod 5))
      (ZMod.natCast_self 5)
  rw [hfive]
  simp

/-- The residue polynomial in docs/6393 §2 is rootless over `ZMod 5`. -/
theorem p0SeedH_mod_five_no_roots (z : ZMod 5) :
    z ^ 2 + z + 1 ≠ 0 := by
  fin_cases z <;> decide

/-- The general-a seed factor has no integer roots; see docs/6393 §2. -/
theorem p0SeedH_eval_ne_zero (a : ℤ) : p0SeedH.eval a ≠ 0 := by
  let hmod : P0SeedModFiveCertificate := p0SeedModFive_cert
  intro hzero
  have hcast :
      (p0SeedH.map (Int.castRingHom (ZMod 5))).eval (a : ZMod 5) = 0 := by
    have heval := Polynomial.eval_map_apply (p := p0SeedH)
      (f := Int.castRingHom (ZMod 5)) a
    change (p0SeedH.map (Int.castRingHom (ZMod 5))).eval
      ((Int.castRingHom (ZMod 5)) a) = 0
    rw [heval]
    exact congrArg (fun z : ℤ => (z : ZMod 5)) hzero
  rw [hmod.mod_five] at hcast
  exact p0SeedH_mod_five_no_roots (a : ZMod 5) (by simpa using hcast)

/-- Evaluation of the determinant `eq:main-polynomial` over ℚ before its real cast. -/
def p0SourceEvalQ (F : P0Family) (m : ℕ) (r : ℚ) : ℚ :=
  (p0CanonicalPolynomial F.a m).eval r

/-- Denominator in the general-a seed factorization from docs/6393 §2. -/
def p0SeedDenominator : ℚ := 2090188800000

/-- Numerator in the general-a seed factorization from docs/6393 §2. -/
def p0SeedFactorNumerator (a : ℤ) : ℚ :=
  (a : ℚ) ^ 9 * ((a - 1 : ℤ) : ℚ) ^ 2 * ((p0SeedH.eval a : ℤ) : ℚ)

/-- Exact general-a seed factorization from docs/6393 §2, isolated as a source check. -/
structure P0GeneralSeedFactorization (F : P0Family) : Prop where
  exact : p0SourceEvalQ F 4 0 =
    p0SeedFactorNumerator F.a / p0SeedDenominator

/--
Nonvanishing of the general-a seed from its exact factorization in
docs/6393 §2. This is distinct from the fixed `(M,p)=(32,83)` seed
certificate `eq:nv-seed` in the a=2 paper.
-/
theorem p0GeneralSeed_nonzero {F : P0Family}
    (hseed : P0GeneralSeedFactorization F) :
    p0SourceEvalQ F 4 0 ≠ 0 := by
  have ha0 : F.a ≠ 0 := by
    intro hz
    have hbase := F.base_abs_ge_two
    rw [hz] at hbase
    norm_num at hbase
  have ha1 : F.a - 1 ≠ 0 := by
    intro hz
    have hone : F.a = 1 := by omega
    have hbase := F.base_abs_ge_two
    rw [hone] at hbase
    norm_num at hbase
  have hH : p0SeedH.eval F.a ≠ 0 := p0SeedH_eval_ne_zero F.a
  have hnum : p0SeedFactorNumerator F.a ≠ 0 := by
    apply mul_ne_zero
    apply mul_ne_zero
    · exact_mod_cast pow_ne_zero 9 ha0
    · exact_mod_cast pow_ne_zero 2 ha1
    · exact_mod_cast hH
  have hden : p0SeedDenominator ≠ 0 := by norm_num [p0SeedDenominator]
  rw [hseed.exact]
  exact div_ne_zero hnum hden

def p0AuxiliaryPrimeNumber (a : ℤ) : ℕ :=
  Nat.factorial 10 * Int.natAbs (a * (a - 1) * p0SeedH.eval a) + 1

/-- The prime from docs/6393 §2 avoids the general-a seed factors. For `M=4`,
`p>10` gives the `p>2M+h` hypothesis in `eq:nv-pencil` (`h=2`). -/
theorem p0_exists_auxiliary_prime (a : ℤ) (ha : 2 ≤ Int.natAbs a) :
    ∃ p : ℕ, Nat.Prime p ∧ 10 < p ∧
      ¬ p ∣ a.natAbs ∧ ¬ p ∣ (a - 1).natAbs ∧
      ¬ p ∣ (p0SeedH.eval a).natAbs := by
  have ha0 : a ≠ 0 := by
    intro hz
    have hbase := ha
    rw [hz] at hbase
    norm_num at hbase
  have ha1 : a - 1 ≠ 0 := by
    intro hz
    have hone : a = 1 := by omega
    have hbase := ha
    rw [hone] at hbase
    norm_num at hbase
  have hH : p0SeedH.eval a ≠ 0 := p0SeedH_eval_ne_zero a
  have hprod : a * (a - 1) * p0SeedH.eval a ≠ 0 :=
    mul_ne_zero (mul_ne_zero ha0 ha1) hH
  have hN : 1 < p0AuxiliaryPrimeNumber a := by
    have hterm : 0 < Nat.factorial 10 *
        Int.natAbs (a * (a - 1) * p0SeedH.eval a) :=
      Nat.mul_pos (Nat.factorial_pos _) (Int.natAbs_pos.mpr hprod)
    dsimp [p0AuxiliaryPrimeNumber]
    omega
  obtain ⟨p, hp, hpdvd⟩ := Nat.exists_prime_and_dvd (by omega :
    p0AuxiliaryPrimeNumber a ≠ 1)
  have hnotprod :
      ¬ p ∣ Int.natAbs (a * (a - 1) * p0SeedH.eval a) := by
    intro hpA
    have hterm : p ∣ Nat.factorial 10 *
        Int.natAbs (a * (a - 1) * p0SeedH.eval a) := dvd_mul_of_dvd_right hpA _
    have hone : p ∣ 1 := (Nat.dvd_add_iff_right hterm).2 hpdvd
    exact hp.not_dvd_one hone
  have habs : Int.natAbs (a * (a - 1) * p0SeedH.eval a) =
      a.natAbs * (a - 1).natAbs * (p0SeedH.eval a).natAbs := by
    simp [Int.natAbs_mul, mul_assoc]
  have hpa : ¬ p ∣ a.natAbs := by
    intro hpa
    apply hnotprod
    rw [habs]
    simpa [Nat.mul_assoc] using
      (dvd_mul_of_dvd_left hpa ((a - 1).natAbs * (p0SeedH.eval a).natAbs))
  have hpa1 : ¬ p ∣ (a - 1).natAbs := by
    intro hpa1
    apply hnotprod
    rw [habs]
    have hpMid : p ∣ a.natAbs * (a - 1).natAbs :=
      dvd_mul_of_dvd_right hpa1 a.natAbs
    exact dvd_mul_of_dvd_left hpMid (p0SeedH.eval a).natAbs
  have hpH : ¬ p ∣ (p0SeedH.eval a).natAbs := by
    intro hpH
    apply hnotprod
    rw [habs]
    exact dvd_mul_of_dvd_right hpH _
  refine ⟨p, hp, ?_, hpa, hpa1, hpH⟩
  by_contra hnot
  have hple : p ≤ 10 := Nat.le_of_not_gt hnot
  have hfac : p ∣ Nat.factorial 10 := Nat.dvd_factorial hp.pos hple
  have hterm : p ∣ Nat.factorial 10 *
      Int.natAbs (a * (a - 1) * p0SeedH.eval a) := dvd_mul_of_dvd_left hfac _
  have hone : p ∣ 1 := (Nat.dvd_add_iff_right hterm).2 hpdvd
  exact hp.not_dvd_one hone

/--
Interface for `output/li2-half-paper-v10/sec-nonvanishing.tex`: `frobenius`
records `eq:nv-pencil`, whose entry reduction uses `eq:nv-lucas`.

The seed and eventual congruence obligations remain explicit certificate
fields.
-/
structure P0FrobeniusTowerCertificate (F : P0Family) (M p : ℕ) where
  M_pos : 0 < M
  M_multiple_four : 4 ∣ M
  p_prime : Nat.Prime p
  /-- Denominator cutoff in `eq:nv-pencil`: `p > 2M+h`, with `h=M/2`. -/
  p_gt_twoM_plus_h : 2 * M + M / 2 < p
  seed : ContourKit.ReducedRational p
  seed_value : seed.value = p0SourceEvalQ F M 0
  seed_residue_nonzero : seed.residue ≠ 0
  seed_argument : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
    ∃ s : ContourKit.ReducedRational p,
      s.value = p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) ∧
      s.residue = seed.residue
  frobenius : ∀ r : ℚ, ∃ k₁, ∀ k : ℕ, k₁ ≤ k →
    ∃ lhs rhs : ContourKit.ReducedRational p,
      lhs.value = (p ^ k : ℚ) ^ (3 * M * p ^ k) *
        p0SourceEvalQ F (M * p ^ k) r ∧
      rhs.value = (p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r)) ^ (p ^ k) ∧
      lhs.residue = rhs.residue ∧
      (∀ s : ContourKit.ReducedRational p,
        s.value = p0SourceEvalQ F M ((p ^ k : ℕ) ^ 2 * r) →
          rhs.residue = s.residue ^ (p ^ k))

/-- Multiplication preserves the paper's `4 | M` index condition in `eq:nv-pencil`. -/
private theorem p0Source_multiple_four {M q : ℕ} (hM : 4 ∣ M) :
    4 ∣ M * q := dvd_mul_of_dvd_left hM q

/--
Transports a rational-source nonzero value to the real polynomial family
defined by `eq:main-polynomial` in `output/li2-half-paper-v10/main.tex`.
-/
private theorem p0_source_ne_zero_implies_family_eval_ne_zero
    (F : P0Family) {m : ℕ} (hm : 4 ∣ m) {r : ℚ}
    (h : p0SourceEvalQ F m r ≠ 0) : (F.G m).eval (r : ℝ) ≠ 0 := by
  rw [F.G_source m hm]
  intro hzero
  have heval := Polynomial.eval_map_apply
    (p := p0CanonicalPolynomial F.a m) (f := algebraMap ℚ ℝ) r
  change ((p0CanonicalPolynomial F.a m).map (algebraMap ℚ ℝ)).eval
    ((algebraMap ℚ ℝ) r) = 0 at hzero
  rw [heval] at hzero
  change ((p0SourceEvalQ F m r : ℚ) : ℝ) = 0 at hzero
  have hzq : p0SourceEvalQ F m r = 0 := by
    exact_mod_cast hzero
  exact h hzq

/--
Residue propagation from the `eq:nv-pencil` tower and seed continuity at
`q^2 r`; both are explicit fields of the certificate for
`output/li2-half-paper-v10/sec-nonvanishing.tex`.
-/
theorem p0FrobeniusTower_source_nonzero {F : P0Family} {M p : ℕ}
    (hcert : P0FrobeniusTowerCertificate F M p) :
    ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k → p0SourceEvalQ F (M * p ^ k) r ≠ 0 := by
  letI : Fact (Nat.Prime p) := ⟨hcert.p_prime⟩
  intro r
  obtain ⟨k₀, hk₀⟩ := hcert.seed_argument r
  obtain ⟨k₁, hk₁⟩ := hcert.frobenius r
  refine ⟨max k₀ k₁, ?_⟩
  intro k hkk
  have hk_seed : k₀ ≤ k := le_trans (Nat.le_max_left _ _) hkk
  have hk_frob : k₁ ≤ k := le_trans (Nat.le_max_right _ _) hkk
  obtain ⟨s, hsval, hsres⟩ := hk₀ k hk_seed
  obtain ⟨lhs, rhs, hlhsval, _hrhsval, hlhsres, hrhsres⟩ := hk₁ k hk_frob
  have hrhs : rhs.residue ≠ 0 := by
    rw [hrhsres s hsval, hsres]
    exact pow_ne_zero _ hcert.seed_residue_nonzero
  have hlhs : lhs.residue ≠ 0 := by rwa [hlhsres]
  have hlhsval_ne : lhs.value ≠ 0 := ContourKit.ReducedRational.value_ne_zero lhs hlhs
  intro hzero
  apply hlhsval_ne
  rw [hlhsval, hzero]
  simp

/--
General M,p consequence of the `eq:nv-pencil` interface. The fixed a=2
rational-point claim is `p0A2FrobeniusTower_nonvanishing`, matching
`eq:nv-final` and `eq:nonvanishing` for `M=32`, `p=83`.
-/
theorem p0FrobeniusTower_nonvanishing {F : P0Family} {M p : ℕ}
    (hcert : P0FrobeniusTowerCertificate F M p) :
    P0NonvanishingStatement F := by
  have hM4 : 4 ≤ M := Nat.le_of_dvd hcert.M_pos hcert.M_multiple_four
  have hMhalf : 2 ≤ M / 2 := by omega
  have hlarge := hcert.p_gt_twoM_plus_h
  have hp10 : 10 < p := by omega
  refine ⟨M, p, hcert.M_pos, hcert.M_multiple_four, hcert.p_prime,
    hp10, ?_⟩
  intro r
  obtain ⟨k₀, hk₀⟩ := p0FrobeniusTower_source_nonzero hcert r
  refine ⟨k₀, ?_⟩
  intro k hkk
  have hsource := hk₀ k hkk
  exact p0_source_ne_zero_implies_family_eval_ne_zero F
    (p0Source_multiple_four hcert.M_multiple_four) hsource

/--
Fixed-base certificate for `output/li2-half-paper-v10/sec-nonvanishing.tex`.
It records `eq:nv-seed` and the `eq:nv-pencil` tower used in `eq:nv-final`;
the finite seed and all-level congruence remain explicit certificate fields.
-/
structure P0A2FrobeniusTowerCertificate (F : P0Family) where
  base_is_two : F.a = 2
  tower : P0FrobeniusTowerCertificate F 32 83
  seed_residue_eq_30 : tower.seed.residue = (30 : ZMod 83)

/--
Specialization of `output/li2-half-paper-v10/sec-nonvanishing.tex`:
`eq:nv-final` gives the fixed-sequence conclusion `eq:nonvanishing` at
`M=32`, `p=83`.
-/
theorem p0A2FrobeniusTower_nonvanishing {F : P0Family}
    (hcert : P0A2FrobeniusTowerCertificate F) :
    P0A2NonvanishingStatement F := by
  intro _ha r
  have _hbase : F.a = 2 := hcert.base_is_two
  obtain ⟨k₀, hk₀⟩ := p0FrobeniusTower_source_nonzero hcert.tower r
  refine ⟨k₀, ?_⟩
  intro k hkk
  have hsource := hk₀ k hkk
  have hm : 4 ∣ 32 * 83 ^ k := by
    refine ⟨8 * 83 ^ k, ?_⟩
    ring
  exact p0_source_ne_zero_implies_family_eval_ne_zero F hm hsource

/-!
The following finite congruences are the Lucas/Frobenius part of
`eq:nv-lucas` in `output/li2-half-paper-v10/sec-nonvanishing.tex`.  They are
kept separate from `P0FrobeniusTowerCertificate`: the latter still records
the rational matrix reduction and block determinant as explicit certificate
fields, while these two lemmas discharge the elementary binomial and power
reductions used by that certificate.
-/

private theorem p0_choose_prime_power_add_modEq
    {p A b k v : ℕ} [Fact p.Prime] (hv : v < p ^ k) :
    Nat.choose (A * p ^ k + v) (b * p ^ k) ≡ Nat.choose A b [MOD p] := by
  induction k generalizing A b v with
  | zero =>
      have hv1 : v < 1 := by simpa using hv
      have hv0 : v = 0 := by omega
      subst v
      simpa using (Nat.ModEq.refl (Nat.choose A b))
  | succ k ih =>
      have hpP : Nat.Prime p := Fact.out
      have hp : 0 < p := hpP.pos
      have hnmod : (A * p ^ k.succ + v) % p = v % p := by
        simp [pow_succ, Nat.add_mod, Nat.mul_mod]
      have hkmod : (b * p ^ k.succ) % p = 0 := by
        simp [pow_succ, Nat.mul_mod]
      have hndiv : (A * p ^ k.succ + v) / p = A * p ^ k + v / p := by
        calc
          (A * p ^ k.succ + v) / p = (v + p * (A * p ^ k)) / p := by
            rw [pow_succ]
            congr 1 <;> ring
          _ = v / p + A * p ^ k := Nat.add_mul_div_left v (A * p ^ k) hp
          _ = A * p ^ k + v / p := Nat.add_comm _ _
      have hkdiv : (b * p ^ k.succ) / p = b * p ^ k := by
        calc
          (b * p ^ k.succ) / p = (p * (b * p ^ k)) / p := by
            rw [pow_succ]
            congr 1 <;> ring
          _ = b * p ^ k := Nat.mul_div_right (b * p ^ k) hp
      have hvdiv : v / p < p ^ k := (Nat.div_lt_iff_lt_mul hp).2 (by
        simpa [pow_succ, mul_comm, mul_left_comm, mul_assoc] using hv)
      have hLucas := Choose.choose_modEq_choose_mod_mul_choose_div_nat
        (n := A * p ^ k.succ + v) (k := b * p ^ k.succ) (p := p)
      have hLucas' : Nat.choose (A * p ^ k.succ + v) (b * p ^ k.succ) ≡
          Nat.choose ((A * p ^ k.succ + v) / p) ((b * p ^ k.succ) / p) [MOD p] := by
        rw [hnmod, hkmod] at hLucas
        simpa using hLucas
      rw [hndiv, hkdiv] at hLucas'
      exact hLucas'.trans (ih hvdiv)

private theorem p0_pow_prime_power_modEq_self
    {p x k : ℕ} [Fact p.Prime] :
    x ^ p ^ k ≡ x [MOD p] := by
  apply (ZMod.natCast_eq_natCast_iff (x ^ p ^ k) x p).mp
  rw [Nat.cast_pow]
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        (x : ZMod p) ^ p ^ k.succ =
            ((x : ZMod p) ^ p) ^ p ^ k := by
              rw [pow_succ, pow_mul]
              ring
        _ = (x : ZMod p) ^ p ^ k := by rw [ZMod.pow_card]
        _ = x := ih

/-- The natural-number `U` congruence in the second half of `eq:nv-lucas`.
The source definition is `U_i^(g) = 2^i * choose (i+g) g`; the rational
matrix uses its cast into `ℚ`, so this lemma is intentionally stated before
that cast. -/
theorem p0U_nat_prime_power_modEq
    {p a h k v : ℕ} [Fact p.Prime] (hv : v < p ^ k) :
    (2 ^ (a * p ^ k + v) * Nat.choose (a * p ^ k + v + h * p ^ k) (h * p ^ k))
      ≡ 2 ^ v * (2 ^ a * Nat.choose (a + h) h) [MOD p] := by
  have hchoose :
      Nat.choose (a * p ^ k + v + h * p ^ k) (h * p ^ k) ≡
        Nat.choose (a + h) h [MOD p] := by
    convert p0_choose_prime_power_add_modEq (p := p) (A := a + h)
      (b := h) (k := k) (v := v) hv using 1 <;> ring
  have hpowq : 2 ^ p ^ k ≡ 2 [MOD p] :=
    p0_pow_prime_power_modEq_self (p := p) (x := 2) (k := k)
  have hpowaq : 2 ^ (a * p ^ k) ≡ 2 ^ a [MOD p] := by
    calc
      2 ^ (a * p ^ k) = 2 ^ (p ^ k * a) := by
        rw [Nat.mul_comm]
      _ = (2 ^ p ^ k) ^ a := by rw [pow_mul]
      _ ≡ 2 ^ a [MOD p] := hpowq.pow a
  have hpow : 2 ^ (a * p ^ k + v) ≡ 2 ^ v * 2 ^ a [MOD p] := by
    calc
      2 ^ (a * p ^ k + v) ≡ 2 ^ (a * p ^ k) * 2 ^ v [MOD p] := by
        simpa [pow_add] using (Nat.ModEq.refl (2 ^ (a * p ^ k + v)))
      _ ≡ 2 ^ a * 2 ^ v [MOD p] := hpowaq.mul (Nat.ModEq.refl _)
      _ ≡ 2 ^ v * 2 ^ a [MOD p] := by
        simpa [Nat.mul_comm] using (Nat.ModEq.refl (2 ^ a * 2 ^ v))
  calc
    2 ^ (a * p ^ k + v) *
          Nat.choose (a * p ^ k + v + h * p ^ k) (h * p ^ k) ≡
        (2 ^ v * 2 ^ a) * Nat.choose (a + h) h [MOD p] :=
      hpow.mul hchoose
    _ ≡ 2 ^ v * (2 ^ a * Nat.choose (a + h) h) [MOD p] := by
      simpa [Nat.mul_assoc] using
        (Nat.ModEq.refl (2 ^ v * (2 ^ a * Nat.choose (a + h) h)))

end

end Li2Lean
