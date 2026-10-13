/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.LayerInterfaces
import Li2Lean.Kit.ReducedRational
import Li2Lean.P0.Integerization

namespace Li2Lean.P0

namespace ControlledResidue

abbrev F83 := ZMod 83

instance : Fact (Nat.Prime 83) := ⟨by norm_num⟩

/-- The subring of rationals whose reduced denominator is invertible at 83. -/
def Good83 : Subring ℚ where
  carrier := {q | Nat.Coprime q.den 83}
  zero_mem' := by simp
  one_mem' := by simp
  add_mem' := by
    intro x y hx hy
    exact Nat.Coprime.of_dvd_left (Rat.add_den_dvd x y)
      (Nat.Coprime.mul_left hx hy)
  neg_mem' := by
    intro x hx
    simpa using hx
  mul_mem' := by
    intro x y hx hy
    exact Nat.Coprime.of_dvd_left (Rat.mul_den_dvd x y)
      (Nat.Coprime.mul_left hx hy)

/-- A denominator coprime to 83 remains invertible in `ZMod 83`. -/
theorem natCast_ne_zero_of_coprime {d : ℕ} (hcop : Nat.Coprime d 83) :
    (d : F83) ≠ 0 := by
  intro hz
  have hzI : ((d : ℤ) : F83) = 0 := by simpa using hz
  have hdvd : (83 : ℤ) ∣ (d : ℤ) :=
    (ZMod.intCast_zmod_eq_zero_iff_dvd (d : ℤ) 83).mp hzI
  have hdvdNat : 83 ∣ d := by exact_mod_cast hdvd
  have h83eq1 : 83 = 1 := hcop.symm.eq_one_of_dvd hdvdNat
  norm_num at h83eq1

/-- Reduction of a good rational is the ordinary rational cast into `F83`. -/
def residueHom : Good83 →+* F83 where
  toFun q := (q.1 : F83)
  map_zero' := by simp
  map_one' := by norm_num
  map_add' := by
    intro x y
    change ((x.1 + y.1 : ℚ) : F83) = (x.1 : F83) + (y.1 : F83)
    exact Rat.cast_add_of_ne_zero
      (natCast_ne_zero_of_coprime x.2)
      (natCast_ne_zero_of_coprime y.2)
  map_mul' := by
    intro x y
    change ((x.1 * y.1 : ℚ) : F83) = (x.1 : F83) * (y.1 : F83)
    exact Rat.cast_mul_of_ne_zero
      (natCast_ne_zero_of_coprime x.2)
      (natCast_ne_zero_of_coprime y.2)

/-- The common bounded-denominator form implies the coprimality premise. -/
theorem natCast_ne_zero_of_pos_lt {d : ℕ} (hd : 0 < d) (h83 : d < 83) :
    (d : F83) ≠ 0 := by
  apply natCast_ne_zero_of_coprime
  exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt hd) h83
    (by norm_num : Nat.Prime 83)).symm

/--
The residue of a rational is only defined here with an explicit denominator
certificate.  This is a local reduction helper, not a map from all rationals.
-/
def residueOf (q : ℚ) (_hcop : Nat.Coprime q.den 83) : F83 :=
  (q.num : F83) * (q.den : F83)⁻¹

theorem residueOf_eq_cast (q : ℚ) (hcop : Nat.Coprime q.den 83) :
    residueOf q hcop = (q : F83) := by
  change (q.num : F83) * (q.den : F83)⁻¹ = (q : F83)
  rw [Rat.cast_def]
  simp [div_eq_mul_inv]

/-- Package a bounded-denominator rational as the project's finite-place
certificate.  The denominator conditions are carried in the result. -/
def reducedOf (q : ℚ) (hcop : Nat.Coprime q.den 83) : ContourKit.ReducedRational 83 :=
  { value := q
    numerator := q.num
    denominator := (q.den : ℤ)
    denominator_ne_zero := by exact_mod_cast q.den_nz
    denominator_residue_ne_zero := by
      exact natCast_ne_zero_of_coprime hcop
    value_eq := by
      simpa using (Rat.num_div_den q).symm
    residue := residueOf q hcop
    residue_eq := by rfl }

theorem reducedOf_value (q : ℚ) (_hcop : Nat.Coprime q.den 83) :
    (reducedOf q _hcop).value = q := rfl

theorem reducedOf_residue (q : ℚ) (hcop : Nat.Coprime q.den 83) :
    (reducedOf q hcop).residue = residueOf q hcop := rfl

/-- Rational seed matrix in the paper's `(C; B - T A)` row order. -/
def sourceSeedQ : Matrix (Fin 64) (Fin 64) ℚ := fun r c =>
  if r.val < 32 then
    p0CQ (2 : ℚ) 16 (8 + r.val) c.val
  else
    p0BQ (2 : ℚ) 16 (8 + (r.val - 32)) c.val

private lemma inv_nat_mem {n : ℕ} (hn : n < 83) : ((n : ℚ)⁻¹) ∈ Good83 := by
  change Nat.Coprime ((n : ℚ)⁻¹).den 83
  rw [Rat.den_inv]
  by_cases hn0 : n = 0
  · simp [hn0]
  · simp [hn0]
    exact (Nat.coprime_of_lt_prime (Nat.ne_of_gt (Nat.pos_of_ne_zero hn0)) hn
      (by norm_num : Nat.Prime 83)).symm

private lemma p0UQ_mem (i : ℕ) : p0UQ (2 : ℚ) 16 i ∈ Good83 := by
  change Nat.Coprime (p0UQ (2 : ℚ) 16 i).den 83
  norm_num [p0UQ, Rat.den_mul]

private lemma p0Q_mem (s : ℕ) : p0Q (2 : ℚ) s ∈ Good83 := by
  change Nat.Coprime (p0Q (2 : ℚ) s).den 83
  norm_num [p0Q, Rat.den_mul]

private lemma choose_mem (n k : ℕ) : ((Nat.choose n k : ℕ) : ℚ) ∈ Good83 := by
  change Nat.Coprime ((Nat.choose n k : ℚ)).den 83
  simp

private lemma p0TQ_mem {i : ℕ} (hi : i < 64) : p0TQ (2 : ℚ) 16 i ∈ Good83 := by
  unfold p0TQ
  apply Good83.add_mem
  · apply Good83.sum_mem
    intro r hr
    rw [div_eq_mul_inv]
    apply Good83.mul_mem (p0UQ_mem (i - (r + 1)))
    convert inv_nat_mem (n := r + 1) (by
      have hrlt : r < i := Finset.mem_range.mp hr
      omega) using 1 <;> norm_num
  · have hpow : ((2 : ℚ) ^ i) ∈ Good83 := by
      change Nat.Coprime ((2 : ℚ) ^ i).den 83
      norm_num [Rat.den_mul]
    apply Good83.mul_mem hpow
    apply Good83.sum_mem
    intro s hs
    have hslt : s < 16 := Finset.mem_range.mp hs
    have hneg : ((-1 : ℚ) ^ s) ∈ Good83 := by
      change Nat.Coprime ((-1 : ℚ) ^ s).den 83
      norm_num [Rat.den_mul]
    have hfrac : ((-1 : ℚ) ^ s / (s + 1 : ℚ)) ∈ Good83 := by
      rw [div_eq_mul_inv]
      have hinv := inv_nat_mem (n := s + 1) (by omega)
      apply Good83.mul_mem hneg
      convert hinv using 1 <;> norm_num
    exact Good83.mul_mem
      (Good83.mul_mem hfrac (choose_mem (i + 16) (16 - (s + 1))))
      (p0Q_mem (s + 1))

private lemma p0BQQ_mem {i : ℕ} (hi : i < 40) : p0BQQ (2 : ℚ) 16 i ∈ Good83 := by
  unfold p0BQQ
  have hpow : ((2 : ℚ) ^ i) ∈ Good83 := by
    change Nat.Coprime ((2 : ℚ) ^ i).den 83
    norm_num [Rat.den_mul]
  apply Good83.sub_mem
  · apply Good83.sum_mem
    intro r hr
    rw [div_eq_mul_inv, ← inv_pow]
    apply Good83.mul_mem (p0UQ_mem (i - (r + 1)))
    have hrlt : r < i := Finset.mem_range.mp hr
    have hinv := inv_nat_mem (n := r + 1) (by omega)
    have hinv' : ((r : ℚ) + 1)⁻¹ ∈ Good83 := by
      convert hinv using 1 <;> norm_num
    simpa [pow_two] using Good83.mul_mem hinv' hinv'
  · apply Good83.mul_mem hpow
    apply Good83.sum_mem
    intro s hs
    have hsl := Finset.mem_Icc.mp hs
    have hneg : ((-1 : ℚ) ^ s) ∈ Good83 := by
      change Nat.Coprime ((-1 : ℚ) ^ s).den 83
      norm_num [Rat.den_mul]
    have hinv : ((s : ℚ)⁻¹) ∈ Good83 := inv_nat_mem (by omega)
    have hfrac : ((-1 : ℚ) ^ s / (s : ℚ)) ∈ Good83 := by
      rw [div_eq_mul_inv]
      exact Good83.mul_mem hneg hinv
    have hinner :
        (∑ r ∈ Finset.range (s - 1), p0Q (2 : ℚ) (r + 1) / (r + 1 : ℚ)) ∈ Good83 := by
      apply Good83.sum_mem
      intro r hr
      rw [div_eq_mul_inv]
      apply Good83.mul_mem (p0Q_mem (r + 1))
      have hrlt : r < s - 1 := Finset.mem_range.mp hr
      have hrle : r + 1 ≤ s - 1 := Nat.succ_le_of_lt hrlt
      have hinv' := inv_nat_mem (n := r + 1) (by omega)
      convert hinv' using 1 <;> norm_num
    exact Good83.mul_mem
      (Good83.mul_mem hfrac (choose_mem (i + 16) (16 - s))) hinner

private lemma inv_int_mem {z : ℤ} (hz : z.natAbs < 83) : ((z : ℚ)⁻¹) ∈ Good83 := by
  change Nat.Coprime ((z : ℚ)⁻¹).den 83
  rw [Rat.den_inv]
  by_cases hz0 : z = 0
  · simp [hz0]
  · simp [hz0]
    exact (Nat.coprime_of_lt_prime (Int.natAbs_ne_zero.mpr hz0) hz
      (by norm_num : Nat.Prime 83)).symm

private lemma inv_diff_mem {i j : ℕ} (hi : i < 40) (hj : j < 64) (_hij : i ≠ j) :
    (((j : ℚ) - (i : ℚ))⁻¹) ∈ Good83 := by
  have habs : ((j : ℤ) - (i : ℤ)).natAbs < 83 := by
    omega
  have hz := inv_int_mem habs
  convert hz using 1 <;> norm_num

private lemma p0CQ_mem {i j : ℕ} (hi : i < 40) (hj : j < 64) :
    p0CQ (2 : ℚ) 16 i j ∈ Good83 := by
  unfold p0CQ
  by_cases hij : i = j
  · subst j
    simp
    apply Good83.mul_mem
    · exact Good83.neg_mem (p0UQ_mem i)
    · apply Good83.sum_mem
      intro s hs
      have hslt : s < 16 := Finset.mem_range.mp hs
      have hinv := inv_nat_mem (n := i + s + 1) (by omega)
      convert hinv using 1 <;> norm_num
  · simp [hij]
    rw [div_eq_mul_inv]
    exact Good83.mul_mem
      (Good83.sub_mem (p0UQ_mem i) (p0UQ_mem j))
      (inv_diff_mem hi hj hij)

private lemma p0BQ_mem {i j : ℕ} (hi : i < 40) (hj : j < 64) :
    p0BQ (2 : ℚ) 16 i j ∈ Good83 := by
  unfold p0BQ
  by_cases hij : i = j
  · subst j
    simp
    exact p0BQQ_mem hi
  · simp [hij]
    rw [div_eq_mul_inv]
    exact Good83.mul_mem
      (Good83.sub_mem (p0TQ_mem (by omega)) (p0TQ_mem hj))
      (inv_diff_mem hi hj hij)

theorem sourceSeedQ_mem (r c : Fin 64) : sourceSeedQ r c ∈ Good83 := by
  by_cases hr : r.val < 32
  · simp [sourceSeedQ, hr]
    exact p0CQ_mem (by omega) c.isLt
  · simp [sourceSeedQ, hr]
    exact p0BQ_mem (by omega) c.isLt

/-- The same seed matrix represented over the good-denominator subring. -/
def sourceSeedGood : Matrix (Fin 64) (Fin 64) Good83 := fun r c =>
  ⟨sourceSeedQ r c, sourceSeedQ_mem r c⟩

theorem sourceSeedGood_coe :
    (fun r c => (sourceSeedGood r c : ℚ)) = sourceSeedQ := by
  rfl

theorem sourceSeedGood_det_coe :
    ((Matrix.det sourceSeedGood : Good83) : ℚ) = Matrix.det sourceSeedQ := by
  have hmap := RingHom.map_det (Good83.subtype) sourceSeedGood
  calc
    ((Matrix.det sourceSeedGood : Good83) : ℚ) =
        (Good83.subtype) (Matrix.det sourceSeedGood) := rfl
    _ = (Good83.subtype.mapMatrix sourceSeedGood).det := hmap
    _ = Matrix.det sourceSeedQ := by
      congr 1

theorem sourceSeedQ_det_mem : Matrix.det sourceSeedQ ∈ Good83 := by
  rw [← sourceSeedGood_det_coe]
  exact (Matrix.det sourceSeedGood).property

/-- The rational seed is the zero evaluation of the literal `m=32` pencil. -/
theorem sourceSeedQ_eq_p0MatrixQ_eval_zero :
    sourceSeedQ = fun r c =>
      (p0MatrixQ (2 : ℚ) 32 r c).eval 0 := by
  funext r c
  by_cases hr : r.val < 32
  · simp [sourceSeedQ, p0MatrixQ, hr]
  · simp [sourceSeedQ, p0MatrixQ, hr]

theorem sourceSeedQ_00 :
    sourceSeedQ (0 : Fin 64) (0 : Fin 64) = p0CQ (2 : ℚ) 16 8 0 := by
  simp [sourceSeedQ]

/-- Determinant packaging for the same `Fin 64` block order. -/
theorem sourceSeedQ_det_eq_p0Canonical_eval_zero :
    Matrix.det sourceSeedQ = (p0CanonicalPolynomial 2 32).eval 0 := by
  rw [sourceSeedQ_eq_p0MatrixQ_eval_zero]
  have hcan : p0CanonicalPolynomial 2 32 =
      (p0MatrixQ (2 : ℚ) 32).det := by
    simp [p0CanonicalPolynomial, show 4 ∣ (32 : ℕ) by norm_num]
  rw [hcan]
  calc
    Matrix.det (fun r c => (p0MatrixQ (2 : ℚ) 32 r c).eval 0) =
        ((Polynomial.evalRingHom (0 : ℚ)).mapMatrix
          (p0MatrixQ (2 : ℚ) 32)).det := by
          congr 1
    _ = (Polynomial.evalRingHom (0 : ℚ)) ((p0MatrixQ (2 : ℚ) 32).det) :=
      (RingHom.map_det (Polynomial.evalRingHom (0 : ℚ))
        (p0MatrixQ (2 : ℚ) 32)).symm

/-- Row-clearing factors for the 32 C-rows followed by the 32 B-rows. -/
def seedScaleQ (d : ℚ) : Fin 64 → ℚ := fun r =>
  if r.val < 32 then d else d ^ 2

theorem seedScaleQ_prod (d : ℚ) :
    (∏ r : Fin 64, seedScaleQ d r) = d ^ 96 := by
  let e : (Fin 32 ⊕ Fin 32) ≃ Fin 64 :=
    finSumFinEquiv
  calc
    (∏ r : Fin 64, seedScaleQ d r) =
        ∏ x : Fin 32 ⊕ Fin 32, seedScaleQ d (e x) := by
          symm
          apply Fintype.prod_equiv e
          intro x
          rfl
    _ = d ^ 96 := by
      rw [Fintype.prod_sum_type]
      have hleft (x : Fin 32) : (e (Sum.inl x)).val < 32 := by
        change (finSumFinEquiv (m := 32) (n := 32) (Sum.inl x)).val < 32
        rw [finSumFinEquiv_apply_left]
        exact x.isLt
      have hright (x : Fin 32) : ¬ (e (Sum.inr x)).val < 32 := by
        change ¬ (finSumFinEquiv (m := 32) (n := 32) (Sum.inr x)).val < 32
        rw [finSumFinEquiv_apply_right]
        simp only [Fin.natAdd]
        omega
      simp only [seedScaleQ, hleft, hright]
      simp
      ring

theorem seedScaleQ_eq_p0RowScale (d : ℕ) :
    seedScaleQ (d : ℚ) = Li2Lean.P0.Integerization.p0RowScale 2 32 d := by
  funext r
  by_cases hr : r.val < 32 <;>
    simp [seedScaleQ, Li2Lean.P0.Integerization.p0RowScale, hr] <;> norm_num

/-- Common row-clearing denominator used for the finite seed. -/
def clearD : ℕ := 32433859254793982911622772305630400

theorem clearD_mod83 : (clearD : F83) = 79 := by
  calc
    (clearD : F83) = ((clearD % 83 : Nat) : F83) :=
      (ZMod.natCast_mod clearD 83).symm
    _ = 79 := by norm_num [clearD]

theorem clearD_pow96_mod83 : (clearD : F83) ^ 96 = 10 := by
  rw [clearD_mod83]
  decide

/-- The integerized determinant residue 51 must be divided by the row
scaling determinant 10 to recover the literal seed determinant residue 30. -/
theorem integerized_residue_normalization :
    (51 : F83) / 10 = 30 := by
  have h10 : (10 : F83) * 25 = 1 := by decide
  rw [div_eq_mul_inv, inv_eq_of_mul_eq_one_right h10]
  decide

/-- The first upper-block entry of the `a=2`, `g=16` seed. -/
theorem p0CQ_2_16_8_0_value :
    p0CQ (2 : ℚ) 16 8 0 = (-188280575 / 8 : ℚ) := by
  norm_num [p0CQ, p0UQ, Nat.choose]

theorem p0CQ_2_16_8_0_residue :
    ∀ hcop : Nat.Coprime (p0CQ (2 : ℚ) 16 8 0).den 83,
      residueOf (p0CQ (2 : ℚ) 16 8 0) hcop = (45 : F83) := by
  intro hcop
  have hq := p0CQ_2_16_8_0_value
  have hnum : (p0CQ (2 : ℚ) 16 8 0).num = -188280575 := by
    have hnum0 := congrArg Rat.num hq
    norm_num at hnum0
    exact hnum0
  have hden : (p0CQ (2 : ℚ) 16 8 0).den = 8 := by
    rw [hq]
    norm_num
  change ((p0CQ (2 : ℚ) 16 8 0).num : F83) *
      ((p0CQ (2 : ℚ) 16 8 0).den : F83)⁻¹ = 45
  rw [hnum, hden]
  change ((-188280575 : F83) * ((8 : F83)⁻¹)) = 45
  have h8inv : ((8 : F83)⁻¹) = 52 := by
    apply inv_eq_of_mul_eq_one_right
    decide
  rw [h8inv]
  decide

theorem p0CQ_2_16_8_0_certificate :
    (reducedOf (p0CQ (2 : ℚ) 16 8 0) (by
      simp only [p0CQ_2_16_8_0_value]
      norm_num)).residue = (45 : F83) := by
  rw [reducedOf_residue]
  apply p0CQ_2_16_8_0_residue

end ControlledResidue

end Li2Lean.P0
