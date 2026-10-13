/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.IntegerizationS08Determinant
import Li2Lean.P0.IntegerizationFeatureBridge
import Li2Lean.P0.IntegerizationScalarSpecialization

/-!
# S08: lift the feature divisibility to every determinant coefficient

1. Bivariate integrality: `d_U^(3m) · formalCanonicalPolynomial m ∈ ℤ[T][a]`
   for `m = 4h` (row scales `d_U` on the top block and `d_U^2` on the lower
   block). Feature divisibility is proved for the formal determinant; its
   equality with the actual matrix is checked at the specialization `a = 2`.
2. Monomial descent: `a^N` divides the integer bivariate polynomial.
3. Specialization `a = 2`: `2^N` divides every `T`-coefficient of the
   integerized actual determinant, i.e. the coefficient witness consumed by
   `p0IntegerizerFeatureDivisibility_of_coeff_witness`.
-/

namespace Li2Lean.P0.Integerization.S08

open Finset

noncomputable section

/-- Integer bivariate polynomials inside `ℚ[T][a]`. -/
abbrev psi : Polynomial (Polynomial ℤ) →+* BivPoly :=
  Polynomial.mapRingHom (Polynomial.mapRingHom (Int.castRingHom ℚ))

/-- Rational constants as a ring hom. -/
abbrev rc : ℚ →+* BivPoly := Polynomial.C.comp Polynomial.C

theorem rc_eq (q : ℚ) : rc q = ratConst q := rfl

theorem int_mem (z : ℤ) : ratConst (z : ℚ) ∈ psi.range :=
  ⟨Polynomial.C (Polynomial.C z), by simp [ratConst]⟩

theorem isInt_mem {q : ℚ} (hq : ∃ z : ℤ, q = z) : ratConst q ∈ psi.range := by
  obtain ⟨z, rfl⟩ := hq
  exact int_mem z

theorem aVar_mem : aVar ∈ psi.range :=
  ⟨Polynomial.X, by simp [aVar]⟩

theorem CX_mem : (Polynomial.C Polynomial.X : BivPoly) ∈ psi.range :=
  ⟨Polynomial.C Polynomial.X, by simp⟩

theorem one_mem' : ratConst 1 ∈ psi.range := by
  simpa using int_mem 1

theorem formalU_mem (g i : ℕ) : formalU g i ∈ psi.range :=
  mul_mem (by simpa using int_mem ((i + g).choose g : ℤ)) (pow_mem aVar_mem _)

theorem formalQNum_mem (g s : ℕ) : formalQNum g s ∈ psi.range :=
  mul_mem (pow_mem (sub_mem aVar_mem one_mem') _)
    (sub_mem (pow_mem aVar_mem _) (pow_mem (sub_mem aVar_mem one_mem') _))

theorem formalA_mem (g i j : ℕ) : formalA g i j ∈ psi.range := by
  unfold formalA
  split_ifs
  · exact formalU_mem g i
  · exact zero_mem _

/-! ### Integer scalars -/

theorem isInt_mul {a b : ℚ} (ha : ∃ z : ℤ, a = z) (hb : ∃ z : ℤ, b = z) :
    ∃ z : ℤ, a * b = z := by
  obtain ⟨x, rfl⟩ := ha
  obtain ⟨y, rfl⟩ := hb
  exact ⟨x * y, by push_cast; ring⟩

theorem isInt_div_of_le {d U k : ℕ} (hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d)
    (hk1 : 1 ≤ k) (hkU : k ≤ U) : ∃ z : ℤ, (d : ℚ) * (k : ℚ)⁻¹ = z := by
  obtain ⟨e, he⟩ := hd k hk1 hkU
  refine ⟨e, ?_⟩
  have hk0 : (k : ℚ) ≠ 0 := by exact_mod_cast (show k ≠ 0 by omega)
  rw [he]
  push_cast
  field_simp

theorem isInt_div_sub {d U i j : ℕ} (hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d)
    (hij : i ≠ j) (hiU : i ≤ U) (hjU : j ≤ U) :
    ∃ z : ℤ, (d : ℚ) * ((j : ℚ) - (i : ℚ))⁻¹ = z := by
  rcases Nat.lt_or_gt_of_ne hij with h | h
  · have e : (j : ℚ) - i = ((j - i : ℕ) : ℚ) := by
      rw [Nat.cast_sub h.le]
    rw [e]
    exact isInt_div_of_le hd (by omega) (by omega)
  · have e : (j : ℚ) - i = -((i - j : ℕ) : ℚ) := by
      rw [Nat.cast_sub h.le]
      ring
    obtain ⟨z, hz⟩ := isInt_div_of_le hd (k := i - j) (by omega) (by omega)
    refine ⟨-z, ?_⟩
    rw [e, inv_neg, mul_neg, hz]
    push_cast
    ring

/-! ### Scaled entries -/

theorem ratConst_mul (a b : ℚ) : ratConst (a * b) = ratConst a * ratConst b := by
  simp [ratConst]

theorem scaled_formalTScaled_mem {d U : ℕ} (hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d) {g x : ℕ} (hgU : g ≤ U) (hxU : x ≤ U) :
    ratConst (d : ℚ) * formalTScaled g x ∈ psi.range := by
  unfold formalTScaled
  rw [mul_add]
  apply add_mem
  · rw [mul_left_comm, mul_sum]
    apply mul_mem (pow_mem (sub_mem aVar_mem one_mem') _)
    apply sum_mem
    intro r hr
    have hr' := mem_range.mp hr
    rw [show ratConst (d : ℚ) * (formalU g (x - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹)) =
        formalU g (x - (r + 1)) * ratConst ((d : ℚ) * (r + 1 : ℚ)⁻¹) by
      rw [ratConst_mul]; ring]
    apply mul_mem (formalU_mem _ _)
    apply isInt_mem
    have := isInt_div_of_le hd (k := r + 1) (by omega) (by omega)
    simpa using this
  · rw [mul_left_comm, mul_sum]
    apply mul_mem (pow_mem aVar_mem _)
    apply sum_mem
    intro s hs
    have hs' := mem_range.mp hs
    rw [← mul_assoc, ← ratConst_mul]
    apply mul_mem _ (formalQNum_mem _ _)
    apply isInt_mem
    obtain ⟨z, hz⟩ := isInt_div_of_le hd (k := s + 1) (by omega) (by omega)
    refine ⟨z * ((-1) ^ s * ((x + g).choose (g - (s + 1)) : ℤ)), ?_⟩
    push_cast at hz ⊢
    rw [← hz]
    ring

theorem scaled_formalBScaled_mem {d U : ℕ} (hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d) {g x : ℕ} (hgU : g ≤ U) (hxU : x ≤ U) :
    ratConst ((d : ℚ) ^ 2) * formalBScaled g x ∈ psi.range := by
  unfold formalBScaled
  rw [mul_sub]
  apply sub_mem
  · rw [mul_left_comm, mul_sum]
    apply mul_mem (pow_mem (sub_mem aVar_mem one_mem') _)
    apply sum_mem
    intro r hr
    have hr' := mem_range.mp hr
    rw [show ratConst ((d : ℚ) ^ 2) *
        (formalU g (x - (r + 1)) * ratConst ((r + 1 : ℚ)⁻¹ ^ 2)) =
        formalU g (x - (r + 1)) * ratConst ((d : ℚ) ^ 2 * (r + 1 : ℚ)⁻¹ ^ 2) by
      rw [ratConst_mul]; ring]
    apply mul_mem (formalU_mem _ _)
    apply isInt_mem
    obtain ⟨z, hz⟩ := isInt_div_of_le hd (k := r + 1) (by omega) (by omega)
    refine ⟨z ^ 2, ?_⟩
    push_cast at hz ⊢
    rw [← hz]
    ring
  · rw [mul_left_comm, mul_sum]
    apply mul_mem (pow_mem aVar_mem _)
    apply sum_mem
    intro s hs
    have hs' := mem_Icc.mp hs
    rw [← mul_assoc, ← ratConst_mul, mul_sum]
    apply sum_mem
    intro r hr
    have hr' := mem_range.mp hr
    rw [← mul_assoc, ← ratConst_mul]
    apply mul_mem _ (formalQNum_mem _ _)
    apply isInt_mem
    obtain ⟨z1, hz1⟩ := isInt_div_of_le hd (k := s) (by omega) (by omega)
    obtain ⟨z2, hz2⟩ := isInt_div_of_le hd (k := r + 1) (by omega) (by omega)
    refine ⟨z1 * z2 * ((-1) ^ s * ((x + g).choose (g - s) : ℤ)), ?_⟩
    push_cast at hz1 hz2 ⊢
    rw [← hz1, ← hz2]
    ring

theorem scaled_formalC_mem {d U : ℕ} (hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d) {g i j : ℕ} (hiU : i ≤ U) (hjU : j ≤ U)
    (hisU : i + g ≤ U) :
    ratConst (d : ℚ) * formalC g i j ∈ psi.range := by
  unfold formalC
  split_ifs with hij
  · rw [show ratConst (d : ℚ) *
        (-formalU g i * ratConst (∑ s ∈ range g, ((i + s + 1 : ℚ)⁻¹))) =
        -(formalU g i * ratConst ((d : ℚ) * ∑ s ∈ range g, ((i + s + 1 : ℚ)⁻¹))) by
      rw [ratConst_mul]; ring]
    apply neg_mem
    apply mul_mem (formalU_mem _ _)
    apply isInt_mem
    rw [mul_sum]
    have hz : ∀ s ∈ range g, ∃ z : ℤ, (d : ℚ) * ((i : ℚ) + s + 1)⁻¹ = z := by
      intro s hs
      have hs' := mem_range.mp hs
      have := isInt_div_of_le hd (k := i + s + 1) (by omega) (by omega)
      simpa using this
    choose! zf hzf using hz
    refine ⟨∑ s ∈ range g, zf s, ?_⟩
    push_cast
    exact sum_congr rfl hzf
  · rw [show ratConst (d : ℚ) *
        ((formalU g i - formalU g j) * ratConst (((j : ℚ) - (i : ℚ))⁻¹)) =
        (formalU g i - formalU g j) * ratConst ((d : ℚ) * ((j : ℚ) - (i : ℚ))⁻¹) by
      rw [ratConst_mul]; ring]
    exact mul_mem (sub_mem (formalU_mem _ _) (formalU_mem _ _))
      (isInt_mem (isInt_div_sub hd hij hiU hjU))

theorem scaled_lower_mem {d U : ℕ} (hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d) {g i j : ℕ} (hiU : i ≤ U) (hjU : j ≤ U) (hgU : g ≤ U) :
    ratConst ((d : ℚ) ^ 2) *
      (formalB g i j - Polynomial.C Polynomial.X * formalA g i j) ∈ psi.range := by
  rw [mul_sub]
  apply sub_mem
  · unfold formalB
    split_ifs with hij
    · exact scaled_formalBScaled_mem hd hgU hiU
    · have e : ratConst ((d : ℚ) ^ 2) *
          ((formalTScaled g i - formalTScaled g j) * ratConst (((j : ℚ) - (i : ℚ))⁻¹)) =
          (ratConst (d : ℚ) * formalTScaled g i - ratConst (d : ℚ) * formalTScaled g j) *
            ratConst ((d : ℚ) * ((j : ℚ) - (i : ℚ))⁻¹) := by
        rw [show (d : ℚ) ^ 2 = (d : ℚ) * (d : ℚ) by ring, ratConst_mul, ratConst_mul]
        ring
      rw [e]
      exact mul_mem (sub_mem (scaled_formalTScaled_mem hd hgU hiU)
        (scaled_formalTScaled_mem hd hgU hjU)) (isInt_mem (isInt_div_sub hd hij hiU hjU))
  · have e : ratConst ((d : ℚ) ^ 2) * (Polynomial.C Polynomial.X * formalA g i j) =
        Polynomial.C Polynomial.X * (ratConst ((d : ℚ) ^ 2) * formalA g i j) := by ring
    rw [e]
    apply mul_mem CX_mem
    apply mul_mem _ (formalA_mem _ _ _)
    exact isInt_mem ⟨(d : ℤ) ^ 2, by push_cast; ring⟩


/-! ### Bivariate integrality of the literal determinant -/

theorem prod_rowScale (m : ℕ) (d : ℚ) :
    ∏ r : Fin (2 * m), (if r.val < m then d else d ^ 2) = d ^ (3 * m) := by
  rw [Fin.prod_univ_eq_prod_range (fun k => if k < m then d else d ^ 2) (2 * m)]
  rw [two_mul, prod_range_add]
  have h1 : ∏ x ∈ range m, (if x < m then d else d ^ 2) = d ^ m := by
    rw [prod_congr rfl (fun x hx => if_pos (mem_range.mp hx))]
    simp
  have h2 : ∏ x ∈ range m, (if m + x < m then d else d ^ 2) = (d ^ 2) ^ m := by
    rw [prod_congr rfl (fun x _ => if_neg (by omega : ¬ m + x < m))]
    simp
  rw [h1, h2, ← pow_mul, ← pow_add]
  ring_nf

theorem formalCanonical_integerized (h : ℕ) (hh : 1 ≤ h) :
    ∃ Z : Polynomial (Polynomial ℤ),
      psi Z = ratConst ((p0DenominatorLcm (4 * h) : ℚ) ^ (3 * (4 * h))) *
        formalCanonicalPolynomial (4 * h) := by
  classical
  set m := 4 * h with hm
  set d := p0DenominatorLcm m with hdd
  set U := p0DenominatorU m with hU
  have hUv : U = 8 * h - 1 := by
    rw [hU, p0DenominatorU]
    omega
  have hd : ∀ s, 1 ≤ s → s ≤ U → s ∣ d := fun s h1 h2 => p0_dvd_denominatorLcm h1 h2
  let scale : Fin (2 * m) → ℚ := fun r => if r.val < m then (d : ℚ) else (d : ℚ) ^ 2
  have hmem : ∀ r c : Fin (2 * m),
      ratConst (scale r) * formalMatrix m r c ∈ psi.range := by
    intro r c
    have hr := r.isLt
    have hc := c.isLt
    have e4 : m / 4 = h := by omega
    have e2 : m / 2 = 2 * h := by omega
    unfold formalMatrix
    by_cases hrm : r.val < m
    · simp only [scale, if_pos hrm]
      apply scaled_formalC_mem hd
      · rw [e4, hUv]; omega
      · rw [hUv]; omega
      · rw [e4, e2, hUv]; omega
    · simp only [scale, if_neg hrm]
      apply scaled_lower_mem hd
      · rw [e4, hUv]; omega
      · rw [hUv]; omega
      · rw [e2, hUv]; omega
  choose Z0 hZ0 using hmem
  refine ⟨Matrix.det (Matrix.of fun r c => Z0 r c), ?_⟩
  rw [RingHom.map_det]
  have hM : psi.mapMatrix (Matrix.of fun r c => Z0 r c) =
      (fun r c => rc (scale r) * formalMatrix m r c) := by
    funext r c
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact hZ0 r c
  rw [hM, det_row_scale, ← map_prod, prod_rowScale m (d : ℚ)]
  rfl

/-! ### The coefficient witness for the actual `a = 2` family -/

theorem mapRingHom_eval (f : ℤ →+* ℚ) (Z : Polynomial (Polynomial ℤ)) (x : Polynomial ℤ) :
    Polynomial.mapRingHom f (Z.eval x) =
      (Z.map (Polynomial.mapRingHom f)).eval (Polynomial.mapRingHom f x) := by
  rw [Polynomial.eval_map, Polynomial.eval, Polynomial.hom_eval₂, RingHom.comp_id]

theorem p0A2_feature_coeff_witness_rat (h : ℕ) (hh : 1 ≤ h) :
    ∃ P : Polynomial ℤ,
      (∀ n, (p0A2TwoFeatureFactor (4 * h) : ℤ) ∣ P.coeff n) ∧
        Polynomial.map (Int.castRingHom ℚ) P =
          Polynomial.C (p0A2BaselineD (4 * h)) * p0CanonicalPolynomial 2 (4 * h) := by
  obtain ⟨Z, hZ⟩ := formalCanonical_integerized h hh
  have hdivQ : (Polynomial.X : BivPoly) ^ (13 * h ^ 2 - 4 * h) ∣
      Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) Z := by
    have : psi Z = Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) Z := rfl
    rw [← this, hZ]
    exact dvd_mul_of_dvd_right (formalCanonical_feature_dvd h hh) _
  have hspec := IntegerizationScalarSpecialization.scalar_two_pow_dvd_of_rat_map Z _ hdivQ
  refine ⟨Z.eval (Polynomial.C 2), ?_, ?_⟩
  · intro n
    rw [p0A2TwoFeatureFactor_eq_explicit (h := h) rfl]
    have := (Polynomial.C_dvd_iff_dvd_coeff _ _).mp hspec n
    simpa using this
  · have h1 := mapRingHom_eval (Int.castRingHom ℚ) Z (Polynomial.C 2)
    rw [Polynomial.coe_mapRingHom] at h1
    rw [h1]
    have h2 : Polynomial.map (Polynomial.mapRingHom (Int.castRingHom ℚ)) Z = psi Z := rfl
    rw [h2, hZ]
    have h3 : Polynomial.map (Int.castRingHom ℚ) (Polynomial.C (2 : ℤ)) =
        Polynomial.C (2 : ℚ) := by rw [Polynomial.map_C]; rfl
    rw [h3]
    have h4 := formalCanonical_outerEval_two (4 * h) (dvd_mul_right 4 h)
    have h5 : outerEval 2 (ratConst ((p0DenominatorLcm (4 * h) : ℚ) ^ (3 * (4 * h))) *
        formalCanonicalPolynomial (4 * h)) =
        Polynomial.C ((p0DenominatorLcm (4 * h) : ℚ) ^ (3 * (4 * h))) *
          p0CanonicalPolynomial 2 (4 * h) := by
      rw [map_mul, h4]
      simp [outerEval, ratConst]
    rw [p0A2BaselineD]
    exact h5

/-- The S08 coefficient witness in exactly the form consumed by
`p0IntegerizerFeatureDivisibility_of_coeff_witness`, for any P0 family with
base `a = 2`. -/
theorem p0A2_feature_coeff_witness (F : P0Family) (hF : F.a = 2) :
    ∀ m, 0 < m → 4 ∣ m →
      ∃ P : Polynomial ℤ,
        (∀ n, (p0A2TwoFeatureFactor m : ℤ) ∣ P.coeff n) ∧
          Polynomial.map (Int.castRingHom ℝ) P =
            Polynomial.C (p0A2BaselineD m : ℝ) * F.G m := by
  intro m hm h4
  obtain ⟨h, rfl⟩ := h4
  have hh : 1 ≤ h := by omega
  obtain ⟨P, hPdiv, hPmap⟩ := p0A2_feature_coeff_witness_rat h hh
  refine ⟨P, hPdiv, ?_⟩
  rw [F.G_source (4 * h) (dvd_mul_right 4 h), hF]
  have hcomp : Polynomial.map (Int.castRingHom ℝ) P =
      Polynomial.map (algebraMap ℚ ℝ) (Polynomial.map (Int.castRingHom ℚ) P) := by
    rw [Polynomial.map_map]
    congr 1
  rw [hcomp, hPmap, Polynomial.map_mul, Polynomial.map_C]
  simp

/-- S08 closes the feature-divisibility field: for the `a = 2` family the
feature-rate certificate needs only the remaining-denominator rate. -/
noncomputable def p0A2FeatureRateCertificate (F : P0Family) (hF : F.a = 2) (rate : ℝ)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (p0A2TwoFeatureD m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε) :
    P0IntegerizerFeatureRateCertificate F rate :=
  p0IntegerizerFeatureDivisibility_of_coeff_witness F rate p0A2TwoFeatureD
    p0A2TwoFeatureFactor (p0A2_feature_coeff_witness F hF)
    (fun _ _ h4 => p0A2TwoFeatureFactor_pos h4)
    (fun _ _ h4 => p0A2TwoFeatureD_factorization h4) hrate

/-- The `featureDivisibility` field of `P0IntegerizerFeatureRateCertificate`
for the explicit 2-adic feature factor, unconditionally. -/
theorem p0A2_feature_divisibility (F : P0Family) (hF : F.a = 2) :
    ∀ m, 0 < m → 4 ∣ m →
      ∃ P : Polynomial ℤ,
        Polynomial.C (p0A2TwoFeatureFactor m : ℤ) ∣ P ∧
          Polynomial.map (Int.castRingHom ℝ) P =
            Polynomial.C (p0A2BaselineD m : ℝ) * F.G m := by
  intro m hm h4
  obtain ⟨P, hPc, hPm⟩ := p0A2_feature_coeff_witness F hF m hm h4
  exact ⟨P, polynomial_C_dvd_of_coeff_dvd P _ hPc, hPm⟩

/-- Integerizer contract at any rate from the degree bound and the
remaining-denominator rate only; the feature divisibility is discharged. -/
theorem p0A2_integerizerBoundAt_of_remaining_rate (F : P0Family) (hF : F.a = 2)
    (rate : ℝ)
    (hdegree : ∀ m, 0 < m → 4 ∣ m → (F.G m).natDegree ≤ m)
    (hrate : ∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (p0A2TwoFeatureD m : ℝ) / (m : ℝ) ^ 2 ≤ rate + ε) :
    P0IntegerizerBoundAt F rate :=
  p0IntegerizerBoundAt_of_feature_rate_certificate F hF hdegree
    (p0A2FeatureRateCertificate F hF rate hrate)

end

end Li2Lean.P0.Integerization.S08

#print axioms Li2Lean.P0.Integerization.S08.formalCanonical_integerized
#print axioms Li2Lean.P0.Integerization.S08.p0A2_feature_coeff_witness_rat
#print axioms Li2Lean.P0.Integerization.S08.p0A2_feature_coeff_witness
#print axioms Li2Lean.P0.Integerization.S08.p0A2FeatureRateCertificate
#print axioms Li2Lean.P0.Integerization.S08.p0A2_feature_divisibility
#print axioms Li2Lean.P0.Integerization.S08.p0A2_integerizerBoundAt_of_remaining_rate
