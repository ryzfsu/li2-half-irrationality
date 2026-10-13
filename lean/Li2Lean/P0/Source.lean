/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.Kit.LogMonomial

open MeasureTheory

namespace Li2Lean

noncomputable section

/-- The base logarithm `L(a)` in the paper's source section, docs/6333 §2. -/
def sourceLog (a : ℝ) : ℝ := Real.log (1 - a⁻¹)

/-- The base dilogarithm series `beta(a)`, docs/6333 §2. -/
def sourceBeta (a : ℝ) : ℝ :=
  ∑' r : ℕ, (a⁻¹) ^ (r + 1) / ((r : ℝ) + 1) ^ 2

/--
Integral representation of the same base dilogarithm series. The power-log
moment helper is used termwise; this auxiliary identity does not replace the
paper's source Mellin statement.
-/
theorem sourceBeta_integral (a : ℝ) (ha : 1 < a) :
    sourceBeta a = ∫ x in (0 : ℝ)..1, (-Real.log x) / (a - x) := by
  let μ : Measure ℝ := volume.restrict (Set.Ioo (0 : ℝ) 1)
  let q : ℝ := a⁻¹
  let F : ℕ → ℝ → ℝ := fun r x => q ^ (r + 1) * (x ^ r * (-Real.log x))
  have ha0 : 0 < a := lt_trans zero_lt_one ha
  have hqpos : 0 < q := by simp [q, ha0]
  have hqmul : a * q = 1 := by simp [q, ha0.ne']
  have hq_lt : q < 1 := by nlinarith [ha, hqpos, hqmul]
  have hqabs : |q| < 1 := by simpa [abs_of_pos hqpos] using hq_lt
  have hqsum : Summable (fun r : ℕ => q ^ (r + 1)) := by
    have hgeom : Summable (fun r : ℕ => q ^ r) :=
      (hasSum_geometric_of_abs_lt_one hqabs).summable
    have hmul : Summable (fun r : ℕ => q * q ^ r) := hgeom.mul_left q
    convert hmul using 1
    ext r
    rw [pow_succ]
    ring
  have hF (r : ℕ) : Integrable (F r) μ := by
    have hbase : IntegrableOn (fun x : ℝ => x ^ r * (-Real.log x))
        (Set.Ioo (0 : ℝ) 1) :=
      (intervalIntegrable_iff_integrableOn_Ioo_of_le
        (by norm_num : (0 : ℝ) ≤ 1)).mp
        (Li2Lean.Kit.intervalIntegrable_pow_neg_log r)
    simpa only [μ, F] using hbase.const_mul (q ^ (r + 1))
  have hbase (r : ℕ) :
      (∫ x : ℝ, x ^ r * (-Real.log x) ∂μ) =
        1 / ((r + 1 : ℕ) : ℝ) ^ 2 := by
    simpa only [μ, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      integral_Ioc_eq_integral_Ioo] using Li2Lean.Kit.integral_pow_neg_log r
  have hterm (r : ℕ) :
      (∫ x : ℝ, F r x ∂μ) = q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2 := by
    change (∫ x : ℝ, q ^ (r + 1) * (x ^ r * (-Real.log x)) ∂μ) = _
    rw [integral_const_mul, hbase]
    ring
  have hnorm (r : ℕ) :
      (∫ x : ℝ, ‖F r x‖ ∂μ) = q ^ (r + 1) / ((r + 1 : ℕ) : ℝ) ^ 2 := by
    calc
      (∫ x : ℝ, ‖F r x‖ ∂μ) = ∫ x : ℝ, F r x ∂μ := by
        apply integral_congr_ae
        filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
        apply Real.norm_of_nonneg
        dsimp [F]
        exact mul_nonneg (pow_nonneg hqpos.le _)
          (mul_nonneg (pow_nonneg hx.1.le _) (neg_nonneg.mpr
            (Real.log_nonpos hx.1.le hx.2.le)))
      _ = _ := hterm r
  have hsum : Summable (fun r : ℕ => ∫ x : ℝ, ‖F r x‖ ∂μ) := by
    apply hqsum.of_norm_bounded
    intro r
    rw [hnorm]
    have hr : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ r + 1 by omega)
    have hr2 : (1 : ℝ) ≤ ((r + 1 : ℕ) : ℝ) ^ 2 := by nlinarith
    rw [Real.norm_of_nonneg (div_nonneg (pow_nonneg hqpos.le _) (sq_nonneg _))]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [mul_nonneg (pow_nonneg hqpos.le (r + 1)) (sub_nonneg.mpr hr2)]
  have hgeom (x : ℝ) (hx : x ∈ Set.Ioo (0 : ℝ) 1) :
      HasSum (fun r : ℕ => F r x) ((-Real.log x) / (a - x)) := by
    have hqx0 : 0 ≤ q * x := mul_nonneg hqpos.le hx.1.le
    have hqx1 : q * x < 1 := by
      have h := mul_pos hqpos (sub_pos.mpr hx.2)
      nlinarith
    have hqx : |q * x| < 1 := by simpa [abs_of_nonneg hqx0] using hqx1
    have hgeo := (hasSum_geometric_of_abs_lt_one hqx).mul_left q
    have hseries : HasSum (fun r : ℕ => q ^ (r + 1) * x ^ r) (q / (1 - q * x)) := by
      convert hgeo using 1
      · ext r
        rw [pow_succ]
        ring
      · simp only [div_eq_mul_inv]
    have hmul : HasSum (fun r : ℕ =>
        (-Real.log x) * (q ^ (r + 1) * x ^ r))
        ((-Real.log x) * (q / (1 - q * x))) := hseries.mul_left (-Real.log x)
    have hterm_eq (r : ℕ) :
        (-Real.log x) * (q ^ (r + 1) * x ^ r) = F r x := by
      dsimp [F]
      ring
    have hvalue : (-Real.log x) * (q / (1 - q * x)) =
        (-Real.log x) / (a - x) := by
      dsimp [q]
      have hax : a - x ≠ 0 := ne_of_gt (sub_pos.mpr (lt_trans hx.2 ha))
      field_simp [ha0.ne', hax]
    simpa only [hterm_eq, hvalue] using hmul
  have hgeom_ae : (fun x : ℝ => ∑' r : ℕ, F r x) =ᵐ[μ]
      (fun x => (-Real.log x) / (a - x)) := by
    filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
    exact (hgeom x hx).tsum_eq
  calc
    sourceBeta a = ∑' r : ℕ, ∫ x : ℝ, F r x ∂μ := by
      simp only [sourceBeta, hterm, q, Nat.cast_add, Nat.cast_one]
    _ = ∫ x : ℝ, ∑' r : ℕ, F r x ∂μ :=
      integral_tsum_of_summable_integral_norm hF hsum
    _ = ∫ x in (0 : ℝ)..1, (-Real.log x) / (a - x) := by
      rw [integral_congr_ae hgeom_ae]
      simp only [μ, intervalIntegral.integral_of_le
        (show (0 : ℝ) ≤ 1 by norm_num), integral_Ioc_eq_integral_Ioo]

/-- The finite first base moment `t_i^0(a)`, docs/6333 §2. -/
def sourceT0 (a : ℝ) (i : ℕ) : ℝ :=
  ∑ r ∈ Finset.range i,
    a ^ (i - (r + 1)) / ((r : ℝ) + 1)

/-- The finite second base moment `b_i^0(a)`, docs/6333 §2. -/
def sourceB0 (a : ℝ) (i : ℕ) : ℝ :=
  ∑ r ∈ Finset.range i,
    a ^ (i - (r + 1)) / ((r : ℝ) + 1) ^ 2

/-- The undeformed divided-difference bank `C^0_ij(a)`, docs/6333 §2. -/
def sourceC0 (a : ℝ) (i j : ℕ) : ℝ :=
  if i = j then 0 else
    (a ^ i - a ^ j) / ((j : ℝ) - (i : ℝ))

/-- The undeformed first-moment bank `B^0_ij(a)`, docs/6333 §2. -/
def sourceB0ij (a : ℝ) (i j : ℕ) : ℝ :=
  if i = j then sourceB0 a i else
    (sourceT0 a i - sourceT0 a j) / ((j : ℝ) - (i : ℝ))

/-- The undeformed diagonal bank `A^0_ij(a)`, docs/6333 §2. -/
def sourceA0 (a : ℝ) (i j : ℕ) : ℝ :=
  if i = j then a ^ i else 0

/-- The Mellin entry `M_ij(a)` in (2.3), docs/6333 §2. -/
def sourceM (a : ℝ) (i j : ℕ) : ℝ :=
  sourceB0ij a i j + sourceLog a * sourceC0 a i j -
    sourceBeta a * sourceA0 a i j

/-- The Mellin-series side of (2.3), indexed from `r = 1`. -/
def sourceMSeries (a : ℝ) (i j : ℕ) : ℝ :=
  -∑' r : ℕ,
    (a⁻¹) ^ (r + 1) /
      ((i + r + 1 : ℕ) : ℝ) / ((j + r + 1 : ℕ) : ℝ)

/-- The integral side of (2.3), with the paper's `dy dx` order. -/
def sourceMIntegral (a : ℝ) (i j : ℕ) : ℝ :=
  -∫ x in (0 : ℝ)..1, ∫ y in (0 : ℝ)..1,
    x ^ i * y ^ j / (a - x * y)

/--
Exact statement of Lemma `lem:source-mellin`, docs/6333 §2 and
`output/li2-half-paper-v10/sec-source.tex`.  The series and integral
normalizations are both part of the interface.
-/
def sourceMellinStatement : Prop :=
  ∀ a : ℝ, 1 < a → ∀ i j : ℕ,
    sourceM a i j = sourceMSeries a i j ∧
      sourceM a i j = sourceMIntegral a i j

/-- The paper's `Q_s(a)=(a/(a-1))^s-1`, docs/6333 §2. -/
def sourceQ (a : ℝ) (s : ℕ) : ℝ :=
  (a / (a - 1)) ^ s - 1

/-- The parameter-dependent `U_i(a)`, docs/6333 §2. -/
def sourceU (a : ℝ) (g i : ℕ) : ℝ :=
  a ^ i * (Nat.choose (i + g) g : ℝ)

/-- The parameter-dependent finite first derivative moment, docs/6333 §2. -/
def sourceT (a : ℝ) (g i : ℕ) : ℝ :=
  (∑ r ∈ Finset.range i,
      sourceU a g (i - (r + 1)) / ((r : ℝ) + 1)) +
    a ^ i * ∑ s ∈ Finset.range g,
      (((-1 : ℝ) ^ s / ((s : ℝ) + 1)) *
        (Nat.choose (i + g) (g - (s + 1)) : ℝ) * sourceQ a (s + 1))

/-- The diagonal parameter-dependent second derivative moment, docs/6333 §2. -/
def sourceBdiag (a : ℝ) (g i : ℕ) : ℝ :=
  (∑ r ∈ Finset.range i,
      sourceU a g (i - (r + 1)) / ((r : ℝ) + 1) ^ 2) -
    a ^ i * ∑ s ∈ Finset.Icc 2 g,
      (((-1 : ℝ) ^ s / (s : ℝ)) *
        (Nat.choose (i + g) (g - s) : ℝ) *
        (∑ r ∈ Finset.range (s - 1),
          sourceQ a (r + 1) / ((r : ℝ) + 1)))

/-- The parameter-dependent `A_ij(a)`, docs/6333 §2. -/
def sourceA (a : ℝ) (g i j : ℕ) : ℝ :=
  if i = j then sourceU a g i else 0

/-- The parameter-dependent `C_ij(a)`, docs/6333 §2. -/
def sourceC (a : ℝ) (g i j : ℕ) : ℝ :=
  if i = j then
    -sourceU a g i * ∑ s ∈ Finset.range g, ((i + s + 1 : ℕ) : ℝ)⁻¹
  else
    (sourceU a g i - sourceU a g j) / ((j : ℝ) - (i : ℝ))

/-- The parameter-dependent `B_ij(a)`, docs/6333 §2. -/
def sourceB (a : ℝ) (g i j : ℕ) : ℝ :=
  if i = j then sourceBdiag a g i else
    (sourceT a g i - sourceT a g j) / ((j : ℝ) - (i : ℝ))

/-- The normalized derivative `D_g M_ij(a)` from docs/6333 §2. -/
def sourceDg (g : ℕ) (f : ℝ → ℝ) (a : ℝ) : ℝ :=
  iteratedDeriv g (fun x : ℝ => x ^ g * f x) a /
    (Nat.factorial g : ℝ)

/-- The derivative bank `D_g M_ij(a)` from docs/6333 §2. -/
def sourceDgM (g : ℕ) (i j : ℕ) (a : ℝ) : ℝ :=
  sourceDg g (fun x => sourceM x i j) a

/-- The weight series in (2.4), using `k+1` for the paper's `r`. -/
def sourceN (g i j : ℕ) : ℝ :=
  (-1 : ℝ) ^ (g + 1) *
    ∑' k : ℕ,
      if g < k + 1 then
        (Nat.choose k g : ℝ) * ((2 : ℝ)⁻¹) ^ (k + 1) /
          ((i + k + 1 : ℕ) : ℝ) / ((j + k + 1 : ℕ) : ℝ)
      else 0

/-- The monomial derivative formula for `D_g`, docs/6333 §2. -/
def sourceDgMonomialStatement : Prop :=
  ∀ g r : ℕ, 1 ≤ r → ∀ a : ℝ, 1 < a →
    sourceDg g (fun x => (x⁻¹) ^ r) a =
      if r ≤ g then 0 else
        (-1 : ℝ) ^ g * (Nat.choose (r - 1) g : ℝ) * (a⁻¹) ^ r

/-- The differentiated Mellin series at `a=2`, equation (2.4), docs/6333 §2. -/
def sourceDgMAtTwoStatement : Prop :=
  ∀ g i j : ℕ, sourceDgM g i j 2 = sourceN g i j

/--
Exact statement of Lemma `lem:source-bank`, docs/6333 §2 and
`output/li2-half-paper-v10/sec-source.tex`. The diagonal and off-diagonal
entries use the same parameter-dependent bank definitions above.
-/
def sourceBankStatement : Prop :=
  ∀ g i j : ℕ, ∀ a : ℝ, 1 < a →
    sourceDgM g i j a =
      sourceB a g i j + sourceLog a * sourceC a g i j -
        sourceBeta a * sourceA a g i j

/--
The explicit source obligations from docs/6333 §2. This is a proposition
passed to later layers, not an axiom; no source theorem is claimed proved by
merely declaring this structure.
-/
structure P0SourceBridge : Prop where
  mellin : sourceMellinStatement
  monomial_derivative : sourceDgMonomialStatement
  differentiated_mellin : sourceDgMAtTwoStatement
  bank : sourceBankStatement

/--
Exact base-two specialization of the corrected rational diagonal term.
For `a=2`, `Q_s(2)=2^s-1`, agreeing with the rational P0 bank.
-/
theorem sourceQ_two (s : ℕ) : sourceQ 2 s = (2 : ℝ) ^ s - 1 := by
  simp [sourceQ]
  norm_num

/-- The rational source bank has the same `Q_s` specialization at `a=2`. -/
theorem p0Q_two (s : ℕ) : p0Q 2 s = (2 : ℚ) ^ s - 1 := by
  norm_num [p0Q]

/-- Regression value distinguishing the corrected general-base diagonal. -/
theorem p0BQQ_three_two_one : p0BQQ 3 2 1 = (1 : ℚ) / 4 := by
  norm_num [p0BQQ, p0Q, p0UQ]

/--
Audit-only copy of the pre-correction diagonal transcription. It is kept out
of the P0 definitions so that the regression below records the exact error
without making the old formula available to later proof layers.
-/
private def legacyP0BQQ (a : ℚ) (g i : ℕ) : ℚ :=
  (∑ r ∈ Finset.range i,
      p0UQ a g (i - (r + 1)) / (r + 1 : ℚ) ^ 2) -
    a ^ i *
      ∑ s ∈ Finset.Icc 2 g,
        ((-1 : ℚ) ^ s / (s : ℚ)) *
          (Nat.choose (i + g) (g - s) : ℚ) *
          (∑ r ∈ Finset.range (s - 1),
            (a ^ (r + 1) - 1) / (r + 1 : ℚ))

/-- Exact difference between the old and corrected source transcriptions. -/
theorem p0BQQ_three_two_one_delta :
    legacyP0BQQ 3 2 1 - p0BQQ 3 2 1 = (-9 : ℚ) / 4 := by
  norm_num [p0BQQ, legacyP0BQQ, p0Q, p0UQ]

end

end Li2Lean
