/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces

namespace Li2Lean
namespace P0

noncomputable section

private theorem p0Entire_product_nat (g i : ℕ) :
    (∏ r ∈ Finset.range g, ((i : ℂ) + (r + 1 : ℕ))) =
      (Nat.factorial g : ℂ) * (Nat.choose (i + g) g : ℂ) := by
  have hnat0 := Nat.ascFactorial_eq_factorial_mul_choose i g
  rw [Nat.ascFactorial_eq_prod_range] at hnat0
  have hnat :
      (∏ r ∈ Finset.range g, (i + (r + 1))) =
        Nat.factorial g * Nat.choose (i + g) g := by
    simpa [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hnat0
  have hcast :
      (∏ r ∈ Finset.range g, (((i + (r + 1)) : ℕ) : ℂ)) =
        ((Nat.factorial g * Nat.choose (i + g) g : ℕ) : ℂ) := by
    exact_mod_cast hnat
  convert hcast using 1 <;> simp [Nat.cast_add, Nat.cast_one]

private theorem p0Entire_exp_nat (i : ℕ) :
    Complex.exp ((i : ℂ) * Complex.ofReal (Real.log 2)) = (2 : ℂ) ^ i := by
  have hlog : Real.exp (Real.log 2) = 2 := Real.exp_log (by norm_num)
  have htwo : Complex.exp (Complex.ofReal (Real.log 2)) = (2 : ℂ) := by
    rw [← Complex.ofReal_exp, hlog]
    norm_num
  rw [Complex.exp_nat_mul, htwo]

/-- At a nonnegative integer, the entire source is the corresponding U_i. -/
theorem p0Entire_nat_eq_U (g i : ℕ) :
    p0Entire g (i : ℂ) = p0U g i := by
  have hfac : (Nat.factorial g : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero g
  rw [p0Entire, p0U, p0Entire_exp_nat, p0Entire_product_nat]
  field_simp

private theorem p0Entire_product_deriv (g : ℕ) (z : ℂ) :
    HasDerivAt (fun w : ℂ => ∏ r ∈ Finset.range g, (w + (r + 1 : ℕ)))
      (∑ r ∈ Finset.range g,
        ∏ j ∈ (Finset.range g).erase r, (z + (j + 1 : ℕ))) z := by
  have h :=
    HasDerivAt.finsetProd
      (u := Finset.range g)
      (f := fun r : ℕ => fun w : ℂ => w + (r + 1 : ℕ))
      (f' := fun _ => (1 : ℂ))
      (x := z) (by
        intro r hr
        simpa using (hasDerivAt_id z).add_const ((r + 1 : ℕ) : ℂ))
  convert h using 1
  · funext w
    simp [Finset.prod_apply]
  · simp only [smul_eq_mul, mul_one]

private theorem p0Entire_product_deriv_nat (g i : ℕ) :
    deriv (fun z : ℂ => ∏ r ∈ Finset.range g, (z + (r + 1 : ℕ))) (i : ℂ) =
      (∏ r ∈ Finset.range g, ((i : ℂ) + (r + 1 : ℕ))) *
        ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹) := by
  have hderiv := p0Entire_product_deriv g (i : ℂ)
  rw [hderiv.deriv, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro r hr
  have hfactor : ((i : ℂ) + (r + 1 : ℕ)) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt (Nat.succ_le_succ (Nat.zero_le (i + r))))
  have herase := Finset.prod_erase_mul (Finset.range g)
    (fun j => (i : ℂ) + (j + 1 : ℕ)) hr
  symm
  rw [← div_eq_mul_inv]
  convert ((eq_div_iff hfactor).2 herase).symm using 1
  simp [Nat.cast_add, Nat.cast_one, Nat.add_assoc]

private theorem p0Entire_hasDerivAt_nat (g i : ℕ) :
    HasDerivAt (p0Entire g)
      ((2 : ℂ) ^ i * (Nat.choose (i + g) g : ℂ) *
        (Complex.ofReal (Real.log 2) +
          ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹))) (i : ℂ) := by
  let P : ℂ → ℂ := fun z => ∏ r ∈ Finset.range g, (z + (r + 1 : ℕ))
  have hExp : HasDerivAt
      (fun z : ℂ => Complex.exp (z * Complex.ofReal (Real.log 2)))
      (Complex.exp ((i : ℂ) * Complex.ofReal (Real.log 2)) *
        Complex.ofReal (Real.log 2)) (i : ℂ) := by
    convert
      (Complex.hasDerivAt_exp
        ((i : ℂ) * Complex.ofReal (Real.log 2))).comp
        (i : ℂ) ((hasDerivAt_id (i : ℂ)).mul_const
          (Complex.ofReal (Real.log 2))) using 1 <;>
      simp [Function.comp_def]
  have hProd : HasDerivAt P
      (∑ r ∈ Finset.range g,
        ∏ j ∈ (Finset.range g).erase r, ((i : ℂ) + (j + 1 : ℕ))) (i : ℂ) := by
    simpa only [P] using p0Entire_product_deriv g (i : ℂ)
  have hPderiv : deriv P (i : ℂ) =
      P (i : ℂ) * ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹) := by
    simpa only [P, Nat.cast_add, Nat.cast_one, Nat.add_assoc] using
      p0Entire_product_deriv_nat g i
  have hErase :
      (∑ r ∈ Finset.range g,
        ∏ j ∈ (Finset.range g).erase r, ((i : ℂ) + (j + 1 : ℕ))) =
        P (i : ℂ) * ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹) := by
    calc
      _ = deriv P (i : ℂ) := hProd.deriv.symm
      _ = _ := hPderiv
  have hProdCompact := hProd
  rw [hErase] at hProdCompact
  have hNum := hExp.mul hProdCompact
  have hFac : (Nat.factorial g : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero g
  have hAll0 := hNum.div_const (Nat.factorial g : ℂ)
  have hAll : HasDerivAt (p0Entire g)
      (((Complex.exp ((i : ℂ) * Complex.ofReal (Real.log 2)) *
          Complex.ofReal (Real.log 2)) * P (i : ℂ) +
          Complex.exp ((i : ℂ) * Complex.ofReal (Real.log 2)) *
            (P (i : ℂ) *
              ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹))) /
        (Nat.factorial g : ℂ)) (i : ℂ) := by
    convert hAll0 using 1
    · funext x
      rfl
  have hPval := p0Entire_product_nat g i
  convert hAll using 1
  dsimp [P]
  rw [p0Entire_exp_nat, hPval]
  field_simp

/-- The diagonal C entry is the derivative residue with its logarithmic
correction isolated. -/
theorem p0C_diag_eq_neg_derivative (g i : ℕ) :
    p0C g i i =
      -deriv (p0Entire g) (i : ℂ) +
        Complex.ofReal (Real.log 2) * p0U g i := by
  rw [p0C, if_pos rfl, (p0Entire_hasDerivAt_nat g i).deriv, p0U]
  ring

/-- The diagonal derivative of the source, including the logarithmic term. -/
theorem p0Entire_deriv_nat (g i : ℕ) :
    deriv (p0Entire g) (i : ℂ) =
      p0U g i * (Complex.ofReal (Real.log 2) +
        ∑ r ∈ Finset.range g, (((i + r + 1 : ℕ) : ℂ)⁻¹)) := by
  exact (p0Entire_hasDerivAt_nat g i).deriv

end

end P0
end Li2Lean
