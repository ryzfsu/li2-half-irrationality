/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.RateProfiles

/-!
# The finite prime-sum majorant for the literal moving-prime exponent

For every odd prime `p ≤ U` that is not squarefull-range, not on one of the
finitely many certificate boundaries, and with `p > m/256`, the maximal source
assignment weight is at most `m` times the sum of the three profiles at `p/m`:
the tail tangent profile, the 756-piece low profile, or the high profile.
Summing over primes yields `P0A2FiniteProfilePrimeBound p0RateW p0RateWallCount`.
-/

namespace Li2Lean.P0.Integerization

open Finset IntegerizationTables

/-- All certificate boundary ratios (low piece starts, tail walls, high cell
starts, and the right end `5/2`). -/
def p0RateBoundaries : List ℚ :=
  lowPieces.map (·.lo) ++ (List.range 65).map (fun j : ℕ => (1 : ℚ) / (2 * ((j : ℚ) + 64))) ++
    p0HighCellData.map (·.cell.lo) ++ [5 / 2]

def p0RateWallCount : ℕ := p0RateBoundaries.length

/-- `p` lies exactly on a certificate boundary ratio. -/
def p0IsBoundary (m p : ℕ) : Prop := ∃ b ∈ p0RateBoundaries, (p : ℚ) = b * m

theorem p0RateBoundaries_low {f : AffinePiece} (hf : f ∈ lowPieces) : f.lo ∈ p0RateBoundaries := by
  unfold p0RateBoundaries
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_left
  exact List.mem_map.mpr ⟨f, hf, rfl⟩

theorem p0RateBoundaries_tail {j : ℕ} (hj : j < 65) :
    1 / (2 * ((j : ℚ) + 64)) ∈ p0RateBoundaries := by
  unfold p0RateBoundaries
  apply List.mem_append_left
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨j, List.mem_range.mpr hj, rfl⟩

theorem p0RateBoundaries_high {h : HCell} (hh : h ∈ p0HighCellData) :
    h.cell.lo ∈ p0RateBoundaries := by
  unfold p0RateBoundaries
  apply List.mem_append_left
  apply List.mem_append_right
  exact List.mem_map.mpr ⟨h, hh, rfl⟩

theorem p0LowData_exists {f : AffinePiece} (hf : f ∈ lowPieces) :
    ∃ d, (f, d) ∈ lowPieces.zip p0LowCellData := by
  obtain ⟨i, hi, hfi⟩ := List.mem_iff_getElem.mp hf
  have hlen := p0LowData_ok.1
  have hi' : i < p0LowCellData.length := by rw [hlen]; exact hi
  refine ⟨p0LowCellData[i], ?_⟩
  have hz : i < (lowPieces.zip p0LowCellData).length := by
    rw [List.length_zip, hlen, min_self]; exact hi
  have hmem := List.getElem_mem hz
  rw [List.getElem_zip] at hmem
  rw [← hfi]
  exact hmem

/-- Per-prime profile bound for the maximal assignment weight. -/
theorem p0Rate_assign_profile (m p : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) (hp : p.Prime)
    (hpU : p ≤ p0DenominatorU m) (hb : ¬ p0IsBoundary m p) (hs : m < 256 * p) :
    ((p0RateAssignMax p m : ℤ) : ℝ) ≤ (m : ℝ) *
      (p0A2LowProfile.eval ((p : ℝ) / m) + p0A2HighProfile.eval ((p : ℝ) / m) +
        p0FiniteTailProfile.eval ((p : ℝ) / m)) := by
  have hmQ : (0 : ℚ) < m := by exact_mod_cast hm
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hpos : 0 < p := hp.pos
  set ρ : ℚ := (p : ℚ) / m with hρ
  have hnb : ∀ b ∈ p0RateBoundaries, ρ ≠ b := by
    intro b hb' heq
    apply hb
    refine ⟨b, hb', ?_⟩
    rw [← heq, hρ]
    field_simp
  have hρlo : ρ * m = p := by rw [hρ]; field_simp
  have hL := p0Profile_eval_nonneg p0A2LowProfile_nonneg ((p : ℝ) / m)
  have hH := p0Profile_eval_nonneg p0A2HighProfile_nonneg ((p : ℝ) / m)
  have hT := p0Profile_eval_nonneg p0FiniteTailProfile_nonneg ((p : ℝ) / m)
  have hxR : ((ρ : ℚ) : ℝ) = (p : ℝ) / m := by rw [hρ]; push_cast; ring
  have hρ2 : ρ < 2 := by
    rw [hρ, div_lt_iff₀ hmQ]
    have : p < 2 * m := by unfold p0DenominatorU at hpU; omega
    exact_mod_cast this
  -- the three regimes
  by_cases htail : ρ < 1 / 128
  · -- tail
    have h128 : 128 * p < m := by
      have : (p : ℚ) < m / 128 := by
        rw [hρ, div_lt_iff₀ hmQ] at htail; linarith
      have : ((128 * p : ℕ) : ℚ) < m := by push_cast; linarith
      exact_mod_cast this
    have hpg : p ≤ m / 2 := by omega
    have hW := p0Tail_assignMax p m hpos hpg
    have hWR : ((p0RateAssignMax p m : ℤ) : ℝ) ≤
        3 * (m : ℝ) - 2 * ((m / p : ℕ) : ℝ) * ((m / 2 % p : ℕ) : ℝ) := by exact_mod_cast hW
    have hprof := p0TailFloorBudget_le_profile m p hm h4 hpos _ hWR
    set k := m / (2 * p) with hk
    have hdm := Nat.div_add_mod m (2 * p)
    have hmod := Nat.mod_lt m (show 0 < 2 * p by omega)
    rw [← hk] at hdm
    have hk1 : 2 * p * k ≤ m := by omega
    have hk2' : m < 2 * p * k + 2 * p := by omega
    have hk64 : 64 ≤ k := by rw [hk, Nat.le_div_iff_mul_le (by omega)]; omega
    have hk128 : k < 128 := by rw [hk, Nat.div_lt_iff_lt_mul (by omega)]; omega
    have hkne : 2 * p * k ≠ m := by
      intro heq
      apply hnb (1 / (2 * (((k - 64 : ℕ) : ℚ) + 64))) (p0RateBoundaries_tail (by omega))
      rw [hρ]
      have hk' : (((k - 64 : ℕ) : ℚ) + 64) = k := by
        rw [Nat.cast_sub hk64]; push_cast; ring
      rw [hk']
      have : (m : ℚ) = 2 * p * k := by exact_mod_cast heq.symm
      rw [this]
      have hkpos : (0 : ℚ) < k := by exact_mod_cast (by omega : 0 < k)
      field_simp
    have hk1' : 2 * p * k < m := lt_of_le_of_ne hk1 hkne
    set q := k - 64 with hq
    have hq64 : q < 64 := by omega
    have hqk : (q : ℝ) + 64 = k := by rw [hq, Nat.cast_sub hk64]; push_cast; ring
    have hpR : (0 : ℝ) < p := by exact_mod_cast hpos
    have hxlo : (((p0FiniteTailPiece q).lo : ℚ) : ℝ) < (p : ℝ) / m := by
      rw [p0FiniteTailPiece_lo]; push_cast
      rw [show (q : ℝ) + 65 = k + 1 by linarith, div_lt_div_iff₀ (by positivity) hmR]
      have : (m : ℝ) < 2 * p * k + 2 * p := by exact_mod_cast hk2'
      nlinarith
    have hxhi : (p : ℝ) / m < (((p0FiniteTailPiece q).hi : ℚ) : ℝ) := by
      rw [p0FiniteTailPiece_hi]; push_cast
      rw [hqk, div_lt_div_iff₀ hmR (by positivity)]
      have : (2 * p * k : ℝ) < m := by exact_mod_cast hk1'
      linarith
    have hmaj := p0FiniteTailPiece_majorizes q ((p : ℝ) / m) hxlo hxhi
    have hmem : p0FiniteTailPiece q ∈ p0FiniteTailProfile.pieces := by
      unfold p0FiniteTailProfile
      exact List.mem_map.mpr ⟨q, List.mem_range.mpr hq64, rfl⟩
    have hge := p0Profile_eval_ge p0FiniteTailProfile_nonneg hmem hxlo.le hxhi
    have hdiv : ((p0RateAssignMax p m : ℤ) : ℝ) / m ≤ p0FiniteTailProfile.eval ((p : ℝ) / m) := by
      linarith
    rw [div_le_iff₀ hmR] at hdiv
    nlinarith
  by_cases hlow : ρ < 1 / 2
  · -- low
    have hcov := p0_affineChain_cover lowPieces (1 / 128) (1 / 2) ρ
      p0LowFiniteProfile_checked.2.1 (not_lt.mp htail) hlow
    obtain ⟨f, hf, hf1, hf2⟩ := hcov
    have hf1' : f.lo < ρ := lt_of_le_of_ne hf1 (fun h => hnb f.lo (p0RateBoundaries_low hf) h.symm)
    obtain ⟨⟨A, B, C, Q, perm, k⟩, hzmem⟩ := p0LowData_exists hf
    have hok := List.all_eq_true.mp p0LowData_ok.2 _ hzmem
    simp only [p0LowEntryOK] at hok
    have hlo' : f.lo * m < p := by
      have := mul_lt_mul_of_pos_right hf1' hmQ; rw [hρlo] at this; exact this
    have hhi' : p < f.hi * m := by
      have := mul_lt_mul_of_pos_right hf2 hmQ; rw [hρlo] at this; exact this
    have hbound := p0Low_cell_bound (c := ⟨f.lo, f.hi, A, B, C, Q, perm⟩)
      _ _ k hok h4 hm hpos hlo' hhi'
    have hboundR : ((p0RateAssignMax p m : ℤ) : ℝ) ≤
        (f.intercept : ℝ) * m + (f.slope : ℝ) * p := by
      exact_mod_cast hbound
    have hge := p0A2LowProfile_eval_ge hf (x := (p : ℝ) / m)
      (by rw [← hxR]; exact_mod_cast hf1) (by rw [← hxR]; exact_mod_cast hf2)
    have hscale : (f.intercept : ℝ) * m + (f.slope : ℝ) * p =
        (m : ℝ) * ((f.slope : ℝ) * ((p : ℝ) / m) + f.intercept) := by
      field_simp; ring
    rw [hscale] at hboundR
    nlinarith
  · -- high
    have hcov := p0_affineChain_cover _ (1 / 2) (5 / 2) ρ p0HighCells_chain (not_lt.mp hlow)
      (by linarith)
    obtain ⟨f, hf, hf1, hf2⟩ := hcov
    obtain ⟨h, hh, rfl⟩ := List.mem_map.mp hf
    have hf1' : h.cell.lo < ρ :=
      lt_of_le_of_ne hf1 (fun e => hnb h.cell.lo (p0RateBoundaries_high hh) e.symm)
    have hok := List.all_eq_true.mp p0HighData_ok h hh
    have hlo' : h.cell.lo * m < p := by
      have := mul_lt_mul_of_pos_right hf1' hmQ; rw [hρlo] at this; exact this
    have hhi' : p < h.cell.hi * m := by
      have := mul_lt_mul_of_pos_right hf2 hmQ; rw [hρlo] at this; exact this
    have hbound := p0High_cell_bound h hok h4 hm hpos hlo' hhi'
    have hboundR : ((p0RateAssignMax p m : ℤ) : ℝ) ≤ (h.icpt : ℝ) * m + (h.slope : ℝ) * p := by
      exact_mod_cast hbound
    have hge := p0HighCell_eval_ge hh (x := (p : ℝ) / m)
      (by rw [← hxR]; exact_mod_cast hf1) (by rw [← hxR]; exact_mod_cast hf2)
    have hscale : (h.icpt : ℝ) * m + (h.slope : ℝ) * p =
        (m : ℝ) * ((h.slope : ℝ) * ((p : ℝ) / m) + h.icpt) := by
      field_simp; ring
    rw [hscale] at hboundR
    nlinarith


theorem p0_two_mem_squarefull (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) : 2 ∈ p0SquarefullPrimes m := by
  rw [mem_p0SquarefullPrimes]
  refine ⟨Nat.prime_two, ?_⟩
  unfold p0SquarefullCutoff p0DenominatorU
  have : 4 ≤ m := Nat.le_of_dvd hm h4
  omega

theorem p0_boundary_card_le (m : ℕ) (hm : 0 < m) (s : Finset ℕ)
    [DecidablePred (fun p => p0IsBoundary m p)] :
    (s.filter (fun p => p0IsBoundary m p)).card ≤ p0RateWallCount := by
  have hmQ : (m : ℚ) ≠ 0 := by exact_mod_cast hm.ne'
  calc (s.filter (fun p => p0IsBoundary m p)).card ≤ p0RateBoundaries.toFinset.card := by
        apply Finset.card_le_card_of_injOn (fun p : ℕ => (p : ℚ) / m)
        · intro p hp
          have hp' := (Finset.mem_filter.mp (Finset.mem_coe.mp hp)).2
          obtain ⟨b, hb, hpb⟩ := hp'
          apply Finset.mem_coe.mpr
          rw [List.mem_toFinset]
          have : (p : ℚ) / m = b := by rw [hpb]; field_simp
          show (p : ℚ) / m ∈ p0RateBoundaries
          rw [this]; exact hb
        · intro a _ b _ hab
          have hab' : (a : ℚ) / m = (b : ℚ) / m := hab
          have : (a : ℚ) = b := by
            have := congrArg (· * (m : ℚ)) hab'
            simpa [div_mul_cancel₀ _ hmQ] using this
          exact_mod_cast this
    _ ≤ p0RateWallCount := List.toFinset_card_le _

/-- Per-prime terms of the majorant. -/
noncomputable def p0RateCostTerm (m p : ℕ) : ℝ :=
  if p = 2 then ((3 * m * Nat.log 2 (p0DenominatorU m) : ℕ) : ℝ) * Real.log 2
  else ((min (p0RateW m p) ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℤ) : ℤ) : ℝ) *
    Real.log p

noncomputable def p0RateSqTerm (m p : ℕ) : ℝ :=
  if p ∈ p0SquarefullPrimes m then
    ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℝ) * Real.log p else 0

open Classical in
noncomputable def p0RateWallTerm (m p : ℕ) : ℝ :=
  if p0IsBoundary m p then 3 * (m : ℝ) * Real.log (3 * m) else 0

noncomputable def p0RateSmallTerm (m p : ℕ) : ℝ :=
  if 256 * p ≤ m then 3 * (m : ℝ) * Real.log p else 0

noncomputable def p0RateProfTerm (m p : ℕ) : ℝ :=
  (p0A2LowProfile.eval ((p : ℝ) / m) + p0A2HighProfile.eval ((p : ℝ) / m) +
    p0FiniteTailProfile.eval ((p : ℝ) / m)) * Real.log p

theorem p0Rate_cost_eq (m : ℕ) (hm : 0 < m) (h4 : 4 ∣ m) :
    p0A2SettledUncreditedPrimeCost m p0RateW =
      ∑ p ∈ Nat.primesLE (p0DenominatorU m), p0RateCostTerm m p := by
  have h2s : 2 ∈ Nat.primesLE (p0DenominatorU m) := by
    rw [Nat.mem_primesLE]
    refine ⟨?_, Nat.prime_two⟩
    unfold p0DenominatorU
    have := Nat.le_of_dvd hm h4
    omega
  rw [← Finset.sum_erase_add _ _ h2s]
  unfold p0A2SettledUncreditedPrimeCost p0A2SettledOddLogSum
  have e1 : ∑ p ∈ (Nat.primesLE (p0DenominatorU m)).erase 2, p0RateCostTerm m p =
      ∑ p ∈ (Nat.primesLE (p0DenominatorU m)).erase 2,
        ((min (p0RateW m p) ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℤ) : ℤ) : ℝ) *
          Real.log p := by
    apply Finset.sum_congr rfl
    intro p hp
    simp only [p0RateCostTerm, if_neg (Finset.ne_of_mem_erase hp)]
  have e2 : p0RateCostTerm m 2 =
      ((3 * m * Nat.log 2 (p0DenominatorU m) : ℕ) : ℝ) * Real.log 2 := by
    simp [p0RateCostTerm]
  rw [e1, e2]

theorem p0Rate_prime_term (m p : ℕ) (hm : 0 < m) (h4 : 4 ∣ m)
    (hp : p ∈ Nat.primesLE (p0DenominatorU m)) :
    p0RateCostTerm m p ≤ p0RateSqTerm m p + p0RateWallTerm m p + p0RateSmallTerm m p +
      (m : ℝ) * p0RateProfTerm m p := by
  classical
  rw [Nat.mem_primesLE] at hp
  obtain ⟨hpU, hpp⟩ := hp
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hlogp : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hpp.one_lt.le)
  have hlog3m : 0 ≤ Real.log (3 * (m : ℝ)) := by
    apply Real.log_nonneg
    have : (1 : ℝ) ≤ m := by exact_mod_cast hm
    linarith
  have hA0 : 0 ≤ p0RateSqTerm m p := by
    unfold p0RateSqTerm
    split
    · exact mul_nonneg (Nat.cast_nonneg _) hlogp
    · exact le_refl 0
  have hB0 : 0 ≤ p0RateWallTerm m p := by
    unfold p0RateWallTerm
    split
    · exact mul_nonneg (by positivity) hlog3m
    · exact le_refl 0
  have hC0 : 0 ≤ p0RateSmallTerm m p := by
    unfold p0RateSmallTerm
    split
    · exact mul_nonneg (by positivity) hlogp
    · exact le_refl 0
  have hP0 : 0 ≤ (m : ℝ) * p0RateProfTerm m p := by
    apply mul_nonneg hmR.le
    unfold p0RateProfTerm
    apply mul_nonneg _ hlogp
    have := p0Profile_eval_nonneg p0A2LowProfile_nonneg ((p : ℝ) / m)
    have := p0Profile_eval_nonneg p0A2HighProfile_nonneg ((p : ℝ) / m)
    have := p0Profile_eval_nonneg p0FiniteTailProfile_nonneg ((p : ℝ) / m)
    linarith
  have hsq2 := p0_two_mem_squarefull m hm h4
  by_cases hsq : p ∈ p0SquarefullPrimes m
  · have hTA : p0RateCostTerm m p ≤ p0RateSqTerm m p := by
      unfold p0RateCostTerm p0RateSqTerm
      rw [if_pos hsq]
      by_cases h2 : p = 2
      · subst h2
        simp
      · rw [if_neg h2]
        apply mul_le_mul_of_nonneg_right _ hlogp
        have h := (Int.cast_le (R := ℝ)).mpr (min_le_right (p0RateW m p)
          ((3 * m * Nat.log p (p0DenominatorU m) : ℕ) : ℤ))
        simpa using h
    linarith
  · have hp2 : p ≠ 2 := fun h => hsq (h ▸ hsq2)
    have hcut : p0SquarefullCutoff m < p ^ 2 := by
      by_contra hcon
      exact hsq (mem_p0SquarefullPrimes.mpr ⟨hpp, not_lt.mp hcon⟩)
    have hlog1 : Nat.log p (p0DenominatorU m) = 1 := by
      rw [Nat.log_eq_one_iff']
      refine ⟨hpU, ?_⟩
      have : p0DenominatorU m < p0SquarefullCutoff m := by
        unfold p0SquarefullCutoff
        have : 4 ≤ m := Nat.le_of_dvd hm h4
        have : 0 < m / 2 := by omega
        omega
      nlinarith
    have hW : p0RateW m p = p0RateAssignMax p m := by
      simp only [p0RateW, if_pos hcut]
    have hT : p0RateCostTerm m p =
        ((min (p0RateAssignMax p m) ((3 * m : ℕ) : ℤ) : ℤ) : ℝ) * Real.log p := by
      unfold p0RateCostTerm
      rw [if_neg hp2, hW, hlog1, mul_one]
    have hT3 : p0RateCostTerm m p ≤ 3 * (m : ℝ) * Real.log p := by
      rw [hT]
      apply mul_le_mul_of_nonneg_right _ hlogp
      have h := (Int.cast_le (R := ℝ)).mpr (min_le_right (p0RateAssignMax p m) ((3 * m : ℕ) : ℤ))
      push_cast at h ⊢
      exact h
    by_cases hbd : p0IsBoundary m p
    · have hlogle : Real.log p ≤ Real.log (3 * m) := by
        apply Real.log_le_log (by exact_mod_cast hpp.pos)
        have : p ≤ 3 * m := by unfold p0DenominatorU at hpU; omega
        exact_mod_cast this
      have : p0RateCostTerm m p ≤ p0RateWallTerm m p := by
        unfold p0RateWallTerm
        rw [if_pos hbd]
        nlinarith
      linarith
    by_cases hct : 256 * p ≤ m
    · have : p0RateCostTerm m p ≤ p0RateSmallTerm m p := by
        unfold p0RateSmallTerm
        rw [if_pos hct]
        exact hT3
      linarith
    · have hprof := p0Rate_assign_profile m p hm h4 hpp hpU hbd (by omega)
      have hTP : p0RateCostTerm m p ≤ (m : ℝ) * p0RateProfTerm m p := by
        rw [hT]
        unfold p0RateProfTerm
        have hmin := (Int.cast_le (R := ℝ)).mpr
          (min_le_left (p0RateAssignMax p m) ((3 * m : ℕ) : ℤ))
        calc ((min (p0RateAssignMax p m) ((3 * m : ℕ) : ℤ) : ℤ) : ℝ) * Real.log p
            ≤ ((p0RateAssignMax p m : ℤ) : ℝ) * Real.log p :=
              mul_le_mul_of_nonneg_right hmin hlogp
          _ ≤ ((m : ℝ) * (p0A2LowProfile.eval ((p : ℝ) / m) +
                p0A2HighProfile.eval ((p : ℝ) / m) +
                p0FiniteTailProfile.eval ((p : ℝ) / m))) * Real.log p :=
              mul_le_mul_of_nonneg_right hprof hlogp
          _ = _ := by ring
      linarith

/-- The finite unnormalized prime-sum majorant for the concrete exponent. -/
theorem p0Rate_finite_profile : P0A2FiniteProfilePrimeBound p0RateW p0RateWallCount := by
  classical
  intro m hm h4
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  rw [p0Rate_cost_eq m hm h4]
  have hsum := Finset.sum_le_sum (fun p hp => p0Rate_prime_term m p hm h4 hp)
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum] at hsum
  set s := Nat.primesLE (p0DenominatorU m) with hs
  have hspr : ∀ p ∈ s, p.Prime := fun p hp => (Nat.mem_primesLE.mp hp).2
  have hA : ∑ p ∈ s, p0RateSqTerm m p ≤ p0SquarefullPrimeLayerCost m := by
    unfold p0RateSqTerm p0SquarefullPrimeLayerCost
    rw [← Finset.sum_filter]
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro p hp
      exact (Finset.mem_filter.mp hp).2
    · intro p hp _
      exact mul_nonneg (Nat.cast_nonneg _)
        (Real.log_nonneg (by exact_mod_cast (mem_p0SquarefullPrimes.mp hp).1.one_lt.le))
  have hB : ∑ p ∈ s, p0RateWallTerm m p ≤
      ((3 * p0RateWallCount * m : ℕ) : ℝ) * Real.log (3 * m) := by
    unfold p0RateWallTerm
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
    have hc := p0_boundary_card_le m hm s
    have hc' : ((s.filter (fun p => p0IsBoundary m p)).card : ℝ) ≤ p0RateWallCount := by
      exact_mod_cast hc
    have hlog3m : 0 ≤ Real.log (3 * (m : ℝ)) := by
      apply Real.log_nonneg
      have : (1 : ℝ) ≤ m := by exact_mod_cast hm
      linarith
    have h3 : 0 ≤ 3 * (m : ℝ) * Real.log (3 * m) := mul_nonneg (by positivity) hlog3m
    have hcast : ((3 * p0RateWallCount * m : ℕ) : ℝ) = 3 * (p0RateWallCount : ℝ) * m := by
      rw [Nat.cast_mul, Nat.cast_mul]; norm_num
    rw [hcast]
    clear hc
    generalize (p0RateWallCount : ℝ) = W at hc' ⊢
    generalize ((s.filter (fun p => p0IsBoundary m p)).card : ℝ) = K at hc' ⊢
    calc K * (3 * (m : ℝ) * Real.log (3 * m)) ≤ W * (3 * (m : ℝ) * Real.log (3 * m)) :=
          mul_le_mul_of_nonneg_right hc' h3
      _ = 3 * W * m * Real.log (3 * m) := by ring
  have hC : ∑ p ∈ s, p0RateSmallTerm m p ≤
      (m : ℝ) * (3 * Chebyshev.theta ((1 / 256 : ℝ) * m)) := by
    unfold p0RateSmallTerm
    rw [← Finset.sum_filter, ← Finset.mul_sum]
    have hsub : ∑ p ∈ s.filter (fun p => 256 * p ≤ m), Real.log p ≤
        Chebyshev.theta ((1 / 256 : ℝ) * m) := by
      unfold Chebyshev.theta
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro p hp
        rw [Finset.mem_filter] at hp
        obtain ⟨hps, hpm⟩ := hp
        have hpp := hspr p hps
        rw [Finset.mem_filter, Finset.mem_Ioc]
        refine ⟨⟨hpp.pos, ?_⟩, hpp⟩
        apply Nat.le_floor
        have : ((256 * p : ℕ) : ℝ) ≤ m := by exact_mod_cast hpm
        push_cast at this
        linarith
      · intro p hp _
        rw [Finset.mem_filter] at hp
        exact Real.log_nonneg (by exact_mod_cast hp.2.one_lt.le)
    nlinarith
  have hP : ∑ p ∈ s, p0RateProfTerm m p ≤ weightedPrimeSum p0A2LowProfile m +
      weightedPrimeSum p0A2HighProfile m + weightedPrimeSum p0FiniteTailProfile m := by
    unfold p0RateProfTerm
    simp only [add_mul, Finset.sum_add_distrib]
    have h1 := p0_partial_le_weightedPrimeSum p0A2LowProfile_nonneg (1 / 2)
      p0A2LowProfile_hi_le hmR s hspr
    have h2 := p0_partial_le_weightedPrimeSum p0A2HighProfile_nonneg (5 / 2)
      p0A2HighProfile_hi_le hmR s hspr
    have h3 := p0_partial_le_weightedPrimeSum p0FiniteTailProfile_nonneg 1
      p0FiniteTailProfile_hi_le hmR s hspr
    linarith
  have hmP := mul_le_mul_of_nonneg_left hP hmR.le
  have hexp : (m : ℝ) * (weightedPrimeSum p0A2LowProfile m + weightedPrimeSum p0A2HighProfile m +
      weightedPrimeSum p0FiniteTailProfile m + 3 * Chebyshev.theta ((1 / 256 : ℝ) * m)) =
      (m : ℝ) * (weightedPrimeSum p0A2LowProfile m + weightedPrimeSum p0A2HighProfile m +
        weightedPrimeSum p0FiniteTailProfile m) +
        (m : ℝ) * (3 * Chebyshev.theta ((1 / 256 : ℝ) * m)) := by ring
  rw [hexp]
  linarith

end Li2Lean.P0.Integerization

#print axioms Li2Lean.P0.Integerization.p0Rate_assign_profile
#print axioms Li2Lean.P0.Integerization.p0Rate_finite_profile
