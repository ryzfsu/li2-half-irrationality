/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.P0.FrequencyFactorial

open Finset

namespace Li2Lean.P0.FrequencyLeaf

noncomputable section

/-! Finite replacement facts for the literal v10 frequency window. -/

/-- The first `m` sites above `g`, namely `{g+1,...,g+m}`. -/
def window (g m : ℕ) : Finset ℕ :=
  (Finset.range m).image (fun k => g + 1 + k)

/-- Frequencies are distinct natural numbers strictly above `g`. -/
def admissible (g m : ℕ) (R : Finset ℕ) : Prop :=
  (∀ r ∈ R, g < r) ∧ R.card = m

lemma window_card (g m : ℕ) : (window g m).card = m := by
  calc
    (window g m).card = (Finset.range m).card := by
      apply card_image_iff.mpr
      intro a ha b hb hab
      change (g + 1) + a = (g + 1) + b at hab
      exact Nat.add_left_cancel hab
    _ = m := card_range m

lemma mem_window_iff (g m x : ℕ) :
    x ∈ window g m ↔ g < x ∧ x ≤ g + m := by
  rw [window, mem_image]
  constructor
  · rintro ⟨k, hk, rfl⟩
    simp only [mem_range] at hk
    omega
  · rintro ⟨hlo, hhi⟩
    refine ⟨x - (g + 1), ?_, ?_⟩
    · simp only [mem_range]
      omega
    · omega

lemma outside_not_window (g m r : ℕ) (h : g + m < r) : r ∉ window g m := by
  intro hr
  have := (mem_window_iff g m r).mp hr
  omega

/-- There is an unused site whenever the frequency set contains a point
strictly beyond the first `m` sites. -/
lemma unused_window_nonempty (g m : ℕ) (R : Finset ℕ)
    (hR : admissible g m R) (r : ℕ) (hr : r ∈ R) (hout : g + m < r) :
    (window g m \ R).Nonempty := by
  have hrnot : r ∉ window g m := outside_not_window g m r hout
  have hinter : window g m ∩ R ⊆ R.erase r := by
    intro x hx
    have hxW := (mem_inter.mp hx).1
    have hxR := (mem_inter.mp hx).2
    have hxr : x ≠ r := by
      intro hEq
      subst x
      exact hrnot hxW
    exact mem_erase.mpr ⟨hxr, hxR⟩
  have hcardint : (window g m ∩ R).card ≤ m - 1 := by
    calc
      (window g m ∩ R).card ≤ (R.erase r).card := card_le_card hinter
      _ = R.card - 1 := card_erase_of_mem hr
      _ = m - 1 := by rw [hR.2]
  have hcardint' : (R ∩ window g m).card ≤ m - 1 := by
    simpa [inter_comm] using hcardint
  have hdiff : (window g m \ R).card = m - (R ∩ window g m).card := by
    rw [card_sdiff, window_card]
  have hpos : (window g m \ R).card > 0 := by
    rw [hdiff]
    have hmpos : 0 < m := by
      have hcard := card_pos.mpr ⟨r, hr⟩
      rw [hR.2] at hcard
      exact hcard
    omega
  exact card_pos.mp hpos

/-- The least unused site in `{g+1,...,g+m}`. -/
def leastUnused (g m : ℕ) (R : Finset ℕ) (hR : admissible g m R)
    (r : ℕ) (hr : r ∈ R) (hout : g + m < r) : ℕ :=
  (window g m \ R).min' (unused_window_nonempty g m R hR r hr hout)

lemma leastUnused_mem (g m : ℕ) (R : Finset ℕ) (hR : admissible g m R)
    (r : ℕ) (hr : r ∈ R) (hout : g + m < r) :
    leastUnused g m R hR r hr hout ∈ window g m \ R := by
  exact min'_mem _ _

lemma leastUnused_spec (g m : ℕ) (R : Finset ℕ) (hR : admissible g m R)
    (r : ℕ) (hr : r ∈ R) (hout : g + m < r) :
    g < leastUnused g m R hR r hr hout ∧
    leastUnused g m R hR r hr hout ≤ g + m ∧
    leastUnused g m R hR r hr hout ∉ R := by
  have hs := mem_sdiff.mp (leastUnused_mem g m R hR r hr hout)
  have hwin := (mem_window_iff g m _).mp hs.1
  exact ⟨hwin.1, hwin.2, hs.2⟩

def replace (_g _m : ℕ) (R : Finset ℕ) (s r : ℕ) : Finset ℕ :=
  insert s (R.erase r)

/-- Replacing the largest point by an unused site preserves cardinality and
the frequency support condition. -/
lemma replace_admissible (g m : ℕ) (R : Finset ℕ) (hR : admissible g m R)
    (r s : ℕ) (hr : r ∈ R) (hs : s ∉ R) (hsg : g < s) :
    admissible g m (replace g m R s r) := by
  constructor
  · intro x hx
    rcases mem_insert.mp hx with rfl | hx
    · exact hsg
    · exact hR.1 x (mem_erase.mp hx).2
  · have hcardpos : 0 < R.card := card_pos.mpr ⟨r, hr⟩
    have hmpos : 1 ≤ m := by rw [← hR.2]; omega
    simp [replace, hs, card_erase_of_mem hr, hR.2, Nat.sub_add_cancel hmpos]

lemma replace_with_leastUnused_admissible (g m : ℕ) (R : Finset ℕ)
    (hR : admissible g m R) (r : ℕ) (hr : r ∈ R) (hout : g + m < r) :
    admissible g m
      (replace g m R (leastUnused g m R hR r hr hout) r) := by
  apply replace_admissible g m R hR r _ hr
  · exact (mem_sdiff.mp (leastUnused_mem g m R hR r hr hout)).2
  · exact (leastUnused_spec g m R hR r hr hout).1

/-- The output remains inside the exact finite cutoff whenever `M ≥ 20m`
and the input was already cut off at `M`. -/
lemma replace_preserves_cutoff (m M : ℕ) (R : Finset ℕ)
    (hM : 20 * m ≤ M) (hRcut : ∀ x ∈ R, x ≤ M)
    (hR : admissible (m / 2) m R) (r : ℕ) (hr : r ∈ R)
    (hrlarge : 20 * m < r) :
    ∀ x ∈ replace (m / 2) m R
      (leastUnused (m / 2) m R hR r hr (by omega)) r, x ≤ M := by
  intro x hx
  rcases mem_insert.mp hx with hx | hx
  · subst x
    have hs := leastUnused_spec (m / 2) m R hR r hr (by omega)
    omega
  · exact hRcut x (mem_erase.mp hx).2

/-- For fixed output and removed largest frequency, each possible source set
is reconstructed from its replacement site. -/
lemma reconstruct_source (g m : ℕ) (R R' : Finset ℕ) (r s : ℕ)
    (hr : r ∈ R) (hs : s ∉ R)
    (hmap : R' = replace g m R s r) :
    R = insert r (R'.erase s) := by
  have hsite : s ∉ R.erase r := by
    intro h
    exact hs (mem_erase.mp h).2
  calc
    R = insert r (R.erase r) := (insert_erase hr).symm
    _ = insert r ((insert s (R.erase r)).erase s) := by
      rw [erase_insert hsite]
    _ = insert r (R'.erase s) := by
      rw [hmap, replace]

def reconstructionFiber (R' : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  R'.image (fun s => insert r (R'.erase s))

lemma source_in_reconstructionFiber (g m : ℕ) (R R' : Finset ℕ) (r s : ℕ)
    (hr : r ∈ R) (hs : s ∉ R) (hmap : R' = replace g m R s r) :
    R ∈ reconstructionFiber R' r := by
  rw [reconstructionFiber, mem_image]
  refine ⟨s, ?_, ?_⟩
  · rw [hmap, replace]
    exact mem_insert_self s (R.erase r)
  · exact (reconstruct_source g m R R' r s hr hs hmap).symm

/-! For a least-unused-site map on any finite family, reconstruction makes
that map injective into the `m` sites. -/
theorem atMostMFiber {g m : ℕ} (R' : Finset ℕ) (r : ℕ)
    (F : Finset (Finset ℕ)) (site : Finset ℕ → ℕ)
    (hcard : (window g m).card = m)
    (hsite : ∀ R ∈ F, site R ∈ window g m)
    (hsource : ∀ R ∈ F, r ∈ R)
    (hunused : ∀ R ∈ F, site R ∉ R)
    (hmap : ∀ R ∈ F, R' = replace g m R (site R) r) :
    F.card ≤ m := by
  have hinj : Set.InjOn site (↑F : Set (Finset ℕ)) := by
    intro R₁ h₁ R₂ h₂ hsites
    have hrec₁ := reconstruct_source g m R₁ R' r (site R₁)
      (hsource R₁ h₁) (hunused R₁ h₁) (hmap R₁ h₁)
    have hrec₂ := reconstruct_source g m R₂ R' r (site R₂)
      (hsource R₂ h₂) (hunused R₂ h₂) (hmap R₂ h₂)
    rw [← hsites] at hrec₂
    rw [hrec₁, hrec₂]
  calc
    F.card = (F.image site).card := (card_image_iff.mpr hinj).symm
    _ ≤ (window g m).card := card_le_card (by
      intro s hs
      rcases mem_image.mp hs with ⟨R, hR, rfl⟩
      exact hsite R hR)
    _ = m := hcard

/-- Finite-cutoff replacement: for `r > 20m`, the least unused site exists
and lies in the paper's literal first window. -/
theorem largestFrequencyReplacement (m : ℕ) (hm4 : 4 ∣ m)
    (R : Finset ℕ) (hR : admissible (m / 2) m R)
    (r : ℕ) (hr : r ∈ R) (hrmax : ∀ u ∈ R, u ≤ r)
    (hrtail : 20 * m < r) :
    let s := leastUnused (m / 2) m R hR r hr (by omega)
    s ∈ window (m / 2) m \ R ∧ s ≤ 3 * m / 2 ∧
      admissible (m / 2) m (replace (m / 2) m R s r) ∧
      (∀ u ∈ R.erase r, u < r) := by
  dsimp
  have hout : m / 2 + m < r := by omega
  let s := leastUnused (m / 2) m R hR r hr hout
  have hs := leastUnused_mem (m / 2) m R hR r hr hout
  have hbound := (mem_window_iff (m / 2) m s).mp (mem_sdiff.mp hs).1
  have hstrict : ∀ u ∈ R.erase r, u < r := by
    intro u hu
    have huR := (mem_erase.mp hu).2
    have huner := (mem_erase.mp hu).1
    have hle := hrmax u huR
    omega
  refine ⟨hs, ?_, ?_, hstrict⟩
  · omega
  · exact replace_with_leastUnused_admissible (m / 2) m R hR r hr hout

/-! Literal weights from docs/6333 §6. -/
def weight (g r : ℕ) : ℝ :=
  (Nat.choose (r - 1) g : ℝ) * (1 / 2 : ℝ) ^ r


lemma separation_scale_identity (m : ℕ) (hm : 0 < m) :
    9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
        (((m : ℝ) / 6) ^ (m - 1) / 3) ^ 2 =
      (m : ℝ) ^ (2 * m) := by
  calc
    9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
        (((m : ℝ) / 6) ^ (m - 1) / 3) ^ 2 =
      (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
        ((m : ℝ) / 6) ^ ((m - 1) * 2) := by
          rw [div_pow, ← pow_mul]
          field_simp
          ring
    _ = (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
          (((m : ℝ) / 6) ^ 2) ^ (m - 1) := by
          rw [← pow_mul, Nat.mul_comm (m - 1) 2]
    _ = (36 * ((m : ℝ) / 6) ^ 2) ^ (m - 1) * (m : ℝ) ^ 2 := by
          calc
            (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
                (((m : ℝ) / 6) ^ 2) ^ (m - 1) =
              (36 : ℝ) ^ (m - 1) *
                (((m : ℝ) / 6) ^ 2) ^ (m - 1) * (m : ℝ) ^ 2 := by ring
            _ = (36 * ((m : ℝ) / 6) ^ 2) ^ (m - 1) * (m : ℝ) ^ 2 := by
              rw [← mul_pow]
    _ = ((m : ℝ) ^ 2) ^ (m - 1) * (m : ℝ) ^ 2 := by
          congr 1
          field_simp
          ring
    _ = ((m : ℝ) ^ 2) ^ m := by
          rw [← pow_succ]
          congr 1
          omega
    _ = (m : ℝ) ^ (2 * m) := by rw [pow_mul]

lemma separationScale_of_lower (m r : ℕ) (hm : 0 < m) (hr : 0 < r)
    (hsep : ((m : ℝ) / 6) ^ (m - 1) / 3 ≤
      (separationFloor m : ℝ)) :
    (m : ℝ) ^ (2 * m) /
        ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2) ≤
      9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 / (r : ℝ) ^ 2 := by
  have hsep_nonneg : 0 ≤ ((m : ℝ) / 6) ^ (m - 1) / 3 := by positivity
  have hsep_sq :
      (((m : ℝ) / 6) ^ (m - 1) / 3) ^ 2 ≤
        (separationFloor m : ℝ) ^ 2 :=
    pow_le_pow_left₀ hsep_nonneg hsep 2
  have htop :
      (m : ℝ) ^ (2 * m) ≤
        9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
          (separationFloor m : ℝ) ^ 2 := by
    rw [← separation_scale_identity m hm]
    gcongr
  have hfloor : 0 < separationFloor m := by
    exact Nat.mul_pos (Nat.factorial_pos _) (Nat.factorial_pos _)
  have hden : 0 < (r : ℝ) ^ 2 *
      (separationFloor m : ℝ) ^ 2 := by
    exact mul_pos (pow_pos (Nat.cast_pos.mpr hr) 2)
      (pow_pos (Nat.cast_pos.mpr hfloor) 2)
  rw [div_le_iff₀ hden]
  calc
    (m : ℝ) ^ (2 * m) ≤
        9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 *
          (separationFloor m : ℝ) ^ 2 := htop
    _ = (9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) *
        ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2) := by
          field_simp

/-- Frozen v10 row and column sets. -/
def I_m (m : ℕ) : Finset ℕ := Icc (m / 4) (5 * m / 4 - 1)
def J_m (m : ℕ) : Finset ℕ := Finset.range (2 * m)

/-- The positive Vandermonde on an integer frequency set. -/
def frequencyVandermonde (R : Finset ℕ) : ℝ :=
  ∏ a ∈ R, ∏ b ∈ R, if a < b then (b - a : ℝ) else 1

/-- The exact frequency-dependent factor f(R) displayed in docs/6333 §7.
The remaining factors of Q_m(S,R,Z) are independent of R. -/
noncomputable def frequencyFactor (m g : ℕ) (S R : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ) : ℝ :=
  ((∏ r ∈ R, weight g r) * (frequencyVandermonde R) ^ 2 *
      (∏ r ∈ R, ∏ z : Fin d, ‖(r : ℂ) + Z z‖)) /
    ((∏ r ∈ R, ∏ i ∈ I_m m, ((r + i : ℕ) : ℝ)) *
      (∏ r ∈ R, ∏ j ∈ J_m m,
        if j ∈ S then 1 else ((r + j : ℕ) : ℝ)))

lemma weight_pos (g r : ℕ) (hgr : g < r) : 0 < weight g r := by
  unfold weight
  have hc : 0 < Nat.choose (r - 1) g := by
    apply Nat.choose_pos
    omega
  positivity

lemma exact_weight_ratio (g m s r : ℕ) (hgs : g < s) (hgr : g < r)
    (hs : s ≤ g + m) :
    weight g r / weight g s ≤ weight g r * (2 : ℝ) ^ (g + m) := by
  have hws : 0 < weight g s := weight_pos g s hgs
  have hwr : 0 ≤ weight g r := (weight_pos g r hgr).le
  have hcNat : 1 ≤ Nat.choose (s - 1) g :=
    Nat.succ_le_of_lt (Nat.choose_pos (by omega))
  have hc : (1 : ℝ) ≤ (Nat.choose (s - 1) g : ℝ) := by exact_mod_cast hcNat
  have hpow : 1 ≤ (2 : ℝ) ^ (g + m - s) := one_le_pow₀ (by norm_num)
  have hcancel : (1 / 2 : ℝ) ^ s * (2 : ℝ) ^ s = 1 := by
    rw [← mul_pow]
    norm_num
  have hsite : s + (g + m - s) = g + m := Nat.add_sub_of_le hs
  have hbound : 1 ≤ weight g s * (2 : ℝ) ^ (g + m) := by
    have hmul : 1 ≤ (Nat.choose (s - 1) g : ℝ) * (2 : ℝ) ^ (g + m - s) := by
      calc
        1 ≤ (Nat.choose (s - 1) g : ℝ) := hc
        _ ≤ (Nat.choose (s - 1) g : ℝ) * (2 : ℝ) ^ (g + m - s) := by
          calc
            (Nat.choose (s - 1) g : ℝ) =
                (Nat.choose (s - 1) g : ℝ) * 1 := by ring
            _ ≤ (Nat.choose (s - 1) g : ℝ) * (2 : ℝ) ^ (g + m - s) :=
              mul_le_mul_of_nonneg_left hpow (by positivity)
    have hexp : (2 : ℝ) ^ (g + m) =
        (2 : ℝ) ^ s * (2 : ℝ) ^ (g + m - s) := by
      calc
        (2 : ℝ) ^ (g + m) = (2 : ℝ) ^ (s + (g + m - s)) := by
          congr 1
          exact hsite.symm
        _ = (2 : ℝ) ^ s * (2 : ℝ) ^ (g + m - s) := by rw [pow_add]
    have heq : weight g s * (2 : ℝ) ^ (g + m) =
        (Nat.choose (s - 1) g : ℝ) * (2 : ℝ) ^ (g + m - s) := by
      unfold weight
      rw [hexp]
      calc
        (Nat.choose (s - 1) g : ℝ) * (1 / 2 : ℝ) ^ s *
            ((2 : ℝ) ^ s * (2 : ℝ) ^ (g + m - s)) =
          (Nat.choose (s - 1) g : ℝ) *
            (((1 / 2 : ℝ) ^ s * (2 : ℝ) ^ s) * (2 : ℝ) ^ (g + m - s)) := by ring
        _ = (Nat.choose (s - 1) g : ℝ) * (2 : ℝ) ^ (g + m - s) := by
          rw [hcancel]
          ring
    rw [heq]
    exact hmul
  rw [div_le_iff₀ hws]
  calc
    weight g r = weight g r * 1 := by ring
    _ ≤ weight g r * (weight g s * (2 : ℝ) ^ (g + m)) :=
      mul_le_mul_of_nonneg_left hbound hwr
    _ = weight g r * (2 : ℝ) ^ (g + m) * weight g s := by ring

lemma two_pow_three_half_le (m : ℕ) (hm2 : 2 ∣ m) :
    (2 : ℝ) ^ (3 * m / 2) ≤ (3 : ℝ) ^ m := by
  have hq : 2 * (3 * m / 2) = 3 * m := by omega
  have hleft : ((2 : ℝ) ^ (3 * m / 2)) ^ 2 = (8 : ℝ) ^ m := by
    calc
      ((2 : ℝ) ^ (3 * m / 2)) ^ 2 =
          (2 : ℝ) ^ ((3 * m / 2) * 2) := by rw [← pow_mul]
      _ = (2 : ℝ) ^ (m * 3) := by congr 1; omega
      _ = (2 : ℝ) ^ (3 * m) := by congr 1; omega
      _ = ((2 : ℝ) ^ 3) ^ m := by rw [pow_mul]
      _ = (8 : ℝ) ^ m := by norm_num
  have hright : ((3 : ℝ) ^ m) ^ 2 = (9 : ℝ) ^ m := by
    calc
      ((3 : ℝ) ^ m) ^ 2 = (3 : ℝ) ^ (m * 2) := by rw [← pow_mul]
      _ = (3 : ℝ) ^ (2 * m) := by congr 1; omega
      _ = ((3 : ℝ) ^ 2) ^ m := by rw [pow_mul]
      _ = (9 : ℝ) ^ m := by norm_num
  have hsquares : ((2 : ℝ) ^ (3 * m / 2)) ^ 2 ≤ ((3 : ℝ) ^ m) ^ 2 := by
    rw [hleft, hright]
    exact pow_le_pow_left₀ (by norm_num) (by norm_num) m
  have hleft_nonneg : 0 ≤ (2 : ℝ) ^ (3 * m / 2) := by positivity
  have hright_nonneg : 0 ≤ (3 : ℝ) ^ m := by positivity
  nlinarith

/-- Numerical simplification of the exact paper constants after the
frequency-weight and factorial estimates. -/
lemma ratio_constant (m : ℕ) (hm : 0 < m) (hm2 : 2 ∣ m) :
    (2 : ℝ) ^ (3 * m / 2) * (77 / 8 : ℝ) ^ m *
        (189 / 16 : ℝ) ^ m * 9 * (36 : ℝ) ^ (m - 1) ≤
      (12500 : ℝ) ^ m / 4 := by
  have hhalf := two_pow_three_half_le m hm2
  have hbase : 3 * (77 / 8 : ℝ) * (189 / 16 : ℝ) * 36 < 12500 := by
    norm_num
  have hpowbase :
      (3 * (77 / 8 : ℝ) * (189 / 16 : ℝ) * 36) ^ m ≤
        (12500 : ℝ) ^ m :=
    pow_le_pow_left₀ (by norm_num) hbase.le m
  have h36 : 9 * (36 : ℝ) ^ (m - 1) = (36 : ℝ) ^ m / 4 := by
    rw [show m = (m - 1) + 1 by omega, pow_succ]
    norm_num
    ring
  have hproduct :
      (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m * (36 : ℝ) ^ m =
        ((77 / 8 : ℝ) * (189 / 16 : ℝ) * 36) ^ m := by
    rw [← mul_pow, ← mul_pow]
  calc
    (2 : ℝ) ^ (3 * m / 2) * (77 / 8 : ℝ) ^ m *
        (189 / 16 : ℝ) ^ m * 9 * (36 : ℝ) ^ (m - 1) =
      (2 : ℝ) ^ (3 * m / 2) *
        ((77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
          (9 * (36 : ℝ) ^ (m - 1))) := by ring
    _ = ((2 : ℝ) ^ (3 * m / 2) *
        ((77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
          (36 : ℝ) ^ m)) / 4 := by rw [h36]; ring
    _ = ((2 : ℝ) ^ (3 * m / 2) *
        ((77 / 8 : ℝ) * (189 / 16 : ℝ) * 36) ^ m) / 4 := by rw [hproduct]
    _ ≤ ((3 : ℝ) ^ m *
        ((77 / 8 : ℝ) * (189 / 16 : ℝ) * 36) ^ m) / 4 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_right hhalf (by positivity)
      · norm_num
    _ = (3 * (77 / 8 : ℝ) * (189 / 16 : ℝ) * 36) ^ m / 4 := by
      rw [← mul_pow]
      ring
    _ ≤ (12500 : ℝ) ^ m / 4 := by
      exact div_le_div_of_nonneg_right hpowbase (by norm_num)

/-- The full v10 displayed pointwise ratio, conditional only on the
explicit three-minor/ellipse estimate. The weight, factorial separation
bound, and numerical constant are proved here with the literal v10
definitions; the geometric estimate remains a separate premise. -/
theorem exactRatioEstimate {m g s k r : ℕ}
    {dZ : ℕ} (S : Finset ℕ) (Z : Fin dZ → ℂ)
    (R R' : Finset ℕ)
    (hm : 0 < m) (hm4 : 4 ∣ m) (hgm : 2 * g = m)
    (hgs : g < s) (hsite : s ≤ g + m) (hgr : g < r)
    (hr : 0 < r)
    (hS : S ⊆ J_m m) (hk : k = S.card)
    (hrep : R' = replace g m R s r)
    (hgeom : S ⊆ J_m m → k = S.card → R' = replace g m R s r →
      frequencyFactor m g S R dZ Z / frequencyFactor m g S R' dZ Z ≤
        (weight g r / weight g s) * (77 / 8 : ℝ) ^ m *
          (189 / 16 : ℝ) ^ (m - k) *
            ((m : ℝ) ^ (2 * m) /
              ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2))) :
    frequencyFactor m g S R dZ Z / frequencyFactor m g S R' dZ Z ≤
      (12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight g r := by
  have hm2 : 2 ∣ m := dvd_trans (by norm_num : 2 ∣ 4) hm4
  have hN : g + m = 3 * m / 2 := by omega
  have hw := exact_weight_ratio g m s r hgs hgr hsite
  rw [hN] at hw
  have hb : (189 / 16 : ℝ) ^ (m - k) ≤ (189 / 16 : ℝ) ^ m :=
    pow_le_pow_right₀ (by norm_num) (Nat.sub_le m k)
  have hsep := separationFloor_lower hm hm4
  have hscale := separationScale_of_lower m r hm hr hsep
  have hscale_nonneg :
      0 ≤ (m : ℝ) ^ (2 * m) /
        ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2) := by positivity
  have hwr : 0 ≤ weight g r := (weight_pos g r hgr).le
  have hgeom' :
      (weight g r / weight g s) * (77 / 8 : ℝ) ^ m *
          (189 / 16 : ℝ) ^ (m - k) *
            ((m : ℝ) ^ (2 * m) /
              ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2)) ≤
        weight g r * (2 : ℝ) ^ (3 * m / 2) *
          (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
            (9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) := by
    calc
      _ ≤ (weight g r * (2 : ℝ) ^ (3 * m / 2)) *
          (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ (m - k) *
            ((m : ℝ) ^ (2 * m) /
              ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2)) := by
        gcongr
      _ ≤ weight g r * (2 : ℝ) ^ (3 * m / 2) *
          (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
            ((m : ℝ) ^ (2 * m) /
              ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2)) := by
        gcongr
      _ ≤ weight g r * (2 : ℝ) ^ (3 * m / 2) *
          (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
            (9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) := by
        gcongr
  have hconstant := ratio_constant m hm hm2
  calc
    frequencyFactor m g S R dZ Z / frequencyFactor m g S R' dZ Z ≤
        (weight g r / weight g s) * (77 / 8 : ℝ) ^ m *
          (189 / 16 : ℝ) ^ (m - k) *
            ((m : ℝ) ^ (2 * m) /
              ((r : ℝ) ^ 2 * (separationFloor m : ℝ) ^ 2)) := by
              apply hgeom hS hk
              exact hrep
    _ ≤ weight g r * (2 : ℝ) ^ (3 * m / 2) *
          (77 / 8 : ℝ) ^ m * (189 / 16 : ℝ) ^ m *
            (9 * (36 : ℝ) ^ (m - 1) * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) :=
      hgeom'
    _ = (weight g r * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) *
          ((2 : ℝ) ^ (3 * m / 2) * (77 / 8 : ℝ) ^ m *
            (189 / 16 : ℝ) ^ m * 9 * (36 : ℝ) ^ (m - 1)) := by ring
    _ ≤ (weight g r * (m : ℝ) ^ 2 / (r : ℝ) ^ 2) *
          ((12500 : ℝ) ^ m / 4) := by
      apply mul_le_mul_of_nonneg_left hconstant
      positivity
    _ = (12500 : ℝ) ^ m * (m : ℝ) ^ 2 /
          (4 * (r : ℝ) ^ 2) * weight g r := by ring

end

end Li2Lean.P0.FrequencyLeaf
