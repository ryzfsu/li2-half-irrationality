/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.FrequencyLeaf

open Finset

namespace Li2Lean.P0.FrequencyFinite

open Li2Lean.P0.FrequencyLeaf

noncomputable section

/-! The literal finite frequency family and the replacement transport in
v10, Section `sec:frequency`. The analytic pointwise ratio is kept separate
from the exact finite combinatorics proved in this file. -/

/-- The paper's frequency sets `R ⊆ (g,M]` with `|R| = m`. -/
def finiteFamily (g m M : ℕ) : Finset (Finset ℕ) :=
  (Ioc g M).powersetCard m

theorem mem_finiteFamily_iff (g m M : ℕ) (R : Finset ℕ) :
    R ∈ finiteFamily g m M ↔ admissible g m R ∧ ∀ r ∈ R, r ≤ M := by
  rw [finiteFamily, mem_powersetCard]
  constructor
  · rintro ⟨hsub, hcard⟩
    exact ⟨⟨fun r hr => (mem_Ioc.mp (hsub hr)).1, hcard⟩,
      fun r hr => (mem_Ioc.mp (hsub hr)).2⟩
  · rintro ⟨hR, hcut⟩
    exact ⟨fun r hr => mem_Ioc.mpr ⟨hR.1 r hr, hcut r hr⟩, hR.2⟩

theorem finiteFamily_mono (g m : ℕ) {L M : ℕ} (hLM : L ≤ M) :
    finiteFamily g m L ⊆ finiteFamily g m M := by
  apply powersetCard_mono
  intro r hr
  exact mem_Ioc.mpr ⟨(mem_Ioc.mp hr).1, (mem_Ioc.mp hr).2.trans hLM⟩

/-- The finite partition function `Z_M` of v10, Section `sec:frequency`. -/
def finiteZ (m M : ℕ) (f : Finset ℕ → ℝ) : ℝ :=
  ∑ R ∈ finiteFamily (m / 2) m M, f R

/-- Exactly the configurations discarded by the cutoff `20m`. -/
def tailFamily (m M : ℕ) : Finset (Finset ℕ) :=
  finiteFamily (m / 2) m M \ finiteFamily (m / 2) m (20 * m)

/-- A total version of the largest frequency; it is zero on the empty set. -/
def largest (R : Finset ℕ) : ℕ := R.sup id

theorem largest_mem (R : Finset ℕ) (hR : R.Nonempty) : largest R ∈ R := by
  simpa [largest] using (Finset.sup_mem_of_nonempty (f := id) hR)

theorem le_largest (R : Finset ℕ) (r : ℕ) (hr : r ∈ R) : r ≤ largest R := by
  exact Finset.le_sup (f := id) hr

theorem tail_nonempty {m M : ℕ} (hm : 0 < m) {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) : R.Nonempty := by
  have hcard := ((mem_finiteFamily_iff _ _ _ _).mp (mem_sdiff.mp hR).1).1.2
  exact card_pos.mp (by omega)

theorem tail_largest_gt {m M : ℕ} {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) : 20 * m < largest R := by
  have hfull := (mem_finiteFamily_iff _ _ _ _).mp (mem_sdiff.mp hR).1
  by_contra h
  have hmax : largest R ≤ 20 * m := by omega
  apply (mem_sdiff.mp hR).2
  apply (mem_finiteFamily_iff _ _ _ _).mpr
  exact ⟨hfull.1, fun r hr => (le_largest R r hr).trans hmax⟩

theorem tail_largest_le {m M : ℕ} (hm : 0 < m) {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) : largest R ≤ M := by
  exact ((mem_finiteFamily_iff _ _ _ _).mp (mem_sdiff.mp hR).1).2 _
    (largest_mem R (tail_nonempty hm hR))

/-- The least unused site in the literal first window, with a harmless
zero value outside the domain on which the replacement argument uses it. -/
def site (m : ℕ) (R : Finset ℕ) : ℕ :=
  if h : (window (m / 2) m \ R).Nonempty then
    (window (m / 2) m \ R).min' h
  else 0

theorem site_eq_leastUnused (m : ℕ) (R : Finset ℕ)
    (hR : admissible (m / 2) m R) (r : ℕ) (hr : r ∈ R)
    (hout : m / 2 + m < r) :
    site m R = leastUnused (m / 2) m R hR r hr hout := by
  rw [site, dite_eq_left (unused_window_nonempty (m / 2) m R hR r hr hout)]
  rfl

theorem site_mem {m M : ℕ} (hm : 0 < m) {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) : site m R ∈ window (m / 2) m \ R := by
  have hadm := ((mem_finiteFamily_iff _ _ _ _).mp (mem_sdiff.mp hR).1).1
  have hr := largest_mem R (tail_nonempty hm hR)
  have hlarge := tail_largest_gt hR
  have hne := unused_window_nonempty (m / 2) m R hadm (largest R) hr (by omega)
  rw [site, dite_eq_left hne]
  exact min'_mem _ _

/-- This proves the least-site condition, in addition to unusedness. -/
theorem site_le_unused {m M : ℕ} (hm : 0 < m) {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) {s : ℕ}
    (hs : s ∈ window (m / 2) m \ R) : site m R ≤ s := by
  have hne : (window (m / 2) m \ R).Nonempty := ⟨_, site_mem hm hR⟩
  rw [site, dite_eq_left hne]
  exact min'_le _ _ hs

theorem site_le_three_halves {m M : ℕ} (hm : 0 < m) {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) : site m R ≤ 3 * m / 2 := by
  have hs := (mem_window_iff _ _ _).mp (mem_sdiff.mp (site_mem hm hR)).1
  omega

/-- Remove the largest frequency and insert the least unused first-window
site. This is precisely the replacement of v10, Section `sec:frequency`. -/
def replacement (m : ℕ) (R : Finset ℕ) : Finset ℕ :=
  replace (m / 2) m R (site m R) (largest R)

/-- The image stays in the same finite cutoff family. -/
theorem replacement_mem {m M : ℕ} (hm : 0 < m) (hM : 20 * m ≤ M)
    {R : Finset ℕ} (hR : R ∈ tailFamily m M) :
    replacement m R ∈ finiteFamily (m / 2) m M := by
  have hfull := (mem_finiteFamily_iff _ _ _ _).mp (mem_sdiff.mp hR).1
  have hs := mem_sdiff.mp (site_mem hm hR)
  have hwin := (mem_window_iff _ _ _).mp hs.1
  have hr := largest_mem R (tail_nonempty hm hR)
  apply (mem_finiteFamily_iff _ _ _ _).mpr
  refine ⟨replace_admissible _ _ _ hfull.1 _ _ hr hs.2 hwin.1, ?_⟩
  intro x hx
  change x ∈ insert (site m R) (R.erase (largest R)) at hx
  rcases mem_insert.mp hx with hx | hx
  · subst x
    omega
  · exact hfull.2 x (mem_erase.mp hx).2

/-- Given its output and removed largest frequency, a source is recovered
by deleting its inserted site and putting the largest frequency back. -/
theorem replacement_reconstruct {m M : ℕ} (hm : 0 < m) {R : Finset ℕ}
    (hR : R ∈ tailFamily m M) :
    R = insert (largest R) ((replacement m R).erase (site m R)) := by
  exact reconstruct_source (m / 2) m R (replacement m R) (largest R) (site m R)
    (largest_mem R (tail_nonempty hm hR)) (mem_sdiff.mp (site_mem hm hR)).2 rfl

/-- The actual finite fiber over a fixed pair `(R',r)`. -/
def replacementFiber (m M : ℕ) (R' : Finset ℕ) (r : ℕ) : Finset (Finset ℕ) :=
  (tailFamily m M).filter (fun R => (replacement m R, largest R) = (R', r))

/-- The paper's at-most-`m` fiber bound, with the source family and map
fully instantiated. There is no assumed fiber bound or low-family image. -/
theorem replacementFiber_card_le {m M : ℕ} (hm : 0 < m)
    (R' : Finset ℕ) (r : ℕ) : (replacementFiber m M R' r).card ≤ m := by
  apply atMostMFiber (g := m / 2) R' r (replacementFiber m M R' r) (site m)
    (window_card _ _)
  · intro R hR
    exact (mem_sdiff.mp (site_mem hm (mem_filter.mp hR).1)).1
  · intro R hR
    have hp := Prod.mk.inj (mem_filter.mp hR).2
    rw [← hp.2]
    exact largest_mem R (tail_nonempty hm (mem_filter.mp hR).1)
  · intro R hR
    exact (mem_sdiff.mp (site_mem hm (mem_filter.mp hR).1)).2
  · intro R hR
    have hp := Prod.mk.inj (mem_filter.mp hR).2
    rw [← hp.1, ← hp.2]
    rfl

theorem finiteZ_sub_eq_tail {m M : ℕ} (hM : 20 * m ≤ M)
    (f : Finset ℕ → ℝ) :
    finiteZ m M f - finiteZ m (20 * m) f = ∑ R ∈ tailFamily m M, f R := by
  unfold finiteZ tailFamily
  exact (eq_sub_iff_add_eq.mpr
    (Finset.sum_sdiff (f := f) (finiteFamily_mono (m / 2) m hM))).symm

/-- Finite replacement transport for the literal cutoff families. The only
pointwise analytic input is `hreplace`; reconstruction, the image family,
and multiplicity `m` are proved here. -/
theorem finiteReplacement_bound {m M : ℕ} (hm : 0 < m) (hM : 20 * m ≤ M)
    (f : Finset ℕ → ℝ) (q : ℕ → ℝ)
    (hf : ∀ R ∈ finiteFamily (m / 2) m M, 0 ≤ f R)
    (hq : ∀ r ∈ Ioc (20 * m) M, 0 ≤ q r)
    (hreplace : ∀ R ∈ tailFamily m M,
      f R ≤ q (largest R) * f (replacement m R)) :
    finiteZ m M f - finiteZ m (20 * m) f ≤
      (m : ℝ) * (∑ r ∈ Ioc (20 * m) M, q r) * finiteZ m M f := by
  have hmaps : ∀ R ∈ tailFamily m M,
      (replacement m R, largest R) ∈
        finiteFamily (m / 2) m M ×ˢ Ioc (20 * m) M := by
    intro R hR
    exact mem_product.mpr ⟨replacement_mem hm hM hR,
      mem_Ioc.mpr ⟨tail_largest_gt hR, tail_largest_le hm hR⟩⟩
  rw [finiteZ_sub_eq_tail hM]
  calc
    ∑ R ∈ tailFamily m M, f R ≤
        ∑ R ∈ tailFamily m M, q (largest R) * f (replacement m R) :=
      Finset.sum_le_sum hreplace
    _ = ∑ p ∈ finiteFamily (m / 2) m M ×ˢ Ioc (20 * m) M,
        ∑ R ∈ (tailFamily m M).filter (fun R => (replacement m R, largest R) = p),
          q p.2 * f p.1 :=
      (Finset.sum_fiberwise_of_maps_to' hmaps (fun p => q p.2 * f p.1)).symm
    _ ≤ ∑ p ∈ finiteFamily (m / 2) m M ×ˢ Ioc (20 * m) M,
        (m : ℝ) * (q p.2 * f p.1) := by
      apply Finset.sum_le_sum
      intro p hp
      have hcard :
          (((tailFamily m M).filter
            (fun R => (replacement m R, largest R) = p)).card : ℝ) ≤ m := by
        exact_mod_cast replacementFiber_card_le (M := M) hm p.1 p.2
      simpa only [Finset.sum_const, nsmul_eq_mul] using
        mul_le_mul_of_nonneg_right hcard
          (mul_nonneg (hq p.2 (mem_product.mp hp).2) (hf p.1 (mem_product.mp hp).1))
    _ = (m : ℝ) * (∑ r ∈ Ioc (20 * m) M, q r) * finiteZ m M f := by
      simp only [finiteZ, Finset.sum_product_right, Finset.mul_sum,
        Finset.sum_mul, mul_assoc]
      exact Finset.sum_comm

/-- Nonnegativity of the literal v10 frequency factor, including its
possible zero factors; no division by this factor is needed. -/
theorem frequencyFactor_nonneg (m g : ℕ) (S R : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ) : 0 ≤ frequencyFactor m g S R d Z := by
  unfold frequencyFactor weight
  positivity

/-- The literal partition function for the `f(R)` displayed in v10. -/
def frequencyZ (m M : ℕ) (S : Finset ℕ) (d : ℕ) (Z : Fin d → ℂ) : ℝ :=
  finiteZ m M (fun R => frequencyFactor m (m / 2) S R d Z)

/-- The finite scalar coefficient before the generating-function estimate. -/
def finiteTailCoefficient (m M : ℕ) : ℝ :=
  ((m : ℝ) / 1600) * (12500 : ℝ) ^ m *
    ∑ r ∈ Ioc (20 * m) M, weight (m / 2) r

/-- The exact `Z_M-Z_{20m} ≤ b_{m,M} Z_M` replacement estimate. Its
analytic input is a pointwise inequality, so zero full integrands cause no
division issue. -/
theorem finiteFrequencyTransfer_of_pointwise {m M : ℕ}
    (hm : 0 < m) (hM : 20 * m ≤ M) (S : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ)
    (hreplace : ∀ R ∈ tailFamily m M,
      frequencyFactor m (m / 2) S R d Z ≤
        ((12500 : ℝ) ^ m / 1600) * weight (m / 2) (largest R) *
          frequencyFactor m (m / 2) S (replacement m R) d Z) :
    frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z ≤
      finiteTailCoefficient m M * frequencyZ m M S d Z := by
  have h := finiteReplacement_bound hm hM
    (fun R => frequencyFactor m (m / 2) S R d Z)
    (fun r => ((12500 : ℝ) ^ m / 1600) * weight (m / 2) r)
    (fun R _ => frequencyFactor_nonneg _ _ _ _ _ _)
    (fun r _ => by unfold weight; positivity) hreplace
  convert h using 1
  · rfl
  · unfold finiteTailCoefficient frequencyZ
    rw [← Finset.mul_sum]
    ring

/-- Above `20m`, the factor `m²/(4r²)` costs at most `1/1600`. -/
theorem largeFrequency_coefficient_le (m r : ℕ) (hr : 20 * m < r) :
    (12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight (m / 2) r ≤
      ((12500 : ℝ) ^ m / 1600) * weight (m / 2) r := by
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast (show 0 < r by omega)
  have hrR : 20 * (m : ℝ) < r := by exact_mod_cast hr
  have hsq : (20 * (m : ℝ)) ^ 2 ≤ (r : ℝ) ^ 2 :=
    pow_le_pow_left₀ (by positivity) hrR.le 2
  have hbase : (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) ≤ 1 / 1600 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith
  calc
    (12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2) * weight (m / 2) r =
        ((12500 : ℝ) ^ m * ((m : ℝ) ^ 2 / (4 * (r : ℝ) ^ 2))) *
          weight (m / 2) r := by ring
    _ ≤ ((12500 : ℝ) ^ m * (1 / 1600)) * weight (m / 2) r := by
      apply mul_le_mul_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hbase (by positivity)
      · unfold weight
        positivity
    _ = ((12500 : ℝ) ^ m / 1600) * weight (m / 2) r := by ring

/-- The finite v10 replacement sum from the displayed pointwise ratio in
multiplicative form. It uses no positivity or inverse of the full factor. -/
theorem finiteFrequencyTransfer_of_ratio {m M : ℕ}
    (hm : 0 < m) (hM : 20 * m ≤ M) (S : Finset ℕ)
    (d : ℕ) (Z : Fin d → ℂ)
    (hratio : ∀ R ∈ tailFamily m M,
      frequencyFactor m (m / 2) S R d Z ≤
        ((12500 : ℝ) ^ m * (m : ℝ) ^ 2 / (4 * (largest R : ℝ) ^ 2) *
          weight (m / 2) (largest R)) *
          frequencyFactor m (m / 2) S (replacement m R) d Z) :
    frequencyZ m M S d Z - frequencyZ m (20 * m) S d Z ≤
      finiteTailCoefficient m M * frequencyZ m M S d Z := by
  apply finiteFrequencyTransfer_of_pointwise hm hM S d Z
  intro R hR
  exact (hratio R hR).trans (mul_le_mul_of_nonneg_right
    (largeFrequency_coefficient_le m (largest R) (tail_largest_gt hR))
    (frequencyFactor_nonneg _ _ _ _ _ _))

end

end Li2Lean.P0.FrequencyFinite
