/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Pinned.QPoly
import Li2Lean.P0.ConfigLogTaylor
import Li2Lean.Kit.LogSegment
import Li2Lean.Kit.EndpointPrimitive

/-!
# Rational logarithm and `x (log |x| - 1)` enclosures

`logI q` encloses `log q` for every rational `q > 0` by binary range
reduction and the proved atanh remainder of `ConfigLogTaylor`.  `FI u`
encloses the C-A primitive `u (log |u| - 1)` at a rational point, including
`u = 0`.  The primitive is antitone on `[-1/3, 1/3]`, which gives exact
one-sided hulls on cells touching a logarithmic singularity.  `termModel`
is a rigorous Taylor model of `c * F(u0 + t)` for `|t| ≤ ρ ≤ |u0|/2`.
-/

namespace Li2Lean.P0.CA.Pinned

open Li2Lean.LogSegment
open Li2Lean.P0.ConfigLogTaylor

/-! ## Atanh series without `Finset` -/

def atanhSum (z : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => atanhSum z n + z ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℚ)

theorem logPolynomial_eq_atanhSum (q : ℚ) (n : ℕ) :
    logPolynomial q n = 2 * atanhSum (logCoordinate q) n := by
  induction n with
  | zero => simp [logPolynomial, atanhSum]
  | succ n ih =>
      rw [logPolynomial, Finset.sum_range_succ, mul_add, ← logPolynomial, ih,
        atanhSum, mul_add]

/-- Fast enclosure of `log m`, `m > 0`, with `n` atanh terms. -/
def logBase (m : ℚ) (n : ℕ) : QI :=
  let P := 2 * atanhSum (logCoordinate m) n
  let R := logRemainder m n
  ⟨P - R, P + R⟩

theorem logBase_sound {m : ℚ} (hm : 0 < m) (n : ℕ) :
    (logBase m n).Contains (Real.log (m : ℝ)) := by
  have h := abs_le.mp (logPolynomial_remainder hm n)
  rw [logPolynomial_eq_atanhSum] at h
  simp only [logBase, QI.Contains]
  push_cast at h ⊢
  constructor <;> linarith [h.1, h.2]

/-- A certified enclosure of `log 2` (width below `10^-30`). -/
def LOG2 : QI :=
  ⟨693147180559945309417232121458176568 / 1000000000000000000000000000000000000,
   693147180559945309417232121458176569 / 1000000000000000000000000000000000000⟩

theorem LOG2_check : QI.subset (logBase 2 40) LOG2 = true := by decide +kernel

theorem log2_mem : LOG2.Contains (Real.log 2) := by
  have h := QI.mem_of_subset LOG2_check (logBase_sound (m := 2) (by norm_num) 40)
  simpa using h

/-! ## Binary range reduction -/

def pow2 : ℤ → ℚ
  | Int.ofNat n => ((2 ^ n : ℕ) : ℚ)
  | Int.negSucc n => 1 / ((2 ^ (n + 1) : ℕ) : ℚ)

theorem pow2_cast (k : ℤ) : ((pow2 k : ℚ) : ℝ) = (2 : ℝ) ^ k := by
  cases k with
  | ofNat n => simp [pow2]
  | negSucc n => simp [pow2, zpow_negSucc]

theorem pow2_pos (k : ℤ) : 0 < pow2 k := by
  cases k with
  | ofNat n => simp [pow2]
  | negSucc n => simp [pow2]

/-- Structural binary length (`Nat.log2` is not structurally recursive). -/
def blen : ℕ → ℕ → ℕ
  | 0, _ => 0
  | fuel + 1, n => if n < 2 then 0 else blen fuel (n / 2) + 1

def logExp (q : ℚ) : ℤ := (blen 512 q.num.natAbs : ℤ) - (blen 512 q.den : ℤ)

/-- Enclosure of `log q` for `q > 0` (the value for `q ≤ 0` is irrelevant). -/
def logI (q : ℚ) : QI :=
  let k := logExp q
  QI.round (QI.add (QI.smul (k : ℚ) LOG2) (logBase (q / pow2 k) 12))

theorem logI_sound {q : ℚ} (hq : 0 < q) : (logI q).Contains (Real.log (q : ℝ)) := by
  unfold logI
  apply QI.mem_round
  set k := logExp q
  have hp := pow2_pos k
  have hm : 0 < q / pow2 k := div_pos hq hp
  have hsplit : Real.log (q : ℝ) = (k : ℝ) * Real.log 2 + Real.log ((q / pow2 k : ℚ) : ℝ) := by
    have hqR : (q : ℝ) = ((q / pow2 k : ℚ) : ℝ) * (2 : ℝ) ^ k := by
      rw [Rat.cast_div, pow2_cast]
      field_simp
    rw [hqR, Real.log_mul (by exact_mod_cast hm.ne') (by positivity), Real.log_zpow]
    · simp only [Rat.cast_div, pow2_cast]
      ring
  rw [hsplit]
  have h1 := QI.mem_smul (k : ℚ) log2_mem
  have h2 := logBase_sound hm 12
  simpa using QI.mem_add h1 h2

/-! ## The primitive at rational points -/

def FI (u : ℚ) : QI :=
  if u = 0 then QI.pt 0 else QI.smul u (QI.sub (logI |u|) (QI.pt 1))

theorem FI_sound (u : ℚ) : (FI u).Contains (primitive (u : ℝ)) := by
  unfold FI
  split_ifs with hu
  · subst hu; simpa [primitive] using QI.mem_pt (0 : ℚ)
  · have hpos : 0 < |u| := abs_pos.mpr hu
    have hl := logI_sound hpos
    have h := QI.mem_smul u (QI.mem_sub hl (QI.mem_pt 1))
    simpa [primitive, Rat.cast_abs] using h

/-! ## Monotone hull near a singular point -/

theorem primitive_neg' (v : ℝ) : primitive (-v) = -primitive v := by
  unfold primitive; rw [abs_neg]; ring

theorem primitive_antitone_nonneg :
    AntitoneOn primitive (Set.Icc (0 : ℝ) (1 / 3)) := by
  have he : (1 / 3 : ℝ) ≤ Real.exp (-1) := by
    have := Real.exp_neg_one_gt_d9
    linarith
  intro x hx y hy hxy
  have h := ContourKit.endpointPrimitive_antitone_Icc he hx hy hxy
  simpa [ContourKit.endpointPrimitive, primitive, abs_of_nonneg hx.1,
    abs_of_nonneg hy.1] using h

theorem primitive_antitone :
    AntitoneOn primitive (Set.Icc (-(1 / 3) : ℝ) (1 / 3)) := by
  have hneg : ∀ a b : ℝ, -(1/3) ≤ a → a ≤ b → b ≤ 0 → primitive b ≤ primitive a := by
    intro a b ha hab hb
    have h := primitive_antitone_nonneg (a := -b) (b := -a)
      ⟨by linarith, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
    rw [primitive_neg', primitive_neg'] at h
    linarith
  intro a ha b hb hab
  rcases le_total b 0 with hb0 | hb0
  · exact hneg a b ha.1 hab hb0
  · rcases le_total a 0 with ha0 | ha0
    · have h1 : primitive b ≤ primitive 0 :=
        primitive_antitone_nonneg ⟨le_rfl, by norm_num⟩ ⟨hb0, hb.2⟩ hb0
      have h2 : primitive 0 ≤ primitive a := hneg a 0 ha.1 ha0 le_rfl
      linarith
    · exact primitive_antitone_nonneg ⟨ha0, ha.2⟩ ⟨hb0, hb.2⟩ hab

/-- Lower bound of `C * F(x + s)` on `[lo, hi]` when `[lo+s, hi+s] ⊂ [-1/3, 1/3]`. -/
def hullLower (C s lo hi : ℚ) : ℚ :=
  if 0 ≤ C then C * (FI (hi + s)).lo else C * (FI (lo + s)).hi

def hullOK (s lo hi : ℚ) : Bool := decide (-(1 / 3) ≤ lo + s ∧ hi + s ≤ 1 / 3)

theorem hullLower_le {C s lo hi : ℚ} (hok : hullOK s lo hi = true) {x : ℝ}
    (hlo : (lo : ℝ) ≤ x) (hhi : x ≤ (hi : ℝ)) :
    (hullLower C s lo hi : ℝ) ≤ (C : ℝ) * primitive (x + s) := by
  have h := of_decide_eq_true hok
  have h1 := (Rat.cast_le (K := ℝ)).mpr h.1
  have h2 := (Rat.cast_le (K := ℝ)).mpr h.2
  push_cast at h1 h2
  have hA : primitive (x + s) ≤ primitive ((lo + s : ℚ) : ℝ) := by
    push_cast
    exact primitive_antitone ⟨h1, by linarith⟩ ⟨by linarith, by linarith⟩ (by linarith)
  have hB : primitive ((hi + s : ℚ) : ℝ) ≤ primitive (x + s) := by
    push_cast
    exact primitive_antitone ⟨by linarith, by linarith⟩ ⟨by linarith, h2⟩ (by linarith)
  unfold hullLower
  split_ifs with hC
  · have hCR : (0 : ℝ) ≤ C := by exact_mod_cast hC
    have hF := (FI_sound (hi + s)).1
    push_cast
    nlinarith
  · have hCR : (C : ℝ) ≤ 0 := by exact_mod_cast (le_of_not_ge hC)
    have hF := (FI_sound (lo + s)).2
    push_cast
    nlinarith

/-! ## Taylor model of a smooth term -/

/-- Coefficients of `P_n(t/u0) = Σ_{i<n} (-1)^i (t/u0)^(i+1)/(i+1)`. -/
def logSeriesPoly (u0 : ℚ) (n : ℕ) : List ℚ :=
  0 :: (List.range n).map (fun i => (-1) ^ i / (((i + 1 : ℕ) : ℚ) * u0 ^ (i + 1)))

theorem hornerR_append (l : List ℝ) (a t : ℝ) :
    hornerR (l ++ [a]) t = hornerR l t + a * t ^ l.length := by
  induction l with
  | nil => simp [hornerR]
  | cons b bs ih => simp only [List.cons_append, hornerR, ih, List.length_cons, pow_succ]; ring

theorem hornerR_range (g : ℕ → ℚ) (n : ℕ) (t : ℝ) :
    hornerR (castL ((List.range n).map g)) t = ∑ i ∈ Finset.range n, (g i : ℝ) * t ^ i := by
  induction n with
  | zero => simp [hornerR, castL]
  | succ n ih =>
      rw [List.range_succ, List.map_append, castL_append]
      simp only [List.map_cons, List.map_nil, castL]
      rw [hornerR_append, ih, castL_length, List.length_map, List.length_range,
        Finset.sum_range_succ]

theorem hornerR_logSeriesPoly {u0 : ℚ} (hu : u0 ≠ 0) (n : ℕ) (t : ℝ) :
    hornerR (castL (logSeriesPoly u0 n)) t =
      -∑ i ∈ Finset.range n, (-(t / u0)) ^ (i + 1) / (i + 1) := by
  have h := hornerR_range (fun i => (-1) ^ i / (((i + 1 : ℕ) : ℚ) * u0 ^ (i + 1))) n t
  simp only [logSeriesPoly, castL, hornerR]
  rw [h, Finset.mul_sum, ← Finset.sum_neg_distrib]
  simp only [Rat.cast_zero, zero_add]
  apply Finset.sum_congr rfl
  intro i _
  have hu' : (u0 : ℝ) ≠ 0 := by exact_mod_cast hu
  push_cast
  rw [show (-(t / (u0 : ℝ))) ^ (i + 1) = (-1) ^ (i + 1) * t ^ (i + 1) / (u0 : ℝ) ^ (i + 1) by
    rw [neg_pow, div_pow]; ring]
  field_simp
  ring

/-- Product of a rational polynomial with `(u0 + t)`. -/
def mulLinear (u0 : ℚ) (p : List ℚ) : List ℚ := addQ (p.map (fun a => u0 * a)) (0 :: p)

theorem hornerR_mulLinear (u0 : ℚ) (p : List ℚ) (t : ℝ) :
    hornerR (castL (mulLinear u0 p)) t = ((u0 : ℝ) + t) * hornerR (castL p) t := by
  rw [mulLinear, castL_addQ, hornerR_addR]
  have h1 : castL (p.map (fun a => u0 * a)) = scaleR (u0 : ℝ) (castL p) :=
    castL_map_mul _ _
  have h2 : castL (0 :: p) = mulX (castL p) := by simp [castL, mulX]
  rw [h1, h2, hornerR_scaleR, hornerR_mulX]
  ring

def pointList (l : List ℚ) : List QI := l.map QI.pt

theorem forall2_pointList (l : List ℚ) :
    List.Forall₂ QI.Contains (pointList l) (castL l) := by
  induction l with
  | nil => exact List.Forall₂.nil
  | cons a as ih => exact List.Forall₂.cons (QI.mem_pt a) ih

/-- Taylor model of `t ↦ c * F(x0 + t + s)` on `|t| ≤ ρ`. -/
def termModel (c x0 s ρ : ℚ) (n : ℕ) : Model :=
  let u0 := x0 + s
  let Lm1 := QI.sub (logI |u0|) (QI.pt 1)
  let σ := ρ / |u0|
  Model.round
    ⟨addI [QI.smul (c * u0) Lm1, QI.smul c Lm1]
        (pointList ((mulLinear u0 (logSeriesPoly u0 n)).map (fun a => c * a))),
     |c| * |u0| * (1 + σ) * σ ^ (n + 1) / (1 - σ)⟩

theorem termModel_holds (c x0 s ρ : ℚ) (n : ℕ) (hρ : 0 < ρ) (h2 : 2 * ρ ≤ |x0 + s|) :
    (termModel c x0 s ρ n).Holds (fun t => (c : ℝ) * primitive ((x0 : ℝ) + t + s)) ρ := by
  unfold termModel
  apply Model.round_holds
  intro t ht
  set u0 : ℚ := x0 + s with hu0def
  have hupos : 0 < |u0| := by linarith
  have hu0 : u0 ≠ 0 := abs_pos.mp hupos
  have hu0R : (u0 : ℝ) ≠ 0 := by exact_mod_cast hu0
  have habsR : (0 : ℝ) < |(u0 : ℝ)| := abs_pos.mpr hu0R
  set σ : ℚ := ρ / |u0| with hσdef
  have hσ : σ ≤ 1 / 2 := by
    rw [hσdef, div_le_iff₀ hupos]; linarith
  have hσ0 : 0 ≤ σ := by positivity
  have hσR : (σ : ℝ) = (ρ : ℝ) / |(u0 : ℝ)| := by
    rw [hσdef]; push_cast; rfl
  set sp : ℝ := t / u0 with hsp
  have hsp_abs : |sp| ≤ (σ : ℝ) := by
    rw [hsp, abs_div, hσR]
    exact div_le_div_of_nonneg_right ht habsR.le
  have hσ1 : (σ : ℝ) ≤ 1 / 2 := by
    have := (Rat.cast_le (K := ℝ)).mpr hσ; push_cast at this; exact this
  have hsp1 : |sp| < 1 := by linarith
  have h1sp : 0 < 1 + sp := by linarith [neg_abs_le sp]
  set L : ℝ := Real.log |(u0 : ℝ)|
  have hL : (QI.sub (logI |u0|) (QI.pt 1)).Contains (L - 1) := by
    have := logI_sound (q := |u0|) hupos
    simpa [L, Rat.cast_abs] using QI.mem_sub this (QI.mem_pt 1)
  have hu0R' : (u0 : ℝ) = x0 + s := by rw [hu0def]; push_cast; ring
  have hsum : (x0 : ℝ) + t + s = (u0 : ℝ) * (1 + sp) := by
    rw [hsp, mul_add, mul_one, mul_div_cancel₀ _ hu0R, hu0R']; ring
  have hprim : primitive ((x0 : ℝ) + t + s) =
      ((u0 : ℝ) + t) * (L - 1) + ((u0 : ℝ) + t) * Real.log (1 + sp) := by
    rw [hsum]
    have habs : |(u0 : ℝ) * (1 + sp)| = |(u0 : ℝ)| * (1 + sp) := by
      rw [abs_mul, abs_of_pos h1sp]
    have hlog : Real.log |(u0 : ℝ) * (1 + sp)| = L + Real.log (1 + sp) := by
      rw [habs, Real.log_mul habsR.ne' h1sp.ne']
    have ht' : (u0 : ℝ) + t = (u0 : ℝ) * (1 + sp) := by rw [hsp]; field_simp
    simp only [primitive, hlog, ht']
    ring
  -- witness coefficients
  set P : List ℚ := logSeriesPoly u0 n
  refine ⟨addR [(c : ℝ) * u0 * (L - 1), (c : ℝ) * (L - 1)]
      (castL ((mulLinear u0 P).map (fun a => c * a))), ?_, ?_⟩
  · apply forall2_addI
    · refine List.Forall₂.cons ?_ (List.Forall₂.cons ?_ List.Forall₂.nil)
      · have := QI.mem_smul (c * u0) hL; push_cast at this; simpa [mul_assoc] using this
      · exact QI.mem_smul c hL
    · exact forall2_pointList _
  · rw [hornerR_addR]
    have hc : castL ((mulLinear u0 P).map (fun a => c * a)) =
        scaleR (c : ℝ) (castL (mulLinear u0 P)) := castL_map_mul _ _
    rw [hc, hornerR_scaleR, hornerR_mulLinear, hornerR_logSeriesPoly hu0]
    simp only [hornerR]
    rw [hprim]
    have key : (c : ℝ) * (((u0 : ℝ) + t) * (L - 1) + ((u0 : ℝ) + t) * Real.log (1 + sp)) -
        ((c : ℝ) * u0 * (L - 1) + t * ((c : ℝ) * (L - 1) + t * 0) +
          (c : ℝ) * (((u0 : ℝ) + t) *
            -∑ i ∈ Finset.range n, (-(t / (u0 : ℝ))) ^ (i + 1) / (i + 1))) =
        (c : ℝ) * ((u0 : ℝ) + t) *
          ((∑ i ∈ Finset.range n, (-sp) ^ (i + 1) / (i + 1)) + Real.log (1 - -sp)) := by
      rw [hsp, sub_neg_eq_add]; ring
    rw [key]
    have hm := Real.abs_log_sub_add_sum_range_le (x := -sp) (by rwa [abs_neg]) n
    rw [abs_neg] at hm
    have hpow : |sp| ^ (n + 1) / (1 - |sp|) ≤ (σ : ℝ) ^ (n + 1) / (1 - σ) := by
      apply div_le_div₀ (by positivity) (pow_le_pow_left₀ (abs_nonneg _) hsp_abs _)
        (by linarith) (by linarith)
    have hlin : |(c : ℝ) * ((u0 : ℝ) + t)| ≤ |(c : ℝ)| * (|(u0 : ℝ)| * (1 + σ)) := by
      rw [abs_mul]
      apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
      have : |t| ≤ |(u0 : ℝ)| * σ := by
        rw [hσR, mul_div_cancel₀ _ habsR.ne']; exact ht
      calc |(u0 : ℝ) + t| ≤ |(u0 : ℝ)| + |t| := abs_add_le _ _
        _ ≤ _ := by nlinarith
    rw [abs_mul]
    calc |(c : ℝ) * ((u0 : ℝ) + t)| * |_| ≤
        (|(c : ℝ)| * (|(u0 : ℝ)| * (1 + σ))) * ((σ : ℝ) ^ (n + 1) / (1 - σ)) :=
          mul_le_mul hlin (hm.trans hpow) (abs_nonneg _) (by positivity)
      _ = _ := by push_cast; ring

end Li2Lean.P0.CA.Pinned
