/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.Arith
import Li2Lean.P0.ConfigLogTaylor

/-!
# Reflected logarithm and arctangent enclosures

`logI q` encloses `Real.log q` for every rational `q ≥ 0` (Lean's `log 0 = 0`),
and `atanI w` encloses `Real.arctan w` for every rational `w`.  The series
remainders are proved (atanh series from `ConfigLogTaylor`, and an arctangent
remainder proved below by monotonicity).  Constants (`log 2`, `π`,
`arctan (k/4)`) are checked by `decide +kernel` against the same series.
-/

namespace Li2Lean.P0.CA.Contour

open QI Li2Lean.P0.ConfigLogTaylor

/-! ## Logarithm -/

def lpr (y : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => lpr y n + y ^ (2 * n + 1) / ((2 * n + 1 : ℕ) : ℚ)

theorem lpr_eq (y : ℚ) (n : ℕ) :
    lpr y n = ∑ k ∈ Finset.range n, y ^ (2 * k + 1) / ((2 * k + 1 : ℕ) : ℚ) := by
  induction n with
  | zero => simp [lpr]
  | succ n ih => rw [lpr, ih, Finset.sum_range_succ]

/-- Horner form `Σ_{i<n} z^i/(2(k+i)+1)`. -/
def hsum (z : ℚ) (k : ℕ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => 1 / ((2 * k + 1 : ℕ) : ℚ) + z * hsum z (k + 1) n

theorem hsum_eq (z : ℚ) (n : ℕ) : ∀ k : ℕ,
    hsum z k n = ∑ i ∈ Finset.range n, z ^ i / ((2 * (k + i) + 1 : ℕ) : ℚ) := by
  induction n with
  | zero => intro k; simp [hsum]
  | succ n ih =>
      intro k
      rw [hsum, ih (k + 1), Finset.sum_range_succ', Finset.mul_sum]
      simp only [pow_zero, add_zero, one_div]
      rw [add_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro i _
      rw [pow_succ]
      have : 2 * (k + 1 + i) + 1 = 2 * (k + (i + 1)) + 1 := by ring
      rw [this]; ring

theorem lpr_hsum (y : ℚ) (n : ℕ) : lpr y n = y * hsum (y ^ 2) 0 n := by
  rw [lpr_eq, hsum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [zero_add, ← pow_mul, pow_succ]; ring

def lpoly (q : ℚ) (n : ℕ) : ℚ := 2 * lpr (logCoordinate q) n

theorem lpoly_eq (q : ℚ) (n : ℕ) : lpoly q n = logPolynomial q n := by
  rw [lpoly, lpr_eq]; rfl

def lrem (q : ℚ) (n : ℕ) : ℚ :=
  2 * (|logCoordinate q| ^ (2 * n + 1) / (1 - logCoordinate q ^ 2))

theorem lrem_eq (q : ℚ) (n : ℕ) : lrem q n = logRemainder q n := rfl

theorem log_lower {q : ℚ} (hq : 0 < q) (n : ℕ) :
    ((lpoly q n - lrem q n : ℚ) : ℝ) ≤ Real.log q := by
  have h := (abs_le.mp (logPolynomial_remainder hq n))
  rw [lpoly_eq, lrem_eq]; push_cast; linarith [h.1, h.2]

theorem log_upper {q : ℚ} (hq : 0 < q) (n : ℕ) :
    Real.log q ≤ ((lpoly q n + lrem q n : ℚ) : ℝ) := by
  have h := (abs_le.mp (logPolynomial_remainder hq n))
  rw [lpoly_eq, lrem_eq]; push_cast; linarith [h.1, h.2]

/-- `log 2` enclosure. -/
def L2 : QI := ⟨693147180559945309417 / 10 ^ 21, 693147180559945309418 / 10 ^ 21⟩

theorem L2_mem : L2.mem (Real.log 2) := by
  have h1 := log_lower (q := 2) (by norm_num) 30
  have h2 := log_upper (q := 2) (by norm_num) 30
  have c1 : L2.lo ≤ lpoly 2 30 - lrem 2 30 := by decide +kernel
  have c2 : lpoly 2 30 + lrem 2 30 ≤ L2.hi := by decide +kernel
  have c1' : (L2.lo : ℝ) ≤ ((lpoly 2 30 - lrem 2 30 : ℚ) : ℝ) := by exact_mod_cast c1
  have c2' : ((lpoly 2 30 + lrem 2 30 : ℚ) : ℝ) ≤ (L2.hi : ℝ) := by exact_mod_cast c2
  push_cast at h1 h2
  exact ⟨by push_cast at c1'; linarith, by push_cast at c2'; linarith⟩

def pow2z (k : ℤ) : ℚ := if 0 ≤ k then 2 ^ k.toNat else 1 / 2 ^ (-k).toNat

theorem pow2z_eq (k : ℤ) : (pow2z k : ℝ) = (2 : ℝ) ^ k := by
  unfold pow2z
  split_ifs with h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    simp
  · push Not at h
    obtain ⟨m, hm⟩ := Int.exists_eq_neg_ofNat (le_of_lt h)
    subst hm
    simp [zpow_neg]

theorem pow2z_pos (k : ℤ) : 0 < pow2z k := by
  unfold pow2z; split_ifs <;> positivity

def logRed (q : ℚ) : ℤ :=
  let k : ℤ := (Nat.log2 q.num.natAbs : ℤ) - (Nat.log2 q.den : ℤ)
  let r := q / pow2z k
  if 4 / 3 < r then k + 1 else if r < 2 / 3 then k - 1 else k

def nLog : ℕ := 6

/-- Fast series value `2 y Σ (y^2)^i/(2i+1)` and its remainder. -/
def lpolyF (q : ℚ) (n : ℕ) : ℚ :=
  2 * (logCoordinate q * hsum (logCoordinate q ^ 2) 0 n)

def lremF (q : ℚ) (n : ℕ) : ℚ :=
  2 * (|logCoordinate q| * (logCoordinate q ^ 2) ^ n / (1 - logCoordinate q ^ 2))

theorem lpolyF_eq (q : ℚ) (n : ℕ) : lpolyF q n = lpoly q n := by
  rw [lpolyF, lpoly, lpr_hsum]

theorem lremF_eq (q : ℚ) (n : ℕ) : lremF q n = lrem q n := by
  unfold lremF lrem
  have e : |logCoordinate q| ^ (2 * n + 1) =
      |logCoordinate q| * (logCoordinate q ^ 2) ^ n := by
    rw [pow_succ, ← pow_mul, (even_two_mul n).pow_abs]; ring
  rw [e]

def logPos (q : ℚ) (k : ℤ) : QI :=
  if rdn (q / pow2z k) ≤ 0 then ⟨1 - 1 / q, q - 1⟩ else
    rnd (add ⟨lpolyF (rdn (q / pow2z k)) nLog - lremF (rdn (q / pow2z k)) nLog,
      lpolyF (rdn (q / pow2z k)) nLog + lremF (rdn (q / pow2z k)) nLog +
        (rup (q / pow2z k) - rdn (q / pow2z k)) / rdn (q / pow2z k)⟩ (smul k L2))

def logI (q : ℚ) : QI :=
  if q ≤ 0 then pt 0 else logPos q (logRed q)

theorem log_le_add_div {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    Real.log b ≤ Real.log a + (b - a) / a := by
  have hb : 0 < b := lt_of_lt_of_le ha hab
  have h := Real.log_le_sub_one_of_pos (div_pos hb ha)
  rw [Real.log_div hb.ne' ha.ne'] at h
  have : b / a - 1 = (b - a) / a := by field_simp
  linarith

theorem logPos_mem {q : ℚ} (h0 : 0 < q) (k : ℤ) : (logPos q k).mem (Real.log q) := by
  unfold logPos
  have hqR : (0 : ℝ) < q := by exact_mod_cast h0
  split_ifs with h1
  · constructor
    · have := Real.log_le_sub_one_of_pos (inv_pos.mpr hqR)
      rw [Real.log_inv] at this
      push_cast; rw [one_div]; linarith
    · have := Real.log_le_sub_one_of_pos hqR
      push_cast; linarith
  · push Not at h1
    set r := q / pow2z k with hr
    have hp := pow2z_pos k
    have hrpos : 0 < r := div_pos h0 hp
    have hsplit : Real.log q = Real.log r + (k : ℝ) * Real.log 2 := by
      have hq' : (q : ℝ) = (r : ℝ) * (2 : ℝ) ^ k := by
        rw [hr]; push_cast; rw [← pow2z_eq]
        have : ((pow2z k : ℚ) : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
        field_simp
      rw [hq', Real.log_mul (by exact_mod_cast hrpos.ne') (by positivity), Real.log_zpow]
    apply mem_rnd
    rw [hsplit]
    have hk : (smul (k : ℚ) L2).mem ((k : ℝ) * Real.log 2) := by
      have := mem_smul (k : ℚ) L2_mem
      push_cast at this; exact this
    apply mem_add _ hk
    have hl : ((rdn r : ℚ) : ℝ) ≤ r := by exact_mod_cast rdn_le r
    have hh : (r : ℝ) ≤ ((rup r : ℚ) : ℝ) := by exact_mod_cast le_rup r
    have hlpos : (0 : ℝ) < ((rdn r : ℚ) : ℝ) := by exact_mod_cast h1
    have lo := log_lower h1 nLog
    have up := log_upper h1 nLog
    rw [← lpolyF_eq, ← lremF_eq] at lo up
    have hrh := log_le_add_div hlpos (hl.trans hh)
    have hr2 := Real.log_le_log (by exact_mod_cast hrpos) hh
    constructor
    · exact lo.trans (Real.log_le_log hlpos hl)
    · push_cast at up ⊢
      linarith

theorem logI_mem {q : ℚ} (hq : 0 ≤ q) : (logI q).mem (Real.log q) := by
  unfold logI
  split_ifs with h0
  · have : q = 0 := le_antisymm h0 hq
    subst this; simpa using mem_pt 0
  · exact logPos_mem (lt_of_not_ge h0) _

/-! ## Arctangent series -/

noncomputable def Sr (n : ℕ) (x : ℝ) : ℝ :=
  ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1)

theorem hasDerivAt_Sr (n : ℕ) (x : ℝ) :
    HasDerivAt (Sr n) (∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k)) x := by
  unfold Sr
  apply HasDerivAt.fun_sum
  intro k _
  have h := ((hasDerivAt_pow (2 * k + 1) x).const_mul ((-1 : ℝ) ^ k)).div_const
    (2 * k + 1 : ℝ)
  refine h.congr_deriv ?_
  have : (2 * k + 1 : ℝ) ≠ 0 := by positivity
  field_simp
  push_cast
  ring

theorem geom_alt (n : ℕ) (x : ℝ) :
    (1 + x ^ 2) * ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k) = 1 - (-1) ^ n * x ^ (2 * n) := by
  induction n with
  | zero => simp
  | succ n ih =>
      rw [Finset.sum_range_succ, mul_add, ih]
      ring

theorem arctan_series_bound (n : ℕ) (x : ℝ) :
    |Real.arctan x - Sr n x| ≤ |x| ^ (2 * n + 1) / (2 * n + 1) := by
  have hden : (0 : ℝ) < 2 * n + 1 := by positivity
  have hd : ∀ y : ℝ, HasDerivAt (fun y => Real.arctan y - Sr n y)
      ((-1) ^ n * y ^ (2 * n) / (1 + y ^ 2)) y := by
    intro y
    have h := (Real.hasDerivAt_arctan y).sub (hasDerivAt_Sr n y)
    refine h.congr_deriv ?_
    have hy : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have hg := geom_alt n y
    field_simp
    linarith
  have hp : ∀ y : ℝ, HasDerivAt (fun y : ℝ => y ^ (2 * n + 1) / (2 * n + 1)) (y ^ (2 * n)) y := by
    intro y
    have h := (hasDerivAt_pow (2 * n + 1) y).div_const (2 * n + 1 : ℝ)
    refine h.congr_deriv ?_
    field_simp
    push_cast
    ring
  have hbound : ∀ y : ℝ, |(-1) ^ n * y ^ (2 * n) / (1 + y ^ 2)| ≤ y ^ (2 * n) := by
    intro y
    have hy : (0 : ℝ) < 1 + y ^ 2 := by positivity
    have he : (0 : ℝ) ≤ y ^ (2 * n) := by rw [pow_mul]; positivity
    rw [abs_div, abs_mul, abs_pow, abs_neg, abs_one, one_pow, one_mul,
      abs_of_nonneg he, abs_of_pos hy, div_le_iff₀ hy]
    nlinarith [sq_nonneg y]
  -- ψ = h + p is monotone, φ = h - p is antitone
  have hψ : Monotone (fun y => (Real.arctan y - Sr n y) + y ^ (2 * n + 1) / (2 * n + 1)) := by
    apply monotone_of_hasDerivAt_nonneg (fun y => (hd y).add (hp y))
    intro y
    have := abs_le.mp (hbound y)
    simp only [Pi.zero_apply]; linarith [this.1]
  have hφ : Monotone (fun y => -((Real.arctan y - Sr n y) - y ^ (2 * n + 1) / (2 * n + 1))) := by
    apply monotone_of_hasDerivAt_nonneg (fun y => ((hd y).sub (hp y)).neg)
    intro y
    have := abs_le.mp (hbound y)
    simp only [Pi.zero_apply]; linarith [this.2]
  have h0 : Real.arctan 0 - Sr n 0 = 0 := by simp [Sr]
  rcases le_total 0 x with hx | hx
  · have a1 := hψ hx
    have a2 := hφ hx
    simp only [h0, zero_add] at a1 a2
    have z : (0 : ℝ) ^ (2 * n + 1) / (2 * n + 1) = 0 := by simp
    rw [z] at a1 a2
    rw [abs_of_nonneg hx, abs_le]
    constructor <;> linarith
  · have a1 := hψ hx
    have a2 := hφ hx
    simp only [h0, zero_add] at a1 a2
    have z : (0 : ℝ) ^ (2 * n + 1) / (2 * n + 1) = 0 := by simp
    rw [z] at a1 a2
    rw [abs_of_nonpos hx, abs_le]
    have hodd : (-x) ^ (2 * n + 1) = -(x ^ (2 * n + 1)) := by
      rw [Odd.neg_pow ⟨n, rfl⟩]
    rw [hodd]
    constructor
    · have : -(-(x ^ (2 * n + 1)) / (2 * n + 1)) = x ^ (2 * n + 1) / (2 * n + 1) := by ring
      linarith
    · have : -(x ^ (2 * n + 1)) / (2 * n + 1) = -(x ^ (2 * n + 1) / (2 * n + 1)) := by ring
      linarith

def spr (x : ℚ) : ℕ → ℚ
  | 0 => 0
  | n + 1 => spr x n + (-1) ^ n * x ^ (2 * n + 1) / (2 * n + 1)

theorem spr_eq (x : ℚ) (n : ℕ) : ((spr x n : ℚ) : ℝ) = Sr n x := by
  induction n with
  | zero => simp [spr, Sr]
  | succ n ih =>
      rw [spr, Sr, Finset.sum_range_succ]
      push_cast
      rw [ih]; rfl

def srem (x : ℚ) (n : ℕ) : ℚ := |x| ^ (2 * n + 1) / (2 * n + 1)

theorem atan_lower (x : ℚ) (n : ℕ) : ((spr x n - srem x n : ℚ) : ℝ) ≤ Real.arctan x := by
  have h := abs_le.mp (arctan_series_bound n x)
  push_cast [srem]; rw [spr_eq]; linarith [h.1]

theorem atan_upper (x : ℚ) (n : ℕ) : Real.arctan x ≤ ((spr x n + srem x n : ℚ) : ℝ) := by
  have h := abs_le.mp (arctan_series_bound n x)
  push_cast [srem]; rw [spr_eq]; linarith [h.2]

def nAtan : ℕ := 6

theorem spr_hsum (x : ℚ) (n : ℕ) : spr x n = x * hsum (-x ^ 2) 0 n := by
  have h1 : ∀ n, spr x n = ∑ k ∈ Finset.range n, (-1) ^ k * x ^ (2 * k + 1) / (2 * k + 1) := by
    intro n; induction n with
    | zero => simp [spr]
    | succ n ih => rw [spr, ih, Finset.sum_range_succ]
  rw [h1, hsum_eq, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [zero_add, show (-x ^ 2) ^ i = (-1) ^ i * x ^ (2 * i) by rw [neg_pow, ← pow_mul]]
  push_cast; ring

def sprF (x : ℚ) (n : ℕ) : ℚ := x * hsum (-x ^ 2) 0 n

def sremF (x : ℚ) (n : ℕ) : ℚ := |x| * (x ^ 2) ^ n / (2 * n + 1)

theorem sremF_eq (x : ℚ) (n : ℕ) : sremF x n = srem x n := by
  unfold sremF srem
  have e : |x| ^ (2 * n + 1) = |x| * (x ^ 2) ^ n := by
    rw [pow_succ, ← pow_mul, (even_two_mul n).pow_abs]; ring
  rw [e]

theorem arctan_sub_le {a b : ℝ} (hab : a ≤ b) : Real.arctan b ≤ Real.arctan a + (b - a) := by
  have hm : Monotone (fun x => x - Real.arctan x) := by
    apply monotone_of_hasDerivAt_nonneg
      (fun x => (hasDerivAt_id x).sub (Real.hasDerivAt_arctan x))
    intro x
    have : 1 / (1 + x ^ 2) ≤ 1 := by
      rw [div_le_one (by positivity)]; nlinarith [sq_nonneg x]
    simp only [Pi.zero_apply]
    linarith
  have := hm hab
  simp only at this
  linarith

def atser (r : ℚ) : QI :=
  ⟨sprF (rdn r) nAtan - sremF (rdn r) nAtan,
    sprF (rdn r) nAtan + sremF (rdn r) nAtan + (rup r - rdn r)⟩

theorem atser_mem (r : ℚ) : (atser r).mem (Real.arctan r) := by
  have hl : ((rdn r : ℚ) : ℝ) ≤ r := by exact_mod_cast rdn_le r
  have hh : (r : ℝ) ≤ ((rup r : ℚ) : ℝ) := by exact_mod_cast le_rup r
  have lo := atan_lower (rdn r) nAtan
  have up := atan_upper (rdn r) nAtan
  rw [spr_hsum, ← sremF_eq] at lo up
  have h2 := arctan_sub_le (hl.trans hh)
  have h3 := Real.arctan_mono hh
  unfold atser sprF
  constructor
  · exact lo.trans (Real.arctan_mono hl)
  · push_cast at up ⊢
    linarith

/-! ## Constants -/

def PI : QI := ⟨314159265358979323846 / 10 ^ 20, 314159265358979323847 / 10 ^ 20⟩

theorem PI_mem : PI.mem Real.pi := by
  have h1 := Real.pi_gt_d20
  have h2 := Real.pi_lt_d20
  unfold PI QI.mem
  push_cast
  constructor <;> norm_num at h1 h2 ⊢ <;> linarith

/-- Table of `arctan (k/4)`, `k = 0..3`. -/
def atTab : ℕ → QI
  | 0 => pt 0
  | 1 => ⟨244978663126864154172 / 10 ^ 21, 244978663126864154174 / 10 ^ 21⟩
  | 2 => ⟨463647609000806116214 / 10 ^ 21, 463647609000806116215 / 10 ^ 21⟩
  | _ => ⟨643501108793284386802 / 10 ^ 21, 643501108793284386803 / 10 ^ 21⟩

theorem atTab_mem_of_check {k : ℕ} {c : ℚ} (n : ℕ)
    (h : decide ((atTab k).lo ≤ spr c n - srem c n ∧ spr c n + srem c n ≤ (atTab k).hi) = true) :
    (atTab k).mem (Real.arctan c) := by
  have h' := of_decide_eq_true h
  have a := atan_lower c n
  have b := atan_upper c n
  have c1 : ((atTab k).lo : ℝ) ≤ ((spr c n - srem c n : ℚ) : ℝ) := by exact_mod_cast h'.1
  have c2 : ((spr c n + srem c n : ℚ) : ℝ) ≤ ((atTab k).hi : ℝ) := by exact_mod_cast h'.2
  exact ⟨c1.trans a, b.trans c2⟩

theorem atTab_mem (k : ℕ) (hk : k ≤ 3) : (atTab k).mem (Real.arctan (((k : ℚ) / 4 : ℚ) : ℝ)) := by
  interval_cases k
  · simpa [atTab] using mem_pt 0
  · exact atTab_mem_of_check (k := 1) (c := ((1 : ℕ) : ℚ) / 4) 40 (by decide +kernel)
  · exact atTab_mem_of_check (k := 2) (c := ((2 : ℕ) : ℚ) / 4) 40 (by decide +kernel)
  · exact atTab_mem_of_check (k := 3) (c := ((3 : ℕ) : ℚ) / 4) 90 (by decide +kernel)

def atIdx (w : ℚ) : ℕ :=
  if w < 1 / 8 then 0 else if w < 3 / 8 then 1 else if w < 5 / 8 then 2 else 3

theorem atIdx_le (w : ℚ) : atIdx w ≤ 3 := by
  unfold atIdx; split_ifs <;> omega

/-- `arctan w` for `w ≥ 0` via `arctan w = arctan c + arctan ((w-c)/(1+wc))`. -/
def atanS (w : ℚ) : QI :=
  let k := atIdx w
  let c : ℚ := (k : ℚ) / 4
  add (atTab k) (atser ((w - c) / (1 + w * c)))

theorem arctan_shift {w c : ℝ} (hw : 0 ≤ w) (hc : 0 ≤ c) :
    Real.arctan w = Real.arctan c + Real.arctan ((w - c) / (1 + w * c)) := by
  have hp : 0 < 1 + w * c := by positivity
  rw [Real.arctan_add]
  · congr 1
    have h2 : 0 < 1 + c ^ 2 := by positivity
    have e1 : c + (w - c) / (1 + w * c) = w * (1 + c ^ 2) / (1 + w * c) := by
      field_simp; ring
    have e2 : 1 - c * ((w - c) / (1 + w * c)) = (1 + c ^ 2) / (1 + w * c) := by
      field_simp; ring
    rw [e1, e2]
    field_simp
  · rw [mul_div_assoc', div_lt_one hp]
    nlinarith [sq_nonneg c]

theorem atanS_mem {w : ℚ} (hw : 0 ≤ w) : (atanS w).mem (Real.arctan w) := by
  unfold atanS
  have hk := atTab_mem (atIdx w) (atIdx_le w)
  have hc : (0 : ℝ) ≤ ((atIdx w : ℚ) / 4 : ℚ) := by positivity
  have hwR : (0 : ℝ) ≤ (w : ℝ) := by exact_mod_cast hw
  rw [arctan_shift hwR hc]
  have := mem_add hk (atser_mem ((w - (atIdx w : ℚ) / 4) / (1 + w * ((atIdx w : ℚ) / 4))))
  push_cast at this ⊢
  exact this

def atanP (w : ℚ) : QI :=
  if 1 < w then sub (smul (1 / 2) PI) (atanS (1 / w)) else atanS w

theorem atanP_mem {w : ℚ} (hw : 0 ≤ w) : (atanP w).mem (Real.arctan w) := by
  unfold atanP
  split_ifs with h
  · have hwpos : (0 : ℝ) < w := by exact_mod_cast (lt_trans zero_lt_one h)
    have e : Real.arctan w = 1 / 2 * Real.pi - Real.arctan (1 / w : ℚ) := by
      have := Real.arctan_inv_of_pos hwpos
      push_cast; rw [one_div (w : ℝ), this]; ring
    rw [e]
    have := mem_sub (mem_smul (1 / 2) PI_mem) (atanS_mem (w := 1 / w) (by positivity))
    push_cast at this ⊢
    exact this
  · exact atanS_mem hw

def atanI (w : ℚ) : QI :=
  rnd (if w < 0 then neg (atanP (-w)) else atanP w)

theorem atanI_mem (w : ℚ) : (atanI w).mem (Real.arctan w) := by
  unfold atanI
  apply mem_rnd
  split_ifs with h
  · have := mem_neg (atanP_mem (w := -w) (by linarith))
    push_cast at this
    rwa [Real.arctan_neg, neg_neg] at this
  · exact atanP_mem (not_lt.mp h)

end Li2Lean.P0.CA.Contour
