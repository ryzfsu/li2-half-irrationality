/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.CA.Contour.FourierConst
import Li2Lean.P0.CA.Frequency.Arith
import Li2Lean.P0.ConfigContourFormula

open scoped BigOperators
namespace Li2Lean.P0.ActualReferenceQLogOutsideCheck
open CA.Contour CA.Contour.QI ConfigContourFormula ConfigContourKernel


def aq : ℚ := 24233 / 20000
def qq : ℚ := 1333 / 24233
def mq : ℚ := 267885951940 / 1000000000000
def dq (t : ℚ) : ℚ := (t + 11281 / 10000)^2 - 4 * aq^2 * qq

def di (t : ℚ) : QI :=
  ⟨CA.Frequency.sqrtLoAt CA.Frequency.roundScale (dq t),
   CA.Frequency.sqrtHiAt CA.Frequency.roundScale (dq t)⟩
def ri (t : ℚ) : QI := smul (1/2) (add (pt (t+11281/10000)) (di t))
def pi (t : ℚ) : QI := ⟨-aq / (ri t).lo, -aq / (ri t).hi⟩
def li (t : ℚ) : QI := ⟨(logI (ri t).lo).lo, (logI (ri t).hi).hi⟩

def powI (I : QI) : ℕ → QI
  | 0 => pt 1
  | n+1 => rnd (mul (powI I n) I)

theorem powI_mem {I : QI} {x : ℝ} (h : I.mem x) (n : ℕ) :
    (powI I n).mem (x^n) := by
  induction n with
  | zero => simpa [powI] using mem_pt 1
  | succ n ih => simpa [powI, pow_succ] using mem_rnd (mem_mul ih h)

theorem aq_cast : (aq : ℝ) = contourScale := by norm_num [aq, contourScale]
theorem qq_cast : (qq : ℝ) = contourRatio := by norm_num [qq, contourRatio]

theorem di_mem {t : ℚ} (ht : 1/2 ≤ t) :
    (di t).mem (Real.sqrt (((t:ℝ)+11281/10000)^2-4*contourScale^2*contourRatio)) := by
  have htR : (1/2:ℝ) ≤ t := CA.Frequency.half_le_cast ht
  have hd := outside_discriminant_nonneg htR
  have he : (dq t : ℝ) = ((t:ℝ)+11281/10000)^2-4*contourScale^2*contourRatio := by
    unfold dq; push_cast; rw [aq_cast, qq_cast]
  have hq : 0 ≤ dq t := by exact_mod_cast (he.symm ▸ hd)
  exact ⟨by simpa [di, he] using CA.Frequency.sqrtLoAt_le CA.Frequency.roundScale_pos hq,
    by simpa [di, he] using CA.Frequency.le_sqrtHiAt CA.Frequency.roundScale_pos hq⟩

theorem ri_mem {t : ℚ} (ht : 1/2 ≤ t) : (ri t).mem (outsideRadius t) := by
  have h := mem_smul (1/2) (mem_add (mem_pt (t+11281/10000)) (di_mem ht))
  convert h using 1 <;> simp only [ri, outsideRadius] <;> push_cast <;> ring

theorem ri_lo_pos {t : ℚ} (ht : 1/2 ≤ t) : 0 < (ri t).lo := by
  have h := CA.Frequency.sqrtLoAt_nonneg CA.Frequency.roundScale_pos (dq t)
  norm_num [ri, smul, add, pt, di]
  linarith

theorem pi_mem {t : ℚ} (ht : 1/2 ≤ t) : (pi t).mem (outsideParameter t) := by
  obtain ⟨hl,hu⟩ := ri_mem ht
  have hp : (0:ℝ) < (ri t).lo := by exact_mod_cast ri_lo_pos ht
  have hR := hp.trans_le hl
  have ha : (0:ℝ) ≤ aq := by norm_num [aq]
  have h1 := div_le_div_of_nonneg_left ha hp hl
  have h2 := div_le_div_of_nonneg_left ha hR hu
  unfold QI.mem pi outsideParameter
  push_cast
  rw [← aq_cast]
  simpa only [neg_div] using And.intro (neg_le_neg h1) (neg_le_neg h2)

theorem li_mem {t : ℚ} (ht : 1/2 ≤ t) : (li t).mem (Real.log (outsideRadius t)) := by
  obtain ⟨hl,hu⟩ := ri_mem ht
  have hp : (0:ℝ) < (ri t).lo := by exact_mod_cast ri_lo_pos ht
  have hR := hp.trans_le hl
  have hhi : 0 ≤ (ri t).hi := by exact_mod_cast (hR.le.trans hu)
  exact ⟨(logI_mem (ri_lo_pos ht).le).1.trans (Real.log_le_log hp hl),
    (Real.log_le_log hR hu).trans (logI_mem hhi).2⟩

noncomputable def logPrimitive (t : ℝ) : ℝ :=
  (t+11281/10000)*Real.log (outsideRadius t) -
    Real.sqrt ((t+11281/10000)^2-4*contourScale^2*contourRatio)
noncomputable def powerPrimitive : ℕ → ℝ → ℝ
  | 0, t => -contourScale * (Real.log (outsideRadius t)+contourRatio*outsideParameter t^2/2)
  | k+1, t => contourScale * (outsideParameter t^(k+1)/(k+1:ℝ)-
      contourRatio*outsideParameter t^(k+3)/(k+3:ℝ))
noncomputable def primitive (t : ℝ) : ℝ :=
  (mq:ℝ)*logPrimitive t - ∑ n ∈ Finset.range 48, CA.Contour.bR n*powerPrimitive n t

def logPrimitiveI (t : ℚ) : QI :=
  rnd (sub (smul (t+11281/10000) (li t)) (di t))
def powerPrimitiveI : ℕ → ℚ → QI
  | 0, t => rnd (smul (-aq) (add (li t) (smul (qq/2) (powI (pi t) 2))))
  | k+1, t => rnd (smul aq (sub (smul (1/(k+1:ℚ)) (powI (pi t) (k+1)))
      (smul (qq/(k+3:ℚ)) (powI (pi t) (k+3)))))
def primitiveI (t : ℚ) : QI := rnd (sub (smul mq (logPrimitiveI t))
  (sumIdx 48 (fun n => rnd (mul (rnd (bLit.getD n ⟨0,0⟩)) (powerPrimitiveI n t)))))

theorem logPrimitiveI_mem {t : ℚ} (ht : 1/2 ≤ t) :
    (logPrimitiveI t).mem (logPrimitive t) := by
  have h := mem_rnd (mem_sub (mem_smul (t+11281/10000) (li_mem ht)) (di_mem ht))
  simpa [logPrimitiveI, logPrimitive] using h

theorem powerPrimitiveI_mem {t : ℚ} (ht : 1/2 ≤ t) (n : ℕ) :
    (powerPrimitiveI n t).mem (powerPrimitive n t) := by
  cases n with
  | zero =>
    have h := mem_rnd (mem_smul (-aq) (mem_add (li_mem ht)
      (mem_smul (qq/2) (powI_mem (pi_mem ht) 2))))
    convert h using 1 <;> simp only [powerPrimitiveI, powerPrimitive]
    push_cast; rw [aq_cast, qq_cast]; ring
  | succ k =>
    have h := mem_rnd (mem_smul aq (mem_sub
      (mem_smul (1/(k+1:ℚ)) (powI_mem (pi_mem ht) (k+1)))
      (mem_smul (qq/(k+3:ℚ)) (powI_mem (pi_mem ht) (k+3)))))
    convert h using 1 <;> simp only [powerPrimitiveI, powerPrimitive]
    push_cast; rw [aq_cast, qq_cast]; ring

theorem primitiveI_mem {t : ℚ} (ht : 1/2 ≤ t) :
    (primitiveI t).mem (primitive t) := by
  exact mem_rnd (mem_sub (mem_smul mq (logPrimitiveI_mem ht))
    (mem_sumIdx fun n hn => mem_rnd (mem_mul (mem_rnd (bLit_mem hn)) (powerPrimitiveI_mem ht n))))

end Li2Lean.P0.ActualReferenceQLogOutsideCheck
