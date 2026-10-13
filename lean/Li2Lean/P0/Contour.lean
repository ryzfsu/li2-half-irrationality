/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.LayerInterfaces
import Li2Lean.Kit.ContourKit

open MeasureTheory
open Filter
open Topology

namespace Li2Lean
namespace P0

noncomputable section

/-- Centre of the ellipse in v10 `sec-contour.tex`. -/
def xi : ℝ := (11281 : ℝ) / 10000

/-- Horizontal semiaxis of the ellipse in v10 `sec-contour.tex`. -/
def axisA : ℝ := (12783 : ℝ) / 10000

/-- Vertical semiaxis of the ellipse in v10 `sec-contour.tex`. -/
def axisB : ℝ := (229 : ℝ) / 200

/-- The two coefficients of the Joukowski map associated to `Gamma`. -/
def alpha : ℝ := (axisA + axisB) / 2

def beta : ℝ := (axisA - axisB) / 2

def xiScaled (m : ℕ) : ℝ := (m : ℝ) * xi

def axisAScaled (m : ℕ) : ℝ := (m : ℝ) * axisA

def axisBScaled (m : ℕ) : ℝ := (m : ℝ) * axisB

def alphaScaled (m : ℕ) : ℝ := (axisAScaled m + axisBScaled m) / 2

def betaScaled (m : ℕ) : ℝ := (axisAScaled m - axisBScaled m) / 2

/-- The logarithm `ell` in v10 `sec-contour.tex`. -/
def ell : ℝ := Real.log 2


/-- The paper's scaled ellipse `m Gamma`, with its real-parameter convention. -/
def ellipsePoint (m : ℕ) (u : ℝ) : ℂ := p0EllipsePoint m u


/-- At scale one, the paper parameterization is the `Tube` curve defining Γ. -/
theorem ellipsePoint_one_eq_gammaPoint (u : ℝ) :
    ellipsePoint 1 u = gammaPoint u := by
  simp [ellipsePoint, p0EllipsePoint, gammaPoint, center, semiMajor, semiMinor]
  <;> ring
/-- The paper's scaled tangent, with the same orientation as `Gamma`. -/
def ellipseTangent (m : ℕ) (u : ℝ) : ℂ := p0EllipseTangent m u

/-- The scaled affine Joukowski map used in the paper-specific pullback. -/
def scaledJoukowski (m : ℕ) (zeta : ℂ) : ℂ :=
  ContourKit.ellipseJoukowski (xiScaled m) (axisAScaled m) (axisBScaled m) zeta

/--
The literal parameter identity for `m Gamma`: the ellipse in v10
`sec-contour.tex` is the Joukowski image of the unit circle with the displayed
centre and coefficients. This is the paper-specific bridge from the generic
`ContourKit` map to the contour actually used in the proof.
-/
theorem ellipsePoint_eq_scaledJoukowski (m : ℕ) (u : ℝ) :
    ellipsePoint m u = scaledJoukowski m (Complex.exp (Complex.I * (u : ℂ))) := by
  have hscale : ellipsePoint m u =
    ContourKit.ellipsePoint (xiScaled m) (axisAScaled m) (axisBScaled m) u := by
    simp [ellipsePoint, p0EllipsePoint, ContourKit.ellipsePoint,
      xiScaled, axisAScaled, axisBScaled, xi, axisA, axisB]
    ring
  have h := ContourKit.ellipseJoukowski_param
    (xiScaled m) (axisAScaled m) (axisBScaled m) u
  rw [hscale, scaledJoukowski]
  exact h.symm

/--
The tangent identity for the scaled v10 contour. The factor `m` is kept
explicit, matching the `m Gamma` scaling in the paper.
-/
theorem ellipseTangent_eq_joukowskiDeriv (m : ℕ) (u : ℝ) :
    ellipseTangent m u =
      ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ)
        (circleMap 0 1 u) * (circleMap 0 1 u * Complex.I) := by
  have hscale : ellipseTangent m u =
      ContourKit.ellipseTangent (xiScaled m) (axisAScaled m) (axisBScaled m) u := by
    simp [ellipseTangent, p0EllipseTangent, ContourKit.ellipseTangent,
      axisAScaled, axisBScaled, axisA, axisB]
    ring
  rw [hscale, ContourKit.ellipseTangent_eq_joukowski]
  rfl

/-- The exact contour-C statement (v10 `eq:contour-C`). -/
def contourCStatement : Prop := P0ContourIdentityStatement

/-! ### The exact source matrix and the Cauchy--Binet subset sum -/

/-- The integer label of row `i` in `I_m`, with `i : Fin m`. -/
def rowIndex (m : ℕ) (i : Fin m) : ℕ := m / 4 + i.val

/-- `I_m`, encoded by its increasing row positions. -/
def Iset (m : ℕ) : Finset ℕ :=
  (Finset.univ : Finset (Fin m)).image (rowIndex m)

/-- `J_m` in the paper. -/
def Jset (m : ℕ) : Finset ℕ := Finset.range (2 * m)

theorem Iset_card (m : ℕ) : (Iset m).card = m := by
  unfold Iset
  rw [Finset.card_image_of_injective]
  · simp
  · intro i j hij
    apply Fin.ext
    dsimp [rowIndex] at hij
    omega

/-- For `4 | m`, the row encoding is exactly the interval `I_m` in the paper. -/
theorem Iset_eq_paper_interval (m : ℕ) (hm : 4 ∣ m) :
    Iset m = Finset.Ico (m / 4) (5 * m / 4) := by
  ext a
  simp only [Iset, Finset.mem_image, Finset.mem_univ, true_and,
    Finset.mem_Ico]
  constructor
  · rintro ⟨i, rfl⟩
    dsimp [rowIndex]
    constructor <;> omega
  · rintro ⟨hlo, hhi⟩
    rcases hm with ⟨q, hq⟩
    have hq' : m = 4 * q := hq
    refine ⟨⟨a - m / 4, ?_⟩, ?_⟩
    · rw [hq']
      omega
    · dsimp [rowIndex]
      omega

/-- The inclusion `I_m subset J_m`, needed for the pinned columns. -/
theorem Iset_subset_Jset (m : ℕ) (hm : 4 ∣ m) : Iset m ⊆ Jset m := by
  rw [Iset_eq_paper_interval m hm]
  intro a ha
  simp only [Finset.mem_Ico] at ha
  simp only [Jset, Finset.mem_range]
  rcases hm with ⟨q, hq⟩
  omega

/-- Increasing enumeration of a finite set, using its canonical order. -/
noncomputable def orderedElem {α : Type} [LinearOrder α]
    (s : Finset α) (i : Fin s.card) : α :=
  (Finset.orderIsoOfFin s rfl i).val

/-- A Cauchy determinant with the explicit increasing row and column orders. -/
def cauchyDet {n : ℕ} (x y : Fin n → ℂ) : ℂ :=
  Matrix.det (fun i j => (x i + y j)⁻¹)

/-- The Cauchy kernel `K(x,y)=1/(x+y)` on the paper's integer labels. -/
def cauchyKernel (x y : ℕ) : ℂ := ((x + y : ℕ) : ℂ)⁻¹

/-- A frequency subset, represented by its unique increasing enumeration. -/
def IncreasingFrequencyTuple (g m : ℕ) :=
  {r : Fin m → ℕ // StrictMono r ∧ ∀ i, g < r i}

/-- The paper's positive frequency weight `w_r`. -/
def frequencyWeight (g r : ℕ) : ℂ :=
  (Nat.choose (r - 1) g : ℂ) / (2 : ℂ) ^ r

/-- Real positive form of the same frequency weight, used in `Q_m`. -/
def frequencyWeightReal (g r : ℕ) : ℝ :=
  (Nat.choose (r - 1) g : ℝ) / (2 : ℝ) ^ r

/-- The literal complex value `G_m(beta)` of the determinant polynomial. -/
noncomputable def GmBeta (m : ℕ) : ℂ :=
  Polynomial.eval₂ (algebraMap ℚ ℂ) (li2InvValue (2 : ℤ) : ℂ)
    (p0CanonicalPolynomial 2 m)

/-- The `m` by `m` Cauchy minor `det K_{I_m,R}` in `eq:contour-CB`. -/
def cauchyMinorIR (m : ℕ) (r : Fin m → ℕ) : ℂ :=
  Matrix.det (fun i j : Fin m => cauchyKernel (rowIndex m i) (r j))

/-- The augmented source minor `[C^{(g)}; K_{R,J_m}]` in `eq:contour-CB`. -/
def augmentedSourceMinor (m : ℕ) (r : Fin m → ℕ) : ℂ :=
  Matrix.det (fun i : Fin (2 * m) => fun j : Fin (2 * m) =>
    if hi : i.val < m then
      p0C (m / 2) (rowIndex m ⟨i.val, hi⟩) j.val
    else
      cauchyKernel (r ⟨i.val - m, by omega⟩) j.val)

/-- One term of the paper's subset expansion, with no permutation factor. -/
def cauchyBinetTerm (m : ℕ) (r : Fin m → ℕ) : ℂ :=
  (∏ i : Fin m, frequencyWeight (m / 2) (r i)) *
    cauchyMinorIR m r * augmentedSourceMinor m r

/--
`eq:contour-CB`: the paper's sum over subsets of distinct frequencies. The
strictly increasing tuple is the canonical subset representation, so it
contains no `m!` multiplicity.
-/
def contourCBStatement : Prop :=
  ∀ m : ℕ, 0 < m → 4 ∣ m →
    Summable (fun r : IncreasingFrequencyTuple (m / 2) m =>
      ‖cauchyBinetTerm m r.val‖) ∧
    GmBeta m =
      (-1 : ℂ) ^ (m * (m / 2 + 1)) *
        ∑' r : IncreasingFrequencyTuple (m / 2) m,
          cauchyBinetTerm m r.val

/-- A-particle list of pinned real positions `S` in the paper's `I_m`. -/
def pinnedPositions (_m : ℕ) (S : Finset ℕ) : List ℂ :=
  ((S.sort (· ≤ ·)).map fun a => (a : ℂ))

/-- The Vandermonde `Delta(X)=prod_{i<j}(x_j-x_i)` on an ordered list. -/
def vandermondeList (X : List ℂ) : ℂ :=
  ∏ i : Fin X.length, ∏ j : Fin X.length,
    if i.val < j.val then X.get j - X.get i else 1

/-- The real `U_i` in the positive absolute integrand. -/
def UReal (g i : ℕ) : ℝ :=
  (2 : ℝ) ^ i * (Nat.choose (i + g) g : ℝ)

/-- The frequency-independent Cauchy minor det K_{I minus S,-Z} in (3.3). -/
noncomputable def contourQLeftMinor {m : ℕ} (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (Z : Fin (m - S.card) → ℂ) : ℂ := by
  classical
  let d := m - S.card
  let Ic := Iset m \ S
  have hIc : Ic.card = d := by
    rw [Finset.card_sdiff_of_subset hSI, Iset_card]
  exact cauchyDet
    (fun i : Fin d => ((orderedElem Ic (Fin.cast hIc.symm i) : ℕ) : ℂ))
    (fun i => -Z i)

/-- The three canonical Cauchy minors in (3.3), before absolute values. -/
noncomputable def contourQMinors {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (_hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) : ℂ × ℂ × ℂ := by
  classical
  let d := m - S.card
  let Ic := Iset m \ S
  let Jc := Jset m \ S
  have hIc : Ic.card = d := by
    rw [Finset.card_sdiff_of_subset hSI, Iset_card]
  have hSJ : S ⊆ Jset m := hSI.trans (Iset_subset_Jset m h4)
  have hScard : S.card ≤ m := by
    rw [← Iset_card m]
    exact Finset.card_le_card hSI
  have hJc : Jc.card = d + m := by
    rw [Finset.card_sdiff_of_subset hSJ]
    simp [d, Jset, Finset.card_range]
    omega
  let left : ℂ := contourQLeftMinor S hSI Z
  let middle : ℂ := cauchyDet
    (fun i : Fin m => ((rowIndex m i : ℕ) : ℂ))
    (fun i => (R i : ℂ))
  let right : ℂ := Matrix.det (fun i : Fin (d + m) => fun j : Fin (d + m) =>
    ((if hi : i.val < d then -Z ⟨i.val, hi⟩ else
        (R ⟨i.val - d, by omega⟩ : ℂ)) +
      ((orderedElem Jc (Fin.cast hJc.symm j) : ℕ) : ℂ))⁻¹)
  exact (left, middle, right)

/--
The absolute integrand `Q_m(S,R,Z)` in v10 `eq:contour-Q`, with the three
Cauchy minors, the actual source weights, and the actual entire function.
-/
def contourQValue {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) : ℝ :=
  let minors := contourQMinors S h4 hSI R hR Z
  (∏ a ∈ S, ell * UReal (m / 2) a) *
    (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
    (∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖) *
    ‖minors.1 * minors.2.1 * minors.2.2‖

/-- The fixed contour factor in v10 eq:contour-Q, independent of `R`. -/
def contourQFixedFactor {m : ℕ} (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (Z : Fin (m - S.card) → ℂ) : ℝ :=
  (∏ a ∈ S, ell * UReal (m / 2) a) *
    (∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖) *
    ‖contourQLeftMinor S hSI Z‖

/-- The two frequency-dependent Cauchy minors and all mixed cross factors. -/
def contourQMinorFrequencyProduct {m : ℕ} (S : Finset ℕ) (h4 : 4 ∣ m)
    (hSI : S ⊆ Iset m) (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) : ℝ :=
  let minors := contourQMinors S h4 hSI R hR Z
  (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
    ‖minors.2.1‖ * ‖minors.2.2‖

/-- Exact factorization of the literal eq:contour-Q integrand. -/
theorem contourQValue_eq_fixedFactor_mul_minorFrequencyProduct {m : ℕ}
    (S : Finset ℕ) (h4 : 4 ∣ m) (hSI : S ⊆ Iset m)
    (R : Fin m → ℕ) (hR : StrictMono R)
    (Z : Fin (m - S.card) → ℂ) :
    contourQValue S h4 hSI R hR Z =
      contourQFixedFactor S hSI Z *
        contourQMinorFrequencyProduct S h4 hSI R hR Z := by
  simp only [contourQValue, contourQFixedFactor, contourQMinorFrequencyProduct,
    contourQMinors, contourQLeftMinor, norm_mul]
  ring

/-- The fixed factor is nonnegative and does not depend on frequencies. -/
theorem contourQFixedFactor_nonneg {m : ℕ} (S : Finset ℕ)
    (hSI : S ⊆ Iset m) (Z : Fin (m - S.card) → ℂ) :
    0 ≤ contourQFixedFactor S hSI Z := by
  have hlog : 0 ≤ ell := le_of_lt (Real.log_pos (by norm_num))
  have hu (i : ℕ) : 0 ≤ UReal (m / 2) i := by
    unfold UReal
    positivity
  have hpinned : 0 ≤ ∏ a ∈ S, ell * UReal (m / 2) a := by
    apply Finset.prod_nonneg
    intro a ha
    exact mul_nonneg hlog (hu a)
  have hentire :
      0 ≤ ∏ i : Fin (m - S.card), ‖p0Entire (m / 2) (Z i)‖ := by
    apply Finset.prod_nonneg
    intro i hi
    exact norm_nonneg _
  exact mul_nonneg (mul_nonneg hpinned hentire) (norm_nonneg _)

/-- The frequency factor is nonnegative. -/
theorem contourQMinorFrequencyProduct_nonneg {m : ℕ} (S : Finset ℕ)
    (h4 : 4 ∣ m) (hSI : S ⊆ Iset m) (R : Fin m → ℕ)
    (hR : StrictMono R) (Z : Fin (m - S.card) → ℂ) :
    0 ≤ contourQMinorFrequencyProduct S h4 hSI R hR Z := by
  have hweights : 0 ≤ ∏ i : Fin m, frequencyWeightReal (m / 2) (R i) := by
    apply Finset.prod_nonneg
    intro i hi
    unfold frequencyWeightReal
    exact div_nonneg (by positivity) (by positivity)
  change 0 ≤
    (∏ i : Fin m, frequencyWeightReal (m / 2) (R i)) *
      ‖(contourQMinors S h4 hSI R hR Z).2.1‖ *
      ‖(contourQMinors S h4 hSI R hR Z).2.2‖
  exact mul_nonneg (mul_nonneg hweights (norm_nonneg _)) (norm_nonneg _)

/-- Bounded frequency subsets in `eq:contour-E`, represented increasingly. -/
def TruncatedFrequencyTuple (g m H : ℕ) :=
  {r : Fin m → Fin (H + 1) //
    StrictMono (fun i => (r i).val) ∧ ∀ i, g < (r i).val}

/-- The parameter measure for one traversal of `m Gamma`. -/
def contourParameterMeasure : Measure ℝ :=
  volume.restrict (Set.Icc (0 : ℝ) (2 * Real.pi))

/-- Product `prod |dz|/(2 pi)` density in the ellipse parameter. -/
def contourArcDensity (m : ℕ) (u : ℝ) : ℝ :=
  ‖p0EllipseTangent m u‖ / (2 * Real.pi)

/-- The normalized absolute contour integral for a fixed pinned set. -/
noncomputable def contourEContribution (m H : ℕ) (h4 : 4 ∣ m)
    (S : Finset ℕ) (hSI : S ⊆ Iset m) : ℝ := by
  classical
  letI : Fintype (TruncatedFrequencyTuple (m / 2) m H) :=
    Fintype.ofInjective Subtype.val Subtype.val_injective
  let d := m - S.card
  exact (Nat.factorial d : ℝ)⁻¹ *
    ∫ u : Fin d → ℝ,
      (∑ r : TruncatedFrequencyTuple (m / 2) m H,
        contourQValue S h4 hSI (fun i => (r.val i).val)
          r.property.1 (fun i => p0EllipsePoint m (u i)) *
          ∏ i : Fin d, contourArcDensity m (u i))
      ∂(ContourKit.productMeasure contourParameterMeasure)

/--
`eq:contour-E`: the exact finite-frequency upper envelope. The subset
symmetrization factor is `1/d!`, and each differential contributes
`|dz|/(2 pi)`.
-/
noncomputable def E (m H : ℕ) (h4 : 4 ∣ m) : ℝ := by
  classical
  exact ∑ S ∈ (Iset m).powerset,
    if hSI : S ⊆ Iset m then contourEContribution m H h4 S hSI else 0

/-- The exact real frequency field `psi` in v10 `eq:contour-psi`. -/
def psi (t : ℝ) : ℝ :=
  t * Real.log t - (t - 1 / 2) * Real.log (t - 1 / 2) -
    (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ) - t * ell

/-! ### The signed product formula, v10 `eq:contour-signed` -/

/-- The paper's factorial denominator `D_m(a)` in `eq:contour-signed`. -/
def signedD (m a : ℕ) : ℕ :=
  let n := m / 4
  (a - n).factorial * (n + m - 1 - a).factorial * a.factorial *
    (2 * m - 1 - a).factorial

/-- The paper's fixed-pole polynomial `P_m(z)` in `eq:contour-signed`. -/
def signedP (m : ℕ) (z : ℂ) : ℂ :=
  (∏ a ∈ Iset m, (z - (a : ℂ))) *
    ∏ a ∈ Jset m, (z - (a : ℂ))

/-- The paper's fixed-frequency polynomial `Q_m^*(r)` in `eq:contour-signed`. -/
def signedQstar (m r : ℕ) : ℂ :=
  (∏ a ∈ Iset m, ((r : ℂ) + (a : ℂ))) *
    ∏ a ∈ Jset m, ((r : ℂ) + (a : ℂ))

/-- Convert a finite complex tuple to its ordered list, preserving its indices. -/
def tupleList {d : ℕ} (x : Fin d → ℂ) : List ℂ := List.ofFn x

/-- The cross product `prod_{y in Y,r in R} (y+r)` in `eq:contour-signed`. -/
def signedCrossProduct (Y R : List ℂ) : ℂ :=
  Y.foldl (fun acc y => acc * R.foldl (fun acc r => acc * (y + r)) 1) 1

/-- The fixed increasing index lists `I_m` and `J_m` for Vandermonde factors. -/
def fixedIList (m : ℕ) : List ℂ :=
  List.ofFn (fun i : Fin m => (rowIndex m i : ℂ))

def fixedJList (m : ℕ) : List ℂ :=
  List.ofFn (fun j : Fin (2 * m) => (j.val : ℂ))

/-- The rational kernel inside the signed contour integral in `eq:contour-signed`. -/
def signedContourKernel (m : ℕ) (S : Finset ℕ)
    (Z : Fin (m - S.card) → ℂ) (R : Fin m → ℕ) : ℂ :=
  let d := m - S.card
  let Y := pinnedPositions m S ++ tupleList Z
  let Rlist := tupleList (fun i : Fin m => (R i : ℂ))
  (vandermondeList Y) ^ 2 * (vandermondeList Rlist) ^ 2 *
    signedCrossProduct Y Rlist /
      ((∏ i : Fin d, signedP m (Z i)) *
        ∏ i : Fin m, signedQstar m (R i)) *
    ∏ i : Fin d, p0Entire (m / 2) (Z i)

/--
The signed multiple contour integral, with one factor `dz/(2 pi i)` for
each coordinate and the paper's counterclockwise ellipse parameterization.
-/
noncomputable def signedContourIntegral (m : ℕ) (S : Finset ℕ)
    (R : Fin m → ℕ) : ℂ := by
  let d := m - S.card
  let c : ℂ := Complex.ofReal (2 * Real.pi) * Complex.I
  exact (c ^ d)⁻¹ *
    ∫ u : Fin d → ℝ,
      signedContourKernel m S (fun i => p0EllipsePoint m (u i)) R *
        ∏ i : Fin d, p0EllipseTangent m (u i)
      ∂(ContourKit.productMeasure contourParameterMeasure)

/-- One summand of `eq:contour-signed`, with `R` represented as a subset. -/
noncomputable def signedContourContribution (m : ℕ) (S : Finset ℕ)
    (R : IncreasingFrequencyTuple (m / 2) m) : ℂ := by
  let d := m - S.card
  exact (-1 : ℂ) ^ (S.card * (m / 4 + 1)) *
    (Complex.ofReal ell) ^ S.card * (Nat.factorial d : ℂ)⁻¹ *
    (∏ a ∈ S, p0U (m / 2) a / (signedD m a : ℂ)) *
    (∏ i : Fin m, frequencyWeight (m / 2) (R.val i)) *
    signedContourIntegral m S R.val

/-- The frequency-subset series for one pinned set in `eq:contour-signed`. -/
noncomputable def signedContourSeriesBlock (m : ℕ) (S : Finset ℕ)
    (_hSI : S ⊆ Iset m) : ℂ :=
  ∑' R : IncreasingFrequencyTuple (m / 2) m,
    signedContourContribution m S R

/-- Absolute convergence of each frequency-subset series in `eq:contour-signed`. -/
def signedContourSeriesAbsConvergent (m : ℕ) : Prop :=
  ∀ S : Finset ℕ, S ⊆ Iset m →
    Summable (fun R : IncreasingFrequencyTuple (m / 2) m =>
      ‖signedContourContribution m S R‖)

/-- The exact right-hand side of the paper's signed product formula. -/
noncomputable def signedContourRhs (m : ℕ) : ℂ :=
  (vandermondeList (fixedIList m)) ^ 2 *
    vandermondeList (fixedJList m) *
    ∑ S ∈ (Iset m).powerset,
      if hSI : S ⊆ Iset m then signedContourSeriesBlock m S hSI else 0

/--
`eq:contour-signed` from v10 `sec-contour.tex`, stated with its required
absolute convergence. The formula remains an explicit L5 bridge until proved.
-/
def signedContourStatement : Prop :=
  ∀ m : ℕ, 0 < m → 4 ∣ m →
    signedContourSeriesAbsConvergent m ∧ GmBeta m = signedContourRhs m

/-! ### P0-specific pole preimages for the Joukowski pullback -/

/--
The Vieta data placing the two preimages of the scaled integer pole `i` in
the unit disk. After scaling by `m`, the pole corresponds to `i/m` on `Gamma`.
-/
def P0PolePreimageCondition (m i : ℕ) : Prop :=
  ∃ z₁ z₂ : ℂ,
    z₁ + z₂ = ((i : ℂ) - (xiScaled m : ℂ)) / (alphaScaled m : ℂ) ∧
    z₁ * z₂ = (betaScaled m : ℂ) / (alphaScaled m : ℂ) ∧
    ‖z₁‖ < 1 ∧ ‖z₂‖ < 1

/--
The geometric range needed by the P0 instance of the Joukowski contour
lemma: every source pole `i < 2m` is strictly inside the scaled ellipse.
-/
def P0PolePreimageRangeStatement : Prop :=
  ∀ m : ℕ, 0 < m → ∀ i : ℕ, i < 2 * m → P0PolePreimageCondition m i

/--
The paper-specific pullback of the logarithmic derivative at an integer pole.
The only unresolved premise is the exact pole-preimage range above; the
analytic contour integral is the generic Joukowski theorem in `ContourKit`.
-/
theorem p0_pole_pullback_log_derivative (m i : ℕ) (hm : 0 < m)
    (hpre : P0PolePreimageCondition m i) :
    ∮ z in C(0, 1),
      ContourKit.joukowskiDeriv (alphaScaled m : ℂ) (betaScaled m : ℂ) z /
        (scaledJoukowski m z - (i : ℂ)) = 2 * (Real.pi : ℂ) * Complex.I := by
  rcases hpre with ⟨z₁, z₂, hsum, hprod, h₁, h₂⟩
  have hmR : 0 < (m : ℝ) := by exact_mod_cast hm
  have hα : 0 < alphaScaled m := by
    unfold alphaScaled axisAScaled axisBScaled axisA axisB
    positivity
  have hαne : (alphaScaled m : ℂ) ≠ 0 := by
    intro h
    have h' : alphaScaled m = 0 := by exact_mod_cast h
    linarith
  have h := ContourKit.joukowski_log_deriv_unitCircle
    (xi := (xiScaled m : ℂ))
    (alpha := (alphaScaled m : ℂ))
    (beta := (betaScaled m : ℂ))
    (w := (i : ℂ)) (z1 := z₁) (z2 := z₂)
    hαne hsum hprod h₁ h₂
  simpa [scaledJoukowski, ContourKit.ellipseJoukowski, alphaScaled, betaScaled] using h

/-! ### The full half-line variational problem -/

/-- Push the pinned measure on the real interval into the complex plane. -/
noncomputable def p0CompanionMeasure (κ : Measure ℝ) (ν : Measure ℂ) : Measure ℂ :=
  Measure.map Complex.ofReal κ + ν

/-- Reflection of a positive-line frequency measure onto the negative real axis. -/
noncomputable def p0ReflectedFrequencyMeasure (μ : Measure ℝ) : Measure ℂ :=
  Measure.map (fun t : ℝ => (-(t : ℂ))) μ

/-- The literal admissible measures in v10 `eq:contour-admissible`. -/
structure P0AdmissibleMeasures where
  kappa : Measure ℝ
  nu : Measure ℂ
  mu : Measure ℝ
  kappa_le_density :
    kappa ≤ volume.restrict (Set.Icc (1 / 4 : ℝ) (5 / 4 : ℝ))
  nu_supported : Measure.support nu ⊆ Gamma
  companion_mass : p0CompanionMeasure kappa nu Set.univ = 1
  mu_le_density : mu ≤ volume.restrict (Set.Ici (1 / 2 : ℝ))
  frequency_mass : mu Set.univ = 1

/-- The companion measure `eta=kappa+nu` in v10 `eq:contour-energy`. -/
noncomputable def P0AdmissibleMeasures.eta (M : P0AdmissibleMeasures) : Measure ℂ :=
  p0CompanionMeasure M.kappa M.nu

/-- The potential `A_0` from v10 `sec-contour.tex`. -/
noncomputable def A0 (z : ℂ) : ℝ :=
  (∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ), Real.log ‖z - (x : ℂ)‖) +
    ∫ x in (0 : ℝ)..(2 : ℝ), Real.log ‖z - (x : ℂ)‖

/-- The potential `B_0` from v10 `sec-contour.tex`. -/
noncomputable def B0 (t : ℝ) : ℝ :=
  (∫ x in (1 / 4 : ℝ)..(5 / 4 : ℝ), Real.log (t + x)) +
    ∫ x in (0 : ℝ)..(2 : ℝ), Real.log (t + x)

/-- The branch-free potential `phi` from v10 `sec-contour.tex`. -/
noncomputable def phi (z : ℂ) : ℝ :=
  z.re * ell +
    (∫ s in (0 : ℝ)..(1 / 2 : ℝ), Real.log ‖z + (s : ℂ)‖) +
    (1 / 2 : ℝ) - (1 / 2 : ℝ) * Real.log (1 / 2 : ℝ)

/-- The regularized frequency field in v10 `eq:contour-regularized`. -/
def p0RegularizedFrequencyField (t : ℝ) : ℝ :=
  B0 t - psi t - 3 * Real.log (1 + t)

/--
The regularized frequency self-kernel. Its chosen value on the diagonal
agrees almost everywhere with the paper's kernel for measures with a density
bound; the null-diagonal consequence is proved in
`DualL6Admissible.frequency_product_diagonal_null`.
-/
def p0RegularizedFrequencyKernel (t s : ℝ) : ℝ :=
  if t = s then 0 else Real.log (((1 + t) * (1 + s)) / |t - s|)

/-- The regularized companion-frequency kernel in v10 `eq:contour-regularized`. -/
def p0RegularizedMixedKernel (z : ℂ) (t : ℝ) : ℝ :=
  Real.log ((1 + t) / ‖z + (t : ℂ)‖)

/-- The companion-field integrand in v10 `eq:contour-energy`. -/
def p0CompanionField (z : ℂ) : ℝ := A0 z - phi z

/--
Finite-energy domain for the regularized formula in v10
`eq:contour-regularized`. It includes the first moment explicitly, so an
infinite first moment is assigned `+infinity` below. Since the real-valued
companion kernel is zero on collisions, atomlessness excludes finite-valued
atomic self-energy; the paper's collision value is `+infinity`. The frequency
diagonal representative is harmless under the density bound: its product-
measure nullity is proved in `DualL6Admissible`.
-/
def P0FiniteEnergyCondition (M : P0AdmissibleMeasures) : Prop :=
  Integrable (fun t : ℝ => t) M.mu ∧
  Integrable (fun z : ℂ => p0CompanionField z) M.eta ∧
  Integrable (fun t : ℝ => p0RegularizedFrequencyField t) M.mu ∧
  Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (M.eta.prod M.eta) ∧
  (∀ z : ℂ, M.eta {z} = 0) ∧
  Integrable (fun x : ℝ × ℝ => p0RegularizedFrequencyKernel x.1 x.2)
    (M.mu.prod M.mu) ∧
  Integrable (fun x : ℂ × ℝ => p0RegularizedMixedKernel x.1 x.2)
    (M.eta.prod M.mu)

/-- The finite value of the regularized energy in v10 `eq:contour-energy`. -/
noncomputable def p0RegularizedEnergyValue (M : P0AdmissibleMeasures) : ℝ :=
  (9 / 2 : ℝ) - 2 * ell +
    ∫ z : ℂ, p0CompanionField z ∂M.eta +
    ∫ t : ℝ, p0RegularizedFrequencyField t ∂M.mu +
    li2LogInteraction M.eta M.eta +
    ∫ x : ℝ × ℝ, p0RegularizedFrequencyKernel x.1 x.2 ∂(M.mu.prod M.mu) +
    ∫ x : ℂ × ℝ, p0RegularizedMixedKernel x.1 x.2 ∂(M.eta.prod M.mu)

/--
The regularized energy on its finite-energy domain, extended by `+infinity`.
Its equivalence with the paper's finite-energy conditions uses the stated
integrability and null-diagonal lemmas and remains to be proved.
-/
noncomputable def p0ExtendedEnergy (M : P0AdmissibleMeasures) : WithTop ℝ := by
  classical
  exact if _h : P0FiniteEnergyCondition M then
    (p0RegularizedEnergyValue M : WithTop ℝ) else ⊤

/-- An atom has the paper's infinite self-energy in the actual alphaGamma domain. -/
theorem p0ExtendedEnergy_eq_top_of_eta_atom (M : P0AdmissibleMeasures)
    {z : ℂ} (hz : M.eta {z} ≠ 0) : p0ExtendedEnergy M = ⊤ := by
  classical
  unfold p0ExtendedEnergy
  apply dif_neg
  intro hfinite
  rcases hfinite with ⟨_, _, _, _, hatomless, _, _⟩
  exact hz (hatomless z)

/-- The full-half-line variational value `alpha_Gamma` in v10 `eq:contour-alpha`. -/
noncomputable def alphaGamma : WithTop ℝ := sInf (Set.range p0ExtendedEnergy)

end

end P0
end Li2Lean
