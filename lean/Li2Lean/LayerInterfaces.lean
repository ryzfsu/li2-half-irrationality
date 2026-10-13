/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Mathlib
import Li2Lean.Statement
import Li2Lean.P0.Tube

open MeasureTheory
open Filter
open Topology

namespace Li2Lean

noncomputable section

/-- The literal general-base `U_i` from docs/6333 §2 and docs/6379 §8.1. -/
def p0UQ (a : ℚ) (g i : ℕ) : ℚ :=
  a ^ i * (Nat.choose (i + g) g : ℚ)

/--
The rational form of `Q_s(a) = (a/(a-1))^s - 1` in docs/6333 §2 and
docs/6379 §8.1.  Keeping this as a named definition prevents the base `a`
from being confused with the specialised value `2` in the diagonal bank.
-/
def p0Q (a : ℚ) (s : ℕ) : ℚ :=
  (a / (a - 1)) ^ s - 1

/-- The literal general-base first moment from docs/6333 §2 and docs/6379 §8.1. -/
def p0TQ (a : ℚ) (g i : ℕ) : ℚ :=
  (∑ r ∈ Finset.range i,
      p0UQ a g (i - (r + 1)) / (r + 1 : ℚ)) +
    a ^ i *
      ∑ s ∈ Finset.range g,
        ((-1 : ℚ) ^ s / (s + 1 : ℚ)) *
          (Nat.choose (i + g) (g - (s + 1)) : ℚ) *
          p0Q a (s + 1)

/-- The literal general-base diagonal second moment, docs/6333 §2, §8.1. -/
def p0BQQ (a : ℚ) (g i : ℕ) : ℚ :=
  (∑ r ∈ Finset.range i,
      p0UQ a g (i - (r + 1)) / (r + 1 : ℚ) ^ 2) -
    a ^ i *
      ∑ s ∈ Finset.Icc 2 g,
        ((-1 : ℚ) ^ s / (s : ℚ)) *
        (Nat.choose (i + g) (g - s) : ℚ) *
        (∑ r ∈ Finset.range (s - 1),
            p0Q a (r + 1) / (r + 1 : ℚ))

/-- The literal general-base divided-difference entry `C_ij`, docs/6333 §2. -/
def p0CQ (a : ℚ) (g i j : ℕ) : ℚ :=
  if i = j then
    -p0UQ a g i * ∑ s ∈ Finset.range g, ((i + s + 1 : ℚ)⁻¹)
  else
    (p0UQ a g i - p0UQ a g j) / ((j : ℚ) - (i : ℚ))

/-- The literal general-base divided-difference entry `B_ij`, docs/6333 §2. -/
def p0BQ (a : ℚ) (g i j : ℕ) : ℚ :=
  if i = j then p0BQQ a g i
  else (p0TQ a g i - p0TQ a g j) / ((j : ℚ) - (i : ℚ))

/-- The literal diagonal pencil entry `A_ij`, docs/6333 §2. -/
def p0AQ (a : ℚ) (g i j : ℕ) : ℚ :=
  if i = j then p0UQ a g i else 0

/-- The literal `2m`-by-`2m` P0 pencil matrix over `Q[T]`, docs/6333 §1--2. -/
def p0MatrixQ (a : ℚ) (m : ℕ) : Matrix (Fin (2 * m)) (Fin (2 * m)) (Polynomial ℚ) :=
  fun r c =>
    let i := m / 4 + (if r.val < m then r.val else r.val - m)
    let j := c.val
    if r.val < m then
      Polynomial.C (p0CQ a (m / 2) i j)
    else
      Polynomial.C (p0BQ a (m / 2) i j) -
        Polynomial.X * Polynomial.C (p0AQ a (m / 2) i j)

/-- The canonical rational P0 determinant, with its paper index convention. -/
def p0CanonicalPolynomial (a : ℤ) (m : ℕ) : Polynomial ℚ :=
  if 4 ∣ m then Matrix.det (p0MatrixQ (a : ℚ) m) else 0

/--
The P0 polynomial family is fixed to the literal determinant of docs/6333
§§1--2, with the general-base source from docs/6379 §8.1. `G_source` prevents
arbitrary polynomial sequences from entering the arithmetic and nonvanishing
interfaces. Values away from positive multiples of four are irrelevant.
-/
structure P0Family where
  a : ℤ
  base_abs_ge_two : 2 ≤ Int.natAbs a
  G : ℕ → Polynomial ℝ
  G_source : ∀ m, 4 ∣ m →
    G m = (p0CanonicalPolynomial a m).map (algebraMap ℚ ℝ)

/-- Exact rational constant `K` from docs/6379, H2. -/
def p0K : ℝ :=
  (28553776527336974955476146348812001767941868552244211097690152323575789752978030410847923958183617568292693602659280722163521 : ℝ) /
    (11232791052646425258075015348173005886715693404430987490377741221297729302263656348751728480374838609207825413384121889792000 : ℝ)

/-- The fixed-base P0 integerizer rate from docs/6379, H2. -/
def p0TauSharp (a : ℤ) : ℝ :=
  p0K + (1 / 16 : ℝ) * Real.log (Int.natAbs (a - 1) : ℝ) -
    (13 / 16 : ℝ) * Real.log (Int.natAbs a : ℝ)

/--
L1 endpoint input from docs/6333 §1. The same polynomial, integerizer,
subsequence, and rate constants must be used in every field.
-/
structure EndpointCertificate (x : ℝ) where
  index : ℕ → ℕ
  G : ℕ → Polynomial ℝ
  D : ℕ → ℚ
  alpha : ℝ
  tau : ℝ
  cLog : ℝ
  cLinear : ℝ
  cConst : ℝ
  index_strictMono : StrictMono index
  index_multiple_four : ∀ k, 4 ∣ index k
  index_ge_eight : ∀ k, 8 ≤ index k
  alpha_gt_tau : tau < alpha
  degree_bound : ∀ k, (G (index k)).natDegree ≤ index k
  integerizer_pos : ∀ k, 0 < D (index k)
  integerizer_poly : ∀ k, ∃ P : Polynomial ℤ,
    P.map (Int.castRingHom ℝ) =
      Polynomial.C (D (index k) : ℝ) * G (index k)
  analytic_bound : ∀ k,
    |(G (index k)).eval x| ≤
      Real.exp (-alpha * (index k : ℝ) ^ 2 +
        cLog * (index k : ℝ) * Real.log (index k : ℝ) +
        cLinear * (index k : ℝ) + cConst)
  integerizer_rate : ∀ ε : ℝ, 0 < ε → ∃ k₀, ∀ k, k₀ ≤ k →
    Real.log (D (index k) : ℝ) / (index k : ℝ) ^ 2 ≤ tau + ε
  nonzero_at_rationals : ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
    (G (index k)).eval (r : ℝ) ≠ 0

/--
Generic form of the integer-contradiction criterion in docs/6333 §1. Its
future proof must derive the integer from `integerizer_poly` and the degree
bound, and use the same fixed rational point in `nonzero_at_rationals`.
-/
def L1EndpointCriterion : Prop :=
  ∀ x : ℝ, EndpointCertificate x → Irrational x

/--
P0's per-base integerization output from docs/6333 §8.5 and docs/6379, H2.
The limit is stated in epsilon form to expose the exact fixed-base quantifier.
-/
def P0IntegerizerBound (F : P0Family) : Prop :=
  ∃ D : ℕ → ℚ,
    (∀ m, 0 < m → 4 ∣ m → 0 < D m) ∧
    (∀ m, 0 < m → 4 ∣ m → (F.G m).natDegree ≤ m) ∧
    (∀ m, 0 < m → 4 ∣ m → ∃ P : Polynomial ℤ,
      P.map (Int.castRingHom ℝ) = Polynomial.C (D m : ℝ) * F.G m) ∧
    (∀ ε : ℝ, 0 < ε → ∃ M, ∀ m, M ≤ m → 0 < m → 4 ∣ m →
      Real.log (D m : ℝ) / (m : ℝ) ^ 2 ≤ p0TauSharp F.a + ε)

/-- A rational affine piece on a positive prime-ratio interval; docs/6379 §8.5. -/
structure PrimeAffinePiece where
  lo : ℚ
  hi : ℚ
  slope : ℚ
  intercept : ℚ
  lo_pos : 0 < lo
  lo_lt_hi : lo < hi

/-- Finite piecewise-affine profiles used by the weighted prime sum, docs/6379 §8.5. -/
structure PrimeAffineProfile where
  pieces : List PrimeAffinePiece

/-- Value of a finite affine profile, with half-open pieces to fix wall conventions. -/
noncomputable def PrimeAffineProfile.eval (P : PrimeAffineProfile) (x : ℝ) : ℝ :=
  (P.pieces.map fun q =>
    if (q.lo : ℝ) ≤ x ∧ x < (q.hi : ℝ) then
      (q.slope : ℝ) * x + (q.intercept : ℝ)
    else 0).sum

/-- The exact PNT hypothesis kept open at L3, docs/6333 §8.5 and docs/6406 L3. -/
def hPNT : Prop :=
  Tendsto (fun x : ℝ => Chebyshev.theta x / x) atTop (𝓝 (1 : ℝ))

/-- Weighted sum over rational primes for a finite affine profile. -/
noncomputable def weightedPrimeSum (P : PrimeAffineProfile) (x : ℝ) : ℝ :=
  ∑' p : ℕ, if Nat.Prime p then
    P.eval ((p : ℝ) / x) * Real.log (p : ℝ)
  else 0

/--
L3 weighted-prime limit from the classical PNT, in the exact normalization
used in docs/6333 §8.5. The sole analytic input is the explicit `hPNT` premise.
-/
def L3WeightedPrimeLimit : Prop :=
  hPNT → ∀ P : PrimeAffineProfile,
    Tendsto (fun x : ℝ => weightedPrimeSum P x / x) atTop
      (𝓝 (∫ t : ℝ, P.eval t))

/--
L4 output for the general-a P0 Frobenius tower, docs/6393 and docs/6379 H2.
The seed exponent `M` is allowed to depend on the fixed base; the prime is
chosen once for that base and works for every fixed rational specialization.
-/
def P0NonvanishingStatement (F : P0Family) : Prop :=
  ∃ M p : ℕ, 0 < M ∧ 4 ∣ M ∧ Nat.Prime p ∧ 10 < p ∧
    ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
      (F.G (M * p ^ k)).eval (r : ℝ) ≠ 0

/--
The fixed `M=32`, `p=83` nonzero subsequence in docs/6333 §9. The threshold
may depend on the fixed rational argument.
-/
def P0A2NonvanishingStatement (F : P0Family) : Prop :=
  F.a = 2 → ∀ r : ℚ, ∃ k₀, ∀ k, k₀ ≤ k →
    (F.G (32 * 83 ^ k)).eval (r : ℝ) ≠ 0

/-- Ellipse used by the P0 contour identity, docs/6333 §3. -/
noncomputable def p0EllipsePoint (m : ℕ) (u : ℝ) : ℂ :=
  Complex.ofReal (m : ℝ) *
    (Complex.ofReal ((11281 : ℝ) / 10000 + ((12783 : ℝ) / 10000) * Real.cos u) +
      Complex.I * Complex.ofReal (((229 : ℝ) / 200) * Real.sin u))

/-- Tangent of the scaled ellipse parameterization in docs/6333 §3. -/
noncomputable def p0EllipseTangent (m : ℕ) (u : ℝ) : ℂ :=
  Complex.ofReal (m : ℝ) *
    (Complex.ofReal (-((12783 : ℝ) / 10000) * Real.sin u) +
      Complex.I * Complex.ofReal (((229 : ℝ) / 200) * Real.cos u))

/-- Counterclockwise normalized integral on the scaled P0 ellipse. -/
noncomputable def p0EllipseIntegral (m : ℕ) (f : ℂ → ℂ) : ℂ :=
  (Complex.ofReal (2 * Real.pi) * Complex.I)⁻¹ *
    (∫ u in (0 : ℝ)..(2 * Real.pi),
      f (p0EllipsePoint m u) * p0EllipseTangent m u)

/-- The entire function `F_g` in docs/6333 §3. -/
noncomputable def p0Entire (g : ℕ) (z : ℂ) : ℂ :=
  Complex.exp (z * Complex.ofReal (Real.log 2)) *
    (∏ r ∈ Finset.range g, (z + (r + 1 : ℕ))) / (Nat.factorial g : ℂ)

/-- The exact `U_i` from docs/6333 §2. -/
noncomputable def p0U (g i : ℕ) : ℂ :=
  (2 : ℂ) ^ i * (Nat.choose (i + g) g : ℂ)

/-- The exact divided-difference entry `C_ij` from docs/6333 §2. -/
noncomputable def p0C (g i j : ℕ) : ℂ :=
  if i = j then
    -p0U g i * ∑ r ∈ Finset.range g, ((i + r + 1 : ℕ) : ℂ)⁻¹
  else
    (p0U g i - p0U g j) / ((j : ℂ) - (i : ℂ))

/--
L5 source statement (3.1) from docs/6333 §3. The restrictions place both
poles inside the contour `m Γ`, where `m=2g`.
-/
def P0ContourIdentityStatement : Prop :=
  ∀ g i j : ℕ, i < 4 * g → j < 4 * g →
    p0C g i j =
      -p0EllipseIntegral (2 * g) (fun z =>
        p0Entire g z / ((z - (i : ℂ)) * (z - (j : ℂ)))
      ) + if i = j then Complex.ofReal (Real.log 2) * p0U g i else 0

/-- Matrix integrand in the finite-dimensional Andréief identity. -/
noncomputable def andreiefIntegrand (d : ℕ) (f : Fin d → ℝ → ℂ)
    (g : ℝ → Fin d → ℂ) (x : Fin d → ℝ) : ℂ :=
  Matrix.det (fun i j => f i (x j)) * Matrix.det (fun i j => g (x i) j)

/-- Product measure for the Andréief integral in docs/6333 §3. -/
noncomputable def andreiefProductMeasure (d : ℕ) (μ : Measure ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi (fun _ : Fin d => μ)

/--
L5 Andréief statement used to pass from the moment matrix to the contour
configuration integral, docs/6333 §3 (3.2)–(3.3).
-/
def L5AndreiefStatement : Prop :=
  ∀ d : ℕ, ∀ μ : Measure ℝ, ∀ f : Fin d → ℝ → ℂ,
    ∀ g : ℝ → Fin d → ℂ,
      (∀ i j, Integrable (fun x => f i x * g x j) μ) →
      Integrable (andreiefIntegrand d f g) (andreiefProductMeasure d μ) →
      Matrix.det (fun i j => ∫ x, f i x * g x j ∂μ) =
        (Nat.factorial d : ℂ)⁻¹ *
          ∫ x : Fin d → ℝ, andreiefIntegrand d f g x ∂(andreiefProductMeasure d μ)

/-- The logarithmic kernel `K_0(z,w)=-log|z-w|`, docs/6333 §3. -/
noncomputable def li2LogKernel (z w : ℂ) : ℝ :=
  -Real.log ‖z - w‖

/-- Logarithmic interaction of two finite-energy measures on the plane. -/
noncomputable def li2LogInteraction (μ ν : Measure ℂ) : ℝ :=
  ∫ x : ℂ × ℂ, li2LogKernel x.1 x.2 ∂(μ.prod ν)

/--
L6 mass-zero log-energy positivity from docs/6333 §5 (5.3). The two finite,
atomless measures have equal mass and finite pairwise logarithmic energy;
compact support is not assumed, matching the paper-v10 extension.
-/
def L6MassZeroEnergyPositivity : Prop :=
  ∀ μ ν : Measure ℂ,
    μ Set.univ ≠ ⊤ → ν Set.univ ≠ ⊤ → μ Set.univ = ν Set.univ →
    (∀ z : ℂ, μ {z} = 0) → (∀ z : ℂ, ν {z} = 0) →
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod μ) →
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (ν.prod ν) →
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν) →
    0 ≤ li2LogInteraction μ μ + li2LogInteraction ν ν -
      2 * li2LogInteraction μ ν

/--
Legacy compact-support contract retained for the historical smoothing bridge.
The active `Li2LayerInterfaces.l6_mass_zero_energy` field uses the stronger
no-compact-support contract above.
-/
def L6CompactMassZeroEnergyPositivity : Prop :=
  ∀ μ ν : Measure ℂ,
    μ Set.univ ≠ ⊤ → ν Set.univ ≠ ⊤ → μ Set.univ = ν Set.univ →
    (∀ z : ℂ, μ {z} = 0) → (∀ z : ℂ, ν {z} = 0) →
    (∃ K : Set ℂ, IsCompact K ∧ μ Kᶜ = 0 ∧ ν Kᶜ = 0) →
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod μ) →
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (ν.prod ν) →
    Integrable (fun x : ℂ × ℂ => li2LogKernel x.1 x.2) (μ.prod ν) →
    0 ≤ li2LogInteraction μ μ + li2LogInteraction ν ν -
      2 * li2LogInteraction μ ν

/-- A point on a circle used in the L7 regularization, docs/6333 §4. -/
noncomputable def p0CirclePoint (z : ℂ) (r t : ℝ) : ℂ :=
  P0.circlePoint z r t

/-- Pair energy of two normalized circle measures, docs/6333 §4. -/
noncomputable def p0CirclePairEnergy (z w : ℂ) (r : ℝ) : ℝ :=
  P0.circlePairEnergy z w r

/--
The exact circle-average logarithm identity from docs/6333 §4; Mathlib's
`circleAverage_log_norm_sub_const_eq_log_radius_add_posLog` is the API target.
-/
def L7CircleAverageStatement : Prop :=
  ∀ x z : ℂ, ∀ r : ℝ, 0 < r →
    (∫ t in (0 : ℝ)..(2 * Real.pi),
      Real.log ‖x - p0CirclePoint z r t‖) / (2 * Real.pi) =
        Real.log (max r ‖x - z‖)

/--
L7 configuration split, docs/6333 §§3--4: collisions have zero `Δ(Y)^2`
weight in (3.5); nonzero Vandermonde configurations use the finite transfer
with pairwise-distinct centers. The finite-value kernel is never used at a
collision, where the paper's extended kernel is `+∞`.
-/
def L7FiniteConfigurationTransfer : Prop := P0.l7CollisionSplit

/-- The analytic target `1992909/10^6` of v10 (5.9), docs/6333 §5. -/
def p0PaperAlphaTarget : ℚ := 1992909 / 1000000

/--
The P0 analytic estimate of docs/6333 §1 (1.2), parameterized by the
quadratic decay rate `alpha`. The lower-order constants `10`, `56`, `301`
are those of the paper; only the leading rate is a parameter. The endpoint
argument needs `p0TauSharp 2 < alpha` (see `Li2Lean.P0.AlphaParam`).
-/
def P0AnalyticEstimateAt (alpha : ℝ) (F : P0Family) : Prop :=
  F.a = 2 → ∀ m, 8 ≤ m → 4 ∣ m →
    |(F.G m).eval (li2InvValue (2 : ℤ))| ≤
      Real.exp (-alpha * (m : ℝ) ^ 2 +
        10 * (m : ℝ) * Real.log (m : ℝ) + 56 * (m : ℝ) + 301)

/--
The assembled P0 analytic estimate from docs/6333 §1 (1.2) and §5 (5.9):
the instance `alpha = 1992909/10^6` of `P0AnalyticEstimateAt`.
-/
def P0AnalyticEstimate (F : P0Family) : Prop :=
  P0AnalyticEstimateAt (1992909 / 1000000 : ℝ) F

/-- The literal paper instance is the parameterized estimate at the paper target. -/
theorem p0AnalyticEstimate_iff_at_paperTarget (F : P0Family) :
    P0AnalyticEstimate F ↔
      P0AnalyticEstimateAt ((p0PaperAlphaTarget : ℚ) : ℝ) F := by
  have h : ((p0PaperAlphaTarget : ℚ) : ℝ) = (1992909 / 1000000 : ℝ) := by
    norm_num [p0PaperAlphaTarget]
  rw [h]
  rfl

/-- A larger decay rate gives a stronger estimate: the estimate is antitone in `alpha`. -/
theorem P0AnalyticEstimateAt.mono {alpha beta : ℝ} {F : P0Family}
    (hle : alpha ≤ beta) (h : P0AnalyticEstimateAt beta F) :
    P0AnalyticEstimateAt alpha F := by
  intro hbase m hm h4
  refine le_trans (h hbase m hm h4) (Real.exp_le_exp.mpr ?_)
  have hsq : 0 ≤ (m : ℝ) ^ 2 := sq_nonneg _
  nlinarith

/-- Rational interval cells for the L8 directed checker, docs/6333 §5, C-A. -/
structure RationalIntervalLowerCell where
  lo : ℚ
  hi : ℚ
  lower : ℚ
  lo_le_hi : lo ≤ hi

/--
Semantic form of a finite rational lower-bound certificate. Every interval is
covered and every local lower bound holds throughout its closed cell.
-/
def RationalIntervalLowerCertificate (f : ℝ → ℝ) (a b lower : ℚ)
    (cells : List RationalIntervalLowerCell) : Prop :=
  (∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) →
    ∃ c, c ∈ cells ∧ (c.lo : ℝ) ≤ x ∧ x ≤ (c.hi : ℝ)) ∧
  (∀ c, c ∈ cells → (lower : ℝ) ≤ c.lower ∧
    ∀ x : ℝ, (c.lo : ℝ) ≤ x → x ≤ (c.hi : ℝ) → (c.lower : ℝ) ≤ f x)

/--
L8 checker soundness target from docs/6333 §5 and Appendix A: exact rational
cell coverage plus per-cell bounds imply the global lower bound.
-/
def L8RationalIntervalCheckerSoundness : Prop :=
  ∀ (f : ℝ → ℝ) (a b lower : ℚ) (cells : List RationalIntervalLowerCell),
    RationalIntervalLowerCertificate f a b lower cells →
    ∀ x : ℝ, (a : ℝ) ≤ x → x ≤ (b : ℝ) → (lower : ℝ) ≤ f x

/-- The semantic interval checker is a direct consequence of its cover and cells. -/
theorem l8RationalIntervalChecker_soundness : L8RationalIntervalCheckerSoundness := by
  intro f a b lower cells hcert x hax hxb
  rcases hcert with ⟨hcover, hcells⟩
  obtain ⟨c, hmem, hlo, hhi⟩ := hcover x hax hxb
  obtain ⟨hlower, hbound⟩ := hcells c hmem
  exact le_trans hlower (hbound x hlo hhi)

/-
The dual certificate records the finite C-A lower-bound data and its
aggregation inequality. It remains separate from `P0AnalyticEstimate`, which
also requires the later contour-to-coefficient argument.
-/
structure P0DualCertificate (F : P0Family) where
  base_eq_two : F.a = 2
  qLog : ℝ
  pinnedPenalty : ℝ
  frequencyPenalty : ℝ
  alphaGamma : ℝ
  qLog_lower : (-(438334707 : ℝ) / 1000000000) < qLog
  pinnedPenalty_upper : pinnedPenalty ≤
    (6905963574153 : ℝ) / 81920000000000
  frequencyPenalty_upper : frequencyPenalty ≤
    (38158094390353 : ℝ) / 409600000000000
  duality_lower :
    (9 / 2 : ℝ) - 2 * Real.log 2 + qLog +
      (-(669 : ℝ) / 200) + (71 : ℝ) / 25 -
      pinnedPenalty - frequencyPenalty ≤ alphaGamma

/-
L8's output is conditional on the fixed base. The `Nonempty` wrapper keeps
this as a certificate interface instead of selecting a witness.
-/
def L8P0DualCertificateOutput (F : P0Family) : Prop :=
  F.a = 2 → Nonempty (P0DualCertificate F)

/--
Frozen S0.5 proof obligations. These propositions are contracts only; no
unproved field is installed as an axiom or used to discharge the S0 theorem.
-/
structure Li2LayerInterfaces : Prop where
  /-- L1 endpoint contradiction, docs/6333 §1. -/
  l1_endpoint : L1EndpointCriterion
  /-- L2 fixed-base P0 integerizer, docs/6333 §8 and docs/6379 H2. -/
  l2_p0_integerizer : hPNT → ∀ F : P0Family, P0IntegerizerBound F
  /-- L3 weighted PNT consequence with the sole open `hPNT` premise, docs/6333 §8.5. -/
  l3_weighted_prime : L3WeightedPrimeLimit
  /-- L4 parametric P0 nonvanishing tower, docs/6393. -/
  l4_p0_nonvanishing : ∀ F : P0Family, P0NonvanishingStatement F
  /-- L4 fixed `32 * 83^k` tower for the `a = 2` P0 source, docs/6333 §9. -/
  l4_a2_fixed_tower : ∀ F : P0Family, P0A2NonvanishingStatement F
  /-- L5 exact contour identity (3.1), docs/6333 §3. -/
  l5_contour : P0ContourIdentityStatement
  /-- L5 Andréief determinant identity, docs/6333 §3. -/
  l5_andreief : L5AndreiefStatement
  /-- L6 mass-zero energy positivity, docs/6333 §5. -/
  l6_mass_zero_energy : L6MassZeroEnergyPositivity
  /-- L7 circle smoothing identity, docs/6333 §4. -/
  l7_circle_average : L7CircleAverageStatement
  /-- L7 finite-configuration transfer, docs/6333 §4. -/
  l7_configuration : L7FiniteConfigurationTransfer
  /-- L8 P0 dual certificate output, docs/6333 §5, C-A. -/
  l8_p0_dual_output : ∀ F : P0Family, L8P0DualCertificateOutput F

end

end Li2Lean
