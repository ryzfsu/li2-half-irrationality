/-
Copyright (c) 2026 Ruiyi Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Ruiyi Zhang (ryzfsu@gmail.com, https://github.com/ryzfsu)
-/
import Li2Lean.P0.Dual

namespace Li2Lean

/-!
Algebraic core of the v10 P0 dual argument, `sec-dual.tex` and docs/6333 §5.
The model keeps the signed-measure positivity input explicit; a concrete
finite-energy measure model must still supply it from L6.
-/

/--
An abstract real measure space with the mass and symmetric logarithmic
interaction used in docs/6333 §3 and §5. `zeroMass_interaction_nonneg` is the
mass-zero energy assertion (5.3), not an axiom of the formalization: it is a
field that the concrete L6 construction must prove.
-/
structure P0DualEnergyModel (V : Type) [AddCommGroup V] [Module ℝ V] where
  mass : V →ₗ[ℝ] ℝ
  interaction : V →ₗ[ℝ] V →ₗ[ℝ] ℝ
  interaction_symmetric : ∀ x y, interaction x y = interaction y x
  zeroMass_interaction_nonneg : ∀ σ, mass σ = 0 → 0 ≤ interaction σ σ

/-- Contour-side first variation from v10 (5.1), with `I=-log`. -/
def p0DualEtaPotential {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (A : V →ₗ[ℝ] ℝ) (eta0 mu0 eta : V) : ℝ :=
  A eta + 2 * M.interaction eta0 eta + M.interaction mu0 eta

/-- Frequency-side first variation from v10 (5.1), after reflection. -/
def p0DualMuPotential {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (B : V →ₗ[ℝ] ℝ) (eta0 mu0 mu : V) : ℝ :=
  B mu + 2 * M.interaction mu0 mu + M.interaction eta0 mu

/-- The positive-log reference constant `Q_log` in v10 (5.2). -/
def p0DualReferenceQLog {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (eta0 mu0 : V) : ℝ :=
  -(M.interaction eta0 eta0 + M.interaction mu0 mu0 +
    M.interaction eta0 mu0)

/-- Quadratic remainder after subtracting the reference pair. -/
def p0DualQuadraticRemainder {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (eta eta0 mu mu0 : V) : ℝ :=
  M.interaction (eta - eta0) (eta - eta0) +
    M.interaction (mu - mu0) (mu - mu0) +
    M.interaction (eta - eta0) (mu - mu0)

/-- The paper's energy functional before taking its infimum. -/
def p0DualEnergy {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (C : ℝ) (A B : V →ₗ[ℝ] ℝ)
    (eta mu : V) : ℝ :=
  C + A eta + B mu + M.interaction eta eta + M.interaction mu mu +
    M.interaction eta mu

/-- Bilinear expansion of the signed variations. -/
theorem p0DualInteraction_sub_sub {V : Type} [AddCommGroup V]
    [Module ℝ V] (I : V →ₗ[ℝ] V →ₗ[ℝ] ℝ) (x x0 y y0 : V) :
    I (x - x0) (y - y0) =
      I x y - I x y0 - I x0 y + I x0 y0 := by
  simp only [map_sub, LinearMap.sub_apply]
  ring

/--
Exact reference/first-variation/quadratic decomposition of the energy. This
is the algebraic expansion used in the proof of `lem:dual-lower`.
-/
theorem p0DualEnergy_decomposition {V : Type} [AddCommGroup V]
    [Module ℝ V] (M : P0DualEnergyModel V) (C : ℝ)
    (A B : V →ₗ[ℝ] ℝ) (eta eta0 mu mu0 : V) :
    p0DualEnergy M C A B eta mu =
      C + p0DualReferenceQLog M eta0 mu0 +
        p0DualEtaPotential M A eta0 mu0 eta +
        p0DualMuPotential M B eta0 mu0 mu +
        p0DualQuadraticRemainder M eta eta0 mu mu0 := by
  have hEtaEta := p0DualInteraction_sub_sub M.interaction eta eta0 eta eta0
  have hMuMu := p0DualInteraction_sub_sub M.interaction mu mu0 mu mu0
  have hEtaMu := p0DualInteraction_sub_sub M.interaction eta eta0 mu mu0
  simp only [p0DualEnergy, p0DualReferenceQLog, p0DualEtaPotential,
    p0DualMuPotential, p0DualQuadraticRemainder]
  rw [hEtaEta, hMuMu, hEtaMu,
    M.interaction_symmetric eta eta0,
    M.interaction_symmetric mu mu0,
    M.interaction_symmetric mu0 eta]
  ring

/-- The polarization identity in (5.3). -/
theorem p0DualQuadraticRemainder_eq_half_sum {V : Type}
    [AddCommGroup V] [Module ℝ V] (M : P0DualEnergyModel V)
    (eta eta0 mu mu0 : V) :
    p0DualQuadraticRemainder M eta eta0 mu mu0 =
      (1 / 2 : ℝ) * M.interaction (eta - eta0) (eta - eta0) +
      (1 / 2 : ℝ) * M.interaction (mu - mu0) (mu - mu0) +
      (1 / 2 : ℝ) * M.interaction
        ((eta - eta0) + (mu - mu0)) ((eta - eta0) + (mu - mu0)) := by
  have hsum : M.interaction
      ((eta - eta0) + (mu - mu0)) ((eta - eta0) + (mu - mu0)) =
      M.interaction (eta - eta0) (eta - eta0) +
      M.interaction (eta - eta0) (mu - mu0) +
      M.interaction (mu - mu0) (eta - eta0) +
      M.interaction (mu - mu0) (mu - mu0) := by
    simp only [map_add, LinearMap.add_apply]
    ring
  rw [p0DualQuadraticRemainder, hsum,
    M.interaction_symmetric (mu - mu0) (eta - eta0)]
  ring

/--
Zero total mass of each variation makes the (5.3) quadratic remainder
nonnegative, using the explicit L6 positivity field of the model.
-/
theorem p0DualQuadraticRemainder_nonneg {V : Type}
    [AddCommGroup V] [Module ℝ V] (M : P0DualEnergyModel V)
    {eta eta0 mu mu0 : V}
    (hEtaMass : M.mass eta = M.mass eta0)
    (hMuMass : M.mass mu = M.mass mu0) :
    0 ≤ p0DualQuadraticRemainder M eta eta0 mu mu0 := by
  have hEtaZero : M.mass (eta - eta0) = 0 := by
    simp [map_sub, hEtaMass]
  have hMuZero : M.mass (mu - mu0) = 0 := by
    simp [map_sub, hMuMass]
  have hSumZero : M.mass ((eta - eta0) + (mu - mu0)) = 0 := by
    simp [map_add, hEtaZero, hMuZero]
  rw [p0DualQuadraticRemainder_eq_half_sum]
  have hEta := M.zeroMass_interaction_nonneg (eta - eta0) hEtaZero
  have hMu := M.zeroMass_interaction_nonneg (mu - mu0) hMuZero
  have hSum := M.zeroMass_interaction_nonneg
    ((eta - eta0) + (mu - mu0)) hSumZero
  positivity

/--
Pointwise v10 dual lower bound for each competitor, assuming only the two
first-variation cap estimates after the L6 energy positivity has been proved.
Its infimum corollary is the target `lem:dual-lower` / (5.2); the
measure-specific infimum assembly remains a separate obligation.
-/
theorem p0DualEnergy_ge_certificate {V : Type} [AddCommGroup V]
    [Module ℝ V] (M : P0DualEnergyModel V) (C hEta hMu P T : ℝ)
    (A B : V →ₗ[ℝ] ℝ) {eta eta0 mu mu0 : V}
    (hEtaMass : M.mass eta = M.mass eta0)
    (hMuMass : M.mass mu = M.mass mu0)
    (hEtaCap : hEta - P ≤ p0DualEtaPotential M A eta0 mu0 eta)
    (hMuCap : hMu - T ≤ p0DualMuPotential M B eta0 mu0 mu) :
    C + p0DualReferenceQLog M eta0 mu0 + hEta + hMu - P - T ≤
      p0DualEnergy M C A B eta mu := by
  rw [p0DualEnergy_decomposition M C A B eta eta0 mu mu0]
  have hRem := p0DualQuadraticRemainder_nonneg M hEtaMass hMuMass
  unfold p0DualEtaPotential p0DualMuPotential at *
  linarith

/-- Energy values attained by a specified set of competitor pairs. -/
def p0DualEnergyValues {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (C : ℝ) (A B : V →ₗ[ℝ] ℝ)
    (competitors : Set (V × V)) : Set ℝ :=
  {e | ∃ p ∈ competitors, e = p0DualEnergy M C A B p.1 p.2}

/-- Abstract variational infimum of the P0 dual model over the given pairs. -/
noncomputable def p0DualAlpha {V : Type} [AddCommGroup V] [Module ℝ V]
    (M : P0DualEnergyModel V) (C : ℝ) (A B : V →ₗ[ℝ] ℝ)
    (competitors : Set (V × V)) : ℝ :=
  sInf (p0DualEnergyValues M C A B competitors)

/--
Infimum form of the pointwise dual lower bound. The caller supplies the exact
competitor set and proves nonemptiness, mass matching, and both cap estimates
for every member. Instantiating the set with the paper's admissible measures
remains separate from this variational order argument.
-/
theorem p0DualInfimum_ge_certificate {V : Type} [AddCommGroup V]
    [Module ℝ V] (M : P0DualEnergyModel V) (C hEta hMu P T : ℝ)
    (A B : V →ₗ[ℝ] ℝ) (competitors : Set (V × V))
    (eta0 mu0 : V)
    (hNonempty : competitors.Nonempty)
    (hEtaMass : ∀ p ∈ competitors, M.mass p.1 = M.mass eta0)
    (hMuMass : ∀ p ∈ competitors, M.mass p.2 = M.mass mu0)
    (hEtaCap : ∀ p ∈ competitors,
      hEta - P ≤ p0DualEtaPotential M A eta0 mu0 p.1)
    (hMuCap : ∀ p ∈ competitors,
      hMu - T ≤ p0DualMuPotential M B eta0 mu0 p.2) :
    C + p0DualReferenceQLog M eta0 mu0 + hEta + hMu - P - T ≤
      p0DualAlpha M C A B competitors := by
  rw [p0DualAlpha]
  apply le_csInf
  · rcases hNonempty with ⟨p, hp⟩
    exact ⟨p0DualEnergy M C A B p.1 p.2, p, hp, rfl⟩
  · intro e he
    rcases he with ⟨p, hp, rfl⟩
    exact p0DualEnergy_ge_certificate M C hEta hMu P T A B
      (eta := p.1) (eta0 := eta0) (mu := p.2) (mu0 := mu0)
      (hEtaMass p hp) (hMuMass p hp) (hEtaCap p hp) (hMuCap p hp)
/-! ### Extended-energy infimum, including infinite-energy competitors -/

/--
Order-theoretic lower-bound passage for the full extended-real infimum in
v10 `eq:contour-alpha`. The argument applies pointwise also when a competitor
has energy `+infinity`.
-/
theorem p0DualExtendedInfimum_ge {X : Type*} (E : X → WithTop ℝ)
    (b : ℝ) (hNonempty : Nonempty X)
    (h : ∀ x, (b : WithTop ℝ) ≤ E x) :
    (b : WithTop ℝ) ≤ sInf (Set.range E) := by
  apply le_csInf
  · rcases hNonempty with ⟨x⟩
    exact ⟨E x, x, rfl⟩
  · intro y hy
    rcases hy with ⟨x, rfl⟩
    exact h x

/--
If the paper's extended energy is its finite real value on a finite-energy
domain and `+infinity` outside, a bound on that domain passes to the full
`WithTop ℝ` infimum. This matches the convention in v10
`P0ExtendedEnergy` / `eq:contour-alpha`.
-/
theorem p0DualExtendedInfimum_ge_of_finiteCases {X : Type*}
    (E : X → WithTop ℝ) (finite : X → Prop) [DecidablePred finite]
    (value : X → ℝ) (b : ℝ)
    (hNonempty : Nonempty X)
    (hE : ∀ x, E x = if finite x then (value x : WithTop ℝ) else ⊤)
    (hBound : ∀ x, finite x → b ≤ value x) :
    (b : WithTop ℝ) ≤ sInf (Set.range E) := by
  classical
  apply p0DualExtendedInfimum_ge E b hNonempty
  intro x
  rw [hE x]
  by_cases hx : finite x
  · rw [if_pos hx]
    exact_mod_cast hBound x hx
  · rw [if_neg hx]
    exact le_top

end Li2Lean
