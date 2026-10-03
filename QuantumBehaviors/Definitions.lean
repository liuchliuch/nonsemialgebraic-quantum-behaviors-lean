import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Instances.RealVectorSpace
import Mathlib.Analysis.Analytic.Basic
import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.Data.Sign.Basic
import Mathlib.Data.Fintype.Pi

/-!
# Mathematical specification: behaviors, models, and finite descriptions

These definitions are the review boundary for the paper and Comparator. They import
only Mathlib, never the project's theorem proofs. `true` denotes outcome 1.
The only lemmas here reduce the two cases of `effect` by reflexivity.
-/
namespace QuantumBehaviors
open scoped Kronecker ComplexOrder

abbrev Input := Fin 4
abbrev Output := Bool
abbrev Coordinate := Input × Input × Output × Output
abbrev Behavior := Coordinate → ℝ

noncomputable def curve (α : ℝ) : Behavior := fun ⟨i, j, a, b⟩ =>
  if i = j then
    if a then (if b then α / 4 else 0)
    else (if b then 0 else 1 - α / 4)
  else
    if a then (if b then α * (α - 1) / 12 else α * (4 - α) / 12)
    else (if b then α * (4 - α) / 12 else (3 - α) * (4 - α) / 12)

def Synchronous (p : Behavior) : Prop :=
  ∀ i, p (i, i, true, false) = 0 ∧ p (i, i, false, true) = 0

def Normalized (p : Behavior) : Prop :=
  ∀ i j, ∑ a : Bool, ∑ b : Bool, p (i, j, a, b) = 1

def Nonnegative (p : Behavior) : Prop := ∀ x, 0 ≤ p x

def Nonsignaling (p : Behavior) : Prop :=
  (∀ i j k a, (∑ b : Bool, p (i, j, a, b)) = ∑ b : Bool, p (i, k, a, b)) ∧
  (∀ i j k b, (∑ a : Bool, p (i, j, a, b)) = ∑ a : Bool, p (k, j, a, b))

noncomputable def witness (p : Behavior) (α : ℝ) : ℝ :=
  (∑ i : Input, ∑ j : Input, p (i, j, true, true)) -
    2 * α * (∑ i : Input, p (i, i, true, true)) + α ^ 2

noncomputable def alpha (m : ℕ) : ℝ := 2 - 2 / (m : ℝ)

def Allowed (α : ℝ) : Prop := ∃ m : ℕ, 3 ≤ m ∧ α = alpha m

noncomputable def correlator (p : Behavior) (i j : Input) : ℝ :=
  p (i, j, false, false) - p (i, j, false, true) -
    p (i, j, true, false) + p (i, j, true, true)

noncomputable def effect {A : Type*} [Sub A] [One A] (P : A) (a : Bool) : A :=
  if a then P else 1 - P

@[simp] theorem effect_true {A : Type*} [Sub A] [One A] (P : A) :
    effect P true = P := rfl

@[simp] theorem effect_false {A : Type*} [Sub A] [One A] (P : A) :
    effect P false = 1 - P := rfl

structure FiniteStrategy (dA dB : ℕ) where
  density : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ
  density_pos : density.PosSemidef
  density_trace : density.trace = 1
  alice : Input → Matrix (Fin dA) (Fin dA) ℂ
  bob : Input → Matrix (Fin dB) (Fin dB) ℂ
  alice_pos : ∀ i, (alice i).PosSemidef
  alice_complement_pos : ∀ i, (1 - alice i).PosSemidef
  bob_pos : ∀ j, (bob j).PosSemidef
  bob_complement_pos : ∀ j, (1 - bob j).PosSemidef

noncomputable def FiniteStrategy.realizes {dA dB : ℕ} (s : FiniteStrategy dA dB)
    (p : Behavior) : Prop := ∀ i j a b,
  (p (i, j, a, b) : ℂ) =
    (s.density * (effect (s.alice i) a ⊗ₖ effect (s.bob j) b)).trace

def Cq : Set Behavior := {p | ∃ dA dB : ℕ, ∃ s : FiniteStrategy dA dB, s.realizes p}

def Cqa : Set Behavior := closure Cq

structure CommutingStrategy (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  state : H
  state_norm : ‖state‖ = 1
  alice : Input → H →L[ℂ] H
  bob : Input → H →L[ℂ] H
  alice_projection : ∀ i, IsStarProjection (alice i)
  bob_projection : ∀ j, IsStarProjection (bob j)
  cross_commute : ∀ i j, Commute (alice i) (bob j)

noncomputable def CommutingStrategy.realizes {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : CommutingStrategy H)
    (p : Behavior) : Prop := ∀ i j a b,
  (p (i, j, a, b) : ℂ) =
    inner ℂ s.state ((effect (s.alice i) a * effect (s.bob j) b) s.state)

/-- The commuting model on an arbitrary complex Hilbert space in the fixed ambient universe. -/
def Cqc : Set Behavior := {p | ∃ (H : Type) (_ : NormedAddCommGroup H)
  (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H), ∃ s : CommutingStrategy H, s.realizes p}

abbrev Response := Input → Bool

noncomputable def deterministic (alice bob : Response) : Behavior :=
  fun ⟨i, j, a, b⟩ => if alice i = a ∧ bob j = b then 1 else 0

/-- A finite convex combination of deterministic local response pairs. -/
def BellLocal (p : Behavior) : Prop :=
  ∃ (n : ℕ) (w : Fin n → ℝ) (A B : Fin n → Response),
    (∀ k, 0 ≤ w k) ∧ (∑ k, w k) = 1 ∧
    ∀ x, p x = ∑ k, w k * deterministic (A k) (B k) x

inductive SignFormula (ι : Type*) where
  | truth : Bool → SignFormula ι
  | atom : ι → SignType → SignFormula ι
  | conj : SignFormula ι → SignFormula ι → SignFormula ι
  | disj : SignFormula ι → SignFormula ι → SignFormula ι
  | neg : SignFormula ι → SignFormula ι

def SignFormula.eval {ι : Type*} (v : ι → SignType) : SignFormula ι → Bool
  | .truth b => b
  | .atom i s => decide (v i = s)
  | .conj f g => f.eval v && g.eval v
  | .disj f g => f.eval v || g.eval v
  | .neg f => !(f.eval v)

/-- Arbitrary finite Boolean sign formulas, with no restriction on the real coefficients. -/
def IsSemialgebraic {ι : Type*} (C : Set (ι → ℝ)) : Prop :=
  ∃ (n : ℕ) (f : Fin n → MvPolynomial ι ℝ) (φ : SignFormula (Fin n)),
    ∀ x, x ∈ C ↔ φ.eval (fun i => SignType.sign (MvPolynomial.eval x (f i))) = true

/-- The exact local analytic-description notion in Proposition S9. -/
def IsSemianalyticAt (C : Set Behavior) (p : Behavior) : Prop :=
  ∃ (U : Set Behavior) (n : ℕ) (f : Fin n → Behavior → ℝ) (φ : SignFormula (Fin n)),
    IsOpen U ∧ p ∈ U ∧ (∀ i, AnalyticOnNhd ℝ (f i) U) ∧
    ∀ x ∈ U, x ∈ C ↔ φ.eval (fun i => SignType.sign (f i x)) = true

inductive Model where
  | q | qa | qc
  deriving DecidableEq

def quantumSet : Model → Set Behavior
  | .q => Cq
  | .qa => Cqa
  | .qc => Cqc

end QuantumBehaviors
