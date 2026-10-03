import QuantumBehaviors.Definitions

/-! General finite Bell scenarios. No proof of the threshold or inheritance is imported. -/
namespace QuantumBehaviors.Scenarios
open scoped BigOperators Kronecker ComplexOrder

abbrev Coordinate (nA nB mA mB : ℕ) := Fin nA × Fin nB × Fin mA × Fin mB
abbrev Behavior (nA nB mA mB : ℕ) := Coordinate nA nB mA mB → ℝ

structure FiniteStrategy (nA nB mA mB dA dB : ℕ) where
  density : Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ
  density_pos : density.PosSemidef
  density_trace : density.trace = 1
  alice : Fin nA → Fin mA → Matrix (Fin dA) (Fin dA) ℂ
  bob : Fin nB → Fin mB → Matrix (Fin dB) (Fin dB) ℂ
  alice_pos : ∀ i a, (alice i a).PosSemidef
  alice_sum : ∀ i, ∑ a, alice i a = 1
  bob_pos : ∀ j b, (bob j b).PosSemidef
  bob_sum : ∀ j, ∑ b, bob j b = 1

noncomputable def FiniteStrategy.realizes {nA nB mA mB dA dB : ℕ}
    (s : FiniteStrategy nA nB mA mB dA dB) (p : Behavior nA nB mA mB) : Prop :=
  ∀ i j a b, (p (i, j, a, b) : ℂ) = (s.density * (s.alice i a ⊗ₖ s.bob j b)).trace

def Cq (nA nB mA mB : ℕ) : Set (Behavior nA nB mA mB) :=
  {p | ∃ dA dB, ∃ s : FiniteStrategy nA nB mA mB dA dB, s.realizes p}

def Cqa (nA nB mA mB : ℕ) : Set (Behavior nA nB mA mB) := closure (Cq nA nB mA mB)

structure CommutingStrategy (nA nB mA mB : ℕ) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  state : H
  state_norm : ‖state‖ = 1
  alice : Fin nA → Fin mA → H →L[ℂ] H
  bob : Fin nB → Fin mB → H →L[ℂ] H
  alice_projection : ∀ i a, IsStarProjection (alice i a)
  alice_sum : ∀ i, ∑ a, alice i a = 1
  bob_projection : ∀ j b, IsStarProjection (bob j b)
  bob_sum : ∀ j, ∑ b, bob j b = 1
  cross_commute : ∀ i j a b, Commute (alice i a) (bob j b)

noncomputable def CommutingStrategy.realizes {nA nB mA mB : ℕ} {H : Type*}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : CommutingStrategy nA nB mA mB H) (p : Behavior nA nB mA mB) : Prop :=
  ∀ i j a b, (p (i, j, a, b) : ℂ) = inner ℂ s.state ((s.alice i a * s.bob j b) s.state)

def Cqc (nA nB mA mB : ℕ) : Set (Behavior nA nB mA mB) :=
  {p | ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H),
    ∃ s : CommutingStrategy nA nB mA mB H, s.realizes p}

def quantumSet (nA nB mA mB : ℕ) : Model → Set (Behavior nA nB mA mB)
  | .q => Cq nA nB mA mB
  | .qa => Cqa nA nB mA mB
  | .qc => Cqc nA nB mA mB

def Synchronous {n : ℕ} (p : Behavior n n 2 2) : Prop :=
  ∀ i a b, a ≠ b → p (i, i, a, b) = 0

def synchronousSet (n : ℕ) (t : Model) : Set (Behavior n n 2 2) :=
  {p | p ∈ quantumSet n n 2 2 t ∧ Synchronous p}

end QuantumBehaviors.Scenarios
