import QuantumBehaviors.Definitions
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-! Cross-commuting binary positive contractions, before dilation. -/
namespace QuantumBehaviors.POVM
open scoped ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

structure BinaryStrategy (IA IB : Type*) (H : Type*) [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] where
  state : H
  state_norm : ‖state‖=1
  alice : IA → H →L[ℂ] H
  bob : IB → H →L[ℂ] H
  alice_nonneg : ∀ i, 0 ≤ alice i
  alice_complement_nonneg : ∀ i, 0 ≤ 1-alice i
  bob_nonneg : ∀ j, 0 ≤ bob j
  bob_complement_nonneg : ∀ j, 0 ≤ 1-bob j
  cross_commute : ∀ i j, Commute (alice i) (bob j)

noncomputable def BinaryStrategy.realizes {IA IB : Type*} (s : BinaryStrategy IA IB H)
    (p : IA × IB × Bool × Bool → ℝ) : Prop := ∀ i j a b,
    (p (i,j,a,b) : ℂ)=inner ℂ s.state ((effect (s.alice i) a*effect (s.bob j) b) s.state)

def CqcPOVM : Set Behavior := {p | ∃ (H : Type) (_ : NormedAddCommGroup H)
  (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H), ∃ s : BinaryStrategy Input Input H, s.realizes p}

end QuantumBehaviors.POVM
