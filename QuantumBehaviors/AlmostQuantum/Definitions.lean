import QuantumBehaviors.Definitions

/-! State-commuting projection models and the finite event certificate. -/
namespace QuantumBehaviors.AlmostQuantum
open scoped BigOperators ComplexOrder

abbrev Event := Unit ⊕ Input ⊕ Input ⊕ (Input × Input)
def emptyEvent : Event := Sum.inl ()
def aliceEvent (i : Input) : Event := Sum.inr (Sum.inl i)
def bobEvent (j : Input) : Event := Sum.inr (Sum.inr (Sum.inl j))
def jointEvent (i j : Input) : Event := Sum.inr (Sum.inr (Sum.inr (i,j)))
def aliceRow (i : Input) : Option Input → Event
  | none => aliceEvent i
  | some j => jointEvent i j
def bobRow (j : Input) : Option Input → Event
  | none => bobEvent j
  | some i => jointEvent i j

structure Strategy (H : Type*) [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] where
  state : H
  state_norm : ‖state‖=1
  alice : Input → H →L[ℂ] H
  bob : Input → H →L[ℂ] H
  alice_projection : ∀ i, IsStarProjection (alice i)
  bob_projection : ∀ j, IsStarProjection (bob j)
  cross_on_state : ∀ i j, alice i (bob j state)=bob j (alice i state)

noncomputable def Strategy.realizes {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : Strategy H) (p : Behavior) : Prop :=
  ∀ i j a b, (p (i,j,a,b) : ℂ)=inner ℂ s.state ((effect (s.alice i) a*effect (s.bob j) b) s.state)

def behaviors : Set Behavior := {p | ∃ (H : Type) (_ : NormedAddCommGroup H)
  (_ : InnerProductSpace ℂ H) (_ : CompleteSpace H), ∃ s : Strategy H, s.realizes p}

noncomputable def bornValue (Γ : Matrix Event Event ℂ) (i j : Input) (a b : Bool) : ℂ :=
  if a then if b then Γ emptyEvent (jointEvent i j)
    else Γ emptyEvent (aliceEvent i)-Γ emptyEvent (jointEvent i j)
  else if b then Γ emptyEvent (bobEvent j)-Γ emptyEvent (jointEvent i j)
    else 1-Γ emptyEvent (aliceEvent i)-Γ emptyEvent (bobEvent j)+Γ emptyEvent (jointEvent i j)

/-- Finite event Gram equations; their equivalence with the operator model is proved below. -/
structure Certificate (p : Behavior) where
  gram : Matrix Event Event ℂ
  positive : gram.PosSemidef
  normalized : gram emptyEvent emptyEvent=1
  alice_empty : ∀ i t, gram (aliceRow i t) emptyEvent=gram (aliceRow i t) (aliceEvent i)
  alice_bob : ∀ i t j, gram (aliceRow i t) (bobEvent j)=gram (aliceRow i t) (jointEvent i j)
  bob_empty : ∀ j t, gram (bobRow j t) emptyEvent=gram (bobRow j t) (bobEvent j)
  bob_alice : ∀ j t i, gram (bobRow j t) (aliceEvent i)=gram (bobRow j t) (jointEvent i j)
  born : ∀ i j a b, (p (i,j,a,b) : ℂ)=bornValue gram i j a b

end QuantumBehaviors.AlmostQuantum
