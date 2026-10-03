import QuantumBehaviors.NPA.Words

/-! Finite NPA moment certificates. Index k corresponds to standard order k+1. -/
namespace QuantumBehaviors.NPA
open scoped BigOperators ComplexOrder

noncomputable def bornValue (k : ℕ) (Γ : Matrix (BoundedWord (k+1)) (BoundedWord (k+1)) ℂ)
    (i j : Input) (a b : Bool) : ℂ :=
  let α := Γ (emptyIndex k) (letterIndex k (Sum.inl i))
  let β := Γ (emptyIndex k) (letterIndex k (Sum.inr j))
  let γ := Γ (letterIndex k (Sum.inl i)) (letterIndex k (Sum.inr j))
  if a then if b then γ else α-γ else if b then β-γ else 1-α-β+γ

/-- Standard order k+1 certificate, with redundant literal words and all generated relations.
Nonnegative probabilities are explicit at order1, as in the source's strengthened Q1 convention. -/
structure Certificate (k : ℕ) (p : Behavior) where
  gram : Matrix (BoundedWord (k+1)) (BoundedWord (k+1)) ℂ
  positive : gram.PosSemidef
  normalized : gram (emptyIndex k) (emptyIndex k)=1
  relations : ∀ u v r s, WordRel (u.val.reverse++v.val) (r.val.reverse++s.val) → gram u v=gram r s
  born : ∀ i j a b, (p (i,j,a,b) : ℂ)=bornValue k gram i j a b
  nonnegative : Nonnegative p

def level (k : ℕ) : Set Behavior := {p | Nonempty (Certificate k p)}

end QuantumBehaviors.NPA
