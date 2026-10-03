import QuantumBehaviors.Scenarios.FixedDimension

namespace QuantumBehaviors

lemma IsSemialgebraic.exists_finite {V J : Type*} [Fintype J] (C : J → Set (V → ℝ))
    (hC : ∀ j, IsSemialgebraic (C j)) : IsSemialgebraic {x | ∃ j, x ∈ C j} := by
  have h := (IsSemialgebraic.forall_finite (fun j => (C j)ᶜ) (fun j => (hC j).compl)).compl
  simpa only [Set.compl_setOf,Set.mem_compl_iff,not_forall,not_not] using h

namespace Scenarios

def BoundedDimensionSet (nA nB mA mB D : ℕ) : Set (Behavior nA nB mA mB) :=
  {p | ∃ dA dB, dA ≤ D ∧ dB ≤ D ∧ p ∈ FixedDimensionSet nA nB mA mB dA dB}

theorem bounded_dimension_semialgebraic (nA nB mA mB D : ℕ) :
    IsSemialgebraic (BoundedDimensionSet nA nB mA mB D) := by
  have h := IsSemialgebraic.exists_finite
    (fun a : Fin (D+1) => {p | ∃ b : Fin (D+1), p ∈ FixedDimensionSet nA nB mA mB a b})
    (fun a => IsSemialgebraic.exists_finite _ (fun b => fixed_dimension_semialgebraic nA nB mA mB a b))
  convert h using 1
  ext p
  constructor
  · rintro ⟨a,b,ha,hb,hp⟩
    exact ⟨⟨a,by omega⟩,⟨b,by omega⟩,hp⟩
  · rintro ⟨a,b,hp⟩
    exact ⟨a,b,by omega,by omega,hp⟩

end Scenarios
end QuantumBehaviors
