import QuantumBehaviors.Scenarios.FixedDimensionCompact
import QuantumBehaviors.Scenarios.BoundedDimension

namespace QuantumBehaviors.Scenarios
open Set

theorem bounded_dimension_compact (nA nB mA mB D : ℕ) :
    IsCompact (BoundedDimensionSet nA nB mA mB D) := by
  have h := isCompact_iUnion (fun a : Fin (D+1) => isCompact_iUnion
    (fun b : Fin (D+1) => fixed_dimension_compact nA nB mA mB a b))
  convert h using 1
  ext p
  simp only [Set.mem_iUnion,Set.mem_setOf_eq,BoundedDimensionSet]
  constructor
  · rintro ⟨a,b,ha,hb,hp⟩
    exact ⟨⟨a,by omega⟩,⟨b,by omega⟩,hp⟩
  · rintro ⟨a,b,hp⟩
    exact ⟨a,b,by omega,by omega,hp⟩

end QuantumBehaviors.Scenarios
