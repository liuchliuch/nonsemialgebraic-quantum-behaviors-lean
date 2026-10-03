import QuantumBehaviors.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Kronecker
import Mathlib.Topology.Instances.RealVectorSpace

/-!
# The three quantum models

`FiniteStrategy` uses arbitrary finite local dimensions, density matrices and binary POVMs,
exactly as equation (1)/(S1). `Cqa` is its Euclidean closure, not an alternative tensor model.
`CommutingStrategy` uses bounded selfadjoint idempotents and a unit vector on a complete complex
inner product space. Output superscripts are encoded by `effect`, with false the complement.
-/

namespace QuantumBehaviors

open scoped Kronecker ComplexOrder

theorem cq_subset_cqa : Cq ⊆ Cqa := subset_closure

@[simp] theorem cqa_isClosed : IsClosed Cqa := isClosed_closure

end QuantumBehaviors
