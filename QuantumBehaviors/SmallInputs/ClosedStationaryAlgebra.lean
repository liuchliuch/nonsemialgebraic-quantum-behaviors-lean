import Mathlib.Analysis.Complex.Basic
import QuantumBehaviors.SmallInputs.FiniteStationaryAlgebra
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Topology.Algebra.StarSubalgebra
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! The algebraic twelve-vector bound also bounds the generated closed star algebra. -/

namespace QuantumBehaviors.SmallInputs

variable {R : Type*} [NormedRing R] [NormedAlgebra ℂ R] [StarRing R]
  [StarModule ℂ R] [ContinuousStar R]

lemma star_triple_eq {A B C : R} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (hC : IsSelfAdjoint C) : star ({A, B, C} : Set R) = ({A, B, C} : Set R) := by
  simp only [Set.insert_eq, Set.union_star, Set.star_singleton, hA.star_eq, hB.star_eq, hC.star_eq]

/-- Topological closure adds no operators to the stationary three-projection algebra. -/
theorem russell_closed_star_algebra {a b : ℂ} {A B C : R}
    (ha : a ≠ 0) (hb : b ≠ 0)
    (hA : IsStarProjection A) (hB : IsStarProjection B) (hC : IsStarProjection C)
    (h₁ : Commute A (a • B + b • C)) (h₂ : Commute B (a • A + C)) :
    FiniteDimensional ℂ (StarAlgebra.adjoin ℂ ({A, B, C} : Set R)) ∧
      Module.finrank ℂ (StarAlgebra.adjoin ℂ ({A, B, C} : Set R)) ≤ 12 ∧
      (StarAlgebra.adjoin ℂ ({A, B, C} : Set R)).topologicalClosure =
        StarAlgebra.adjoin ℂ ({A, B, C} : Set R) := by
  have he : (StarAlgebra.adjoin ℂ ({A, B, C} : Set R)).toSubalgebra =
      Algebra.adjoin ℂ ({A, B, C} : Set R) := by
    rw [StarAlgebra.adjoin_toSubalgebra,
      star_triple_eq hA.isSelfAdjoint hB.isSelfAdjoint hC.isSelfAdjoint, Set.union_self]
  obtain ⟨hf, hd⟩ := russell_adjoin_finiteDimensional ha hb
    hA.isIdempotentElem hB.isIdempotentElem hC.isIdempotentElem h₁ h₂
  rw [← he] at hf hd
  letI : FiniteDimensional ℂ (StarAlgebra.adjoin ℂ ({A, B, C} : Set R)) := hf
  refine ⟨hf, hd, ?_⟩
  apply SetLike.coe_injective
  exact ((StarAlgebra.adjoin ℂ ({A, B, C} : Set R)).toSubmodule.closed_of_finiteDimensional).closure_eq

end QuantumBehaviors.SmallInputs
