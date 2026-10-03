import QuantumBehaviors.LiftDefinitions
import QuantumBehaviors.Main
import QuantumBehaviors.Projection.TarskiSeidenberg

/-! The finite-semialgebraic-lift obstruction, using the fully proved projection theorem. -/
namespace QuantumBehaviors

/-- Corollary S11: no intermediate quantum set is any finite semialgebraic projection. -/
theorem intermediate_no_finite_semialgebraic_lift {C : Set Behavior}
    (hq : Cq ⊆ C) (hqc : C ⊆ Cqc) : ¬ HasFiniteSemialgebraicLift C := by
  rintro ⟨r, Z, hZ, hC⟩
  have hproj := hZ.project
  have heq : C = {p | ∃ z : Fin r → ℝ, Sum.elim p z ∈ Z} := Set.ext hC
  rw [← heq] at hproj
  exact intermediate_not_semialgebraic hq hqc hproj

theorem quantum_no_finite_semialgebraic_lift (t : Model) :
    ¬ HasFiniteSemialgebraicLift (quantumSet t) :=
  intermediate_no_finite_semialgebraic_lift (cq_subset_quantumSet t) (quantumSet_subset_cqc t)

end QuantumBehaviors
