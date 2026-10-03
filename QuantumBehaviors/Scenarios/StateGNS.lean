import QuantumBehaviors.Scenarios.Basic
import QuantumBehaviors.StateGNS

/-! Density/projection vector representations for arbitrary finite input and output counts. -/
namespace QuantumBehaviors.Scenarios

open Matrix ContinuousLinearMap
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator
set_option synthInstance.maxHeartbeats 200000

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]
noncomputable local instance : CStarAlgebra (Matrix ι ι ℂ) where

variable {nA nB mA mB : ℕ}

theorem cqc_of_density (p : Behavior nA nB mA mB) (ρ : Matrix ι ι ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (A : Fin nA → Fin mA → Matrix ι ι ℂ) (B : Fin nB → Fin mB → Matrix ι ι ℂ)
    (hA : ∀ i a, IsStarProjection (A i a)) (hB : ∀ j b, IsStarProjection (B j b))
    (hAsum : ∀ i, ∑ a, A i a = 1) (hBsum : ∀ j, ∑ b, B j b = 1)
    (hAB : ∀ i j a b, Commute (A i a) (B j b))
    (hreal : ∀ i j a b, (p (i, j, a, b) : ℂ) = (ρ * (A i a * B j b)).trace) :
    p ∈ Cqc nA nB mA mB := by
  let f := densityFunctional ρ hρ
  let π := f.gnsStarAlgHom
  let s : CommutingStrategy nA nB mA mB f.GNS := {
    state := densityGNSState ρ hρ
    state_norm := densityGNSState_norm ρ hρ htr
    alice := fun i a => π (A i a)
    bob := fun j b => π (B j b)
    alice_projection := fun i a => (hA i a).map π
    bob_projection := fun j b => (hB j b).map π
    alice_sum := fun i => by rw [← map_sum, hAsum, map_one]
    bob_sum := fun j => by rw [← map_sum, hBsum, map_one]
    cross_commute := fun i j a b => (hAB i j a b).map π }
  refine ⟨f.GNS, inferInstance, inferInstance, inferInstance, s, ?_⟩
  intro i j a b
  change (p (i, j, a, b) : ℂ) = inner ℂ (densityGNSState ρ hρ)
    ((π (A i a) * π (B j b)) (densityGNSState ρ hρ))
  rw [← map_mul, densityGNSState_expectation]
  exact hreal i j a b

end QuantumBehaviors.Scenarios
