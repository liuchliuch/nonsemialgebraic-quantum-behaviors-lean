import QuantumBehaviors.Dimension.SharedLower
import QuantumBehaviors.Dimension.BornBehavior
import QuantumBehaviors.Dimension.UniformMeasure

namespace QuantumBehaviors.Dimension
open MeasureTheory Filter
open scoped BigOperators

/-- Uniform finite randomization is a special case of unrestricted probability-space mixtures. -/
theorem shared_of_uniform_mixture {J : Type} [Fintype J] [Nonempty J] {dA dB : ℕ}
    (r : J → Behavior) (p : Behavior) (hr : ∀ j, BoundedFiniteBehavior dA dB (r j))
    (hp : ∀ x, (Fintype.card J : ℝ)⁻¹ * ∑ j, r j x = p x) : SharedBoundedBehavior dA dB p := by
  letI : MeasurableSpace J := ⊤
  letI : MeasurableSingletonClass J := ⟨fun _ => trivial⟩
  refine ⟨J,inferInstance,uniformMeasure J,inferInstance,r,?_⟩
  constructor
  · intro x
    exact Integrable.of_finite
  · intro x
    rw [integral_uniformMeasure]
    exact hp x
  · exact Eventually.of_forall hr

theorem bounded_implies_shared {dA dB : ℕ} {p : Behavior} (hp : BoundedFiniteBehavior dA dB p) :
    SharedBoundedBehavior dA dB p := by
  apply shared_of_uniform_mixture (fun _ : Unit => p) p (fun _ => hp)
  intro x
  simp

/-- The paper's random-permutation realization uses exactly m quantum dimensions per party. -/
theorem curve_shared_upper_bound {m : ℕ} (hm : 3 ≤ m) : SharedBoundedBehavior m m (curve (alpha m)) := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨R,hRself,hR,hRsum⟩ := FiniteConstruction.exists_four_real_projections m hm
  let f : Matrix (Fin m) (Fin m) ℝ →ₐ[ℝ] Matrix (Fin m) (Fin m) ℂ := (Algebra.ofId ℝ ℂ).mapMatrix
  let P : Input → Matrix (Fin m) (Fin m) ℂ := fun i => f (R i)
  have hself : ∀ i, (P i).conjTranspose = P i := by
    intro i
    change ((R i).map (algebraMap ℝ ℂ)).conjTranspose = (R i).map (algebraMap ℝ ℂ)
    ext r s
    have hs := congrFun (congrFun (hRself i) r) s
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply] using congrArg (fun x : ℝ => (x : ℂ)) hs
  have hP : ∀ i, P i * P i = P i := by intro i; dsimp [P]; rw [← map_mul, hR i]
  have hsum : (∑ i, P i) = (alpha m : ℂ) • 1 := by
    dsimp [P]
    rw [← map_sum,hRsum,map_smul,map_one]
  apply shared_of_uniform_mixture (fun π => (permutationStrategy P hself hP π).behavior)
    (curve (alpha m))
  · intro π
    exact ⟨m,m,le_rfl,le_rfl,permutationStrategy P hself hP π,FiniteStrategy.realizes_behavior _⟩
  · intro x
    simpa only [card_labelPermutation, Nat.cast_ofNat] using permutationStrategy_average P hself hP hsum x

end QuantumBehaviors.Dimension
