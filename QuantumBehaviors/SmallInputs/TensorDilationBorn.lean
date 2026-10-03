import QuantumBehaviors.SmallInputs.TensorDilationProduct
import QuantumBehaviors.EntangledTrace
import Mathlib.LinearAlgebra.TensorProduct.Matrix
import Mathlib.Analysis.InnerProductSpace.Trace

/-! A finite Hilbert tensor vector realization is exactly a finite density/POVM Born strategy. -/
namespace QuantumBehaviors.SmallInputs
open Matrix InnerProductSpace TensorProduct
open scoped BigOperators Kronecker ComplexOrder

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]
variable {J : Type*} [Fintype J] [DecidableEq J]

noncomputable def operatorMatrix (b : OrthonormalBasis J ℂ H) : (H →L[ℂ] H) →+* Matrix J J ℂ :=
  (LinearMap.toMatrixOrthonormal b).toRingHom.comp ContinuousLinearMap.toLinearMapRingHom

@[simp] lemma operatorMatrix_apply (b : OrthonormalBasis J ℂ H) (T : H →L[ℂ] H) :
    operatorMatrix b T=LinearMap.toMatrix b.toBasis b.toBasis T.toLinearMap := rfl

lemma operatorMatrix_projection (b : OrthonormalBasis J ℂ H) {P : H →L[ℂ] H}
    (hP : IsStarProjection P) : IsStarProjection (operatorMatrix b P) := by
  constructor
  · exact hP.isIdempotentElem.map (operatorMatrix b)
  · change (operatorMatrix b P).conjTranspose=operatorMatrix b P
    rw [operatorMatrix_apply,← LinearMap.toMatrix_adjoint,linear_adjoint_eq_of_selfadjoint hP.isSelfAdjoint]

noncomputable def vectorDensity (b : OrthonormalBasis J ℂ H) (ψ : H) : Matrix J J ℂ :=
  Matrix.vecMulVec (b.repr ψ) (star (b.repr ψ))

lemma vectorDensity_positive (b : OrthonormalBasis J ℂ H) (ψ : H) : (vectorDensity b ψ).PosSemidef :=
  Matrix.posSemidef_vecMulVec_self_star _

lemma vectorDensity_eq_matrix (b : OrthonormalBasis J ℂ H) (ψ : H) :
    vectorDensity b ψ=operatorMatrix b (rankOne ℂ ψ ψ) := by
  simpa only [operatorMatrix_apply,vectorDensity,OrthonormalBasis.coe_toBasis_repr_apply] using
    (InnerProductSpace.toMatrix_rankOne ψ ψ b.toBasis b).symm

lemma matrix_trace_eq_operator_trace (b : OrthonormalBasis J ℂ H) (T : H →L[ℂ] H) :
    (operatorMatrix b T).trace=LinearMap.trace ℂ H T.toLinearMap :=
  (LinearMap.trace_eq_matrix_trace ℂ b.toBasis T.toLinearMap).symm

lemma vectorDensity_expectation (b : OrthonormalBasis J ℂ H) (ψ : H) (T : H →L[ℂ] H) :
    (vectorDensity b ψ*operatorMatrix b T).trace=inner ℂ ψ (T ψ) := by
  rw [Matrix.trace_mul_comm,vectorDensity_eq_matrix,← map_mul]
  have hm : T*rankOne ℂ ψ ψ=rankOne ℂ (T ψ) ψ := comp_rankOne ψ ψ T
  rw [hm,matrix_trace_eq_operator_trace]
  exact InnerProductSpace.trace_rankOne _ _

lemma vectorDensity_trace (b : OrthonormalBasis J ℂ H) (ψ : H) (hψ : ‖ψ‖=1) :
    (vectorDensity b ψ).trace=1 := by
  have h := vectorDensity_expectation b ψ (1 : H →L[ℂ] H)
  simpa [hψ,inner_self_eq_norm_sq_to_K] using h

lemma operatorMatrix_tensor (b : OrthonormalBasis J ℂ H) (A B : H →L[ℂ] H) :
    operatorMatrix (b.tensorProduct b) (tensorLeft A*tensorRight B)=
      operatorMatrix b A ⊗ₖ operatorMatrix b B := by
  have hmap : (tensorLeft A*tensorRight B).toLinearMap=TensorProduct.map A.toLinearMap B.toLinearMap := by
    apply TensorProduct.ext'
    intro x y
    rfl
  rw [operatorMatrix_apply,hmap,OrthonormalBasis.toBasis_tensorProduct]
  exact TensorProduct.toMatrix_map b.toBasis b.toBasis b.toBasis b.toBasis _ _

/-- Exact natural local dimensions are obtained from orthonormal coordinates, without dilation. -/
theorem tensor_vector_to_finite_strategy {nA nB mA mB : ℕ}
    (A : Fin nA → Fin mA → H →L[ℂ] H) (B : Fin nB → Fin mB → H →L[ℂ] H)
    (hA : ∀ i a, IsStarProjection (A i a)) (hB : ∀ j b, IsStarProjection (B j b))
    (hAs : ∀ i, ∑ a, A i a=1) (hBs : ∀ j, ∑ b, B j b=1)
    (ψ : H ⊗[ℂ] H) (hψ : ‖ψ‖=1) (p : Scenarios.Behavior nA nB mA mB)
    (hp : ∀ i j a b, (p (i,j,a,b) : ℂ)=inner ℂ ψ ((tensorLeft (A i a)*tensorRight (B j b)) ψ)) :
    ∃ t : Scenarios.FiniteStrategy nA nB mA mB (Module.finrank ℂ H) (Module.finrank ℂ H), t.realizes p := by
  let b := stdOrthonormalBasis ℂ H
  let ρ := vectorDensity (b.tensorProduct b) ψ
  let t : Scenarios.FiniteStrategy nA nB mA mB (Module.finrank ℂ H) (Module.finrank ℂ H) := {
    density := ρ
    density_pos := vectorDensity_positive _ _
    density_trace := vectorDensity_trace _ _ hψ
    alice := fun i a => operatorMatrix b (A i a)
    bob := fun j c => operatorMatrix b (B j c)
    alice_pos := fun i a => projection_positive (operatorMatrix_projection b (hA i a)).isSelfAdjoint.star_eq
      (operatorMatrix_projection b (hA i a)).isIdempotentElem.eq
    alice_sum := fun i => by rw [← map_sum,hAs,map_one]
    bob_pos := fun j c => projection_positive (operatorMatrix_projection b (hB j c)).isSelfAdjoint.star_eq
      (operatorMatrix_projection b (hB j c)).isIdempotentElem.eq
    bob_sum := fun j => by rw [← map_sum,hBs,map_one] }
  refine ⟨t,?_⟩
  intro i j a c
  change (p (i,j,a,c) : ℂ)=(ρ*(operatorMatrix b (A i a) ⊗ₖ operatorMatrix b (B j c))).trace
  rw [← operatorMatrix_tensor]
  exact (hp i j a c).trans (vectorDensity_expectation (b.tensorProduct b) ψ _).symm

/-- The finite faithful cyclic strategy has a genuine tensor-product matrix realization. -/
theorem finite_cyclic_to_finite_strategy {n : ℕ} (s : Scenarios.CommutingStrategy n n 2 2 H)
    (heval : Function.Bijective (algebraEvaluation (aliceAlgebra s) s.state))
    {p : Scenarios.Behavior n n 2 2} (hp : s.realizes p) :
    ∃ t : Scenarios.FiniteStrategy n n 2 2 (Module.finrank ℂ H) (Module.finrank ℂ H), t.realizes p := by
  obtain ⟨ψ,hψ,hprob⟩ := finite_cyclic_tensor_vector s heval
  apply tensor_vector_to_finite_strategy s.alice s.bob s.alice_projection s.bob_projection
    s.alice_sum s.bob_sum ψ hψ p
  intro i j a b
  exact (hp i j a b).trans (hprob i j a b).symm

end QuantumBehaviors.SmallInputs
