import QuantumBehaviors.SmallInputs.TensorDilationNormalization
import QuantumBehaviors.SmallInputs.FiniteCyclicStrategy
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! Multiplication transported through a faithful cyclic evaluation map yields a tensor dilation. -/
namespace QuantumBehaviors.SmallInputs
open TensorProduct
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
  [FiniteDimensional ℂ H]

noncomputable def tensorLeft (A : H →L[ℂ] H) : H ⊗[ℂ] H →L[ℂ] H ⊗[ℂ] H :=
  (TensorProduct.map A.toLinearMap (LinearMap.id : H →ₗ[ℂ] H)).toContinuousLinearMap
noncomputable def tensorRight (B : H →L[ℂ] H) : H ⊗[ℂ] H →L[ℂ] H ⊗[ℂ] H :=
  (TensorProduct.map (LinearMap.id : H →ₗ[ℂ] H) B.toLinearMap).toContinuousLinearMap

@[simp] theorem tensorLeft_tmul (A : H →L[ℂ] H) (x y : H) : tensorLeft A (x ⊗ₜ[ℂ] y)=A x ⊗ₜ[ℂ] y := rfl
@[simp] theorem tensorRight_tmul (B : H →L[ℂ] H) (x y : H) : tensorRight B (x ⊗ₜ[ℂ] y)=x ⊗ₜ[ℂ] B y := rfl

lemma linear_adjoint_eq_of_selfadjoint {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) :
    LinearMap.adjoint A.toLinearMap=A.toLinearMap := by
  apply LinearMap.ext
  intro x
  exact congrArg (fun T : H →L[ℂ] H => T x) hA.star_eq

lemma tensorLeft_selfadjoint {A : H →L[ℂ] H} (hA : IsSelfAdjoint A) : IsSelfAdjoint (tensorLeft A) := by
  change ContinuousLinearMap.adjoint (tensorLeft A)=tensorLeft A
  rw [tensorLeft,← LinearMap.adjoint_toContinuousLinearMap,TensorProduct.adjoint_map,
    linear_adjoint_eq_of_selfadjoint hA]
  simp

lemma tensorRight_selfadjoint {B : H →L[ℂ] H} (hB : IsSelfAdjoint B) : IsSelfAdjoint (tensorRight B) := by
  change ContinuousLinearMap.adjoint (tensorRight B)=tensorRight B
  rw [tensorRight,← LinearMap.adjoint_toContinuousLinearMap,TensorProduct.adjoint_map,
    linear_adjoint_eq_of_selfadjoint hB]
  simp

variable {n : ℕ} (s : Scenarios.CommutingStrategy n n 2 2 H)
  (heval : Function.Bijective (algebraEvaluation (aliceAlgebra s) s.state))

noncomputable def evaluationEquiv : aliceAlgebra s ≃ₗ[ℂ] H :=
  LinearEquiv.ofBijective _ heval

@[simp] theorem evaluationEquiv_apply (X : aliceAlgebra s) : evaluationEquiv s heval X=X.1 s.state := rfl

noncomputable def cyclicProductBilinear : H →ₗ[ℂ] H →ₗ[ℂ] H where
  toFun x := ((evaluationEquiv s heval).symm x).1.toLinearMap
  map_add' x y := by
    apply LinearMap.ext
    intro z
    change (((evaluationEquiv s heval).symm (x+y)).1) z=_
    rw [map_add]
    rfl
  map_smul' c x := by
    apply LinearMap.ext
    intro z
    change (((evaluationEquiv s heval).symm (c • x)).1) z=_
    rw [map_smul]
    rfl

noncomputable def cyclicProduct : H ⊗[ℂ] H →L[ℂ] H :=
  (TensorProduct.lift (cyclicProductBilinear s heval)).toContinuousLinearMap

@[simp] theorem cyclicProduct_tmul (x y : H) :
    cyclicProduct s heval (x ⊗ₜ[ℂ] y)=((evaluationEquiv s heval).symm x).1 y := rfl

lemma cyclicProduct_surjective : Function.Surjective (cyclicProduct s heval) := by
  have hu : (evaluationEquiv s heval).symm s.state=1 := by
    apply (evaluationEquiv s heval).injective
    rw [LinearEquiv.apply_symm_apply]
    rfl
  intro y
  exact ⟨s.state ⊗ₜ[ℂ] y,by simp [hu]⟩

lemma evaluationEquiv_alice (i : Fin n) (a : Fin 2) (x : H) :
    (evaluationEquiv s heval).symm (s.alice i a x) =
      ⟨s.alice i a,alice_mem_algebra s i a⟩*(evaluationEquiv s heval).symm x := by
  apply (evaluationEquiv s heval).injective
  rw [LinearEquiv.apply_symm_apply]
  change s.alice i a x=s.alice i a (evaluationEquiv s heval ((evaluationEquiv s heval).symm x))
  rw [LinearEquiv.apply_symm_apply]

lemma cyclicProduct_intertwines_alice (i : Fin n) (a : Fin 2) :
    (cyclicProduct s heval).comp (tensorLeft (s.alice i a))=(s.alice i a).comp (cyclicProduct s heval) := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro x y
  change cyclicProduct s heval (s.alice i a x ⊗ₜ[ℂ] y)=s.alice i a (cyclicProduct s heval (x ⊗ₜ[ℂ] y))
  rw [cyclicProduct_tmul,cyclicProduct_tmul,evaluationEquiv_alice]
  rfl

lemma cyclicProduct_intertwines_bob (j : Fin n) (b : Fin 2) :
    (cyclicProduct s heval).comp (tensorRight (s.bob j b))=(s.bob j b).comp (cyclicProduct s heval) := by
  apply ContinuousLinearMap.coe_injective
  apply TensorProduct.ext'
  intro x y
  change cyclicProduct s heval (x ⊗ₜ[ℂ] s.bob j b y)=s.bob j b (cyclicProduct s heval (x ⊗ₜ[ℂ] y))
  rw [cyclicProduct_tmul,cyclicProduct_tmul]
  exact congrArg (fun T : H →L[ℂ] H => T y)
    (aliceAlgebra_commute_bob_outcome s ((evaluationEquiv s heval).symm x).property j b).eq

include heval in
/-- A faithful cyclic finite representation admits a same-local-dimension tensor vector state. -/
theorem finite_cyclic_tensor_vector : ∃ ψ : H ⊗[ℂ] H, ‖ψ‖=1 ∧
    ∀ i j a b, inner ℂ ψ ((tensorLeft (s.alice i a)*tensorRight (s.bob j b)) ψ)=
      inner ℂ s.state ((s.alice i a*s.bob j b) s.state) := by
  obtain ⟨V,hV,hinter⟩ := exists_isometric_intertwiner (cyclicProduct s heval) (cyclicProduct_surjective s heval)
  refine ⟨V s.state,?_,?_⟩
  · have hi := hV s.state s.state
    have he : ‖V s.state‖^2=‖s.state‖^2 := by
      rw [inner_self_eq_norm_sq_to_K,inner_self_eq_norm_sq_to_K] at hi
      exact_mod_cast hi
    exact ((sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp he).trans s.state_norm
  · intro i j a b
    have hA := hinter (tensorLeft (s.alice i a)) (s.alice i a)
      (tensorLeft_selfadjoint (s.alice_projection i a).isSelfAdjoint)
      (s.alice_projection i a).isSelfAdjoint (cyclicProduct_intertwines_alice s heval i a)
    have hB := hinter (tensorRight (s.bob j b)) (s.bob j b)
      (tensorRight_selfadjoint (s.bob_projection j b).isSelfAdjoint)
      (s.bob_projection j b).isSelfAdjoint (cyclicProduct_intertwines_bob s heval j b)
    have hAv (x : H) := congrArg (fun T : H →L[ℂ] H ⊗[ℂ] H => T x) hA
    have hBv (x : H) := congrArg (fun T : H →L[ℂ] H ⊗[ℂ] H => T x) hB
    simp only [ContinuousLinearMap.comp_apply] at hAv hBv
    simp only [ContinuousLinearMap.mul_apply,hBv,hAv,hV]

end QuantumBehaviors.SmallInputs
