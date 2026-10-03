import QuantumBehaviors.Ultralimit
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Tactic.Positivity

/-! Uniformly contractive operators descend to, and extend on, the Hilbert ultralimit. -/
namespace QuantumBehaviors
namespace HilbertUltralimit

open Filter UniformSpace
open scoped Topology ENNReal

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℂ (H n)]
variable (U : Ultrafilter ℕ)

noncomputable def pointwiseLinear (T : ∀ n, H n →L[ℂ] H n) (hT : ∀ n, ‖T n‖ ≤ 1) :
    PreHilbert H U →ₗ[ℂ] PreHilbert H U where
  toFun x := (toBounded H U).symm
    ⟨fun n => T n (toBounded H U x n), memℓp_infty ⟨‖toBounded H U x‖, by
      rintro r ⟨n, rfl⟩
      calc
        ‖T n (toBounded H U x n)‖ ≤ ‖T n‖ * ‖toBounded H U x n‖ := (T n).le_opNorm _
        _ ≤ 1 * ‖toBounded H U x n‖ := mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
        _ ≤ ‖toBounded H U x‖ := by simpa using lp.norm_apply_le_norm ENNReal.top_ne_zero (toBounded H U x) n⟩⟩
  map_add' x y := by
    apply (toBounded H U).injective
    apply lp.ext
    funext n
    exact map_add (T n) _ _
  map_smul' c x := by
    apply (toBounded H U).injective
    apply lp.ext
    funext n
    exact map_smul (T n) c _

@[simp] theorem pointwiseLinear_apply (T : ∀ n, H n →L[ℂ] H n) (hT : ∀ n, ‖T n‖ ≤ 1)
    (x : PreHilbert H U) (n : ℕ) :
    toBounded H U (pointwiseLinear U T hT x) n = T n (toBounded H U x n) := rfl

theorem pointwiseLinear_contractive (T : ∀ n, H n →L[ℂ] H n) (hT : ∀ n, ‖T n‖ ≤ 1)
    (x : PreHilbert H U) : ‖pointwiseLinear U T hT x‖ ≤ ‖x‖ := by
  apply (sq_le_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ), norm_sq_eq_re_inner (𝕜 := ℂ)]
  apply le_of_tendsto_of_tendsto
    (Complex.continuous_re.continuousAt.tendsto.comp
      (tendsto_inner H U (pointwiseLinear U T hT x) (pointwiseLinear U T hT x)))
    (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_inner H U x x))
  apply Filter.Eventually.of_forall
  intro n
  change RCLike.re (inner ℂ (T n (toBounded H U x n)) (T n (toBounded H U x n))) ≤
    RCLike.re (inner ℂ (toBounded H U x n) (toBounded H U x n))
  rw [inner_self_eq_norm_sq, inner_self_eq_norm_sq]
  apply pow_le_pow_left₀ (norm_nonneg _)
  calc
    ‖T n (toBounded H U x n)‖ ≤ ‖T n‖ * ‖toBounded H U x n‖ := (T n).le_opNorm _
    _ ≤ 1 * ‖toBounded H U x n‖ := mul_le_mul_of_nonneg_right (hT n) (norm_nonneg _)
    _ = _ := one_mul _

noncomputable def pointwiseContinuous (T : ∀ n, H n →L[ℂ] H n) (hT : ∀ n, ‖T n‖ ≤ 1) :
    PreHilbert H U →L[ℂ] PreHilbert H U :=
  (pointwiseLinear U T hT).mkContinuous 1 fun x => by
    simpa using pointwiseLinear_contractive U T hT x

noncomputable def operator (T : ∀ n, H n →L[ℂ] H n) (hT : ∀ n, ‖T n‖ ≤ 1) :
    Space H U →L[ℂ] Space H U := (pointwiseContinuous U T hT).completion

@[simp] theorem operator_apply_coe (T : ∀ n, H n →L[ℂ] H n) (hT : ∀ n, ‖T n‖ ≤ 1)
    (x : PreHilbert H U) :
    operator U T hT (x : Space H U) = (pointwiseLinear U T hT x : Space H U) := by
  exact ContinuousLinearMap.completion_apply_coe _ _

variable [∀ n, CompleteSpace (H n)]

theorem operator_projection (T : ∀ n, H n →L[ℂ] H n)
    (hT : ∀ n, IsStarProjection (T n)) :
    IsStarProjection (operator U T (fun n => (hT n).norm_le)) := by
  constructor
  · ext x
    induction x using Completion.induction_on with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x =>
        simp only [ContinuousLinearMap.mul_apply, operator_apply_coe]
        congr 1
        apply (toBounded H U).injective
        apply lp.ext
        funext n
        exact congrArg (fun A : H n →L[ℂ] H n => A (toBounded H U x n)) (hT n).isIdempotentElem.eq
  · apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
    intro x y
    change inner ℂ (operator U T (fun n => (hT n).norm_le) x) y =
      inner ℂ x (operator U T (fun n => (hT n).norm_le) y)
    induction x, y using Completion.induction_on₂ with
    | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
    | ih x y =>
        simp only [operator_apply_coe, inner_completion_coe]
        unfold limitInner
        congr 1
        funext n
        simp only [pointwiseLinear_apply]
        exact (hT n).isSelfAdjoint.isSymmetric _ _

theorem operator_commute (T S : ∀ n, H n →L[ℂ] H n)
    (hT : ∀ n, ‖T n‖ ≤ 1) (hS : ∀ n, ‖S n‖ ≤ 1)
    (hcomm : ∀ n, Commute (T n) (S n)) :
    Commute (operator U T hT) (operator U S hS) := by
  change operator U T hT * operator U S hS = operator U S hS * operator U T hT
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
      simp only [ContinuousLinearMap.mul_apply, operator_apply_coe]
      congr 1
      apply (toBounded H U).injective
      apply lp.ext
      funext n
      exact congrArg (fun A : H n →L[ℂ] H n => A (toBounded H U x n)) (hcomm n).eq

noncomputable def statePre (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1) : PreHilbert H U :=
  (toBounded H U).symm ⟨ψ, memℓp_infty ⟨1, by rintro r ⟨n, rfl⟩; exact (hψ n).le⟩⟩

noncomputable def state (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1) : Space H U :=
  (statePre U ψ hψ : Space H U)

theorem state_norm (ψ : ∀ n, H n) (hψ : ∀ n, ‖ψ n‖ = 1) : ‖state U ψ hψ‖ = 1 := by
  have hinner : inner ℂ (state U ψ hψ) (state U ψ hψ) = 1 := by
    rw [state, inner_completion_coe]
    unfold limitInner
    apply scalarLimit_eq_of_tendsto
    have heq : (fun n => inner ℂ (ψ n) (ψ n)) = fun _ => (1 : ℂ) := by
      funext n
      rw [inner_self_eq_norm_sq_to_K, hψ n]
      norm_num
    change Tendsto (fun n => inner ℂ (ψ n) (ψ n)) U (𝓝 1)
    rw [heq]
    exact tendsto_const_nhds
  have hnorm : ‖state U ψ hψ‖ ^ 2 = 1 := by
    have := congrArg Complex.re hinner
    change RCLike.re (inner ℂ (state U ψ hψ) (state U ψ hψ)) = 1 at this
    rwa [inner_self_eq_norm_sq] at this
  nlinarith [norm_nonneg (state U ψ hψ)]

end HilbertUltralimit
end QuantumBehaviors
