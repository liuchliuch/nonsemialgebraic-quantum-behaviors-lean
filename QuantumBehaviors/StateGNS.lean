import QuantumBehaviors.Models
import Mathlib.Analysis.CStarAlgebra.GelfandNaimarkSegal
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order

/-!
# A density matrix as a genuine vector state

We use Mathlib's proved GNS construction with the positive functional Tr(ρ·).
This replaces the paper's finite purification step without assuming a representation theorem.
The cyclic vector is explicitly the image of the identity matrix.
-/
namespace QuantumBehaviors
set_option synthInstance.maxHeartbeats 200000

open Matrix ContinuousLinearMap UniformSpace
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

noncomputable local instance : CStarAlgebra (Matrix ι ι ℂ) where

noncomputable def densityFunctional (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    Matrix ι ι ℂ →ₚ[ℂ] ℂ :=
  PositiveLinearMap.mk₀
    { toFun := fun X => (ρ * X).trace
      map_add' := fun X Y => by simp [mul_add]
      map_smul' := fun c X => by simp [mul_smul_comm] }
    (by
      intro X hX
      let S := CFC.sqrt ρ
      have hS : S.conjTranspose = S := (CFC.sqrt_nonneg ρ).isSelfAdjoint
      have hSS : S * S = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
      have hpos := (show X.PosSemidef from hX.posSemidef).mul_mul_conjTranspose_same S
      have ht : (S * X * S.conjTranspose).trace = (ρ * X).trace := by
        rw [hS, Matrix.trace_mul_cycle, hSS]
      change 0 ≤ (ρ * X).trace
      rw [← ht]
      exact hpos.trace_nonneg)

@[simp] theorem densityFunctional_apply (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (X : Matrix ι ι ℂ) : densityFunctional ρ hρ X = (ρ * X).trace := rfl

noncomputable def densityGNSState (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) :
    (densityFunctional ρ hρ).GNS :=
  ((densityFunctional ρ hρ).toPreGNS 1 : (densityFunctional ρ hρ).GNS)

theorem densityGNSState_expectation (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef)
    (X : Matrix ι ι ℂ) :
    inner ℂ (densityGNSState ρ hρ)
      ((densityFunctional ρ hρ).gnsStarAlgHom X (densityGNSState ρ hρ)) = (ρ * X).trace := by
  simp [densityGNSState, PositiveLinearMap.gnsStarAlgHom,
    PositiveLinearMap.preGNS_inner_def]

theorem densityGNSState_norm (ρ : Matrix ι ι ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ‖densityGNSState ρ hρ‖ = 1 := by
  have h := densityGNSState_expectation ρ hρ 1
  simp only [map_one, ContinuousLinearMap.one_apply, mul_one, htr] at h
  have hr := congrArg Complex.re h
  change RCLike.re (inner ℂ (densityGNSState ρ hρ) (densityGNSState ρ hρ)) = 1 at hr
  rw [inner_self_eq_norm_sq] at hr
  nlinarith [norm_nonneg (densityGNSState ρ hρ)]

/-- A finite-dimensional density/projection commuting table has the actual Cqc vector model. -/
theorem cqc_of_commuting_density (p : Behavior) (ρ : Matrix ι ι ℂ)
    (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (A B : Input → Matrix ι ι ℂ)
    (hA : ∀ i, IsStarProjection (A i)) (hB : ∀ j, IsStarProjection (B j))
    (hAB : ∀ i j, Commute (A i) (B j))
    (hreal : ∀ i j a b, (p (i, j, a, b) : ℂ) =
      (ρ * (effect (A i) a * effect (B j) b)).trace) : p ∈ Cqc := by
  let f := densityFunctional ρ hρ
  let π := f.gnsStarAlgHom
  let s : CommutingStrategy f.GNS := {
    state := densityGNSState ρ hρ
    state_norm := densityGNSState_norm ρ hρ htr
    alice := fun i => π (A i)
    bob := fun j => π (B j)
    alice_projection := fun i => (hA i).map π
    bob_projection := fun j => (hB j).map π
    cross_commute := fun i j => (hAB i j).map π }
  refine ⟨f.GNS, inferInstance, inferInstance, inferInstance, s, ?_⟩
  intro i j a b
  have heff : ∀ (X : Matrix ι ι ℂ) (a : Bool), effect (π X) a = π (effect X a) := by
    intro X a
    cases a <;> simp [effect]
  change (p (i, j, a, b) : ℂ) = inner ℂ (densityGNSState ρ hρ)
    ((effect (π (A i)) a * effect (π (B j)) b) (densityGNSState ρ hρ))
  rw [heff, heff, ← map_mul, densityGNSState_expectation]
  exact hreal i j a b

end QuantumBehaviors
