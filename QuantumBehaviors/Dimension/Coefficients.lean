import QuantumBehaviors.Dimension.DensityMoments
import QuantumBehaviors.Dimension.RangeRestriction
import QuantumBehaviors.FiniteToCommuting

/-! Tensor actions and nonzero density columns, without a change to the local dimensions. -/
namespace QuantumBehaviors.Dimension

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

def reshape (v : ι × κ → ℂ) : Matrix ι κ ℂ := fun i j => v (i, j)

@[simp] theorem reshape_zero : reshape (0 : ι × κ → ℂ) = 0 := rfl
@[simp] theorem reshape_add (v w : ι × κ → ℂ) : reshape (v + w) = reshape v + reshape w := rfl
@[simp] theorem reshape_sub (v w : ι × κ → ℂ) : reshape (v - w) = reshape v - reshape w := rfl
@[simp] theorem reshape_smul (c : ℂ) (v : ι × κ → ℂ) : reshape (c • v) = c • reshape v := rfl

@[simp] theorem reshape_sum {J : Type*} (s : Finset J) (v : J → ι × κ → ℂ) :
    reshape (∑ j ∈ s, v j) = ∑ j ∈ s, reshape (v j) := by ext i k; simp [reshape, Matrix.sum_apply]

theorem reshape_ne_zero {v : ι × κ → ℂ} (hv : v ≠ 0) : reshape v ≠ 0 := by
  intro h
  apply hv
  funext x
  rcases x with ⟨i, j⟩
  exact congrFun (congrFun h i) j

@[simp] theorem reshape_alice (E : Matrix ι ι ℂ) (v : ι × κ → ℂ) :
    reshape ((E ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ v) = E * reshape v := by
  ext i j
  simp [reshape, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_assoc]

@[simp] theorem reshape_bob (G : Matrix κ κ ℂ) (v : ι × κ → ℂ) :
    reshape (((1 : Matrix ι ι ℂ) ⊗ₖ G) *ᵥ v) = reshape v * G.transpose := by
  ext i j
  simp [reshape, Matrix.mulVec, dotProduct, Matrix.mul_apply, Fintype.sum_prod_type,
    Matrix.kronecker_apply, Matrix.one_apply, mul_comm]

theorem column_of_mul_zero {J : Type*} [Fintype J] {M R : Matrix J J ℂ}
    (h : M * R = 0) (k : J) : M *ᵥ (fun j => R j k) = 0 := by
  funext i
  exact congrFun (congrFun h i) k

theorem density_has_nonzero_column {J : Type} [Fintype J] [DecidableEq J]
    (ρ : Matrix J J ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1) :
    ∃ k : J, (fun j => CFC.sqrt ρ j k) ≠ 0 := by
  by_contra h
  push_neg at h
  have hs : CFC.sqrt ρ = 0 := by
    ext i j
    exact congrFun (h j) i
  have hρzero : ρ = 0 := by
    have hsq := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
    simpa [hs] using hsq.symm
  simpa [hρzero] using htr

/-- Algebraic local coefficient identities extracted from vector support identities. -/
theorem coefficient_relations (v : ι × κ → ℂ)
    (E : Input → Matrix ι ι ℂ) (G : Input → Matrix κ κ ℂ)
    (hxy : ∀ i, (E i ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ v = ((1 : Matrix ι ι ℂ) ⊗ₖ G i) *ᵥ v)
    (hee : ∀ i, ((E i * E i) ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ v = (E i ⊗ₖ 1) *ᵥ v)
    (hgg : ∀ i, ((1 : Matrix ι ι ℂ) ⊗ₖ (G i * G i)) *ᵥ v = (1 ⊗ₖ G i) *ᵥ v)
    {α : ℝ} (hs : (∑ i, E i ⊗ₖ (1 : Matrix κ κ ℂ)) *ᵥ v = (α : ℂ) • v) :
    (∀ i, E i * reshape v = reshape v * (G i).transpose) ∧
    (∀ i, (E i * E i) * reshape v = E i * reshape v) ∧
    (∀ i, (G i * G i) * (reshape v).transpose = G i * (reshape v).transpose) ∧
    (∑ i, E i) * reshape v = (α : ℂ) • reshape v ∧
    (∑ i, G i) * (reshape v).transpose = (α : ℂ) • (reshape v).transpose := by
  have hinter : ∀ i, E i * reshape v = reshape v * (G i).transpose := by
    intro i
    simpa only [reshape_alice, reshape_bob] using congrArg reshape (hxy i)
  have hE : ∀ i, (E i * E i) * reshape v = E i * reshape v := by
    intro i
    simpa only [reshape_alice] using congrArg reshape (hee i)
  have hG : ∀ i, (G i * G i) * (reshape v).transpose = G i * (reshape v).transpose := by
    intro i
    have h := congrArg reshape (hgg i)
    simp only [reshape_bob] at h
    simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose h
  have hS : (∑ i, E i) * reshape v = (α : ℂ) • reshape v := by
    have h := congrArg reshape hs
    simp only [Matrix.sum_mulVec, reshape_sum, reshape_alice, reshape_smul] at h
    simpa only [Matrix.sum_mul] using h
  have hT : (∑ i, G i) * (reshape v).transpose = (α : ℂ) • (reshape v).transpose := by
    have h : (∑ i, reshape v * (G i).transpose) = (α : ℂ) • reshape v := by
      simp_rw [← hinter]
      simpa only [Matrix.sum_mul] using hS
    have ht := congrArg Matrix.transpose h
    simpa only [Matrix.transpose_sum, Matrix.transpose_mul, Matrix.transpose_transpose,
      Matrix.transpose_smul, Matrix.sum_mul] using ht
  exact ⟨hinter, hE, hG, hS, hT⟩

end QuantumBehaviors.Dimension
