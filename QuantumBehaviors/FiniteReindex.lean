import QuantumBehaviors.EntangledTrace

/-! Reindexing actual finite Born strategies to the natural-number dimensions in Cq. -/
namespace QuantumBehaviors

open Matrix
open scoped Kronecker ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Finite index types are exactly the same finite-dimensional model as natural dimensions. -/
theorem cq_of_indexed_matrices (p : Behavior)
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (A : Input → Matrix ι ι ℂ) (B : Input → Matrix κ κ ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hA0 : ∀ i, (1 - A i).PosSemidef)
    (hB : ∀ j, (B j).PosSemidef) (hB0 : ∀ j, (1 - B j).PosSemidef)
    (hreal : ∀ i j a b, (p (i, j, a, b) : ℂ) =
      (ρ * (effect (A i) a ⊗ₖ effect (B j) b)).trace) : p ∈ Cq := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let f : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let g := Equiv.prodCongr e f
  let s : FiniteStrategy (Fintype.card ι) (Fintype.card κ) := {
    density := ρ.submatrix g g
    density_pos := hρ.submatrix g
    density_trace := (trace_submatrix_equiv g ρ).trans htr
    alice := fun i => (A i).submatrix e e
    bob := fun j => (B j).submatrix f f
    alice_pos := fun i => (hA i).submatrix e
    alice_complement_pos := fun i => by simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] using (hA0 i).submatrix e
    bob_pos := fun j => (hB j).submatrix f
    bob_complement_pos := fun j => by simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] using (hB0 j).submatrix f }
  refine ⟨Fintype.card ι, Fintype.card κ, s, ?_⟩
  intro i j a b
  have hea : effect ((A i).submatrix e e) a = (effect (A i) a).submatrix e e := by
    cases a <;> simp [effect, Matrix.submatrix_sub, Matrix.submatrix_one_equiv]
  have heb : effect ((B j).submatrix f f) b = (effect (B j) b).submatrix f f := by
    cases b <;> simp [effect, Matrix.submatrix_sub, Matrix.submatrix_one_equiv]
  change (p (i, j, a, b) : ℂ) =
    (ρ.submatrix g g * (effect ((A i).submatrix e e) a ⊗ₖ effect ((B j).submatrix f f) b)).trace
  rw [hea, heb]
  have hk : (effect (A i) a).submatrix e e ⊗ₖ (effect (B j) b).submatrix f f =
      (effect (A i) a ⊗ₖ effect (B j) b).submatrix g g := rfl
  rw [hk, Matrix.submatrix_mul_equiv, trace_submatrix_equiv]
  exact hreal i j a b

end QuantumBehaviors
