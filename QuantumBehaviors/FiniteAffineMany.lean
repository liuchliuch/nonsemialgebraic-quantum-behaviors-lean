import QuantumBehaviors.FiniteAffine
namespace QuantumBehaviors
open scoped BigOperators ComplexOrder

/-- Arbitrary finite auxiliary/equality index types really give the natural-number SDP interface. -/
theorem HasFiniteComplexSDPLift.of_finiteMany {Z J K : Type*} [Fintype Z] [Fintype J] [Fintype K]
    {C : Set Behavior} (size : K → ℕ) (A : ∀ k, ComplexAffineMatrix (Coordinate ⊕ Z) (size k))
    (L : J → AffineScalar (Coordinate ⊕ Z))
    (hC : ∀ p, p ∈ C ↔ ∃ z : Z → ℝ, (∀ k, ((A k).eval (Sum.elim p z)).PosSemidef) ∧
      ∀ j, (L j).eval (Sum.elim p z)=0) : HasFiniteComplexSDPLift C := by
  classical
  let eZ := Fintype.equivFin Z
  let eJ := Fintype.equivFin J
  let eK := Fintype.equivFin K
  let e : (Coordinate ⊕ Z) ≃ (Coordinate ⊕ Fin (Fintype.card Z)) := Equiv.sumCongr (Equiv.refl _) eZ
  refine ⟨Fintype.card Z,Fintype.card K,Fintype.card J,(fun k => size (eK.symm k)),
    (fun k => (A (eK.symm k)).reindexVariables e),(fun j => AffineScalar.reindex e (L (eJ.symm j))),?_⟩
  intro p
  rw [hC p]
  constructor
  · rintro ⟨z,hA,hL⟩
    refine ⟨z ∘ eZ.symm,?_,?_⟩
    · intro i
      rw [ComplexAffineMatrix.eval_reindexVariables]
      have heq : Sum.elim p (z ∘ eZ.symm) ∘ e=Sum.elim p z := by funext x;cases x <;> simp [e]
      rw [heq]
      exact hA _
    · intro j
      rw [AffineScalar.eval_reindex]
      have heq : Sum.elim p (z ∘ eZ.symm) ∘ e=Sum.elim p z := by funext x;cases x <;> simp [e]
      rw [heq]
      exact hL _
  · rintro ⟨z,hA,hL⟩
    refine ⟨z ∘ eZ,?_,?_⟩
    · intro k
      obtain ⟨i,rfl⟩ := eK.symm.surjective k
      have h := hA i
      rw [ComplexAffineMatrix.eval_reindexVariables] at h
      have heq : Sum.elim p z ∘ e=Sum.elim p (z ∘ eZ) := by funext x;cases x <;> rfl
      rwa [heq] at h
    · intro j
      have h := hL (eJ j)
      rw [AffineScalar.eval_reindex,Equiv.symm_apply_apply] at h
      have heq : Sum.elim p z ∘ e=Sum.elim p (z ∘ eZ) := by funext x;cases x <;> rfl
      rwa [heq] at h

end QuantumBehaviors
