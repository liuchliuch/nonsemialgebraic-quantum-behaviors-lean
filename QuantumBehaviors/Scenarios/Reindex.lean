import QuantumBehaviors.Scenarios.Basic
import QuantumBehaviors.EntangledTrace

namespace QuantumBehaviors.Scenarios
open Matrix
open scoped BigOperators Kronecker ComplexOrder
variable {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
variable {nA nB mA mB : ℕ}

theorem strategy_of_indexed_matrices (p : Behavior nA nB mA mB)
    (ρ : Matrix (I×J) (I×J) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace=1)
    (A : Fin nA → Fin mA → Matrix I I ℂ) (B : Fin nB → Fin mB → Matrix J J ℂ)
    (hA : ∀ i a, (A i a).PosSemidef) (hAs : ∀ i, ∑ a, A i a=1)
    (hB : ∀ j b, (B j b).PosSemidef) (hBs : ∀ j, ∑ b, B j b=1)
    (hp : ∀ i j a b, (p (i,j,a,b) : ℂ)=(ρ*(A i a ⊗ₖ B j b)).trace) :
    ∃ t : FiniteStrategy nA nB mA mB (Fintype.card I) (Fintype.card J), t.realizes p := by
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  let f : Fin (Fintype.card J) ≃ J := (Fintype.equivFin J).symm
  let g := Equiv.prodCongr e f
  let t : FiniteStrategy nA nB mA mB (Fintype.card I) (Fintype.card J) := {
    density := ρ.submatrix g g
    density_pos := hρ.submatrix g
    density_trace := (trace_submatrix_equiv g ρ).trans htr
    alice := fun i a => (A i a).submatrix e e
    bob := fun j b => (B j b).submatrix f f
    alice_pos := fun i a => (hA i a).submatrix e
    bob_pos := fun j b => (hB j b).submatrix f
    alice_sum := by
      intro i
      have h := congrArg (fun M : Matrix I I ℂ => M.submatrix e e) (hAs i)
      apply Matrix.ext
      intro r s
      have hh := congrFun (congrFun h r) s
      simpa only [Matrix.submatrix_apply,Matrix.sum_apply,Matrix.one_apply,e.injective.eq_iff] using hh
    bob_sum := by
      intro j
      have h := congrArg (fun M : Matrix J J ℂ => M.submatrix f f) (hBs j)
      apply Matrix.ext
      intro r s
      have hh := congrFun (congrFun h r) s
      simpa only [Matrix.submatrix_apply,Matrix.sum_apply,Matrix.one_apply,f.injective.eq_iff] using hh }
  refine ⟨t,?_⟩
  intro i j a b
  change (p (i,j,a,b) : ℂ)=(ρ.submatrix g g*((A i a).submatrix e e ⊗ₖ (B j b).submatrix f f)).trace
  have hk : (A i a).submatrix e e ⊗ₖ (B j b).submatrix f f=(A i a ⊗ₖ B j b).submatrix g g := rfl
  rw [hk,Matrix.submatrix_mul_equiv,trace_submatrix_equiv]
  exact hp i j a b

end QuantumBehaviors.Scenarios
