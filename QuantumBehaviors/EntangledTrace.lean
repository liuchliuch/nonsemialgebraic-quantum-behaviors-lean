import QuantumBehaviors.Models
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Tactic.NoncommRing

/-! The maximally entangled density matrix and its exact normalized-trace identity. -/
namespace QuantumBehaviors

open Matrix
open scoped Kronecker ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def diagonalVector : (ι × ι) → ℂ := fun x => if x.1 = x.2 then 1 else 0

noncomputable def entangledDensity : Matrix (ι × ι) (ι × ι) ℂ :=
  (1 / (Fintype.card ι : ℝ)) •
    Matrix.vecMulVec (diagonalVector (ι := ι)) (star (diagonalVector (ι := ι)))

theorem entangledDensity_positive : (entangledDensity (ι := ι)).PosSemidef :=
  (Matrix.posSemidef_vecMulVec_self_star diagonalVector).smul (by positivity)

theorem entangledDensity_trace [Nonempty ι] : (entangledDensity (ι := ι)).trace = 1 := by
  have hd : (Fintype.card ι : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Fintype.card_ne_zero)
  rw [entangledDensity, Matrix.trace_smul, Matrix.trace_vecMulVec]
  simp [dotProduct, diagonalVector, Fintype.sum_prod_type, hd]

/-- Equation (13)/(S17) in density-matrix form; no real or symmetric assumption on X,Y. -/
theorem entangledDensity_trace_kronecker (X Y : Matrix ι ι ℂ) :
    (entangledDensity * (X ⊗ₖ Y.transpose)).trace =
      (1 / (Fintype.card ι : ℝ)) • (X * Y).trace := by
  rw [entangledDensity, smul_mul_assoc, Matrix.trace_smul]
  congr 1
  rw [Matrix.vecMulVec_mul, Matrix.trace_vecMulVec]
  simp only [Matrix.vecMul, dotProduct, Matrix.kronecker_apply, Matrix.transpose_apply,
    Matrix.trace, Matrix.diag_apply, Matrix.mul_apply, Fintype.sum_prod_type]
  simp [diagonalVector, Matrix.vecMul, dotProduct, mul_comm]
  rw [Finset.sum_comm]

/-- Selfadjoint idempotent matrices really are positive semidefinite. -/
theorem projection_positive {P : Matrix ι ι ℂ} (hstar : P.conjTranspose = P)
    (hsq : P * P = P) : P.PosSemidef := by
  simpa only [hstar, hsq] using Matrix.posSemidef_conjTranspose_mul_self P

theorem projection_complement_positive {P : Matrix ι ι ℂ} (hstar : P.conjTranspose = P)
    (hsq : P * P = P) : (1 - P).PosSemidef := by
  apply projection_positive
  · simp [hstar]
  · noncomm_ring [hsq]

/-- Trace is invariant under an arbitrary finite coordinate equivalence. -/
theorem trace_submatrix_equiv {κ : Type*} [Fintype κ] (e : κ ≃ ι) (M : Matrix ι ι ℂ) :
    (M.submatrix e e).trace = M.trace := by
  exact e.sum_comp (fun i => M i i)

end QuantumBehaviors
