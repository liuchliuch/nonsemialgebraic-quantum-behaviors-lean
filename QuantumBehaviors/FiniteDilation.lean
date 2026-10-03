import QuantumBehaviors.Models
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.Data.Matrix.Block
import Mathlib.Tactic.NoncommRing

/-! Common binary POVM dilation on the same doubled local space, as equation (S9). -/
namespace QuantumBehaviors

open Matrix
open scoped ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def binaryDilation (E : Matrix ι ι ℂ) : Matrix (ι ⊕ ι) (ι ⊕ ι) ℂ :=
  let S := CFC.sqrt (E * (1 - E))
  Matrix.fromBlocks E S S (1 - E)

theorem binaryDilation_projection (E : Matrix ι ι ℂ)
    (hE : E.PosSemidef) (hE0 : (1 - E).PosSemidef) : IsStarProjection (binaryDilation E) := by
  let S := CFC.sqrt (E * (1 - E))
  have hcomm : Commute E (1 - E) := by change E * (1 - E) = (1 - E) * E; noncomm_ring
  have hpos : 0 ≤ E * (1 - E) := Commute.mul_nonneg hE.nonneg hE0.nonneg hcomm
  have hSS : S * S = E * (1 - E) := CFC.sqrt_mul_sqrt_self _ hpos
  have hSself : S.conjTranspose = S := (CFC.sqrt_nonneg _).isSelfAdjoint
  have hSEbase : Commute (E * (1 - E)) E := by
    change E * (1 - E) * E = E * (E * (1 - E))
    noncomm_ring
  have hSE : S * E = E * S := (hSEbase.cfcₙ_nnreal NNReal.sqrt).eq
  constructor
  · change binaryDilation E * binaryDilation E = binaryDilation E
    unfold binaryDilation
    rw [Matrix.fromBlocks_multiply]
    congr 1
    · change E * E + S * S = E
      rw [hSS]
      noncomm_ring
    · change E * S + S * (1 - E) = S
      noncomm_ring [hSE]
    · change S * E + (1 - E) * S = S
      noncomm_ring [hSE]
    · change S * S + (1 - E) * (1 - E) = 1 - E
      rw [hSS]
      noncomm_ring
  · change (binaryDilation E).conjTranspose = binaryDilation E
    unfold binaryDilation
    rw [Matrix.fromBlocks_conjTranspose]
    change Matrix.fromBlocks E.conjTranspose S.conjTranspose S.conjTranspose
      (1 - E).conjTranspose = Matrix.fromBlocks E S S (1 - E)
    rw [hE.isHermitian.eq, hE0.isHermitian.eq, hSself]

@[simp] theorem binaryDilation_compression (E : Matrix ι ι ℂ) :
    (binaryDilation E).submatrix Sum.inl Sum.inl = E := rfl

@[simp] theorem binaryDilation_outcome_compression (E : Matrix ι ι ℂ) (a : Bool) :
    (effect (binaryDilation E) a).submatrix Sum.inl Sum.inl = effect E a := by
  cases a
  · ext i j
    simp [effect, Matrix.submatrix_apply, Matrix.one_apply, binaryDilation]
  · rfl

end QuantumBehaviors
