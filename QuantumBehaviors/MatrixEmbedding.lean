import QuantumBehaviors.EntangledTrace

/-! Rectangular isometries for injective coordinate embeddings and preservation of Born traces. -/
namespace QuantumBehaviors

open Matrix
open scoped ComplexOrder

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

noncomputable def embeddingMatrix (e : ι → κ) : Matrix κ ι ℂ :=
  fun x i => if x = e i then 1 else 0

/-- Compression along basis vectors is exactly the corresponding submatrix. -/
theorem embedding_compression (e : ι → κ) (M : Matrix κ κ ℂ) :
    (embeddingMatrix e).conjTranspose * M * embeddingMatrix e = M.submatrix e e := by
  ext i j
  simp [embeddingMatrix, Matrix.mul_apply, Matrix.conjTranspose_apply, Matrix.submatrix_apply]

theorem embedding_isometry (e : ι → κ) (he : Function.Injective e) :
    (embeddingMatrix e).conjTranspose * embeddingMatrix e = 1 := by
  have h := embedding_compression e (1 : Matrix κ κ ℂ)
  have hsub : (1 : Matrix κ κ ℂ).submatrix e e = 1 := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, he.eq_iff]
  simpa [hsub] using h

noncomputable def embeddedDensity (e : ι → κ) (ρ : Matrix ι ι ℂ) : Matrix κ κ ℂ :=
  embeddingMatrix e * ρ * (embeddingMatrix e).conjTranspose

theorem embeddedDensity_positive (e : ι → κ) {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) :
    (embeddedDensity e ρ).PosSemidef := hρ.mul_mul_conjTranspose_same (embeddingMatrix e)

theorem embeddedDensity_expectation (e : ι → κ) (ρ : Matrix ι ι ℂ) (M : Matrix κ κ ℂ) :
    (embeddedDensity e ρ * M).trace = (ρ * M.submatrix e e).trace := by
  unfold embeddedDensity
  calc
    _ = (embeddingMatrix e * (ρ * ((embeddingMatrix e).conjTranspose * M))).trace := by
      rw [Matrix.mul_assoc, Matrix.mul_assoc]
    _ = (ρ * ((embeddingMatrix e).conjTranspose * M) * embeddingMatrix e).trace :=
      Matrix.trace_mul_comm _ _
    _ = (ρ * ((embeddingMatrix e).conjTranspose * M * embeddingMatrix e)).trace := by
      rw [Matrix.mul_assoc]
    _ = _ := by rw [embedding_compression]

theorem embeddedDensity_trace (e : ι → κ) (he : Function.Injective e) (ρ : Matrix ι ι ℂ) :
    (embeddedDensity e ρ).trace = ρ.trace := by
  have h := embeddedDensity_expectation e ρ 1
  have hsub : (1 : Matrix κ κ ℂ).submatrix e e = 1 := by
    ext i j
    simp [Matrix.submatrix_apply, Matrix.one_apply, he.eq_iff]
  simpa [hsub] using h

end QuantumBehaviors
