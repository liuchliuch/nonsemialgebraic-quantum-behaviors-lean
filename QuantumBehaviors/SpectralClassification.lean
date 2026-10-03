import QuantumBehaviors.SpectralAlgebra
import QuantumBehaviors.SpectralDescent
import Mathlib.Analysis.InnerProductSpace.StarOrder

/-!
# Scalar sums of four projections on arbitrary complex Hilbert spaces

This proves Proposition S2 of arXiv:2609.18865 without a dimension restriction.
The only analytic inputs are standard C⋆-algebra facts already proved in
Mathlib: the real spectrum of a self-adjoint operator is nonempty, and the
spectrum of a positive operator is nonnegative.  Reflection and affine
spectral transport have explicit algebraic proofs in `SpectralAlgebra`.
-/

namespace QuantumBehaviors

section CStarAlgebra

variable {A : Type*} [CStarAlgebra A] [PartialOrder A] [StarOrderedRing A]
  [Nontrivial A]

/-- Dimension-independent classification, in the stronger generality of a
nontrivial unital C⋆-algebra. -/
theorem four_projections_allowed_cstar {P Q R S : A}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    {α : ℝ} (hsum : P + Q + R + S = algebraMap ℝ A α)
    (hα₁ : 1 < α) (hα₂ : α < 2) : Allowed α := by
  have hcomplement : R + S = algebraMap ℝ A α - (P + Q) := by
    rw [← hsum]
    abel
  apply allowed_of_reflected_sets (S := spectrum ℝ (P + Q))
    (T := spectrum ℝ (R + S)) hα₁ hα₂
  · exact ContinuousFunctionalCalculus.spectrum_nonempty (P + Q)
      (hP.isSelfAdjoint.add hQ.isSelfAdjoint)
  · intro x hx
    exact spectrum_nonneg_of_nonneg (add_nonneg hP.nonneg hQ.nonneg) hx
  · intro x hx
    exact spectrum_nonneg_of_nonneg (add_nonneg hR.nonneg hS.nonneg) hx
  · intro x
    rw [hcomplement]
    exact spectrum_scalar_sub_iff (P + Q) α x
  · intro x hx hx₀ hx₂
    exact spectral_reflection_real hP.isIdempotentElem hQ.isIdempotentElem hx₀ hx₂ hx
  · intro x hx hx₀ hx₂
    exact spectral_reflection_real hR.isIdempotentElem hS.isIdempotentElem hx₀ hx₂ hx

end CStarAlgebra

section Hilbert

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [CompleteSpace H] [Nontrivial H]

/-- Four bounded self-adjoint idempotents on a nonzero complex Hilbert space
can sum to `α I`, for `1 < α < 2`, only at `α = 2 - 2/m`, `m ≥ 3`. -/
theorem four_projections_allowed {P Q R S : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    (hR : IsStarProjection R) (hS : IsStarProjection S)
    {α : ℝ} (hsum : P + Q + R + S = algebraMap ℝ (H →L[ℂ] H) α)
    (hα₁ : 1 < α) (hα₂ : α < 2) : Allowed α :=
  four_projections_allowed_cstar hP hQ hR hS hsum hα₁ hα₂

/-- The indexed version used by four-input quantum strategies. -/
theorem four_indexed_projections_allowed (P : Input → H →L[ℂ] H)
    (hP : ∀ i, IsStarProjection (P i)) {α : ℝ}
    (hsum : ∑ i : Input, P i = algebraMap ℝ (H →L[ℂ] H) α)
    (hα₁ : 1 < α) (hα₂ : α < 2) : Allowed α := by
  apply four_projections_allowed (hP 0) (hP 1) (hP 2) (hP 3) ?_ hα₁ hα₂
  simpa only [Input, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
    zero_add, add_zero, add_assoc] using hsum

/-- Complex spectral reflection for the original operator-theoretic statement. -/
theorem hilbert_spectral_reflection {P Q : H →L[ℂ] H}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q)
    {z : ℝ} (hz₀ : 0 < z) (hz₂ : z < 2)
    (hz : (z : ℂ) ∈ spectrum ℂ (P + Q)) :
    ((2 - z : ℝ) : ℂ) ∈ spectrum ℂ (P + Q) := by
  have hself : IsSelfAdjoint (P + Q) := hP.isSelfAdjoint.add hQ.isSelfAdjoint
  rw [hself.coe_mem_spectrum_complex] at hz ⊢
  exact spectral_reflection_real hP.isIdempotentElem hQ.isIdempotentElem hz₀ hz₂ hz

end Hilbert

end QuantumBehaviors
