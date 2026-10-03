import QuantumBehaviors.SmallInputs.CyclicStrategy
import Mathlib.Analysis.SpecialFunctions.Exponential
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.LocalExtr.Basic

/-! The unitary first-variation argument, with its exact positive-square derivative. -/

namespace QuantumBehaviors.SmallInputs

open NormedSpace

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The commutator of two selfadjoint operators is skew-adjoint. -/
lemma commutator_star {D P : H →L[ℂ] H} (hD : IsSelfAdjoint D) (hP : IsSelfAdjoint P) :
    star (D * P - P * D) = -(D * P - P * D) := by
  rw [star_sub, star_mul, star_mul, hD.star_eq, hP.star_eq]
  noncomm_ring

/-- A real-valued expectation along an exponential conjugation orbit. -/
noncomputable def variation (ψ : H) (D P K : H →L[ℂ] H) (t : ℝ) : ℝ :=
  (inner ℂ ψ ((D * (exp ((t : ℂ) • K) * P * exp ((t : ℂ) • (-K)))) ψ)).re

lemma variation_derivative (ψ : H) (D P K : H →L[ℂ] H) :
    HasDerivAt (variation ψ D P K)
      (vectorFunctional ψ (D * (K * P - P * K))).re 0 := by
  have hp : HasDerivAt (fun z : ℂ => exp (z • K)) K 0 := by
    simpa using (hasDerivAt_exp_smul_const K (0 : ℂ))
  have hm : HasDerivAt (fun z : ℂ => exp (z • (-K))) (-K) 0 := by
    simpa using (hasDerivAt_exp_smul_const (-K) (0 : ℂ))
  have hop : HasDerivAt (fun z : ℂ => D * (exp (z • K) * P * exp (z • (-K))))
      (D * (K * P - P * K)) 0 := by
    convert (hasDerivAt_const (0 : ℂ) D).mul ((hp.mul (hasDerivAt_const (0 : ℂ) P)).mul hm) using 1 <;>
      simp [sub_eq_add_neg, add_mul, mul_add]
  have hvec := hop.clm_apply (hasDerivAt_const (0 : ℂ) ψ)
  have hc := (innerSL ℂ ψ).hasFDerivAt.comp_hasDerivAt (0 : ℂ) hvec
  have hc' : HasDerivAt
      (fun z : ℂ => inner ℂ ψ ((D * (exp (z • K) * P * exp (z • (-K)))) ψ))
      (vectorFunctional ψ (D * (K * P - P * K))) 0 := by
    simpa only [ContinuousLinearMap.add_apply, map_zero, add_zero,
      innerSL_apply_apply, vectorFunctional_apply] using hc
  exact hc'.real_of_complex

/-- Exact derivative as a squared norm; traciality is used only for one cyclic rotation. -/
lemma variation_square (ψ : H) (D P : H →L[ℂ] H)
    (hD : IsSelfAdjoint D) (hP : IsSelfAdjoint P)
    (htr : vectorFunctional ψ ((D * (D * P - P * D)) * P) =
      vectorFunctional ψ (P * (D * (D * P - P * D)))) :
    vectorFunctional ψ (D * ((D * P - P * D) * P - P * (D * P - P * D))) =
      inner ℂ ((D * P - P * D) ψ) ((D * P - P * D) ψ) := by
  let K := D * P - P * D
  have hstar : star K = -K := commutator_star hD hP
  have he : D * (K * P - P * K) - (D * K) * P + P * (D * K) = star K * K := by
    rw [hstar]
    dsimp [K]
    noncomm_ring
  have hf := congrArg (vectorFunctional ψ) he
  change vectorFunctional ψ ((D * K) * P) = vectorFunctional ψ (P * (D * K)) at htr
  simp only [map_add, map_sub] at hf
  rw [htr] at hf
  rw [vectorFunctional_star_mul] at hf
  simpa only [sub_add_cancel] using hf

/-- At a local maximum, the commutator annihilates the vector state.
The subsequent cyclic reduction, rather than an unproved faithful-state
assumption, turns this into the required operator commutation relation. -/
theorem variation_maximum_annihilates (ψ : H) (D P : H →L[ℂ] H)
    (hD : IsSelfAdjoint D) (hP : IsSelfAdjoint P)
    (htr : vectorFunctional ψ ((D * (D * P - P * D)) * P) =
      vectorFunctional ψ (P * (D * (D * P - P * D))))
    (hmax : IsLocalMax (variation ψ D P (D * P - P * D)) 0) :
    (D * P - P * D) ψ = 0 := by
  have hd := variation_derivative ψ D P (D * P - P * D)
  rw [variation_square ψ D P hD hP htr] at hd
  have hz := hmax.hasDerivAt_eq_zero hd
  change RCLike.re (inner ℂ ((D * P - P * D) ψ) ((D * P - P * D) ψ)) = 0 at hz
  rw [inner_self_eq_norm_sq] at hz
  exact norm_eq_zero.mp (by nlinarith [norm_nonneg ((D * P - P * D) ψ)])

end QuantumBehaviors.SmallInputs
