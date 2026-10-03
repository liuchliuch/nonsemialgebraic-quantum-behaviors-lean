import Mathlib.Analysis.InnerProductSpace.StarOrder
import Mathlib.Analysis.Normed.Operator.Banach
import Mathlib.Analysis.SpecialFunctions.ContinuousFunctionalCalculus.Rpow.Basic
import Mathlib.Analysis.CStarAlgebra.ContinuousFunctionalCalculus.Commute
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Tactic.NoncommRing

/-! Surjective finite-Hilbert intertwiners admit isometric adjoint-polar lifts. -/
namespace QuantumBehaviors.SmallInputs
open ContinuousLinearMap
variable {G H : Type*} [NormedAddCommGroup G] [InnerProductSpace ℂ G] [CompleteSpace G]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] [FiniteDimensional ℂ H]

lemma adjoint_injective_of_surjective (m : G →L[ℂ] H) (hm : Function.Surjective m) :
    Function.Injective (ContinuousLinearMap.adjoint m) := by
  intro x y h
  apply ext_inner_left ℂ
  intro z
  obtain ⟨v,rfl⟩ := hm z
  rw [← m.adjoint_inner_right,← m.adjoint_inner_right,h]

/-- The lift preserves all inner products and simultaneously intertwines every selfadjoint
operator pair already intertwined by the original surjection. -/
theorem exists_isometric_intertwiner (m : G →L[ℂ] H) (hm : Function.Surjective m) :
    ∃ V : H →L[ℂ] G,
      (∀ x y, inner ℂ (V x) (V y)=inner ℂ x y) ∧
      ∀ (P : G →L[ℂ] G) (A : H →L[ℂ] H), IsSelfAdjoint P → IsSelfAdjoint A →
        m.comp P=A.comp m → P.comp V=V.comp A := by
  let Q : H →L[ℂ] H := m.comp (ContinuousLinearMap.adjoint m)
  have hQpos : 0 ≤ Q := (ContinuousLinearMap.nonneg_iff_isPositive Q).mpr (isPositive_self_comp_adjoint m)
  have hQi : Function.Injective Q := (m.self_comp_adjoint_injective_iff).mpr (adjoint_injective_of_surjective m hm)
  have hQu : IsUnit Q := ContinuousLinearMap.isUnit_iff_bijective.mpr
    ⟨hQi,(LinearMap.injective_iff_surjective (f := Q.toLinearMap)).mp hQi⟩
  let S := CFC.sqrt Q
  have hS : IsSelfAdjoint S := (CFC.sqrt_nonneg Q).isSelfAdjoint
  have hSu : IsUnit S := (CFC.isUnit_sqrt_iff Q hQpos).mpr hQu
  let R := Ring.inverse S
  have hRS : R*S=1 := Ring.inverse_mul_cancel S hSu
  have hSR : S*R=1 := Ring.mul_inverse_cancel S hSu
  have hR : IsSelfAdjoint R := by
    change star (Ring.inverse S)=Ring.inverse S
    rw [← Ring.inverse_star,hS.star_eq]
  have hRQR : R*Q*R=1 := by
    rw [← CFC.sqrt_mul_sqrt_self Q hQpos]
    change R*(S*S)*R=1
    calc
      _ = (R*S)*(S*R) := by noncomm_ring
      _ = 1 := by rw [hRS,hSR,one_mul]
  let V : H →L[ℂ] G := (ContinuousLinearMap.adjoint m).comp R
  refine ⟨V,?_,?_⟩
  · intro x y
    change inner ℂ ((ContinuousLinearMap.adjoint m) (R x)) ((ContinuousLinearMap.adjoint m) (R y))=inner ℂ x y
    rw [m.adjoint_inner_left]
    change inner ℂ (R x) (Q (R y))=inner ℂ x y
    have hsym : inner ℂ (R x) (Q (R y))=inner ℂ x (R (Q (R y))) := hR.isSymmetric x (Q (R y))
    rw [hsym]
    have hp := congrArg (fun T : H →L[ℂ] H => T y) hRQR
    change R (Q (R y))=y at hp
    rw [hp]
  · intro P A hP hA hma
    have hPa : ContinuousLinearMap.adjoint P=P := hP.star_eq
    have hAa : ContinuousLinearMap.adjoint A=A := hA.star_eq
    have hAdj : P.comp (ContinuousLinearMap.adjoint m)=(ContinuousLinearMap.adjoint m).comp A := by
      have h := congrArg ContinuousLinearMap.adjoint hma
      simpa only [ContinuousLinearMap.adjoint_comp,hPa,hAa] using h
    have hQA : Commute Q A := by
      change Q*A=A*Q
      ext x
      have h1 := congrArg (fun T : H →L[ℂ] G => T x) hAdj
      have h2 := congrArg (fun T : G →L[ℂ] H => T ((ContinuousLinearMap.adjoint m) x)) hma
      change m ((ContinuousLinearMap.adjoint m) (A x))=A (m ((ContinuousLinearMap.adjoint m) x))
      change P ((ContinuousLinearMap.adjoint m) x)=(ContinuousLinearMap.adjoint m) (A x) at h1
      change m (P ((ContinuousLinearMap.adjoint m) x))=A (m ((ContinuousLinearMap.adjoint m) x)) at h2
      rw [← h1,h2]
    have hSA : S*A=A*S := (hQA.cfcₙ_nnreal NNReal.sqrt).eq
    have hRA : R*A=A*R := by
      calc
        R*A = R*A*(S*R) := by rw [hSR,mul_one]
        _ = R*(A*S)*R := by noncomm_ring
        _ = R*(S*A)*R := by rw [← hSA]
        _ = (R*S)*A*R := by noncomm_ring
        _ = A*R := by rw [hRS,one_mul]
    ext x
    change P ((ContinuousLinearMap.adjoint m) (R x))=(ContinuousLinearMap.adjoint m) (R (A x))
    have hp := congrArg (fun T : H →L[ℂ] G => T (R x)) hAdj
    change P ((ContinuousLinearMap.adjoint m) (R x))=(ContinuousLinearMap.adjoint m) (A (R x)) at hp
    rw [hp]
    exact congrArg (ContinuousLinearMap.adjoint m) (congrArg (fun T : H →L[ℂ] H => T x) hRA.symm)

end QuantumBehaviors.SmallInputs
