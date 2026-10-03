import QuantumBehaviors.SmallInputs.UnitaryVariation
import Mathlib.Algebra.Star.UnitaryStarAlgAut

/-! Mirrored exponential operators for synchronized left/right actions. -/

namespace QuantumBehaviors.SmallInputs

open NormedSpace

noncomputable section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma synchronized_powers {K L : H →L[ℂ] H} {ψ : H}
    (hKL : Commute K L) (hψ : K ψ = L ψ) (n : ℕ) : (K ^ n) ψ = (L ^ n) ψ := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ, ContinuousLinearMap.mul_apply, hψ]
    have hc := congrArg (fun T : H →L[ℂ] H => T ψ) (hKL.pow_left n).eq
    change (K ^ n) (L ψ) = L ((K ^ n) ψ) at hc
    rw [hc, ih, ← ContinuousLinearMap.mul_apply, ← pow_succ']

/-- Exponentiation preserves the shared state-vector action of commuting mirrors. -/
lemma synchronized_exponentials {K L : H →L[ℂ] H} {ψ : H}
    (hKL : Commute K L) (hψ : K ψ = L ψ) : exp K ψ = exp L ψ := by
  let ev : (H →L[ℂ] H) →L[ℂ] H := ContinuousLinearMap.apply ℂ H ψ
  have hK := (exp_series_hasSum_exp' (𝕂 := ℂ) K).map ev ev.continuous
  have hL := (exp_series_hasSum_exp' (𝕂 := ℂ) L).map ev ev.continuous
  have he : (fun n : ℕ => ev ((n.factorial : ℂ)⁻¹ • K ^ n)) =
      (fun n : ℕ => ev ((n.factorial : ℂ)⁻¹ • L ^ n)) := by
    funext n
    change ((n.factorial : ℂ)⁻¹) • (K ^ n) ψ = ((n.factorial : ℂ)⁻¹) • (L ^ n) ψ
    rw [synchronized_powers hKL hψ n]
  simp only [Function.comp_def] at hK hL
  rw [he] at hK
  exact hK.unique hL

/-- Exponentiating a real multiple of a skew-adjoint operator gives a genuine unitary. -/
noncomputable def skewUnitary (K : H →L[ℂ] H) (hK : star K = -K) (t : ℝ) :
    unitary (H →L[ℂ] H) :=
  letI : NormedAlgebra ℚ (H →L[ℂ] H) := NormedAlgebra.restrictScalars ℚ ℂ _
  ⟨exp ((t : ℂ) • K), exp_mem_unitary_of_mem_skewAdjoint (by
    change star ((t : ℂ) • K) = -((t : ℂ) • K)
    simp [hK])⟩

@[simp] lemma skewUnitary_coe (K : H →L[ℂ] H) (hK : star K = -K) (t : ℝ) :
    (skewUnitary K hK t : H →L[ℂ] H) = exp ((t : ℂ) • K) := rfl

@[simp] lemma skewUnitary_star (K : H →L[ℂ] H) (hK : star K = -K) (t : ℝ) :
    ((star (skewUnitary K hK t) : unitary (H →L[ℂ] H)) : H →L[ℂ] H) = exp ((t : ℂ) • (-K)) := by
  change star (exp ((t : ℂ) • K)) = _
  rw [star_exp]
  simp [hK]

lemma synchronized_skewUnitary {K L : H →L[ℂ] H} {ψ : H}
    (hK : star K = -K) (hL : star L = -L) (hKL : Commute K L)
    (hψ : K ψ = L ψ) (t : ℝ) :
    (skewUnitary K hK t : H →L[ℂ] H) ψ = (skewUnitary L hL t : H →L[ℂ] H) ψ ∧
      (star (skewUnitary K hK t) : H →L[ℂ] H) ψ =
        (star (skewUnitary L hL t) : H →L[ℂ] H) ψ := by
  constructor
  · apply synchronized_exponentials ((hKL.smul_left (t : ℂ)).smul_right (t : ℂ))
    simpa only [ContinuousLinearMap.smul_apply] using congrArg ((t : ℂ) • ·) hψ
  · change (star (exp ((t : ℂ) • K))) ψ = (star (exp ((t : ℂ) • L))) ψ
    rw [star_exp, star_exp]
    simp only [star_smul, Complex.star_def, Complex.conj_ofReal, hK, hL]
    apply synchronized_exponentials (((hKL.neg_left.neg_right).smul_left (t : ℂ)).smul_right (t : ℂ))
    simpa only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.neg_apply] using
      congrArg (fun x : H => (t : ℂ) • (-x)) hψ

end
end QuantumBehaviors.SmallInputs
