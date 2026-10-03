import QuantumBehaviors.UltralimitOperators

/-! Finite operator identities are preserved by the constructed Hilbert ultralimit. -/
namespace QuantumBehaviors.HilbertUltralimit

open UniformSpace
open scoped BigOperators

variable {H : ℕ → Type*} [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]
variable {ι : Type*} [Fintype ι]

theorem operator_sum_one (U : Ultrafilter ℕ) (T : ι → ∀ n, H n →L[ℂ] H n)
    (hT : ∀ i n, ‖T i n‖ ≤ 1) (hsum : ∀ n, (∑ i, T i n) = 1) :
    (∑ i, operator U (T i) (hT i)) = (1 : Space H U →L[ℂ] Space H U) := by
  ext x
  induction x using Completion.induction_on with
  | hp => exact isClosed_eq (by fun_prop) (by fun_prop)
  | ih x =>
      simp only [ContinuousLinearMap.sum_apply, operator_apply_coe, ContinuousLinearMap.one_apply]
      have hpre : (∑ i, pointwiseLinear U (T i) (hT i) x) = x := by
        apply (toBounded H U).injective
        apply lp.ext
        funext n
        have h := congrArg (fun A : H n →L[ℂ] H n => A (toBounded H U x n)) (hsum n)
        simpa only [map_sum, lp.coeFn_sum, Finset.sum_apply, pointwiseLinear_apply,
          ContinuousLinearMap.sum_apply, ContinuousLinearMap.one_apply] using h
      change (∑ i, (Completion.toComplL : PreHilbert H U →L[ℂ] Space H U)
        (pointwiseLinear U (T i) (hT i) x)) = (Completion.toComplL : PreHilbert H U →L[ℂ] Space H U) x
      rw [← map_sum, hpre]

end QuantumBehaviors.HilbertUltralimit
