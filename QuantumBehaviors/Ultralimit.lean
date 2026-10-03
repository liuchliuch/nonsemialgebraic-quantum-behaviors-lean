import Mathlib.Analysis.InnerProductSpace.Completion
import Mathlib.Analysis.Normed.Lp.lpSpace
import Mathlib.Topology.Algebra.LinearMapCompletion
import Mathlib.Topology.Compactness.Compact
import Mathlib.Order.Filter.Ultrafilter.Basic

/-!
# A Hilbert-space ultralimit of bounded vector sequences

This gives a proof-equivalent compactness route for Lemma S4. It uses an ultrafilter
refining the original convergent sequence and the completion of the limiting positive
semidefinite inner product. It does not postulate a GNS representation or closure of Cqc.
-/

namespace QuantumBehaviors
namespace HilbertUltralimit

noncomputable section

open Filter Set UniformSpace
open scoped Topology ENNReal

noncomputable def scalarLimit (U : Ultrafilter ℕ) (f : ℕ → ℂ) : ℂ :=
  limUnder (U : Filter ℕ) f

theorem bounded_has_limit (U : Ultrafilter ℕ) {f : ℕ → ℂ}
    (hf : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C) : ∃ z : ℂ, Tendsto f U (𝓝 z) := by
  obtain ⟨C, hC⟩ := hf
  have hmem : Metric.closedBall (0 : ℂ) C ∈ U.map f := by
    change {n | f n ∈ Metric.closedBall (0 : ℂ) C} ∈ (U : Filter ℕ)
    apply Filter.Eventually.of_forall
    intro n
    simpa [Metric.mem_closedBall, dist_zero_right] using hC n
  obtain ⟨z, hz, hlim⟩ := (isCompact_closedBall (0 : ℂ) C).ultrafilter_le_nhds' (U.map f) hmem
  exact ⟨z, hlim⟩

theorem scalarLimit_tendsto (U : Ultrafilter ℕ) {f : ℕ → ℂ}
    (hf : ∃ C : ℝ, ∀ n, ‖f n‖ ≤ C) : Tendsto f U (𝓝 (scalarLimit U f)) :=
  tendsto_nhds_limUnder (bounded_has_limit U hf)

theorem scalarLimit_eq_of_tendsto (U : Ultrafilter ℕ) {f : ℕ → ℂ} {z : ℂ}
    (hf : Tendsto f U (𝓝 z)) : scalarLimit U f = z := hf.limUnder_eq

variable (H : ℕ → Type*) [∀ n, NormedAddCommGroup (H n)] [∀ n, InnerProductSpace ℂ (H n)]

/-- Bounded vector sequences, with a new seminorm supplied by the limiting inner product. -/
def PreHilbert (U : Ultrafilter ℕ) := lp H ∞

variable (U : Ultrafilter ℕ)

instance : AddCommGroup (PreHilbert H U) := inferInstanceAs (AddCommGroup (lp H ∞))
instance : Module ℂ (PreHilbert H U) := inferInstanceAs (Module ℂ (lp H ∞))

noncomputable def toBounded : PreHilbert H U ≃ₗ[ℂ] lp H ∞ := LinearEquiv.refl ℂ _

theorem bounded_inner (x y : PreHilbert H U) :
    ∃ C : ℝ, ∀ n, ‖inner ℂ (toBounded H U x n) (toBounded H U y n)‖ ≤ C := by
  refine ⟨‖toBounded H U x‖ * ‖toBounded H U y‖, ?_⟩
  intro n
  exact (norm_inner_le_norm _ _).trans (mul_le_mul
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (toBounded H U x) n)
    (lp.norm_apply_le_norm ENNReal.top_ne_zero (toBounded H U y) n)
    (norm_nonneg _) (norm_nonneg _))

noncomputable def limitInner (x y : PreHilbert H U) : ℂ :=
  scalarLimit U fun n => inner ℂ (toBounded H U x n) (toBounded H U y n)

theorem tendsto_inner (x y : PreHilbert H U) :
    Tendsto (fun n => inner ℂ (toBounded H U x n) (toBounded H U y n)) U
      (𝓝 (limitInner H U x y)) := scalarLimit_tendsto U (bounded_inner H U x y)

noncomputable abbrev preInnerCore : PreInnerProductSpace.Core ℂ (PreHilbert H U) where
  inner := limitInner H U
  conj_inner_symm x y := by
    have h := (tendsto_inner H U y x).star
    have h' := tendsto_inner H U x y
    simp only [← starRingEnd_apply, inner_conj_symm] at h
    exact tendsto_nhds_unique h h'
  re_inner_nonneg x := by
    exact le_of_tendsto_of_tendsto tendsto_const_nhds
      (Complex.continuous_re.continuousAt.tendsto.comp (tendsto_inner H U x x))
      (Filter.Eventually.of_forall fun n => inner_self_nonneg (𝕜 := ℂ) (x := toBounded H U x n))
  add_left x y z := by
    have h := (tendsto_inner H U x z).add (tendsto_inner H U y z)
    have h' := tendsto_inner H U (x + y) z
    apply tendsto_nhds_unique h' 
    simpa [toBounded, lp.coeFn_add, inner_add_left] using h
  smul_left x y c := by
    have h := (tendsto_const_nhds (x := (starRingEnd ℂ) c)).mul (tendsto_inner H U x y)
    have h' := tendsto_inner H U (c • x) y
    apply tendsto_nhds_unique h'
    simpa [toBounded, lp.coeFn_smul, inner_smul_left] using h

noncomputable instance : SeminormedAddCommGroup (PreHilbert H U) :=
  InnerProductSpace.Core.toSeminormedAddCommGroup (c := preInnerCore H U)

noncomputable instance : InnerProductSpace ℂ (PreHilbert H U) :=
  InnerProductSpace.ofCore (preInnerCore H U)

/-- Hilbert-space completion of the limiting pre-inner-product space. -/
abbrev Space := Completion (PreHilbert H U)

@[simp] theorem inner_preHilbert (x y : PreHilbert H U) :
    inner ℂ x y = limitInner H U x y := rfl

@[simp] theorem inner_completion_coe (x y : PreHilbert H U) :
    inner ℂ (x : Space H U) (y : Space H U) = limitInner H U x y := by
  exact Completion.inner_coe x y

end

end HilbertUltralimit
end QuantumBehaviors
