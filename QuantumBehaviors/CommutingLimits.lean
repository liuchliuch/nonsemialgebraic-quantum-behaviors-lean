import QuantumBehaviors.Models
import QuantumBehaviors.UltralimitOperators
import Mathlib.Topology.Sequences

/-!
# Closedness of the commuting model from Hilbert ultralimits

The limiting Hilbert space, state and operators are built explicitly. Closure is not assumed.
-/
namespace QuantumBehaviors

open Filter UniformSpace
open scoped Topology

variable {H : ℕ → Type} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable def limitCommutingStrategy (U : Ultrafilter ℕ) (s : ∀ n, CommutingStrategy (H n)) :
    CommutingStrategy (HilbertUltralimit.Space H U) where
  state := HilbertUltralimit.state U (fun n => (s n).state) (fun n => (s n).state_norm)
  state_norm := HilbertUltralimit.state_norm U _ _
  alice i := HilbertUltralimit.operator U (fun n => (s n).alice i)
    (fun n => ((s n).alice_projection i).norm_le)
  bob j := HilbertUltralimit.operator U (fun n => (s n).bob j)
    (fun n => ((s n).bob_projection j).norm_le)
  alice_projection i := HilbertUltralimit.operator_projection U _ (fun n => (s n).alice_projection i)
  bob_projection j := HilbertUltralimit.operator_projection U _ (fun n => (s n).bob_projection j)
  cross_commute i j := HilbertUltralimit.operator_commute U _ _ _ _
    (fun n => (s n).cross_commute i j)

theorem limit_strategy_probability (U : Ultrafilter ℕ) (s : ∀ n, CommutingStrategy (H n))
    (i j : Input) (a b : Bool) :
    inner ℂ (limitCommutingStrategy U s).state
      ((effect ((limitCommutingStrategy U s).alice i) a *
        effect ((limitCommutingStrategy U s).bob j) b) (limitCommutingStrategy U s).state) =
      HilbertUltralimit.scalarLimit U (fun n => inner ℂ (s n).state
        ((effect ((s n).alice i) a * effect ((s n).bob j) b) (s n).state)) := by
  cases a <;> cases b <;>
    simp only [effect, Bool.false_eq_true, ↓reduceIte, ContinuousLinearMap.mul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply, map_sub,
      limitCommutingStrategy, HilbertUltralimit.state,
      HilbertUltralimit.operator_apply_coe, ← Completion.coe_sub,
      HilbertUltralimit.inner_completion_coe]
  all_goals unfold HilbertUltralimit.limitInner
  all_goals congr 1
  all_goals funext n
  all_goals
    change inner ℂ (s n).state
      ((s n).state - (s n).bob j (s n).state -
        ((s n).alice i (s n).state - (s n).alice i ((s n).bob j (s n).state))) = _
    congr 1
    abel

/-- Convergence of the observed finite table is preserved by the explicitly constructed strategy. -/
theorem limit_strategy_realizes (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ∀ n, CommutingStrategy (H n)) (p : ℕ → Behavior) (q : Behavior)
    (hreal : ∀ n, (s n).realizes (p n)) (hlim : Tendsto p atTop (𝓝 q)) :
    (limitCommutingStrategy U s).realizes q := by
  intro i j a b
  rw [limit_strategy_probability]
  have hcoord : Tendsto (fun n => (p n (i, j, a, b) : ℂ)) U (𝓝 (q (i, j, a, b) : ℂ)) := by
    exact Complex.continuous_ofReal.continuousAt.tendsto.comp
      (((continuous_apply (i, j, a, b)).tendsto q).comp (hlim.mono_left hU))
  apply Eq.symm
  apply HilbertUltralimit.scalarLimit_eq_of_tendsto
  simpa only [fun n => hreal n i j a b] using hcoord

/-- Every convergent sequence of commuting behaviors has a commuting realization. -/
theorem limit_mem_cqc {p : ℕ → Behavior} {q : Behavior}
    (hp : ∀ n, p n ∈ Cqc) (hlim : Tendsto p atTop (𝓝 q)) : q ∈ Cqc := by
  choose H hN hI hC s hs using hp
  letI : ∀ n, NormedAddCommGroup (H n) := hN
  letI : ∀ n, InnerProductSpace ℂ (H n) := hI
  letI : ∀ n, CompleteSpace (H n) := hC
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  refine ⟨HilbertUltralimit.Space H U, inferInstance, inferInstance, inferInstance,
    limitCommutingStrategy U s, ?_⟩
  exact limit_strategy_realizes U hU s p q hs hlim

/-- Closedness used in the `Cqa ⊆ Cqc` part of Lemma S4. -/
theorem cqc_isClosed : IsClosed Cqc := by
  apply isSeqClosed_iff_isClosed.mp
  intro p q hp hlim
  exact limit_mem_cqc hp hlim

end QuantumBehaviors
