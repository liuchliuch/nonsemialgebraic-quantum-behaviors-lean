import QuantumBehaviors.Scenarios.Basic
import QuantumBehaviors.UltralimitSums
import Mathlib.Topology.Sequences

/-! Closedness of the commuting model in every fixed finite scenario. -/
namespace QuantumBehaviors.Scenarios

open Filter UniformSpace
open scoped Topology

variable {nA nB mA mB : ℕ} {H : ℕ → Type} [∀ n, NormedAddCommGroup (H n)]
  [∀ n, InnerProductSpace ℂ (H n)] [∀ n, CompleteSpace (H n)]

noncomputable def limitStrategy (U : Ultrafilter ℕ)
    (s : ∀ n, CommutingStrategy nA nB mA mB (H n)) :
    CommutingStrategy nA nB mA mB (HilbertUltralimit.Space H U) where
  state := HilbertUltralimit.state U (fun n => (s n).state) (fun n => (s n).state_norm)
  state_norm := HilbertUltralimit.state_norm U _ _
  alice i a := HilbertUltralimit.operator U (fun n => (s n).alice i a)
    (fun n => ((s n).alice_projection i a).norm_le)
  bob j b := HilbertUltralimit.operator U (fun n => (s n).bob j b)
    (fun n => ((s n).bob_projection j b).norm_le)
  alice_projection i a := HilbertUltralimit.operator_projection U _
    (fun n => (s n).alice_projection i a)
  bob_projection j b := HilbertUltralimit.operator_projection U _
    (fun n => (s n).bob_projection j b)
  alice_sum i := HilbertUltralimit.operator_sum_one U _ _ (fun n => (s n).alice_sum i)
  bob_sum j := HilbertUltralimit.operator_sum_one U _ _ (fun n => (s n).bob_sum j)
  cross_commute i j a b := HilbertUltralimit.operator_commute U _ _ _ _
    (fun n => (s n).cross_commute i j a b)

theorem limitStrategy_probability (U : Ultrafilter ℕ)
    (s : ∀ n, CommutingStrategy nA nB mA mB (H n))
    (i : Fin nA) (j : Fin nB) (a : Fin mA) (b : Fin mB) :
    inner ℂ (limitStrategy U s).state
      (((limitStrategy U s).alice i a * (limitStrategy U s).bob j b) (limitStrategy U s).state) =
      HilbertUltralimit.scalarLimit U (fun n => inner ℂ (s n).state
        (((s n).alice i a * (s n).bob j b) (s n).state)) := by
  simp only [limitStrategy, HilbertUltralimit.state, ContinuousLinearMap.mul_apply,
    HilbertUltralimit.operator_apply_coe, HilbertUltralimit.inner_completion_coe]
  rfl

theorem limitStrategy_realizes (U : Ultrafilter ℕ) (hU : (U : Filter ℕ) ≤ atTop)
    (s : ∀ n, CommutingStrategy nA nB mA mB (H n)) (p : ℕ → Behavior nA nB mA mB)
    (q : Behavior nA nB mA mB) (hreal : ∀ n, (s n).realizes (p n))
    (hlim : Tendsto p atTop (𝓝 q)) : (limitStrategy U s).realizes q := by
  intro i j a b
  rw [limitStrategy_probability]
  apply Eq.symm
  apply HilbertUltralimit.scalarLimit_eq_of_tendsto
  have hcoord : Tendsto (fun n => (p n (i, j, a, b) : ℂ)) U (𝓝 (q (i, j, a, b) : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp
      (((continuous_apply (i, j, a, b)).tendsto q).comp (hlim.mono_left hU))
  simpa only [fun n => hreal n i j a b] using hcoord

theorem cqc_isClosed (nA nB mA mB : ℕ) : IsClosed (Cqc nA nB mA mB) := by
  apply isSeqClosed_iff_isClosed.mp
  intro p q hp hlim
  choose H hN hI hC s hs using hp
  letI : ∀ n, NormedAddCommGroup (H n) := hN
  letI : ∀ n, InnerProductSpace ℂ (H n) := hI
  letI : ∀ n, CompleteSpace (H n) := hC
  let U : Ultrafilter ℕ := Ultrafilter.of atTop
  have hU : (U : Filter ℕ) ≤ atTop := Ultrafilter.of_le atTop
  exact ⟨HilbertUltralimit.Space H U, inferInstance, inferInstance, inferInstance,
    limitStrategy U s, limitStrategy_realizes U hU s p q hs hlim⟩

end QuantumBehaviors.Scenarios
