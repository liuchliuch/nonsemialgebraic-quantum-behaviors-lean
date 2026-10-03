import QuantumBehaviors.AlmostQuantum.Definitions
import QuantumBehaviors.Models
import Mathlib.Analysis.InnerProductSpace.GramMatrix

/-!
# The genuine bipartite almost-quantum model and its finite event-Gram constraints

The operator definition is Definition1 of Navascués–Guryanova–Hoban–Acín,
arXiv:1403.4621v1, specialized to two parties and binary outcomes. Cross-party
products agree on the state; operator-wide commutation is not imposed.
-/
namespace QuantumBehaviors.AlmostQuantum
open Matrix
open scoped BigOperators ComplexOrder

/-- Binary complements satisfy the full outcome-by-outcome condition of the cited definition. -/
theorem Strategy.all_outcomes_commute_on_state {H : Type*} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : Strategy H) (i j : Input) (a b : Bool) :
    effect (s.alice i) a (effect (s.bob j) b s.state)=
      effect (s.bob j) b (effect (s.alice i) a s.state) := by
  cases a <;> cases b <;>
    simp [effect,ContinuousLinearMap.sub_apply,map_sub,s.cross_on_state]
  abel

theorem cqc_subset : Cqc ⊆ behaviors := by
  rintro p ⟨H,hN,hI,hC,s,hp⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  let t : Strategy H := {
    state := s.state, state_norm := s.state_norm, alice := s.alice, bob := s.bob
    alice_projection := s.alice_projection, bob_projection := s.bob_projection
    cross_on_state := fun i j => congrArg (fun T : H →L[ℂ] H => T s.state) (s.cross_commute i j).eq }
  exact ⟨H,inferInstance,inferInstance,inferInstance,t,hp⟩

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def Strategy.eventVector (s : Strategy H) : Event → H :=
  Sum.elim (fun _ => s.state) (Sum.elim (fun i => s.alice i s.state)
    (Sum.elim (fun j => s.bob j s.state) (fun ij => s.alice ij.1 (s.bob ij.2 s.state))))

lemma projection_twice (P : H →L[ℂ] H) (hP : IsStarProjection P) (x : H) : P (P x)=P x :=
  congrArg (fun T : H →L[ℂ] H => T x) hP.isIdempotentElem.eq

lemma Strategy.aliceRow_fixed (s : Strategy H) (i : Input) (t : Option Input) :
    s.alice i (s.eventVector (aliceRow i t))=s.eventVector (aliceRow i t) := by
  cases t with
  | none => exact projection_twice _ (s.alice_projection i) _
  | some j => exact projection_twice _ (s.alice_projection i) _

lemma Strategy.bobRow_fixed (s : Strategy H) (j : Input) (t : Option Input) :
    s.bob j (s.eventVector (bobRow j t))=s.eventVector (bobRow j t) := by
  cases t with
  | none => exact projection_twice _ (s.bob_projection j) _
  | some i =>
      change s.bob j (s.alice i (s.bob j s.state))=s.alice i (s.bob j s.state)
      rw [s.cross_on_state,projection_twice _ (s.bob_projection j)]

lemma selfadjoint_inner_left (P : H →L[ℂ] H) (hP : IsSelfAdjoint P) (x y : H) :
    inner ℂ (P x) y=inner ℂ x (P y) := hP.isSymmetric x y

noncomputable def Strategy.certificate (s : Strategy H) {p : Behavior} (hp : s.realizes p) : Certificate p where
  gram := Matrix.gram ℂ s.eventVector
  positive := Matrix.posSemidef_gram ℂ _
  normalized := by simp [Matrix.gram_apply,Strategy.eventVector,emptyEvent,inner_self_eq_norm_sq_to_K,s.state_norm]
  alice_empty := by
    intro i t
    have h := selfadjoint_inner_left (s.alice i) (s.alice_projection i).isSelfAdjoint (s.eventVector (aliceRow i t)) s.state
    rw [s.aliceRow_fixed] at h
    exact h
  alice_bob := by
    intro i t j
    have h := selfadjoint_inner_left (s.alice i) (s.alice_projection i).isSelfAdjoint (s.eventVector (aliceRow i t)) (s.bob j s.state)
    rw [s.aliceRow_fixed] at h
    exact h
  bob_empty := by
    intro j t
    have h := selfadjoint_inner_left (s.bob j) (s.bob_projection j).isSelfAdjoint (s.eventVector (bobRow j t)) s.state
    rw [s.bobRow_fixed] at h
    exact h
  bob_alice := by
    intro j t i
    have h := selfadjoint_inner_left (s.bob j) (s.bob_projection j).isSelfAdjoint (s.eventVector (bobRow j t)) (s.alice i s.state)
    rw [s.bobRow_fixed,← s.cross_on_state] at h
    exact h
  born := by
    intro i j a b
    rw [hp]
    have hψ : inner ℂ s.state s.state=1 := by simp [inner_self_eq_norm_sq_to_K,s.state_norm]
    cases a <;> cases b <;>
      simp [effect,bornValue,Matrix.gram_apply,Strategy.eventVector,emptyEvent,aliceEvent,bobEvent,jointEvent,
        ContinuousLinearMap.mul_apply,ContinuousLinearMap.sub_apply,map_sub,inner_sub_right,hψ,s.state_norm]
    ring

end QuantumBehaviors.AlmostQuantum
