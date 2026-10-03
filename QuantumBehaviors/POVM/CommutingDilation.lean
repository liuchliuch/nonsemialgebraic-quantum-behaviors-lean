import QuantumBehaviors.POVM.Definitions
import QuantumBehaviors.POVM.SeparateAncillas
import QuantumBehaviors.Models
import QuantumBehaviors.Scenarios.Basic

/-! Remark S5 on arbitrary complex Hilbert spaces, with separate ancillas and exact joint probabilities. -/
namespace QuantumBehaviors.POVM
open Matrix
open scoped BigOperators ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def dilatedAlice (E : H →L[ℂ] H) : Amplification Ancilla H →L[ℂ] Amplification Ancilla H :=
  matrixOperator (onAlice (dilationEntries E))
noncomputable def dilatedBob (F : H →L[ℂ] H) : Amplification Ancilla H →L[ℂ] Amplification Ancilla H :=
  matrixOperator (onBob (dilationEntries F))

lemma dilatedAlice_projection (E : H →L[ℂ] H) (hE : 0 ≤ E) (hE0 : 0 ≤ 1-E) :
    IsStarProjection (dilatedAlice E) := matrixOperator_projection (onAlice_projection (dilationEntries_projection E hE hE0))
lemma dilatedBob_projection (E : H →L[ℂ] H) (hE : 0 ≤ E) (hE0 : 0 ≤ 1-E) :
    IsStarProjection (dilatedBob E) := matrixOperator_projection (onBob_projection (dilationEntries_projection E hE hE0))
lemma dilated_cross_commute {E F : H →L[ℂ] H} (h : Commute E F) : Commute (dilatedAlice E) (dilatedBob F) :=
  matrixOperator_commute (separateAncillas_commute _ _ (dilationEntries_commute h))

lemma matrixOperator_effect {J : Type*} [Fintype J] [DecidableEq J]
    (M : Matrix J J (H →L[ℂ] H)) (a : Bool) :
    effect (matrixOperator M) a=matrixOperator (effect M a) := by
  cases a <;> simp [effect]

lemma onAlice_effect (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) (a : Bool) :
    effect (onAlice M) a=onAlice (effect M a) := by cases a <;> simp [effect]
lemma onBob_effect (M : Matrix (Fin 2) (Fin 2) (H →L[ℂ] H)) (a : Bool) :
    effect (onBob M) a=onBob (effect M a) := by cases a <;> simp [effect]

lemma effect_dilation_initial (E : H →L[ℂ] H) (a : Bool) :
    effect (dilationEntries E) a 0 0=effect E a := by cases a <;> simp [effect,dilationEntries]

/-- Compression on the common initial ancilla vector preserves every binary joint expectation. -/
theorem dilated_joint_expectation (E F : H →L[ℂ] H) (ψ : H) (a b : Bool) :
    inner ℂ (initial (0,0) ψ) ((effect (dilatedAlice E) a*effect (dilatedBob F) b) (initial (0,0) ψ)) =
      inner ℂ ψ ((effect E a*effect F b) ψ) := by
  have hprod : effect (dilatedAlice E) a*effect (dilatedBob F) b =
      matrixOperator (onAlice (effect (dilationEntries E) a)*onBob (effect (dilationEntries F) b)) := by
    change effect (matrixOperator (onAlice (dilationEntries E))) a *
      effect (matrixOperator (onBob (dilationEntries F))) b = _
    rw [matrixOperator_effect,matrixOperator_effect,onAlice_effect,onBob_effect,← matrixOperator_mul]
  rw [hprod,initial_expectation,onAlice_mul_onBob,effect_dilation_initial,effect_dilation_initial]

noncomputable def BinaryStrategy.toCommuting (s : BinaryStrategy Input Input H) :
    CommutingStrategy (Amplification Ancilla H) where
  state := initial (0,0) s.state
  state_norm := (initial_norm _ _).trans s.state_norm
  alice := fun i => dilatedAlice (s.alice i)
  bob := fun j => dilatedBob (s.bob j)
  alice_projection := fun i => dilatedAlice_projection _ (s.alice_nonneg i) (s.alice_complement_nonneg i)
  bob_projection := fun j => dilatedBob_projection _ (s.bob_nonneg j) (s.bob_complement_nonneg j)
  cross_commute := fun i j => dilated_cross_commute (s.cross_commute i j)

theorem BinaryStrategy.toCommuting_realizes (s : BinaryStrategy Input Input H) {p : Behavior}
    (hp : s.realizes p) : s.toCommuting.realizes p := by
  intro i j a b
  change (p (i,j,a,b) : ℂ)=inner ℂ (initial (0,0) s.state)
    ((effect (dilatedAlice (s.alice i)) a*effect (dilatedBob (s.bob j)) b) (initial (0,0) s.state))
  rw [dilated_joint_expectation]
  exact hp i j a b

/-- The commuting binary-POVM formulation uses positive contractions on an arbitrary Hilbert space. -/
theorem commuting_povm_subset_cqc : CqcPOVM ⊆ Cqc := by
  rintro p ⟨H,hN,hI,hC,s,hp⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  exact ⟨Amplification Ancilla H,inferInstance,inferInstance,inferInstance,s.toCommuting,s.toCommuting_realizes hp⟩

theorem cqc_subset_commuting_povm : Cqc ⊆ CqcPOVM := by
  rintro p ⟨H,hN,hI,hC,s,hp⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  let t : BinaryStrategy Input Input H := {
    state := s.state, state_norm := s.state_norm, alice := s.alice, bob := s.bob
    alice_nonneg := fun i => (s.alice_projection i).nonneg
    alice_complement_nonneg := fun i => (s.alice_projection i).one_sub.nonneg
    bob_nonneg := fun j => (s.bob_projection j).nonneg
    bob_complement_nonneg := fun j => (s.bob_projection j).one_sub.nonneg
    cross_commute := s.cross_commute }
  exact ⟨H,inferInstance,inferInstance,inferInstance,t,hp⟩

/-- S5: binary commuting POVMs and commuting projections describe exactly the same behaviors. -/
theorem remark_S5 : CqcPOVM=Cqc := Set.Subset.antisymm commuting_povm_subset_cqc cqc_subset_commuting_povm

noncomputable def BinaryStrategy.toScenario {nA nB : ℕ} (s : BinaryStrategy (Fin nA) (Fin nB) H) :
    Scenarios.CommutingStrategy nA nB 2 2 (Amplification Ancilla H) where
  state := initial (0,0) s.state
  state_norm := (initial_norm _ _).trans s.state_norm
  alice := fun i a => effect (dilatedAlice (s.alice i)) (decide (a=1))
  bob := fun j b => effect (dilatedBob (s.bob j)) (decide (b=1))
  alice_projection := by
    intro i a
    have h := dilatedAlice_projection _ (s.alice_nonneg i) (s.alice_complement_nonneg i)
    fin_cases a
    · exact h.one_sub
    · exact h
  alice_sum := by intro i; simp [Fin.sum_univ_two,effect]
  bob_projection := by
    intro j b
    have h := dilatedBob_projection _ (s.bob_nonneg j) (s.bob_complement_nonneg j)
    fin_cases b
    · exact h.one_sub
    · exact h
  bob_sum := by intro j; simp [Fin.sum_univ_two,effect]
  cross_commute := by
    intro i j a b
    have h := dilated_cross_commute (s.cross_commute i j)
    fin_cases a <;> fin_cases b
    · exact commute_one_sub_right (commute_one_sub_left h)
    · exact commute_one_sub_left h
    · exact commute_one_sub_right h
    · exact h

/-- The same verified ancilla construction works for every finite pair of input counts. -/
theorem BinaryStrategy.toScenario_realizes {nA nB : ℕ}
    (s : BinaryStrategy (Fin nA) (Fin nB) H) (p : Scenarios.Behavior nA nB 2 2)
    (hp : ∀ i j a b, (p (i,j,a,b) : ℂ)=inner ℂ s.state
      ((effect (s.alice i) (decide (a=1))*effect (s.bob j) (decide (b=1))) s.state)) :
    s.toScenario.realizes p := by
  intro i j a b
  change (p (i,j,a,b) : ℂ)=inner ℂ (initial (0,0) s.state)
    ((effect (dilatedAlice (s.alice i)) (decide (a=1))*
      effect (dilatedBob (s.bob j)) (decide (b=1))) (initial (0,0) s.state))
  rw [dilated_joint_expectation]
  exact hp i j a b

end QuantumBehaviors.POVM
