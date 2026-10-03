import QuantumBehaviors.SmallInputs.CyclicFaithfulness

/-! Faithful cyclic realization of the actual synchronous commuting model. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma synchronous_vector_outcome (s : Scenarios.CommutingStrategy n n 2 2 H)
    {p : Scenarios.Behavior n n 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (i : Fin n) (a : Fin 2) : s.alice i a s.state = s.bob i a s.state := by
  fin_cases a
  · have hA0 : s.alice i 0 = 1 - s.alice i 1 := by
      have he : s.alice i 0 + s.alice i 1 = 1 := by simpa [Fin.sum_univ_succ] using s.alice_sum i
      exact eq_sub_iff_add_eq.mpr he
    have hB0 : s.bob i 0 = 1 - s.bob i 1 := by
      have he : s.bob i 0 + s.bob i 1 = 1 := by simpa [Fin.sum_univ_succ] using s.bob_sum i
      exact eq_sub_iff_add_eq.mpr he
    change s.alice i 0 s.state = s.bob i 0 s.state
    rw [hA0, hB0]
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      synchronous_vector s hr hp i]
  · exact synchronous_vector s hr hp i

abbrev bobFamily (s : Scenarios.CommutingStrategy n n 2 2 H) :
    Fin n × Fin 2 → H →L[ℂ] H := fun ia => s.bob ia.1 ia.2

noncomputable abbrev strategyCyclicSpace (s : Scenarios.CommutingStrategy n n 2 2 H) :=
  cyclicSpaceAny (bobFamily s) s.state

lemma alice_preserves_strategyCyclicSpace (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (i : Fin n) (a : Fin 2) :
    ∀ x ∈ strategyCyclicSpace s, s.alice i a x ∈ strategyCyclicSpace s :=
  synchronized_preserves_cyclicAny (fun ⟨j,b⟩ => s.cross_commute i j a b) (i,a) (hsync i a)

/-- Restriction to the closed cyclic subspace preserves the full genuine strategy. -/
noncomputable def cyclicStrategy (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) :
    Scenarios.CommutingStrategy n n 2 2 (strategyCyclicSpace s) where
  state := cyclicState (bobFamily s) s.state
  state_norm := s.state_norm
  alice i a := QuantumBehaviors.restrictOperator _ (s.alice i a)
    (alice_preserves_strategyCyclicSpace s hsync i a)
  bob j b := cyclicGenerator (bobFamily s) s.state (j,b)
  alice_projection i a := QuantumBehaviors.restrictOperator_projection _ _ _ (s.alice_projection i a)
  bob_projection j b := QuantumBehaviors.restrictOperator_projection _ _ _ (s.bob_projection j b)
  alice_sum i := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ((∑ a, QuantumBehaviors.restrictOperator _ (s.alice i a) _) x : H) = (x : H)
    simp only [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
    change (∑ a, s.alice i a (x : H)) = (x : H)
    rw [← ContinuousLinearMap.sum_apply, s.alice_sum, ContinuousLinearMap.one_apply]
  bob_sum j := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    change ((∑ b, cyclicGenerator (bobFamily s) s.state (j,b)) x : H) = (x : H)
    simp only [ContinuousLinearMap.sum_apply, Submodule.coe_sum]
    change (∑ b, s.bob j b (x : H)) = (x : H)
    rw [← ContinuousLinearMap.sum_apply, s.bob_sum, ContinuousLinearMap.one_apply]
  cross_commute i j a b := by
    apply ContinuousLinearMap.ext
    intro x
    apply Subtype.ext
    exact congrArg (fun T : H →L[ℂ] H => T x) (s.cross_commute i j a b).eq

lemma cyclicStrategy_realizes (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    {p : Scenarios.Behavior n n 2 2} (hr : s.realizes p) :
    (cyclicStrategy s hsync).realizes p := hr

lemma cyclicStrategy_commutant_faithful (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    {X : strategyCyclicSpace s →L[ℂ] strategyCyclicSpace s}
    (hX : X ∈ aliceAlgebra (cyclicStrategy s hsync))
    (hzero : X (cyclicStrategy s hsync).state = 0) : X = 0 := by
  apply cyclic_commutant_faithful (bobFamily s) s.state X _ hzero
  intro ia
  apply Commute.symm
  apply commute_adjoin (K := ℂ) _ X hX
  rintro P ⟨i,rfl⟩
  exact ((cyclicStrategy s hsync).cross_commute i ia.1 1 ia.2).symm

lemma vectorFunctional_star_mul (ψ : H) (X : H →L[ℂ] H) :
    vectorFunctional ψ (star X * X) = inner ℂ (X ψ) (X ψ) := by
  exact ContinuousLinearMap.adjoint_inner_right X ψ (X ψ)

/-- No faithfulness assumption is imposed on the input state: it is proved after reduction. -/
theorem cyclicStrategy_trace_faithful (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    {X : strategyCyclicSpace s →L[ℂ] strategyCyclicSpace s}
    (hX : X ∈ aliceAlgebra (cyclicStrategy s hsync))
    (hzero : vectorFunctional (cyclicStrategy s hsync).state (star X * X) = 0) : X = 0 := by
  rw [vectorFunctional_star_mul] at hzero
  exact cyclicStrategy_commutant_faithful s hsync hX ((inner_self_eq_zero (𝕜 := ℂ)).mp hzero)

end QuantumBehaviors.SmallInputs
