import QuantumBehaviors.SmallInputs.CompactCommuting

/-! Reading real probabilities and synchronous moments from an actual strategy. -/

namespace QuantumBehaviors.SmallInputs

variable {nA nB mA mB : ℕ} {H : Type*} [NormedAddCommGroup H]
  [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def strategyBehavior (s : Scenarios.CommutingStrategy nA nB mA mB H) :
    Scenarios.Behavior nA nB mA mB :=
  fun ⟨i,j,a,b⟩ => (inner ℂ s.state ((s.alice i a * s.bob j b) s.state)).re

lemma strategyBehavior_realizes (s : Scenarios.CommutingStrategy nA nB mA mB H) :
    s.realizes (strategyBehavior s) := by
  intro i j a b
  have hP := (s.alice_projection i a).mul (s.bob_projection j b) (s.cross_commute i j a b)
  have hi : (inner ℂ s.state ((s.alice i a * s.bob j b) s.state)).im = 0 := by
    exact hP.isSelfAdjoint.isSymmetric.im_inner_self_apply s.state
  apply Complex.ext
  · rfl
  · exact hi.symm

lemma strategyBehavior_eq {s : Scenarios.CommutingStrategy nA nB mA mB H}
    {p : Scenarios.Behavior nA nB mA mB} (hr : s.realizes p) : strategyBehavior s = p := by
  funext x
  rcases x with ⟨i,j,a,b⟩
  exact (congrArg Complex.re (hr i j a b)).symm

lemma binary_projection_orthogonal {R : Type*} [Ring R] (P : Fin 2 → R)
    (hs : ∑ a, P a = 1) (h1 : IsIdempotentElem (P 1)) {a b : Fin 2} (hab : a ≠ b) :
    P a * P b = 0 := by
  have h0 : P 0 = 1 - P 1 := by
    apply eq_sub_iff_add_eq.mpr
    simpa [Fin.sum_univ_succ] using hs
  fin_cases a <;> fin_cases b <;> simp_all [h0, mul_sub, sub_mul, h1.eq]

lemma strategyBehavior_synchronous {n : ℕ} (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) :
    Scenarios.Synchronous (strategyBehavior s) := by
  intro i a b hab
  have ho := binary_projection_orthogonal (s.alice i) (s.alice_sum i)
    (s.alice_projection i 1).isIdempotentElem hab
  have he : (s.alice i a * s.bob i b) s.state = 0 := by
    rw [ContinuousLinearMap.mul_apply, ← hsync, ← ContinuousLinearMap.mul_apply, ho]
    rfl
  simp only [strategyBehavior, he, inner_zero_right, Complex.zero_re]

lemma strategyBehavior_alice_moment {n : ℕ} (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (i j : Fin n) (a b : Fin 2) :
    strategyBehavior s (i,j,a,b) = (vectorFunctional s.state (s.alice i a * s.alice j b)).re := by
  simp only [strategyBehavior, vectorFunctional_apply, ContinuousLinearMap.mul_apply, hsync]

lemma strategyBehavior_mem_cqc {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H]
    (s : Scenarios.CommutingStrategy nA nB mA mB H) :
    strategyBehavior s ∈ Scenarios.Cqc nA nB mA mB :=
  ⟨H, inferInstance, inferInstance, inferInstance, s, strategyBehavior_realizes s⟩

lemma strategyBehavior_mem_synchronous {n : ℕ} {H : Type} [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] [CompleteSpace H] (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) :
    strategyBehavior s ∈ Scenarios.synchronousSet n .qc :=
  ⟨strategyBehavior_mem_cqc s, strategyBehavior_synchronous s hsync⟩

end QuantumBehaviors.SmallInputs
