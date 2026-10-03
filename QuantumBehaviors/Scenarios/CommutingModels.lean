import QuantumBehaviors.Scenarios.FiniteModels

/-! Input repetition and outcome merging in the arbitrary-Hilbert commuting model. -/
namespace QuantumBehaviors.Scenarios

open scoped BigOperators

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def operatorBorn (ψ : H) : (H →L[ℂ] H) →ₗ[ℂ] (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun A := {
    toFun := fun B => inner ℂ ψ ((A * B) ψ)
    map_add' := fun B C => by simp [mul_add, inner_add_right]
    map_smul' := fun c B => by simp [mul_smul_comm, inner_smul_right] }
  map_add' A B := by ext C; simp [add_mul, inner_add_right]
  map_smul' c A := by ext B; simp [smul_mul_assoc, inner_smul_right]

@[simp] theorem operatorBorn_apply (ψ : H) (A B : H →L[ℂ] H) :
    operatorBorn ψ A B = inner ℂ ψ ((A * B) ψ) := rfl

lemma effect_commute {R : Type*} [Ring R] {A B : R} (h : Commute A B) (a b : Bool) :
    Commute (effect A a) (effect B b) := by
  change effect A a * effect B b = effect B b * effect A a
  cases a <;> cases b <;> dsimp [effect] <;> noncomm_ring [h.eq]

lemma pad_effect_projection {m : ℕ} (hm : 2 ≤ m) (A : H →L[ℂ] H)
    (hA : IsStarProjection A) (a : Fin m) : IsStarProjection (padBinary hm (effect A) a) := by
  unfold padBinary
  split_ifs
  · exact hA.one_sub
  · exact hA
  · exact IsStarProjection.zero _

lemma pad_effect_commute {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n) {A B : H →L[ℂ] H}
    (h : Commute A B) (a : Fin m) (b : Fin n) :
    Commute (padBinary hm (effect A) a) (padBinary hn (effect B) b) := by
  unfold padBinary
  split_ifs <;> first | exact effect_commute h _ _ | exact Commute.zero_left _ | exact Commute.zero_right _

variable {nA nB mA mB : ℕ}

theorem extend_cqc (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Set.MapsTo (extend (nA := nA) (nB := nB) hmA hmB) QuantumBehaviors.Cqc (Cqc nA nB mA mB) := by
  rintro p ⟨H, hN, hI, hC, s, hs⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  let t : CommutingStrategy nA nB mA mB H := {
    state := s.state
    state_norm := s.state_norm
    alice := fun i => padBinary hmA (effect (s.alice (extendInput i)))
    bob := fun j => padBinary hmB (effect (s.bob (extendInput j)))
    alice_projection := fun i a => pad_effect_projection hmA _ (s.alice_projection _) a
    alice_sum := fun i => pad_effect_sum hmA _
    bob_projection := fun j b => pad_effect_projection hmB _ (s.bob_projection _) b
    bob_sum := fun j => pad_effect_sum hmB _
    cross_commute := fun i j a b => pad_effect_commute hmA hmB (s.cross_commute _ _) a b }
  refine ⟨H, inferInstance, inferInstance, inferInstance, t, ?_⟩
  intro i j a b
  rw [extend_complex_entry]
  change _ = operatorBorn s.state (padBinary hmA (effect (s.alice (extendInput i))) a)
    (padBinary hmB (effect (s.bob (extendInput j))) b)
  rw [pad_bilinear]
  congr 1
  funext x
  congr 1
  funext y
  exact hs _ _ x y

theorem retract_cqc (hnA : 4 ≤ nA) (hnB : 4 ≤ nB) (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) :
    Set.MapsTo (retract hnA hnB hmA hmB) (Cqc nA nB mA mB) QuantumBehaviors.Cqc := by
  rintro p ⟨H, hN, hI, hC, s, hs⟩
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  let t : QuantumBehaviors.CommutingStrategy H := {
    state := s.state
    state_norm := s.state_norm
    alice := fun i => s.alice (originalInput hnA i) (outcomeOne hmA)
    bob := fun j => s.bob (originalInput hnB j) (outcomeOne hmB)
    alice_projection := fun i => s.alice_projection _ _
    bob_projection := fun j => s.bob_projection _ _
    cross_commute := fun i j => s.cross_commute _ _ _ _ }
  refine ⟨H, inferInstance, inferInstance, inferInstance, t, ?_⟩
  intro i j a b
  rw [retract_complex_entry]
  simp only [CommutingStrategy.realizes] at hs
  simp_rw [hs]
  change mergeBinary hmA (fun x => mergeBinary hmB
    (fun y => operatorBorn s.state (s.alice (originalInput hnA i) x)
      (s.bob (originalInput hnB j) y)) b) a = _
  rw [merge_bilinear, merge_binary_effect hmA _ (s.alice_sum _),
    merge_binary_effect hmB _ (s.bob_sum _)]
  rfl

end QuantumBehaviors.Scenarios
