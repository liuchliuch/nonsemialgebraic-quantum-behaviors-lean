import QuantumBehaviors.SmallInputs.ConjugateStrategy
import QuantumBehaviors.SmallInputs.StrategyBehavior

/-! Actual admissible one-input exponential paths, with arbitrary real interaction weights. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators
open NormedSpace

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def weightedAlice (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ) :
    H →L[ℂ] H := ∑ i, (d i : ℂ) • s.alice i 1
noncomputable def weightedBob (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ) :
    H →L[ℂ] H := ∑ i, (d i : ℂ) • s.bob i 1

lemma weightedAlice_selfadjoint (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ) :
    IsSelfAdjoint (weightedAlice s d) := by
  apply isSelfAdjoint_sum
  intro i hi
  exact (by simp [isSelfAdjoint_iff] : IsSelfAdjoint (d i : ℂ)).smul (s.alice_projection i 1).isSelfAdjoint
lemma weightedBob_selfadjoint (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ) :
    IsSelfAdjoint (weightedBob s d) := by
  apply isSelfAdjoint_sum
  intro i hi
  exact (by simp [isSelfAdjoint_iff] : IsSelfAdjoint (d i : ℂ)).smul (s.bob_projection i 1).isSelfAdjoint

lemma weightedAlice_commute_bob (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ)
    (j : Fin n) (b : Fin 2) : Commute (weightedAlice s d) (s.bob j b) :=
  Commute.sum_left _ _ _ fun i _ => (s.cross_commute i j 1 b).smul_left (d i : ℂ)
lemma weightedBob_commute_alice (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ)
    (i : Fin n) (a : Fin 2) : Commute (weightedBob s d) (s.alice i a) :=
  Commute.sum_left _ _ _ fun j _ => (s.cross_commute i j a 1).symm.smul_left (d j : ℂ)

lemma weighted_synchronized (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (d : Fin n → ℝ) :
    weightedAlice s d s.state = weightedBob s d s.state := by
  simp only [weightedAlice, weightedBob, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.smul_apply, hsync]

noncomputable def aliceCommutator (s : Scenarios.CommutingStrategy n n 2 2 H) (k : Fin n) (d : Fin n → ℝ) :
    H →L[ℂ] H := weightedAlice s d * s.alice k 1 - s.alice k 1 * weightedAlice s d
noncomputable def bobCommutator (s : Scenarios.CommutingStrategy n n 2 2 H) (k : Fin n) (d : Fin n → ℝ) :
    H →L[ℂ] H := s.bob k 1 * weightedBob s d - weightedBob s d * s.bob k 1

lemma aliceCommutator_skew (s : Scenarios.CommutingStrategy n n 2 2 H) (k : Fin n) (d : Fin n → ℝ) :
    star (aliceCommutator s k d) = -aliceCommutator s k d :=
  commutator_star (weightedAlice_selfadjoint s d) (s.alice_projection k 1).isSelfAdjoint
lemma bobCommutator_skew (s : Scenarios.CommutingStrategy n n 2 2 H) (k : Fin n) (d : Fin n → ℝ) :
    star (bobCommutator s k d) = -bobCommutator s k d :=
  commutator_star (s.bob_projection k 1).isSelfAdjoint (weightedBob_selfadjoint s d)

lemma aliceCommutator_commute_bob (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (j : Fin n) (b : Fin 2) :
    Commute (aliceCommutator s k d) (s.bob j b) :=
  ((weightedAlice_commute_bob s d j b).mul_left (s.cross_commute k j 1 b)).sub_left
    ((s.cross_commute k j 1 b).mul_left (weightedAlice_commute_bob s d j b))
lemma bobCommutator_commute_alice (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (i : Fin n) (a : Fin 2) :
    Commute (bobCommutator s k d) (s.alice i a) :=
  ((s.cross_commute i k a 1).symm.mul_left (weightedBob_commute_alice s d i a)).sub_left
    ((weightedBob_commute_alice s d i a).mul_left (s.cross_commute i k a 1).symm)

lemma commutators_commute (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) : Commute (aliceCommutator s k d) (bobCommutator s k d) := by
  have hB := aliceCommutator_commute_bob s k d k 1
  have hD : Commute (aliceCommutator s k d) (weightedBob s d) :=
    Commute.sum_right _ _ _ fun j _ => (aliceCommutator_commute_bob s k d j 1).smul_right (d j : ℂ)
  exact (hB.mul_right hD).sub_right (hD.mul_right hB)

lemma commutators_synchronized (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (k : Fin n) (d : Fin n → ℝ) :
    aliceCommutator s k d s.state = bobCommutator s k d s.state := by
  have he₁ := congrArg (fun T : H →L[ℂ] H => T s.state) (weightedAlice_commute_bob s d k 1).eq
  have he₂ := congrArg (fun T : H →L[ℂ] H => T s.state) (weightedBob_commute_alice s d k 1).symm.eq
  simp only [ContinuousLinearMap.mul_apply] at he₁ he₂
  simp only [aliceCommutator, bobCommutator, ContinuousLinearMap.sub_apply, ContinuousLinearMap.mul_apply]
  rw [hsync, he₁, weighted_synchronized s hsync d,
    he₂, hsync]

noncomputable def rotationAliceUnitary (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) : unitary (H →L[ℂ] H) :=
  skewUnitary (aliceCommutator s k d) (aliceCommutator_skew s k d) t
noncomputable def rotationBobUnitary (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) : unitary (H →L[ℂ] H) :=
  skewUnitary (bobCommutator s k d) (bobCommutator_skew s k d) t

lemma rotationAlice_commute_bob (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (j : Fin n) (b : Fin 2) :
    Commute (rotationAliceUnitary s k d t : H →L[ℂ] H) (s.bob j b) :=
  ((aliceCommutator_commute_bob s k d j b).smul_left (t : ℂ)).exp_left
lemma rotationBob_commute_alice (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (i : Fin n) (a : Fin 2) :
    Commute (rotationBobUnitary s k d t : H →L[ℂ] H) (s.alice i a) :=
  ((bobCommutator_commute_alice s k d i a).smul_left (t : ℂ)).exp_left
lemma rotationUnitary_commute (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) :
    Commute (rotationAliceUnitary s k d t : H →L[ℂ] H) (rotationBobUnitary s k d t : H →L[ℂ] H) :=
  (((commutators_commute s k d).smul_left (t : ℂ)).smul_right (t : ℂ)).exp
lemma rotationUnitary_commute_star (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) :
    Commute (rotationAliceUnitary s k d t : H →L[ℂ] H)
      (star (rotationBobUnitary s k d t : H →L[ℂ] H)) := by
  change Commute (exp ((t : ℂ) • aliceCommutator s k d)) (star (exp ((t : ℂ) • bobCommutator s k d)))
  rw [star_exp]
  simp only [star_smul, Complex.star_def, Complex.conj_ofReal, bobCommutator_skew]
  exact ((((commutators_commute s k d).neg_right).smul_left (t : ℂ)).smul_right (t : ℂ)).exp

noncomputable def rotationStrategy (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) : Scenarios.CommutingStrategy n n 2 2 H :=
  conjugateStrategy s k (rotationAliceUnitary s k d t) (rotationBobUnitary s k d t)
    (rotationAlice_commute_bob s k d t) (rotationBob_commute_alice s k d t)
    (rotationUnitary_commute s k d t) (rotationUnitary_commute_star s k d t)

lemma rotationStrategy_synchronized (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) :
    ∀ i a, (rotationStrategy s k d t).alice i a (rotationStrategy s k d t).state =
      (rotationStrategy s k d t).bob i a (rotationStrategy s k d t).state := by
  obtain ⟨hψ,hψs⟩ := synchronized_skewUnitary (aliceCommutator_skew s k d)
    (bobCommutator_skew s k d) (commutators_commute s k d) (commutators_synchronized s hsync k d) t
  exact conjugateStrategy_synchronized s k _ _ _ _ _ _ hsync hψ hψs

lemma mirrored_conjugation_expectation (ψ : H) (P : H →L[ℂ] H) (hP : IsSelfAdjoint P)
    (U V : unitary (H →L[ℂ] H)) (hVP : Commute (V : H →L[ℂ] H) P)
    (hψs : (star (U : H →L[ℂ] H)) ψ = (star (V : H →L[ℂ] H)) ψ) :
    vectorFunctional ψ (Unitary.conjStarAlgAut ℂ _ U P) = vectorFunctional ψ P := by
  change inner ℂ ψ ((U : H →L[ℂ] H) (P ((star (U : H →L[ℂ] H)) ψ))) = inner ℂ ψ (P ψ)
  rw [← ContinuousLinearMap.adjoint_inner_left]
  change inner ℂ ((star (U : H →L[ℂ] H)) ψ) (P ((star (U : H →L[ℂ] H)) ψ)) = _
  rw [hψs]
  have he := congrArg (fun T : H →L[ℂ] H => T ψ) (commute_star_left_of_selfadjoint hVP hP).symm.eq
  change P ((star (V : H →L[ℂ] H)) ψ) = (star (V : H →L[ℂ] H)) (P ψ) at he
  rw [he]
  exact Unitary.inner_map_map (star V) ψ (P ψ)

lemma rotationStrategy_marginal (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (i : Fin n) (a : Fin 2) :
    vectorFunctional s.state ((rotationStrategy s k d t).alice i a) =
      vectorFunctional s.state (s.alice i a) := by
  obtain ⟨hψ,hψs⟩ := synchronized_skewUnitary (aliceCommutator_skew s k d)
    (bobCommutator_skew s k d) (commutators_commute s k d) (commutators_synchronized s hsync k d) t
  dsimp only [rotationStrategy, conjugateStrategy]
  split_ifs
  · exact mirrored_conjugation_expectation s.state _ (s.alice_projection i a).isSelfAdjoint _ _
      (rotationBob_commute_alice s k d t i a) hψs
  · rfl

lemma rotationStrategy_alice_same (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (a : Fin 2) :
    (rotationStrategy s k d t).alice k a =
      exp ((t : ℂ) • aliceCommutator s k d) * s.alice k a * exp ((t : ℂ) • (-aliceCommutator s k d)) := by
  dsimp only [rotationStrategy, conjugateStrategy]
  simp only [↓reduceIte, Unitary.conjStarAlgAut_apply]
  change exp ((t : ℂ) • aliceCommutator s k d) * s.alice k a *
    star (exp ((t : ℂ) • aliceCommutator s k d)) = _
  rw [star_exp]
  simp only [star_smul, Complex.star_def, Complex.conj_ofReal, aliceCommutator_skew]

lemma rotationStrategy_alice_other (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (i : Fin n) (a : Fin 2) (hi : i ≠ k) :
    (rotationStrategy s k d t).alice i a = s.alice i a := by
  dsimp only [rotationStrategy, conjugateStrategy]
  rw [if_neg hi]

@[simp] lemma rotationStrategy_state (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) : (rotationStrategy s k d t).state = s.state := rfl

end QuantumBehaviors.SmallInputs
