import QuantumBehaviors.SmallInputs.RotationStrategy

/-! The six independent moments of a binary synchronous three-input strategy. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

noncomputable def firstMoment (s : Scenarios.CommutingStrategy n n 2 2 H) (i : Fin n) : ℝ :=
  (vectorFunctional s.state (s.alice i 1)).re
noncomputable def pairMoment (s : Scenarios.CommutingStrategy n n 2 2 H) (i j : Fin n) : ℝ :=
  (vectorFunctional s.state (s.alice i 1 * s.alice j 1)).re

lemma pairMoment_diag (s : Scenarios.CommutingStrategy n n 2 2 H) (i : Fin n) :
    pairMoment s i i = firstMoment s i := by
  simp only [pairMoment, firstMoment, (s.alice_projection i 1).isIdempotentElem.eq]

lemma pairMoment_symm (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (i j : Fin n) :
    pairMoment s i j = pairMoment s j i := by
  apply congrArg Complex.re
  exact synchronous_trace s (strategyBehavior_realizes s) (strategyBehavior_synchronous s hsync)
    (Algebra.subset_adjoin ⟨i,rfl⟩) (Algebra.subset_adjoin ⟨j,rfl⟩)

@[simp] lemma firstMoment_rotation (s : Scenarios.CommutingStrategy n n 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (i : Fin n) :
    firstMoment (rotationStrategy s k d t) i = firstMoment s i :=
  congrArg Complex.re (rotationStrategy_marginal s hsync k d t i 1)

lemma pairMoment_rotation_other (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (i j : Fin n) (hi : i ≠ k) (hj : j ≠ k) :
    pairMoment (rotationStrategy s k d t) i j = pairMoment s i j := by
  simp only [pairMoment, rotationStrategy_state, rotationStrategy_alice_other s k d t i 1 hi,
    rotationStrategy_alice_other s k d t j 1 hj]

lemma variation_eq_weighted_pairs (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (t : ℝ) (hd : d k = 0) :
    variation s.state (weightedAlice s d) (s.alice k 1) (aliceCommutator s k d) t =
      ∑ j, d j * pairMoment (rotationStrategy s k d t) j k := by
  have hv : variation s.state (weightedAlice s d) (s.alice k 1) (aliceCommutator s k d) t =
      (vectorFunctional s.state (weightedAlice s d * (rotationStrategy s k d t).alice k 1)).re := by
    rw [rotationStrategy_alice_same]
    rfl
  rw [hv]
  simp only [weightedAlice, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    smul_eq_mul, Complex.re_sum, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  apply Finset.sum_congr rfl
  intro j hj
  by_cases he : j = k
  · subst j
    simp only [hd, zero_mul]
  · simp only [pairMoment, rotationStrategy_state, rotationStrategy_alice_other s k d t j 1 he]

/-- Observable moments in their actual behavior coordinates. -/
def sixMoments (p : Scenarios.Behavior 3 3 2 2) : Fin 6 → ℝ :=
  ![p (0,0,1,1), p (1,1,1,1), p (2,2,1,1), p (0,1,1,1), p (0,2,1,1), p (1,2,1,1)]

def momentObjective (c : Fin 6 → ℝ) (p : Scenarios.Behavior 3 3 2 2) : ℝ :=
  ∑ r, c r * sixMoments p r

noncomputable def stateObjective (s : Scenarios.CommutingStrategy 3 3 2 2 H) (c : Fin 6 → ℝ) : ℝ :=
  c 0 * firstMoment s 0 + c 1 * firstMoment s 1 + c 2 * firstMoment s 2 +
    c 3 * pairMoment s 0 1 + c 4 * pairMoment s 0 2 + c 5 * pairMoment s 1 2

lemma objective_strategyBehavior (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state) (c : Fin 6 → ℝ) :
    momentObjective c (strategyBehavior s) = stateObjective s c := by
  simp only [momentObjective, sixMoments, Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.reduceSucc, Fin.sum_univ_zero, add_zero]
  have hproj : ∀ i, s.alice i 1 * s.alice i 1 = s.alice i 1 := fun i =>
    (s.alice_projection i 1).isIdempotentElem.eq
  simp only [strategyBehavior_alice_moment s hsync, stateObjective, pairMoment, firstMoment, hproj]
  ring

/-- Interaction weights of a one-input variation, with the diagonal omitted. -/
def localWeights (c : Fin 6 → ℝ) (k : Fin 3) : Fin 3 → ℝ :=
  if k = 0 then ![0,c 3,c 4] else if k = 1 then ![c 3,0,c 5] else ![c 4,c 5,0]

@[simp] lemma localWeights_self (c : Fin 6 → ℝ) (k : Fin 3) : localWeights c k k = 0 := by
  fin_cases k <;> norm_num [localWeights]

noncomputable def localRemainder (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (c : Fin 6 → ℝ) (k : Fin 3) : ℝ :=
  c 0 * firstMoment s 0 + c 1 * firstMoment s 1 + c 2 * firstMoment s 2 +
    if k = 0 then c 5 * pairMoment s 1 2
    else if k = 1 then c 4 * pairMoment s 0 2 else c 3 * pairMoment s 0 1

lemma stateObjective_pair_decompose (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (c : Fin 6 → ℝ) (k : Fin 3) (hsym : ∀ i j, pairMoment s i j = pairMoment s j i) :
    stateObjective s c = localRemainder s c k + ∑ j, localWeights c k j * pairMoment s j k := by
  fin_cases k
  · norm_num [stateObjective, localRemainder, localWeights, Fin.sum_univ_succ]
    rw [hsym 1 0, hsym 2 0]
    ring
  · norm_num [stateObjective, localRemainder, localWeights, Fin.sum_univ_succ]
    rw [hsym 2 1]
    ring
  · change stateObjective s c = localRemainder s c (2 : Fin 3) + ∑ j, localWeights c (2 : Fin 3) j * pairMoment s j (2 : Fin 3)
    have h20 : (2 : Fin 3) ≠ 0 := by decide
    have h21 : (2 : Fin 3) ≠ 1 := by decide
    simp only [stateObjective, localRemainder, localWeights, h20, h21, ↓reduceIte,
      Fin.sum_univ_succ, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_succ,
      Fin.reduceSucc, Fin.sum_univ_zero, zero_mul, add_zero]
    ring

lemma localRemainder_rotation (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (c : Fin 6 → ℝ) (k : Fin 3) (d : Fin 3 → ℝ) (t : ℝ) :
    localRemainder (rotationStrategy s k d t) c k = localRemainder s c k := by
  simp only [localRemainder, firstMoment_rotation s hsync]
  fin_cases k
  · norm_num
    left
    exact pairMoment_rotation_other s 0 d t 1 2 (by decide) (by decide)
  · norm_num
    left
    exact pairMoment_rotation_other s 1 d t 0 2 (by decide) (by decide)
  · norm_num
    left
    exact pairMoment_rotation_other s _ d t 0 1 (by decide) (by decide)

lemma objective_rotation_decompose (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (hsync : ∀ i a, s.alice i a s.state = s.bob i a s.state)
    (c : Fin 6 → ℝ) (k : Fin 3) (t : ℝ) :
    stateObjective (rotationStrategy s k (localWeights c k) t) c = localRemainder s c k +
      variation s.state (weightedAlice s (localWeights c k)) (s.alice k 1)
        (aliceCommutator s k (localWeights c k)) t := by
  rw [variation_eq_weighted_pairs s k (localWeights c k) t (localWeights_self c k),
    stateObjective_pair_decompose (rotationStrategy s k (localWeights c k) t) c k
      (pairMoment_symm _ (rotationStrategy_synchronized s hsync k (localWeights c k) t)),
    localRemainder_rotation s hsync]

lemma rotationStrategy_alice_zero (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) (i : Fin n) (a : Fin 2) :
    (rotationStrategy s k d 0).alice i a = s.alice i a := by
  by_cases hi : i = k
  · subst i
    simp only [rotationStrategy_alice_same, Complex.ofReal_zero, zero_smul,
      NormedSpace.exp_zero, one_mul, mul_one]
  · exact rotationStrategy_alice_other s k d 0 i a hi

@[simp] lemma stateObjective_rotation_zero (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    (k : Fin 3) (d : Fin 3 → ℝ) (c : Fin 6 → ℝ) :
    stateObjective (rotationStrategy s k d 0) c = stateObjective s c := by
  simp only [stateObjective, firstMoment, pairMoment, rotationStrategy_state, rotationStrategy_alice_zero]

end QuantumBehaviors.SmallInputs
