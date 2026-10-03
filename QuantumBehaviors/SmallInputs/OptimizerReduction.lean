import QuantumBehaviors.SmallInputs.ThreeMoments
import QuantumBehaviors.SmallInputs.FiniteCyclicStrategy
import QuantumBehaviors.SmallInputs.TensorDilationBorn
import QuantumBehaviors.Scenarios.BoundedDimension
import QuantumBehaviors.Scenarios.BinaryLimits

/-! Actual global support maximizers have uniform finite-dimensional realizations. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators Topology

variable {n : ℕ} {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma weightedAlice_mem_algebra (s : Scenarios.CommutingStrategy n n 2 2 H) (d : Fin n → ℝ) :
    weightedAlice s d ∈ aliceAlgebra s := by
  apply Subalgebra.sum_mem
  intro i hi
  exact (aliceAlgebra s).smul_mem (alice_mem_algebra s i 1) (d i : ℂ)

lemma aliceCommutator_mem_algebra (s : Scenarios.CommutingStrategy n n 2 2 H)
    (k : Fin n) (d : Fin n → ℝ) : aliceCommutator s k d ∈ aliceAlgebra s :=
  (aliceAlgebra s).sub_mem ((aliceAlgebra s).mul_mem (weightedAlice_mem_algebra s d) (alice_mem_algebra s k 1))
    ((aliceAlgebra s).mul_mem (alice_mem_algebra s k 1) (weightedAlice_mem_algebra s d))

def Maximizes (c : Fin 6 → ℝ) (p : Scenarios.Behavior 3 3 2 2) : Prop :=
  ∀ q ∈ Scenarios.synchronousSet 3 .qc, momentObjective c q ≤ momentObjective c p

lemma optimizer_variation_local_maximum (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    {p : Scenarios.Behavior 3 3 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (c : Fin 6 → ℝ) (hmax : Maximizes c p) (k : Fin 3) :
    IsLocalMax (variation s.state (weightedAlice s (localWeights c k)) (s.alice k 1)
      (aliceCommutator s k (localWeights c k))) 0 := by
  have hsync := synchronous_vector_outcome s hr hp
  have hobj : momentObjective c p = stateObjective s c := by
    rw [← strategyBehavior_eq hr]
    exact objective_strategyBehavior s hsync c
  apply Filter.Eventually.of_forall
  intro t
  have ht := hmax (strategyBehavior (rotationStrategy s k (localWeights c k) t))
    (strategyBehavior_mem_synchronous _ (rotationStrategy_synchronized s hsync k (localWeights c k) t))
  rw [objective_strategyBehavior _ (rotationStrategy_synchronized s hsync k (localWeights c k) t), hobj,
    objective_rotation_decompose s hsync c k t] at ht
  have hz := objective_rotation_decompose s hsync c k 0
  rw [stateObjective_rotation_zero] at hz
  rw [hz] at ht
  exact (add_le_add_iff_left _).mp ht

/-- The optimizer calculation applies to a possibly nonfaithful vector state. -/
theorem optimizer_commutator_annihilates (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    {p : Scenarios.Behavior 3 3 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (c : Fin 6 → ℝ) (hmax : Maximizes c p) (k : Fin 3) :
    aliceCommutator s k (localWeights c k) s.state = 0 := by
  apply variation_maximum_annihilates s.state (weightedAlice s (localWeights c k)) (s.alice k 1)
    (weightedAlice_selfadjoint s _) (s.alice_projection k 1).isSelfAdjoint
  · exact synchronous_trace s hr hp
      ((aliceAlgebra s).mul_mem (weightedAlice_mem_algebra s _) (aliceCommutator_mem_algebra s k _))
      (alice_mem_algebra s k 1)
  · exact optimizer_variation_local_maximum s hr hp c hmax k

/-- After the proved faithful cyclic reduction, the optimizer relations hold as
operator identities, rather than merely modulo a null state. -/
theorem cyclic_optimizer_commutes (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    {p : Scenarios.Behavior 3 3 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (c : Fin 6 → ℝ) (hmax : Maximizes c p) (k : Fin 3) :
    let hs := synchronous_vector_outcome s hr hp
    Commute (weightedAlice (cyclicStrategy s hs) (localWeights c k)) ((cyclicStrategy s hs).alice k 1) := by
  dsimp only
  let hs := synchronous_vector_outcome s hr hp
  have hz := optimizer_commutator_annihilates (cyclicStrategy s hs) (cyclicStrategy_realizes s hs hr) hp c hmax k
  have hzero := cyclicStrategy_commutant_faithful s hs
    (aliceCommutator_mem_algebra (cyclicStrategy s hs) k (localWeights c k)) hz
  exact sub_eq_zero.mp hzero

lemma weightedAlice_local_zero (s : Scenarios.CommutingStrategy 3 3 2 2 H) (c : Fin 6 → ℝ) :
    weightedAlice s (localWeights c 0) = (c 3 : ℂ) • s.alice 1 1 + (c 4 : ℂ) • s.alice 2 1 := by
  norm_num [weightedAlice, localWeights, Fin.sum_univ_succ]

lemma weightedAlice_local_one (s : Scenarios.CommutingStrategy 3 3 2 2 H) (c : Fin 6 → ℝ) :
    weightedAlice s (localWeights c 1) = (c 3 : ℂ) • s.alice 0 1 + (c 5 : ℂ) • s.alice 2 1 := by
  norm_num [weightedAlice, localWeights, Fin.sum_univ_succ]

/-- With nonzero pair coefficients, the optimizer's faithful Alice algebra is at most
12-dimensional. No claim about zero coefficients is made here; they are covered by
`DenseSupport.generic_support_mem_closedConvexHull` in the final convex argument. -/
theorem optimizer_algebra_bound (s : Scenarios.CommutingStrategy 3 3 2 2 H)
    {p : Scenarios.Behavior 3 3 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (c : Fin 6 → ℝ) (hmax : Maximizes c p) (h3 : c 3 ≠ 0) (h4 : c 4 ≠ 0) (h5 : c 5 ≠ 0) :
    let hs := synchronous_vector_outcome s hr hp
    FiniteDimensional ℂ (aliceAlgebra (cyclicStrategy s hs)) ∧
      Module.finrank ℂ (aliceAlgebra (cyclicStrategy s hs)) ≤ 12 := by
  dsimp only
  let hs := synchronous_vector_outcome s hr hp
  let s' := cyclicStrategy s hs
  have h0 : Commute (s'.alice 0 1) ((c 3 : ℂ) • s'.alice 1 1 + (c 4 : ℂ) • s'.alice 2 1) := by
    simpa only [weightedAlice_local_zero] using (cyclic_optimizer_commutes s hr hp c hmax 0).symm
  have h1 : Commute (s'.alice 1 1) ((c 3 : ℂ) • s'.alice 0 1 + (c 5 : ℂ) • s'.alice 2 1) := by
    simpa only [weightedAlice_local_one] using (cyclic_optimizer_commutes s hr hp c hmax 1).symm
  have h3c : (c 3 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h3
  have h4c : (c 4 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h4
  have h5c : (c 5 : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h5
  have h0' : Commute (s'.alice 0 1)
      (((c 3 : ℂ) / c 5) • s'.alice 1 1 + ((c 4 : ℂ) / c 5) • s'.alice 2 1) := by
    simpa only [smul_add, smul_smul, div_eq_mul_inv, mul_comm] using h0.smul_right (c 5 : ℂ)⁻¹
  have h1' : Commute (s'.alice 1 1) (((c 3 : ℂ) / c 5) • s'.alice 0 1 + s'.alice 2 1) := by
    simpa only [smul_add, smul_smul, inv_mul_cancel₀ h5c, one_smul, div_eq_mul_inv, mul_comm] using h1.smul_right (c 5 : ℂ)⁻¹
  rw [three_alice_algebra s']
  exact russell_adjoin_finiteDimensional (div_ne_zero h3c h5c) (div_ne_zero h4c h5c)
    (s'.alice_projection 0 1).isIdempotentElem (s'.alice_projection 1 1).isIdempotentElem
    (s'.alice_projection 2 1).isIdempotentElem h0' h1'

/-- The full optimizer, in the genuine tensor-product model, has both local dimensions ≤12. -/
theorem optimizer_mem_bounded {p : Scenarios.Behavior 3 3 2 2}
    (hp : p ∈ Scenarios.synchronousSet 3 .qc) (c : Fin 6 → ℝ) (hmax : Maximizes c p)
    (h3 : c 3 ≠ 0) (h4 : c 4 ≠ 0) (h5 : c 5 ≠ 0) :
    p ∈ Scenarios.BoundedDimensionSet 3 3 2 2 12 := by
  obtain ⟨⟨H,hN,hI,hC,s,hr⟩,hsyncp⟩ := hp
  letI : NormedAddCommGroup H := hN
  letI : InnerProductSpace ℂ H := hI
  letI : CompleteSpace H := hC
  let hs := synchronous_vector_outcome s hr hsyncp
  obtain ⟨hf,hd⟩ := optimizer_algebra_bound s hr hsyncp c hmax h3 h4 h5
  letI : FiniteDimensional ℂ (aliceAlgebra (cyclicStrategy s hs)) := hf
  have heval := cyclicStrategy_evaluation_bijective s hs
  let E := algebraEvaluation (aliceAlgebra (cyclicStrategy s hs)) (cyclicStrategy s hs).state
  letI : FiniteDimensional ℂ (strategyCyclicSpace s) := FiniteDimensional.of_surjective E heval.2
  have hdim : Module.finrank ℂ (strategyCyclicSpace s) ≤ 12 := by
    rw [← (LinearEquiv.ofBijective E heval).finrank_eq]
    exact hd
  obtain ⟨t,ht⟩ := finite_cyclic_to_finite_strategy (cyclicStrategy s hs) heval
    (cyclicStrategy_realizes s hs hr)
  exact ⟨_,_,hdim,hdim,t,ht⟩

lemma sixMoments_continuous : Continuous sixMoments := by
  apply continuous_pi
  intro i
  fin_cases i <;> exact continuous_apply _

lemma momentObjective_continuous (c : Fin 6 → ℝ) : Continuous (momentObjective c) := by
  apply continuous_finset_sum
  intro i hi
  exact continuous_const.mul ((continuous_apply i).comp sixMoments_continuous)

/-- Matching every nondegenerate supporting direction is proved by an actual
compact-set optimizer and an actual finite tensor strategy. -/
theorem generic_objective_bounded_support {p : Scenarios.Behavior 3 3 2 2}
    (hp : p ∈ Scenarios.synchronousSet 3 .qc) (c : Fin 6 → ℝ) (hc : ∀ i, c i ≠ 0) :
    ∃ q, q ∈ Scenarios.BoundedDimensionSet 3 3 2 2 12 ∧ Scenarios.Synchronous q ∧
      momentObjective c p ≤ momentObjective c q := by
  obtain ⟨q,hq,hmax⟩ := (synchronous_cqc_compact 3).exists_isMaxOn ⟨p,hp⟩
    (momentObjective_continuous c).continuousOn
  exact ⟨q,optimizer_mem_bounded hq c hmax (hc 3) (hc 4) (hc 5),hq.2,hmax hp⟩

end QuantumBehaviors.SmallInputs
