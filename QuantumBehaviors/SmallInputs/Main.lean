import QuantumBehaviors.SmallInputs.CompactConvexHull
import QuantumBehaviors.SmallInputs.InputReduction
import QuantumBehaviors.SmallInputs.TensorConvexFinite

/-!
# The full small-input synchronous threshold (S15)

All sets below are the original finite-tensor, closure, and arbitrary-Hilbert
commuting strategy sets. The proof derives the uniform local dimension bound
444; it does not assume a finite-realization theorem or use a certificate type.
-/

namespace QuantumBehaviors.SmallInputs

/-- Every genuine three-input synchronous commuting behavior has a tensor
realization whose two local dimensions are at most 37 · 12 = 444. -/
theorem synchronous_three_cqc_bounded {p : Scenarios.Behavior 3 3 2 2}
    (hp : p ∈ Scenarios.synchronousSet 3 .qc) : p ∈ boundedSynchronous 3 444 := by
  obtain ⟨q,hq,he⟩ := synchronous_moments_in_convexHull
    (compact_convexHull_boundedSynchronous 3 12) hp
  have hqb : q ∈ Scenarios.BoundedDimensionSet 3 3 2 2 444 :=
    three_convexHull_bounded444 (convexHull_mono (fun _ h => h.1) hq)
  have hqs := convexHull_boundedSynchronous_synchronous hq
  have hqc := boundedSynchronous_subset_cqc 3 444 ⟨hqb,hqs⟩
  have hpq : p = q := sixMoments_injective_on_synchronous hp hqc he.symm
  exact hpq.symm ▸ ⟨hqb,hqs⟩

lemma boundedSynchronous_subset_model (n D : ℕ) (t : Model) :
    boundedSynchronous n D ⊆ Scenarios.synchronousSet n t := by
  rintro p ⟨⟨dA,dB,hdA,hdB,s,hr⟩,hs⟩
  have hq : p ∈ Scenarios.Cq n n 2 2 := ⟨dA,dB,s,hr⟩
  refine ⟨?_,hs⟩
  cases t
  · exact hq
  · exact subset_closure hq
  · exact Scenarios.binary_cq_subset_cqc n n hq

/-- An exact bounded polynomial parametrization for each of the three models. -/
theorem synchronous_three_eq_bounded (t : Model) :
    Scenarios.synchronousSet 3 t = boundedSynchronous 3 444 := by
  apply Set.Subset.antisymm
  · intro p hp
    apply synchronous_three_cqc_bounded
    refine ⟨?_,hp.2⟩
    cases t
    · exact Scenarios.binary_cq_subset_cqc 3 3 hp.1
    · exact Scenarios.lemma_S4 3 3 hp.1
    · exact hp.1
  · exact boundedSynchronous_subset_model 3 444 t

/-- The positive three-input conclusion uses actual polynomial quantifier elimination. -/
theorem synchronous_three_semialgebraic (t : Model) :
    IsSemialgebraic (Scenarios.synchronousSet 3 t) := by
  rw [synchronous_three_eq_bounded]
  exact boundedSynchronous_semialgebraic 3 444

end QuantumBehaviors.SmallInputs

namespace QuantumBehaviors.Scenarios

/-- The missing positive half of S15, including the zero-input edge case. -/
theorem synchronous_semialgebraic_of_le_three {n : ℕ} (hn : n ≤ 3) (t : Model) :
    IsSemialgebraic (synchronousSet n t) := by
  by_cases hz : n = 0
  · subst n
    exact SmallInputs.empty_synchronous_semialgebraic t
  · exact SmallInputs.small_synchronous_semialgebraic_of_three (by omega) hn t
      (SmallInputs.synchronous_three_semialgebraic t)

/-- S15 in full: for each original quantum model, the synchronous sector is
semialgebraic exactly when there are at most three binary inputs per party. -/
theorem theorem_S15 (n : ℕ) (t : Model) : IsSemialgebraic (synchronousSet n t) ↔ n ≤ 3 := by
  constructor
  · intro h
    by_contra hn
    exact synchronous_not_semialgebraic (by omega : 4 ≤ n) t h
  · intro hn
    exact synchronous_semialgebraic_of_le_three hn t

/-- The three genuine synchronous models also coincide throughout the small-input range. -/
theorem synchronous_models_eq_of_le_three {n : ℕ} (hn : n ≤ 3) (t u : Model) :
    synchronousSet n t = synchronousSet n u := by
  by_cases hz : n = 0
  · subst n
    rw [SmallInputs.empty_synchronousSet, SmallInputs.empty_synchronousSet]
  · have hn0 : 0 < n := by omega
    rw [SmallInputs.small_synchronous_preimage hn0 hn t, SmallInputs.small_synchronous_preimage hn0 hn u,
      SmallInputs.synchronous_three_eq_bounded, SmallInputs.synchronous_three_eq_bounded]

end QuantumBehaviors.Scenarios
