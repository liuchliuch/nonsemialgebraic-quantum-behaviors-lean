import QuantumBehaviors.SmallInputs.OptimizerReduction
import QuantumBehaviors.SmallInputs.MomentReconstruction
import QuantumBehaviors.SmallInputs.DenseSupport

/-! From the verified optimizers to the closed convex hull of bounded tensor strategies. -/

namespace QuantumBehaviors.SmallInputs

/-- Actual bounded-dimension synchronous tensor behaviors. -/
def boundedSynchronous (n D : ℕ) : Set (Scenarios.Behavior n n 2 2) :=
  {p | p ∈ Scenarios.BoundedDimensionSet n n 2 2 D ∧ Scenarios.Synchronous p}

lemma boundedSynchronous_subset_cqc (n D : ℕ) : boundedSynchronous n D ⊆ Scenarios.synchronousSet n .qc := by
  rintro p ⟨⟨dA,dB,hdA,hdB,s,hr⟩,hs⟩
  exact ⟨Scenarios.binary_cq_subset_cqc n n ⟨dA,dB,s,hr⟩,hs⟩

lemma sixMoments_unit_cube {p : Scenarios.Behavior 3 3 2 2}
    (hp : p ∈ Scenarios.synchronousSet 3 .qc) :
    ∀ i, 0 ≤ sixMoments p i ∧ sixMoments p i ≤ 1 := by
  have h := cqc_subset_unit_cube hp.1
  intro i
  fin_cases i <;> exact ⟨h.1 _,h.2 _⟩

/-- Every actual synchronous commuting behavior is in the closed convex hull of
six-moment vectors having genuine tensor realizations of local dimension ≤12. -/
theorem synchronous_moments_mem_closedConvexHull {p : Scenarios.Behavior 3 3 2 2}
    (hp : p ∈ Scenarios.synchronousSet 3 .qc) :
    sixMoments p ∈ closedConvexHull ℝ (sixMoments '' boundedSynchronous 3 12) := by
  refine generic_support_mem_closedConvexHull _ ?_ _ (sixMoments_unit_cube hp) ?_
  · rintro y ⟨q,hq,rfl⟩
    exact sixMoments_unit_cube (boundedSynchronous_subset_cqc 3 12 hq)
  · intro c hc
    obtain ⟨q,hq,hs,hobj⟩ := generic_objective_bounded_support hp c hc
    exact ⟨sixMoments q,⟨q,⟨hq,hs⟩,rfl⟩,hobj⟩

def sixMomentsLinear : Scenarios.Behavior 3 3 2 2 →ₗ[ℝ] (Fin 6 → ℝ) where
  toFun := sixMoments
  map_add' p q := by funext i; fin_cases i <;> rfl
  map_smul' c p := by funext i; fin_cases i <;> rfl

lemma synchronous_convex (n : ℕ) : Convex ℝ {p : Scenarios.Behavior n n 2 2 | Scenarios.Synchronous p} := by
  intro p hp q hq a b ha hb hab
  intro i x y hxy
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, hp i x y hxy, hq i x y hxy, mul_zero, add_zero]

lemma convexHull_boundedSynchronous_synchronous {n D : ℕ} {p : Scenarios.Behavior n n 2 2}
    (hp : p ∈ convexHull ℝ (boundedSynchronous n D)) : Scenarios.Synchronous p :=
  convexHull_min (fun _ h => h.2) (synchronous_convex n) hp

/-- General final-assembly lemma: compact convexification removes the closure
in the previously proved support reduction. -/
theorem synchronous_moments_in_convexHull
    (hcompact : IsCompact (convexHull ℝ (boundedSynchronous 3 12)))
    {p : Scenarios.Behavior 3 3 2 2} (hp : p ∈ Scenarios.synchronousSet 3 .qc) :
    ∃ q ∈ convexHull ℝ (boundedSynchronous 3 12), sixMoments q = sixMoments p := by
  have hc : Convex ℝ (sixMoments '' convexHull ℝ (boundedSynchronous 3 12)) :=
    (convex_convexHull ℝ _).linear_image sixMomentsLinear
  have hk : IsClosed (sixMoments '' convexHull ℝ (boundedSynchronous 3 12)) :=
    (hcompact.image sixMoments_continuous).isClosed
  have hsub : sixMoments '' boundedSynchronous 3 12 ⊆
      sixMoments '' convexHull ℝ (boundedSynchronous 3 12) :=
    Set.image_mono (subset_convexHull ℝ _)
  exact closedConvexHull_min hsub hc hk (synchronous_moments_mem_closedConvexHull hp)

lemma synchronous_semialgebraic (n : ℕ) :
    IsSemialgebraic {p : Scenarios.Behavior n n 2 2 | Scenarios.Synchronous p} := by
  classical
  apply IsSemialgebraic.forall_finite
  intro i
  apply IsSemialgebraic.forall_finite
  intro a
  apply IsSemialgebraic.forall_finite
  intro b
  by_cases hab : a = b
  · simpa only [hab, ne_eq, not_true_eq_false, false_implies, Set.setOf_true] using
      (IsSemialgebraic.univ (ι := Scenarios.Coordinate n n 2 2))
  · simpa [hab] using
      IsSemialgebraic.polynomial_zero (MvPolynomial.X (i,i,a,b))

lemma boundedSynchronous_semialgebraic (n D : ℕ) : IsSemialgebraic (boundedSynchronous n D) :=
  (Scenarios.bounded_dimension_semialgebraic n n 2 2 D).inter (synchronous_semialgebraic n)

end QuantumBehaviors.SmallInputs
