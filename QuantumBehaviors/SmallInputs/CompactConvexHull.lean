import QuantumBehaviors.SmallInputs.ConvexReduction
import QuantumBehaviors.Scenarios.BoundedDimensionCompact
import Mathlib.Analysis.Convex.Caratheodory
import Mathlib.LinearAlgebra.AffineSpace.FiniteDimensional

/-! Compact convexification with an explicit finite Carathéodory parameter space. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators

section General
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]

/-- All convex combinations of exactly `k` points, allowing zero weights. -/
noncomputable def combinationImage (S : Set E) (k : ℕ) : Set E :=
  (fun z : (Fin k → ℝ) × (Fin k → E) => ∑ i, z.1 i • z.2 i) ''
    (stdSimplex ℝ (Fin k) ×ˢ Set.pi Set.univ (fun _ : Fin k => S))

lemma combinationImage_compact {S : Set E} (hS : IsCompact S) (k : ℕ) : IsCompact (combinationImage S k) := by
  apply ((isCompact_stdSimplex ℝ (Fin k)).prod (isCompact_univ_pi fun _ : Fin k => hS)).image
  apply continuous_finset_sum
  intro i hi
  exact ((continuous_apply i).comp continuous_fst).smul ((continuous_apply i).comp continuous_snd)

lemma combinationImage_subset_convexHull (S : Set E) (k : ℕ) : combinationImage S k ⊆ convexHull ℝ S := by
  rintro x ⟨⟨w,z⟩,⟨hw,hz⟩,rfl⟩
  exact (convex_convexHull ℝ S).sum_mem (fun i _ => hw.1 i) hw.2
    (fun i _ => subset_convexHull ℝ S (hz i (Set.mem_univ i)))

/-- A cardinal-bounded version of the library's proved Carathéodory theorem. -/
theorem mem_convexHull_finite_combination {S : Set E} {x : E} (hx : x ∈ convexHull ℝ S) :
    ∃ (k : ℕ), k ≤ Module.finrank ℝ E + 1 ∧ x ∈ combinationImage S k := by
  classical
  obtain ⟨ι,hι,z,w,hz,hind,hwpos,hwsum,hwx⟩ := eq_pos_convex_span_of_mem_convexHull hx
  letI : Fintype ι := hι
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  have hk : Fintype.card ι ≤ Module.finrank ℝ E + 1 :=
    hind.card_le_finrank_succ.trans (Nat.add_le_add_right (Submodule.finrank_le _) 1)
  refine ⟨Fintype.card ι,hk,⟨(w ∘ e,z ∘ e),⟨⟨?_,?_⟩,?_⟩,?_⟩⟩
  · intro i
    exact (hwpos (e i)).le
  · exact (Equiv.sum_comp e w).trans hwsum
  · intro i hi
    exact hz ⟨e i,rfl⟩
  · exact (Equiv.sum_comp e (fun i => w i • z i)).trans hwx

/-- The convex hull in finite dimension is a finite union of compact simplex images. -/
theorem convexHull_eq_bounded_combination_union (S : Set E) :
    convexHull ℝ S = ⋃ k : Fin (Module.finrank ℝ E + 2), combinationImage S k.val := by
  ext x
  constructor
  · intro hx
    obtain ⟨k,hk,hx⟩ := mem_convexHull_finite_combination hx
    exact Set.mem_iUnion.mpr ⟨⟨k,by omega⟩,hx⟩
  · intro hx
    obtain ⟨k,hk⟩ := Set.mem_iUnion.mp hx
    exact combinationImage_subset_convexHull S k hk

/-- Compactness of convex hulls of compact sets in finite-dimensional real spaces. -/
theorem compact_convexHull_of_finiteDimensional {S : Set E} (hS : IsCompact S) :
    IsCompact (convexHull ℝ S) := by
  rw [convexHull_eq_bounded_combination_union]
  exact isCompact_iUnion fun k : Fin (Module.finrank ℝ E + 2) => combinationImage_compact hS k

end General

lemma boundedSynchronous_compact (n D : ℕ) : IsCompact (boundedSynchronous n D) :=
  (Scenarios.bounded_dimension_compact n n 2 2 D).inter_right (synchronous_isClosed n)

/-- Compactness of the exact convex hull used in the small-input proof. -/
theorem compact_convexHull_boundedSynchronous (n D : ℕ) :
    IsCompact (convexHull ℝ (boundedSynchronous n D)) :=
  compact_convexHull_of_finiteDimensional (boundedSynchronous_compact n D)

end QuantumBehaviors.SmallInputs
