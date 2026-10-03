import QuantumBehaviors.Geometry
import QuantumBehaviors.Classical
import QuantumBehaviors.QuantumMoments
import QuantumBehaviors.FiniteRealization
import QuantumBehaviors.FiniteToCommuting

/-!
# Main exact slice and local obstructions

These paper entrypoints use the independently defined physical quantum models. No exact-slice,
realization, spectral, closure, semialgebraic, or analytic obstruction premise remains here.
-/
namespace QuantumBehaviors

open Set

theorem cq_subset_quantumSet (t : Model) : Cq ⊆ quantumSet t := by
  cases t
  · exact subset_rfl
  · exact cq_subset_cqa
  · exact cq_subset_cqc

theorem quantumSet_subset_cqc (t : Model) : quantumSet t ⊆ Cqc := by
  cases t
  · exact cq_subset_cqc
  · exact cqa_subset_cqc
  · exact subset_rfl

/-- Theorem S7, pointwise exact membership for each of the three original models. -/
theorem quantum_exact_membership (t : Model) {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) :
    curve α ∈ quantumSet t ↔ Allowed α := by
  constructor
  · intro h
    exact curve_commuting_only_allowed hα₁ hα₂ (quantumSet_subset_cqc t h)
  · intro h
    exact cq_subset_quantumSet t (allowed_curve_mem_cq h)

/-- Exact slice written as equality of subsets of the real line. -/
theorem quantum_exact_slice (t : Model) :
    {α : ℝ | α ∈ Ioo (1 : ℝ) 2 ∧ curve α ∈ quantumSet t} = {α | Allowed α} := by
  ext α
  constructor
  · rintro ⟨hα, hmem⟩
    exact (quantum_exact_membership t hα.1 hα.2).mp hmem
  · intro hα
    have hi : α ∈ Ioo (1 : ℝ) 2 := by
      obtain ⟨m, hm, rfl⟩ := hα
      exact alpha_mem_Ioo hm
    exact ⟨hi, (quantum_exact_membership t hi.1 hi.2).mpr hα⟩

theorem intermediate_exact_membership {C : Set Behavior} (hq : Cq ⊆ C) (hqc : C ⊆ Cqc)
    {α : ℝ} (hα₁ : 1 < α) (hα₂ : α < 2) : curve α ∈ C ↔ Allowed α :=
  ⟨fun h => curve_commuting_only_allowed hα₁ hα₂ (hqc h),
    fun h => hq (allowed_curve_mem_cq h)⟩

/-- Corollary S8: every intermediate quantum set has no finite polynomial sign description. -/
theorem intermediate_not_semialgebraic {C : Set Behavior} (hq : Cq ⊆ C) (hqc : C ⊆ Cqc) :
    ¬ IsSemialgebraic C :=
  exact_slice_not_semialgebraic fun α hα => intermediate_exact_membership hq hqc hα.1 hα.2

/-- Proposition S9: failure of finite analytic descriptions at the explicitly classical endpoint. -/
theorem intermediate_not_semianalytic {C : Set Behavior} (hq : Cq ⊆ C) (hqc : C ⊆ Cqc) :
    BellLocal (curve 2) ∧ ¬ IsSemianalyticAt C (curve 2) := by
  refine ⟨curve_two_local, ?_⟩
  exact exact_slice_not_semianalytic fun α hα => intermediate_exact_membership hq hqc hα.1 hα.2

/-- Theorem 1: exact intersections and both finite-description obstructions. -/
theorem theorem_one : BellLocal (curve 2) ∧ ∀ t : Model,
    {α : ℝ | α ∈ Ioo (1 : ℝ) 2 ∧ curve α ∈ quantumSet t} = {α | Allowed α} ∧
      ¬ IsSemialgebraic (quantumSet t) ∧ ¬ IsSemianalyticAt (quantumSet t) (curve 2) := by
  refine ⟨curve_two_local, ?_⟩
  intro t
  exact ⟨quantum_exact_slice t,
    intermediate_not_semialgebraic (cq_subset_quantumSet t) (quantumSet_subset_cqc t),
    (intermediate_not_semianalytic (cq_subset_quantumSet t) (quantumSet_subset_cqc t)).2⟩

/-- Corollary 2 / Proposition S12: every finite semialgebraic outer approximation has a full tail. -/
theorem corollary_two {R : Set Behavior} (hR : IsSemialgebraic R) (hq : Cq ⊆ R) :
    ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, curve α ∈ R := by
  apply semialgebraic_tail hR
  intro m hm
  exact hq (allowed_curve_mem_cq ⟨m, hm, rfl⟩)

end QuantumBehaviors
