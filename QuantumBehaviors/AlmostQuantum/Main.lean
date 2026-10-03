import QuantumBehaviors.AlmostQuantum.SDP

/-! The paper's almost-quantum finite-SDP outer-approximation consequence. -/
namespace QuantumBehaviors.AlmostQuantum
open Set

@[simp] theorem card_event : Fintype.card Event=25 := by norm_num [Event,Input]
@[simp] theorem card_auxiliary : Fintype.card Auxiliary=1250 := by simp [Auxiliary]

theorem semialgebraic : IsSemialgebraic behaviors := finite_complex_sdp.semialgebraic

theorem cq_subset : Cq ⊆ behaviors := fun _ hp => cqc_subset (cq_subset_cqc hp)

theorem curve_tail : ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, curve α ∈ behaviors :=
  corollary_two semialgebraic cq_subset

/-- Every sufficiently near-classical forbidden parameter is almost quantum but not commuting quantum. -/
theorem forbidden_tail : ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, ¬ Allowed α →
    curve α ∈ behaviors ∧ curve α ∉ Cqc := by
  obtain ⟨β,hβ,ht⟩ := curve_tail
  refine ⟨β,hβ,?_⟩
  intro α hα hnot
  exact ⟨ht α hα,fun h => hnot (curve_commuting_only_allowed (hβ.1.trans hα.1) hα.2 h)⟩

theorem cqc_strict_subset : Cqc ⊂ behaviors := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨cqc_subset,?_⟩
  intro heq
  obtain ⟨β,hβ,ht⟩ := forbidden_tail
  obtain ⟨α,hα,hnot⟩ := (allowed_and_forbidden_in_tail hβ.2).2
  have hmem := ht α ⟨(le_max_right 1 β).trans_lt hα.1,hα.2⟩ hnot
  exact hmem.2 (heq.symm ▸ hmem.1)

end QuantumBehaviors.AlmostQuantum
