import QuantumBehaviors.NPA.SDP
import QuantumBehaviors.NPA.Limits

/-! All stated finite-level NPA consequences, together with genuine hierarchy completeness. -/
namespace QuantumBehaviors.NPA
open Set

theorem level_semialgebraic (k : ℕ) : IsSemialgebraic (level k) := (finite_complex_sdp k).semialgebraic

theorem cq_subset_level (k : ℕ) : Cq ⊆ level k := fun _ hp => cqc_subset_level k (cq_subset_cqc hp)

theorem finite_level_tail (k : ℕ) : ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, curve α ∈ level k :=
  corollary_two (level_semialgebraic k) (cq_subset_level k)

theorem finite_level_forbidden_tail (k : ℕ) : ∃ β ∈ Ioo (1 : ℝ) 2, ∀ α ∈ Ioo β 2, ¬ Allowed α →
    curve α ∈ level k ∧ curve α ∉ Cqc := by
  obtain ⟨β,hβ,ht⟩ := finite_level_tail k
  refine ⟨β,hβ,?_⟩
  intro α hα hn
  exact ⟨ht α hα,fun h => hn (curve_commuting_only_allowed (hβ.1.trans hα.1) hα.2 h)⟩

theorem finite_level_strict (k : ℕ) : Cqc ⊂ level k := by
  refine Set.ssubset_iff_subset_ne.mpr ⟨cqc_subset_level k,?_⟩
  intro heq
  obtain ⟨β,hβ,ht⟩ := finite_level_forbidden_tail k
  obtain ⟨α,hα,hn⟩ := (allowed_and_forbidden_in_tail hβ.2).2
  have hp := ht α ⟨(le_max_right 1 β).trans_lt hα.1,hα.2⟩ hn
  exact hp.2 (heq.symm ▸ hp.1)

theorem finite_level_not_equal_quantum (k : ℕ) (t : Model) : level k ≠ quantumSet t := by
  intro heq
  have hs := level_semialgebraic k
  rw [heq] at hs
  exact (theorem_one.2 t).2.1 hs

/-- Every forbidden point in the physical curve is individually excluded at some finite order. -/
theorem forbidden_eventually_excluded {α : ℝ} (hα : α ∈ Ioo (1 : ℝ) 2) (hn : ¬ Allowed α) :
    ∃ k, curve α ∉ level k :=
  excluded_at_finite_level (fun hp => hn (curve_commuting_only_allowed hα.1 hα.2 hp))

/-- Exclusion, once attained, persists at every higher finite level. -/
theorem excluded_at_all_higher {p : Behavior} (hp : p ∉ Cqc) :
    ∃ k, ∀ l, k ≤ l → p ∉ level l := by
  obtain ⟨k,hk⟩ := excluded_at_finite_level hp
  exact ⟨k,fun l hkl hl => hk (level_antitone hkl hl)⟩

/-- There is no single finite level resolving all the near-classical membership gaps. -/
theorem no_uniform_finite_level (k : ℕ) {β : ℝ} (hβ : β < 2) :
    ∃ α ∈ Ioo (max 1 β) 2, curve α ∈ level k ∧ curve α ∉ Cqc := by
  obtain ⟨b,hb,ht⟩ := finite_level_forbidden_tail k
  have hm : max b β < 2 := max_lt hb.2 hβ
  obtain ⟨α,hα,hn⟩ := (allowed_and_forbidden_in_tail hm).2
  have haB : b < α := (le_max_left b β).trans_lt ((le_max_right 1 (max b β)).trans_lt hα.1)
  have haβ : β < α := (le_max_right b β).trans_lt ((le_max_right 1 (max b β)).trans_lt hα.1)
  have ha1 : 1 < α := (le_max_left 1 (max b β)).trans_lt hα.1
  exact ⟨α,⟨max_lt ha1 haβ,hα.2⟩,ht α ⟨haB,hα.2⟩ hn⟩

end QuantumBehaviors.NPA
