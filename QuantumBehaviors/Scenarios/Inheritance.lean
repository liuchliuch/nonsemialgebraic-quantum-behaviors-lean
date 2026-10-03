import QuantumBehaviors.Main
import QuantumBehaviors.Scenarios.CommutingModels

/-! Corollary S16 and the n≥4 half of the synchronous threshold, for the actual larger models. -/
namespace QuantumBehaviors.Scenarios

open Set

variable {nA nB mA mB : ℕ}

theorem extend_quantumSet (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) (t : Model) :
    MapsTo (extend (nA := nA) (nB := nB) hmA hmB) (QuantumBehaviors.quantumSet t)
      (quantumSet nA nB mA mB t) := by
  cases t
  · exact extend_cq hmA hmB
  · exact extend_cqa hmA hmB
  · exact extend_cqc hmA hmB

theorem retract_quantumSet (hnA : 4 ≤ nA) (hnB : 4 ≤ nB)
    (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) (t : Model) :
    MapsTo (retract hnA hnB hmA hmB) (quantumSet nA nB mA mB t)
      (QuantumBehaviors.quantumSet t) := by
  cases t
  · exact retract_cq hnA hnB hmA hmB
  · exact retract_cqa hnA hnB hmA hmB
  · exact retract_cqc hnA hnB hmA hmB

theorem extend_mem_quantum_iff (hnA : 4 ≤ nA) (hnB : 4 ≤ nB)
    (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) (t : Model) (p : QuantumBehaviors.Behavior) :
    extend hmA hmB p ∈ quantumSet nA nB mA mB t ↔ p ∈ QuantumBehaviors.quantumSet t := by
  constructor
  · intro h
    have hp := retract_quantumSet hnA hnB hmA hmB t h
    simpa only [retract_extend] using hp
  · intro h
    exact extend_quantumSet (nA := nA) (nB := nB) hmA hmB t h

/-- Corollary S16: every fixed larger Bell scenario is nonsemialgebraic in all three models. -/
theorem larger_scenario_not_semialgebraic (hnA : 4 ≤ nA) (hnB : 4 ≤ nB)
    (hmA : 2 ≤ mA) (hmB : 2 ≤ mB) (t : Model) :
    ¬ IsSemialgebraic (quantumSet nA nB mA mB t) := by
  intro h
  have hpre := semialgebraic_preimage_extend hmA hmB h
  have heq : extend hmA hmB ⁻¹' quantumSet nA nB mA mB t = QuantumBehaviors.quantumSet t := by
    ext p
    exact extend_mem_quantum_iff hnA hnB hmA hmB t p
  rw [heq] at hpre
  exact (theorem_one.2 t).2.1 hpre

theorem extend_synchronous {n : ℕ} {p : QuantumBehaviors.Behavior}
    (hp : QuantumBehaviors.Synchronous p) :
    Synchronous (extend (nA := n) (nB := n) (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) p) := by
  intro i a b hab
  fin_cases a <;> fin_cases b
  · exact False.elim (hab rfl)
  · simpa [extend, padBinary, outcomeZero, outcomeOne] using (hp (extendInput i)).2
  · simpa [extend, padBinary, outcomeZero, outcomeOne] using (hp (extendInput i)).1
  · exact False.elim (hab rfl)

/-- The large-input half of S15; the n≤3 half is a separate Russell dependency. -/
theorem synchronous_not_semialgebraic {n : ℕ} (hn : 4 ≤ n) (t : Model) :
    ¬ IsSemialgebraic (synchronousSet n t) := by
  intro h
  have hpre := semialgebraic_preimage_extend (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) h
  apply exact_slice_not_semialgebraic (C := extend (nA := n) (nB := n)
    (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) ⁻¹' synchronousSet n t) ?_ hpre
  intro α hα
  change (extend (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) (curve α) ∈ quantumSet n n 2 2 t ∧
    Synchronous (extend (by decide : 2 ≤ 2) (by decide : 2 ≤ 2) (curve α))) ↔ Allowed α
  rw [extend_mem_quantum_iff hn hn (by decide) (by decide) t]
  simp only [extend_synchronous (curve_synchronous α), and_true]
  exact quantum_exact_membership t hα.1 hα.2

end QuantumBehaviors.Scenarios
