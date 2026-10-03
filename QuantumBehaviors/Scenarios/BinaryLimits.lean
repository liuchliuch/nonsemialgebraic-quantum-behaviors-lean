import QuantumBehaviors.Scenarios.StateGNS
import QuantumBehaviors.Scenarios.ClosedCommuting
import QuantumBehaviors.Scenarios.CommutingModels
import QuantumBehaviors.FiniteToCommuting

/-! Lemma S4 with its full stated generality: arbitrary finite input counts, binary outputs. -/
namespace QuantumBehaviors.Scenarios

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable def binaryBit (a : Fin 2) : Bool := decide (a.val = 1)

@[simp] theorem pad_two {V : Type*} [Zero V] (v : Bool → V) (a : Fin 2) :
    padBinary (by decide : 2 ≤ 2) v a = v (binaryBit a) := by
  fin_cases a <;> simp [padBinary, outcomeZero, outcomeOne, binaryBit]

lemma effect_binary_family {R : Type*} [Ring R] (A : Fin 2 → R) (hA : ∑ a, A a = 1)
    (a : Fin 2) : effect (A (outcomeOne (by decide : 2 ≤ 2))) (binaryBit a) = A a := by
  have hsum : A 0 + A 1 = 1 := by simpa [Fin.sum_univ_succ] using hA
  fin_cases a
  · simp only [binaryBit, Fin.val_zero, Nat.zero_ne_one, decide_false, effect_false, outcomeOne]
    exact (eq_sub_iff_add_eq.mpr hsum).symm
  · rfl

lemma pad_starProjection {R : Type*} [Ring R] [StarRing R] {m : ℕ} (hm : 2 ≤ m)
    (P : R) (hP : IsStarProjection P) (a : Fin m) : IsStarProjection (padBinary hm (effect P) a) := by
  unfold padBinary
  split_ifs
  · exact hP.one_sub
  · exact hP
  · exact IsStarProjection.zero _

lemma pad_cross_commute {R : Type*} [Ring R] {m n : ℕ} (hm : 2 ≤ m) (hn : 2 ≤ n)
    {P Q : R} (h : Commute P Q) (a : Fin m) (b : Fin n) :
    Commute (padBinary hm (effect P) a) (padBinary hn (effect Q) b) := by
  unfold padBinary
  split_ifs <;> first | exact effect_commute h _ _ | exact Commute.zero_left _ | exact Commute.zero_right _

theorem binary_cq_subset_cqc (nA nB : ℕ) : Cq nA nB 2 2 ⊆ Cqc nA nB 2 2 := by
  rintro p ⟨dA, dB, s, hs⟩
  have hdA : 0 < dA := by
    by_contra h
    have hz : dA = 0 := by omega
    subst dA
    have ht := s.density_trace
    simpa using ht
  have hdB : 0 < dB := by
    by_contra h
    have hz : dB = 0 := by omega
    subst dB
    have ht := s.density_trace
    simpa using ht
  letI : NeZero dA := ⟨Nat.ne_zero_of_lt hdA⟩
  letI : NeZero dB := ⟨Nat.ne_zero_of_lt hdB⟩
  let e : Fin dA × Fin dB → (Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB) :=
    fun x => (Sum.inl x.1, Sum.inl x.2)
  have he : Function.Injective e := by
    intro x y h
    exact Prod.ext (Sum.inl.inj (congrArg Prod.fst h)) (Sum.inl.inj (congrArg Prod.snd h))
  let E := fun i : Fin nA => s.alice i (outcomeOne (by decide : 2 ≤ 2))
  let G := fun j : Fin nB => s.bob j (outcomeOne (by decide : 2 ≤ 2))
  let A : Fin nA → Fin 2 → Matrix ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB))
      ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB)) ℂ :=
    fun i => padBinary (by decide : 2 ≤ 2) (effect (binaryDilation (E i) ⊗ₖ 1))
  let B : Fin nB → Fin 2 → Matrix ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB))
      ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB)) ℂ :=
    fun j => padBinary (by decide : 2 ≤ 2) (effect (1 ⊗ₖ binaryDilation (G j)))
  have hEA : ∀ i, IsStarProjection (binaryDilation (E i)) := fun i =>
    binaryDilation_projection _ (s.alice_pos _ _)
      (complement_positive_of_sum_one (by decide : 2 ≤ 2) _ (s.alice_pos i) (s.alice_sum i))
  have hGB : ∀ j, IsStarProjection (binaryDilation (G j)) := fun j =>
    binaryDilation_projection _ (s.bob_pos _ _)
      (complement_positive_of_sum_one (by decide : 2 ≤ 2) _ (s.bob_pos j) (s.bob_sum j))
  apply cqc_of_density p (embeddedDensity e s.density) (embeddedDensity_positive e s.density_pos)
    ((embeddedDensity_trace e he s.density).trans s.density_trace) A B
  · intro i a
    exact pad_starProjection (by decide) _ (kronecker_projection (hEA i) (IsStarProjection.one _)) a
  · intro j b
    exact pad_starProjection (by decide) _ (kronecker_projection (IsStarProjection.one _) (hGB j)) b
  · intro i
    exact pad_effect_sum (by decide) _
  · intro j
    exact pad_effect_sum (by decide) _
  · intro i j a b
    exact pad_cross_commute (by decide) (by decide) (cross_kronecker_commute _ _) a b
  · intro i j a b
    rw [embeddedDensity_expectation]
    change (p (i, j, a, b) : ℂ) = (s.density *
      (padBinary (by decide : 2 ≤ 2) (effect (binaryDilation (E i) ⊗ₖ 1)) a *
        padBinary (by decide : 2 ≤ 2) (effect (1 ⊗ₖ binaryDilation (G j))) b).submatrix e e).trace
    rw [pad_two, pad_two, effect_kronecker_one, effect_one_kronecker,
      ← Matrix.mul_kronecker_mul, mul_one, one_mul]
    have hc : (effect (binaryDilation (E i)) (binaryBit a) ⊗ₖ
        effect (binaryDilation (G j)) (binaryBit b)).submatrix e e = s.alice i a ⊗ₖ s.bob j b := by
      ext x y
      simp only [Matrix.submatrix_apply, Matrix.kronecker_apply, e, binaryDilation_outcome_apply]
      rw [effect_binary_family (s.alice i) (s.alice_sum i),
        effect_binary_family (s.bob j) (s.bob_sum j)]
      rfl
    rw [hc]
    exact hs i j a b

/-- Lemma S4 for every fixed finite bipartite scenario with binary outputs. -/
theorem lemma_S4 (nA nB : ℕ) : Cqa nA nB 2 2 ⊆ Cqc nA nB 2 2 :=
  closure_minimal (binary_cq_subset_cqc nA nB) (cqc_isClosed nA nB 2 2)

end QuantumBehaviors.Scenarios
