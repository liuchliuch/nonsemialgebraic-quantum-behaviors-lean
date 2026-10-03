import QuantumBehaviors.AlmostQuantum.Reconstruction

/-! The almost-quantum operator definition automatically gives proper nonsignalling probabilities. -/
namespace QuantumBehaviors.AlmostQuantum
open scoped BigOperators ComplexOrder
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

lemma effect_projection {P : H →L[ℂ] H} (hP : IsStarProjection P) (a : Bool) :
    IsStarProjection (effect P a) := by cases a;exact hP.one_sub;exact hP

lemma product_expectation_nonnegative (P Q : H →L[ℂ] H) (hP : IsStarProjection P)
    (hQ : IsStarProjection Q) (ψ : H) (hPQ : P (Q ψ)=Q (P ψ)) :
    0 ≤ (inner ℂ ψ (P (Q ψ))).re := by
  have hPy : P (P (Q ψ))=P (Q ψ) := projection_twice P hP _
  have hQy : Q (P (Q ψ))=P (Q ψ) := by rw [hPQ,projection_twice Q hQ]
  have hi : inner ℂ (P (Q ψ)) (P (Q ψ))=inner ℂ ψ (P (Q ψ)) := by
    calc
      _ = inner ℂ (Q (P ψ)) (P (Q ψ)) := by rw [hPQ]
      _ = inner ℂ (P ψ) (Q (P (Q ψ))) := selfadjoint_inner_left Q hQ.isSelfAdjoint _ _
      _ = inner ℂ (P ψ) (P (Q ψ)) := by rw [hQy]
      _ = inner ℂ ψ (P (P (Q ψ))) := selfadjoint_inner_left P hP.isSelfAdjoint _ _
      _ = _ := by rw [hPy]
  rw [← hi]
  exact inner_self_nonneg (𝕜 := ℂ) (x := P (Q ψ))

theorem Strategy.nonnegative (s : Strategy H) {p : Behavior} (hp : s.realizes p) : Nonnegative p := by
  rintro ⟨i,j,a,b⟩
  have h := product_expectation_nonnegative (effect (s.alice i) a) (effect (s.bob j) b)
    (effect_projection (s.alice_projection i) a) (effect_projection (s.bob_projection j) b)
    s.state (s.all_outcomes_commute_on_state i j a b)
  have he := congrArg Complex.re (hp i j a b)
  simp only [Complex.ofReal_re,ContinuousLinearMap.mul_apply] at he
  rw [he]
  exact h

theorem Certificate.probabilities_normalized {p : Behavior} (c : Certificate p) : Normalized p := by
  intro i j
  apply Complex.ofReal_injective
  simp only [Complex.ofReal_sum,Complex.ofReal_one]
  simp_rw [c.born]
  simp [bornValue]

theorem Certificate.probabilities_nonsignaling {p : Behavior} (c : Certificate p) : Nonsignaling p := by
  constructor
  · intro i j k a
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum]
    simp_rw [c.born]
    cases a <;> simp [bornValue] <;> ring
  · intro i j k b
    apply Complex.ofReal_injective
    simp only [Complex.ofReal_sum]
    simp_rw [c.born]
    cases b <;> simp [bornValue] <;> ring

theorem Strategy.physical (s : Strategy H) {p : Behavior} (hp : s.realizes p) :
    Nonnegative p ∧ Normalized p ∧ Nonsignaling p :=
  ⟨s.nonnegative hp,(s.certificate hp).probabilities_normalized,(s.certificate hp).probabilities_nonsignaling⟩

end QuantumBehaviors.AlmostQuantum
