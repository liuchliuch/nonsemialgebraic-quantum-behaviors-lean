import QuantumBehaviors.Scenarios.Inheritance
import QuantumBehaviors.SmallInputs.CompressedSpan

/-! The tracial state carried by any genuine binary synchronous commuting strategy. -/

namespace QuantumBehaviors.SmallInputs

open scoped BigOperators

variable {n : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The actual vector functional, as a complex-linear map on bounded operators. -/
noncomputable def vectorFunctional (ψ : H) : (H →L[ℂ] H) →ₗ[ℂ] ℂ where
  toFun T := inner ℂ ψ (T ψ)
  map_add' T U := by simp [inner_add_right]
  map_smul' c T := by simp [inner_smul_right]

@[simp] lemma vectorFunctional_apply (ψ : H) (T : H →L[ℂ] H) :
    vectorFunctional ψ T = inner ℂ ψ (T ψ) := rfl

lemma selfadjoint_inner_left (P : H →L[ℂ] H) (hP : IsSelfAdjoint P) (x y : H) :
    inner ℂ (P x) y = inner ℂ x (P y) := by
  exact hP.isSymmetric x y

lemma projection_inner_self (P : H →L[ℂ] H) (hP : IsStarProjection P) (ψ : H) :
    inner ℂ (P ψ) (P ψ) = inner ℂ ψ (P ψ) := by
  rw [selfadjoint_inner_left P hP.isSelfAdjoint]
  have h := congrArg (fun T : H →L[ℂ] H => T ψ) hP.isIdempotentElem.eq
  simpa only [ContinuousLinearMap.mul_apply] using congrArg (inner ℂ ψ) h

/-- Synchrony equates Alice's and Bob's one-outcome vectors, for every input count. -/
theorem synchronous_vector (s : Scenarios.CommutingStrategy n n 2 2 H)
    {p : Scenarios.Behavior n n 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (i : Fin n) : s.alice i 1 s.state = s.bob i 1 s.state := by
  have hA0 : s.alice i 0 = 1 - s.alice i 1 := by
    have he : s.alice i 0 + s.alice i 1 = 1 := by simpa [Fin.sum_univ_succ] using s.alice_sum i
    exact eq_sub_iff_add_eq.mpr he
  have hB0 : s.bob i 0 = 1 - s.bob i 1 := by
    have he : s.bob i 0 + s.bob i 1 = 1 := by simpa [Fin.sum_univ_succ] using s.bob_sum i
    exact eq_sub_iff_add_eq.mpr he
  let A := s.alice i 1
  let B := s.bob i 1
  let ψ := s.state
  have hA := s.alice_projection i 1
  have hB := s.bob_projection i 1
  have hAB : A (B ψ) = B (A ψ) :=
    congrArg (fun T : H →L[ℂ] H => T ψ) (s.cross_commute i i 1 1).eq
  have h10 : inner ℂ ψ (A ψ) - inner ℂ ψ (A (B ψ)) = 0 := by
    have h := hr i i 1 0
    rw [hp i 1 0 (by decide), hB0] at h
    simpa [ψ, A, B, ContinuousLinearMap.mul_apply, map_sub, inner_sub_right] using h.symm
  have h01 : inner ℂ ψ (B ψ) - inner ℂ ψ (A (B ψ)) = 0 := by
    have h := hr i i 0 1
    rw [hp i 0 1 (by decide), hA0] at h
    simpa [ψ, A, B, ContinuousLinearMap.mul_apply, inner_sub_right] using h.symm
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜 := ℂ)).mp
  rw [inner_sub_left, inner_sub_right, inner_sub_right,
    projection_inner_self A hA ψ, projection_inner_self B hB ψ,
    selfadjoint_inner_left A hA.isSelfAdjoint, selfadjoint_inner_left B hB.isSelfAdjoint, ← hAB]
  linear_combination h10 + h01

/-- Alice's single-outcome algebra. It is an actual operator subalgebra. -/
def aliceAlgebra (s : Scenarios.CommutingStrategy n n 2 2 H) : Subalgebra ℂ (H →L[ℂ] H) :=
  Algebra.adjoin ℂ (Set.range fun i => s.alice i 1)

lemma aliceAlgebra_commute_bob (s : Scenarios.CommutingStrategy n n 2 2 H)
    {X : H →L[ℂ] H} (hX : X ∈ aliceAlgebra s) (j : Fin n) : Commute X (s.bob j 1) := by
  apply Commute.symm
  apply commute_adjoin (K := ℂ) (T := s.bob j 1) _ X hX
  rintro P ⟨i, rfl⟩
  exact (s.cross_commute i j 1 1).symm

lemma synchronous_generator_trace (s : Scenarios.CommutingStrategy n n 2 2 H)
    {p : Scenarios.Behavior n n 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    (i : Fin n) {X : H →L[ℂ] H} (hX : X ∈ aliceAlgebra s) :
    vectorFunctional s.state (s.alice i 1 * X) =
      vectorFunctional s.state (X * s.alice i 1) := by
  simp only [vectorFunctional_apply, ContinuousLinearMap.mul_apply]
  rw [← selfadjoint_inner_left _ (s.alice_projection i 1).isSelfAdjoint,
    synchronous_vector s hr hp i, selfadjoint_inner_left _ (s.bob_projection i 1).isSelfAdjoint]
  have he := congrArg (fun T : H →L[ℂ] H => T s.state) (aliceAlgebra_commute_bob s hX i).eq
  simp only [ContinuousLinearMap.mul_apply] at he
  rw [← he, ← synchronous_vector s hr hp i]

/-- The vector state is tracial on the whole generated operator algebra. -/
theorem synchronous_trace (s : Scenarios.CommutingStrategy n n 2 2 H)
    {p : Scenarios.Behavior n n 2 2} (hr : s.realizes p) (hp : Scenarios.Synchronous p)
    {X Y : H →L[ℂ] H} (hX : X ∈ aliceAlgebra s) (hY : Y ∈ aliceAlgebra s) :
    vectorFunctional s.state (X * Y) = vectorFunctional s.state (Y * X) := by
  suffices ∀ X ∈ aliceAlgebra s, ∀ Y ∈ aliceAlgebra s,
      vectorFunctional s.state (X * Y) = vectorFunctional s.state (Y * X) from this X hX Y hY
  intro X hX
  induction hX using Algebra.adjoin_induction with
  | mem X hX =>
    obtain ⟨i, rfl⟩ := hX
    exact fun Y hY => synchronous_generator_trace s hr hp i hY
  | algebraMap c =>
    intro Y hY
    rw [Algebra.commutes c Y]
  | add X Z hX hZ ihX ihZ =>
    intro Y hY
    simp only [add_mul, mul_add, map_add, ihX Y hY, ihZ Y hY]
  | mul X Z hX hZ ihX ihZ =>
    intro Y hY
    rw [mul_assoc, ihX (Z * Y) ((aliceAlgebra s).mul_mem hZ hY), mul_assoc,
      ihZ (Y * X) ((aliceAlgebra s).mul_mem hY hX), mul_assoc]

end QuantumBehaviors.SmallInputs
