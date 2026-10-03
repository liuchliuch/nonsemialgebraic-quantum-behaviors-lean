import QuantumBehaviors.FiniteDilation
import QuantumBehaviors.MatrixEmbedding
import QuantumBehaviors.StateGNS
import QuantumBehaviors.CommutingLimits

/-!
# The finite-model and closure inclusions

Each local binary effect is dilated on the same doubled local space. The density is
embedded by a literal coordinate isometry. A proved GNS representation turns the
resulting finite commuting projection/density model into the vector-state model Cqc.
-/
namespace QuantumBehaviors

open Matrix
open scoped Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

theorem kronecker_projection {P : Matrix ι ι ℂ} {Q : Matrix κ κ ℂ}
    (hP : IsStarProjection P) (hQ : IsStarProjection Q) : IsStarProjection (P ⊗ₖ Q) := by
  constructor
  · change (P ⊗ₖ Q) * (P ⊗ₖ Q) = P ⊗ₖ Q
    rw [← Matrix.mul_kronecker_mul, hP.isIdempotentElem.eq, hQ.isIdempotentElem.eq]
  · change (P ⊗ₖ Q).conjTranspose = P ⊗ₖ Q
    rw [Matrix.conjTranspose_kronecker]
    exact congrArg₂ (fun X Y => X ⊗ₖ Y) hP.isSelfAdjoint.star_eq hQ.isSelfAdjoint.star_eq

theorem cross_kronecker_commute (P : Matrix ι ι ℂ) (Q : Matrix κ κ ℂ) :
    Commute (P ⊗ₖ (1 : Matrix κ κ ℂ)) ((1 : Matrix ι ι ℂ) ⊗ₖ Q) := by
  change (P ⊗ₖ 1) * (1 ⊗ₖ Q) = (1 ⊗ₖ Q) * (P ⊗ₖ 1)
  simp only [← Matrix.mul_kronecker_mul, mul_one, one_mul]

theorem effect_kronecker_one (P : Matrix ι ι ℂ) (a : Bool) :
    effect (P ⊗ₖ (1 : Matrix κ κ ℂ)) a = effect P a ⊗ₖ (1 : Matrix κ κ ℂ) := by
  cases a
  · ext ⟨i, j⟩ ⟨k, l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [effect, Matrix.kronecker_apply, Matrix.one_apply, hik, hjl]
  · rfl

theorem effect_one_kronecker (Q : Matrix κ κ ℂ) (b : Bool) :
    effect ((1 : Matrix ι ι ℂ) ⊗ₖ Q) b = (1 : Matrix ι ι ℂ) ⊗ₖ effect Q b := by
  cases b
  · ext ⟨i, j⟩ ⟨k, l⟩
    by_cases hik : i = k <;> by_cases hjl : j = l <;>
      simp [effect, Matrix.kronecker_apply, Matrix.one_apply, hik, hjl]
  · rfl

@[simp] theorem binaryDilation_outcome_apply (E : Matrix ι ι ℂ) (a : Bool) (i j : ι) :
    effect (binaryDilation E) a (Sum.inl i) (Sum.inl j) = effect E a i j :=
  congrFun (congrFun (binaryDilation_outcome_compression E a) i) j

/-- The actual finite density/POVM model embeds in the actual commuting-projection model. -/
theorem cq_subset_cqc : Cq ⊆ Cqc := by
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
  let A : Input → Matrix ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB))
      ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB)) ℂ :=
    fun i => binaryDilation (s.alice i) ⊗ₖ 1
  let B : Input → Matrix ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB))
      ((Fin dA ⊕ Fin dA) × (Fin dB ⊕ Fin dB)) ℂ :=
    fun j => 1 ⊗ₖ binaryDilation (s.bob j)
  apply cqc_of_commuting_density p (embeddedDensity e s.density)
    (embeddedDensity_positive e s.density_pos)
    ((embeddedDensity_trace e he s.density).trans s.density_trace) A B
  · intro i
    exact kronecker_projection
      (binaryDilation_projection _ (s.alice_pos i) (s.alice_complement_pos i)) (IsStarProjection.one _)
  · intro j
    exact kronecker_projection (IsStarProjection.one _)
      (binaryDilation_projection _ (s.bob_pos j) (s.bob_complement_pos j))
  · intro i j
    exact cross_kronecker_commute _ _
  · intro i j a b
    rw [embeddedDensity_expectation]
    change (p (i, j, a, b) : ℂ) =
      (s.density * (effect (binaryDilation (s.alice i) ⊗ₖ 1) a *
        effect (1 ⊗ₖ binaryDilation (s.bob j)) b).submatrix e e).trace
    rw [effect_kronecker_one, effect_one_kronecker,
      ← Matrix.mul_kronecker_mul, mul_one, one_mul]
    have hc : (effect (binaryDilation (s.alice i)) a ⊗ₖ effect (binaryDilation (s.bob j)) b).submatrix e e =
        effect (s.alice i) a ⊗ₖ effect (s.bob j) b := by
      ext x y
      simp [Matrix.submatrix_apply, Matrix.kronecker_apply, e]
    rw [hc]
    exact hs i j a b

/-- Lemma S4: Euclidean limits of finite quantum behaviors have commuting realizations. -/
theorem cqa_subset_cqc : Cqa ⊆ Cqc :=
  closure_minimal cq_subset_cqc cqc_isClosed

end QuantumBehaviors
