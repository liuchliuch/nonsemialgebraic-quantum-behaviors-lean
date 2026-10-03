import QuantumBehaviors.SmallInputs.WeightedAlgebra
import Mathlib.Data.Fintype.Prod
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.Tactic.FinCases

/-! Finite Boolean-word span for the central factor annihilating commutators. -/

namespace QuantumBehaviors.SmallInputs

variable {K R : Type*} [Field K] [Ring R] [Algebra K R]

/-- Eight ordered square-free words, with the empty word included. -/
def booleanWord (A B C : R) (i : Bool × Bool × Bool) : R :=
  (if i.1 then A else 1) * (if i.2.1 then B else 1) * (if i.2.2 then C else 1)

/-- Multiplication by the central factor turns the generator algebra commutative. -/
def compressedSpan (T A B C : R) : Submodule K R :=
  Submodule.span K (Set.range fun i => T * booleanWord A B C i)

lemma compressedWord_mem (T A B C : R) (i : Bool × Bool × Bool) :
    T * booleanWord A B C i ∈ compressedSpan (K := K) T A B C :=
  Submodule.subset_span ⟨i, rfl⟩

lemma weighted_swap_suffix {T A B : R} (h : T * (B * A) = T * (A * B)) (X : R) :
    T * (B * (A * X)) = T * (A * (B * X)) := by
  simpa only [mul_assoc] using congrArg (fun z => z * X) h

/-- The left generator `A` preserves the eight-word span. -/
lemma compressedWord_mul_A {T A B C : R} (hTA : Commute T A) (hA : IsIdempotentElem A)
    (i : Bool × Bool × Bool) :
    A * (T * booleanWord A B C i) = T * booleanWord A B C (true, i.2.1, i.2.2) := by
  rcases i with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp only [booleanWord, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      hTA.symm.left_comm, hTA.symm.eq, ← mul_assoc, hA.eq]

lemma compressedWord_mul_B {T A B C : R} (hTB : Commute T B)
    (hB : IsIdempotentElem B) (hBA : T * (B * A) = T * (A * B))
    (i : Bool × Bool × Bool) :
    B * (T * booleanWord A B C i) = T * booleanWord A B C (i.1, true, i.2.2) := by
  have hBB : ∀ X : R, B * (B * X) = B * X := fun X => by rw [← mul_assoc, hB.eq]
  rcases i with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp only [booleanWord, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      hTB.symm.left_comm, hTB.symm.eq, mul_assoc, hBB, hB.eq, hBA, weighted_swap_suffix hBA]

lemma compressedWord_mul_C {T A B C : R} (hTA : Commute T A) (hTC : Commute T C)
    (hC : IsIdempotentElem C) (hCA : T * (C * A) = T * (A * C))
    (hCB : T * (C * B) = T * (B * C))
    (i : Bool × Bool × Bool) :
    C * (T * booleanWord A B C i) = T * booleanWord A B C (i.1, i.2.1, true) := by
  have hCC : ∀ X : R, C * (C * X) = C * X := fun X => by rw [← mul_assoc, hC.eq]
  rcases i with ⟨a,b,c⟩
  cases a <;> cases b <;> cases c <;>
    simp only [booleanWord, Bool.false_eq_true, ↓reduceIte, mul_one, one_mul,
      hTC.symm.left_comm, hTC.symm.eq, mul_assoc, hCC, hC.eq, hCA, hCB,
      weighted_swap_suffix hCA, weighted_swap_suffix hCB] <;>
    simp only [hTA.left_comm, hCB, weighted_swap_suffix hCB, mul_assoc, hCC, hC.eq]

lemma span_left_mul_closed {V : Submodule K R} {f : Type*} (b : f → R) (P : R)
    (h : ∀ i, P * b i ∈ V) :
    ∀ x ∈ Submodule.span K (Set.range b), P * x ∈ V := by
  intro x hx
  induction hx using Submodule.span_induction with
  | mem x hx => obtain ⟨i, rfl⟩ := hx; exact h i
  | zero => simpa using V.zero_mem
  | add x y hx hy ihx ihy => simpa only [mul_add] using V.add_mem ihx ihy
  | smul c x hx ih => simpa only [mul_smul_comm] using V.smul_mem c ih

lemma compressedSpan_mul_A {T A B C : R} (hTA : Commute T A) (hA : IsIdempotentElem A) :
    ∀ x ∈ compressedSpan (K := K) T A B C, A * x ∈ compressedSpan (K := K) T A B C := by
  apply span_left_mul_closed
  intro i
  rw [compressedWord_mul_A hTA hA]
  exact compressedWord_mem _ _ _ _ _

lemma compressedSpan_mul_B {T A B C : R} (hTB : Commute T B)
    (hB : IsIdempotentElem B) (hBA : T * (B * A) = T * (A * B)) :
    ∀ x ∈ compressedSpan (K := K) T A B C, B * x ∈ compressedSpan (K := K) T A B C := by
  apply span_left_mul_closed
  intro i
  rw [compressedWord_mul_B hTB hB hBA]
  exact compressedWord_mem _ _ _ _ _

lemma compressedSpan_mul_C {T A B C : R} (hTA : Commute T A) (hTC : Commute T C)
    (hC : IsIdempotentElem C) (hCA : T * (C * A) = T * (A * C))
    (hCB : T * (C * B) = T * (B * C)) :
    ∀ x ∈ compressedSpan (K := K) T A B C, C * x ∈ compressedSpan (K := K) T A B C := by
  apply span_left_mul_closed
  intro i
  rw [compressedWord_mul_C hTA hTC hC hCA hCB]
  exact compressedWord_mem _ _ _ _ _

/-- Invariance under generators extends to their algebraic adjoin. -/
lemma adjoin_left_invariant {s : Set R} {V : Submodule K R}
    (h : ∀ P ∈ s, ∀ x ∈ V, P * x ∈ V) :
    ∀ P ∈ Algebra.adjoin K s, ∀ x ∈ V, P * x ∈ V := by
  intro P hP
  induction hP using Algebra.adjoin_induction with
  | mem P hP => exact h P hP
  | algebraMap c =>
    intro x hx
    simpa only [Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul] using V.smul_mem c hx
  | add P Q hP hQ ihP ihQ =>
    intro x hx
    simpa only [add_mul] using V.add_mem (ihP x hx) (ihQ x hx)
  | mul P Q hP hQ ihP ihQ =>
    intro x hx
    simpa only [mul_assoc] using ihP (Q * x) (ihQ x hx)

lemma adjoin_le_of_left_invariant {s : Set R} {V : Submodule K R}
    (h1 : (1 : R) ∈ V) (h : ∀ P ∈ s, ∀ x ∈ V, P * x ∈ V) :
    (Algebra.adjoin K s).toSubmodule ≤ V := by
  intro P hP
  simpa only [mul_one] using adjoin_left_invariant h P hP 1 h1

lemma commute_adjoin {s : Set R} {T : R} (h : ∀ P ∈ s, Commute T P) :
    ∀ P ∈ Algebra.adjoin K s, Commute T P := by
  intro P hP
  induction hP using Algebra.adjoin_induction with
  | mem P hP => exact h P hP
  | algebraMap c => exact (Algebra.commutes c T).symm
  | add P Q hP hQ ihP ihQ => exact ihP.add_right ihQ
  | mul P Q hP hQ ihP ihQ => exact ihP.mul_right ihQ

lemma booleanWord_mem_adjoin (A B C : R) (i : Bool × Bool × Bool) :
    booleanWord A B C i ∈ Algebra.adjoin K ({A, B, C} : Set R) := by
  apply Subalgebra.mul_mem
  · apply Subalgebra.mul_mem
    · split_ifs
      · exact Algebra.subset_adjoin (by simp)
      · exact Subalgebra.one_mem _
    · split_ifs
      · exact Algebra.subset_adjoin (by simp)
      · exact Subalgebra.one_mem _
  · split_ifs
    · exact Algebra.subset_adjoin (by simp)
    · exact Subalgebra.one_mem _

lemma compressedSpan_right_invariant {T A B C : R}
    (hcomm : ∀ P ∈ ({A, B, C} : Set R), Commute T P)
    (hleft : ∀ P ∈ ({A, B, C} : Set R), ∀ x ∈ compressedSpan (K := K) T A B C,
      P * x ∈ compressedSpan (K := K) T A B C) :
    ∀ P ∈ Algebra.adjoin K ({A, B, C} : Set R),
      ∀ x ∈ compressedSpan (K := K) T A B C,
        x * P ∈ compressedSpan (K := K) T A B C := by
  have hT : T ∈ compressedSpan (K := K) T A B C := by
    simpa only [booleanWord, Bool.false_eq_true, ↓reduceIte, mul_one] using
      compressedWord_mem (K := K) T A B C (false, false, false)
  have hmul : ∀ P ∈ Algebra.adjoin K ({A, B, C} : Set R),
      T * P ∈ compressedSpan (K := K) T A B C := by
    intro P hP
    rw [(commute_adjoin hcomm P hP).eq]
    exact adjoin_left_invariant hleft P hP T hT
  intro P hP x hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    rw [mul_assoc]
    exact hmul _ ((Algebra.adjoin K ({A, B, C} : Set R)).mul_mem
      (booleanWord_mem_adjoin A B C i) hP)
  | zero => simp
  | add x y hx hy ihx ihy =>
    simpa only [add_mul] using (compressedSpan (K := K) T A B C).add_mem ihx ihy
  | smul c x hx ih =>
    simpa only [smul_mul_assoc] using (compressedSpan (K := K) T A B C).smul_mem c ih

instance compressedSpan_finiteDimensional (T A B C : R) :
    FiniteDimensional K (compressedSpan (K := K) T A B C) :=
  FiniteDimensional.span_of_finite K (Set.finite_range _)

lemma compressedSpan_finrank_le (T A B C : R) :
    Module.finrank K (compressedSpan (K := K) T A B C) ≤ 8 := by
  simpa only [Fintype.card_prod, Fintype.card_bool] using
    finrank_range_le_card (R := K) (fun i => T * booleanWord A B C i)

end QuantumBehaviors.SmallInputs
