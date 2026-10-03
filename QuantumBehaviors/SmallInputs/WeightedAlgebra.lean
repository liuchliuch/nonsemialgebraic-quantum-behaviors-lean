import QuantumBehaviors.SpectralAlgebra
import Mathlib.Tactic.Module
import Mathlib.Tactic.LinearCombination
import Mathlib.LinearAlgebra.FiniteDimensional.Basic
import Mathlib.Algebra.Algebra.Subalgebra.Lattice

/-!
# The stationary three-projection algebra

This file proves algebraic consequences of Russell's stationary relations.
No classification theorem, irreducible representation, or mandatory matrix summand
is assumed. The weights are allowed to be arbitrary until a nonzero hypothesis
is explicitly used.
-/

namespace QuantumBehaviors.SmallInputs

section Ring

variable {K R : Type*} [Field K] [Ring R] [Algebra K R]

/-- Weighted sum used to reduce the three-generator stationary algebra. -/
def weightedSum (u v w : K) (A B C : R) : R := u • A + v • B + w • C

/-- Pairwise weighted stationarity makes the weighted sum central on its generators. -/
theorem weightedSum_commute_left {u v w : K} {A B C : R}
    (h : Commute A (v • B + w • C)) : Commute A (weightedSum u v w A B C) := by
  simpa only [weightedSum, add_assoc] using ((Commute.refl A).smul_right u).add_right h

theorem weightedSum_commute_middle {u v w : K} {A B C : R}
    (h : Commute B (u • A + w • C)) : Commute B (weightedSum u v w A B C) := by
  have he : weightedSum u v w A B C = v • B + (u • A + w • C) := by
    unfold weightedSum; module
  rw [he]
  exact ((Commute.refl B).smul_right v).add_right h

/-- Scalar-multiple idempotent relation after eliminating the third generator. -/
theorem eliminated_square {u v w : K} {A B C S : R}
    (hC : IsIdempotentElem C) (hs : weightedSum u v w A B C = S) :
    (S - u • A - v • B) * (S - u • A - v • B) =
      w • (S - u • A - v • B) := by
  have he : S - u • A - v • B = w • C := by rw [← hs, weightedSum]; module
  rw [he, smul_mul_assoc, mul_smul_comm, hC.eq]

/-- The anticommutator relation of the two remaining idempotents. -/
theorem weighted_anticommutator {u v w : K} {A B C S : R}
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) (hC : IsIdempotentElem C)
    (hs : weightedSum u v w A B C = S) (hAS : Commute A S) (hBS : Commute B S) :
    (u * v) • (A * B + B * A) =
      -(S * S) + w • S + u • ((2 : K) • (S * A) - (u + w) • A) +
        v • ((2 : K) • (S * B) - (v + w) • B) := by
  have he := eliminated_square hC hs
  linear_combination (norm :=
    (simp only [add_mul, mul_add, sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm,
      hA.eq, hB.eq, hAS.eq, hBS.eq]; module)) he

/-- The noncommuting part is supported at one value of the central weighted sum. -/
theorem weighted_commutator_support {u v w : K} {A B C S : R}
    (hv : v ≠ 0)
    (hA : IsIdempotentElem A) (hB : IsIdempotentElem B) (hC : IsIdempotentElem C)
    (hs : weightedSum u v w A B C = S) (hAS : Commute A S) (hBS : Commute B S) :
    ((2 : K) • S - (u + v + w) • (1 : R)) * (A * B - B * A) = 0 := by
  have he := weighted_anticommutator hA hB hC hs hAS hBS
  have hAA : ∀ X : R, A * (A * X) = A * X := fun X => by rw [← mul_assoc, hA.eq]
  have he' : v • (((2 : K) • S - (u + v + w) • (1 : R)) * (A * B - B * A)) = 0 := by
    linear_combination (norm :=
      (simp only [add_mul, mul_add, sub_mul, mul_sub, neg_mul, mul_neg,
        smul_mul_assoc, mul_smul_comm, mul_assoc, hAA, hA.eq,
        hAS.left_comm, hAS.eq, one_mul, mul_one]; module)) -(A * he - he * A)
  exact (smul_eq_zero.mp he').resolve_left hv

/-- The third centrality relation follows without a third stationarity hypothesis. -/
theorem weightedSum_commute_third {u v w : K} {A B C S : R}
    (hw : w ≠ 0) (hs : weightedSum u v w A B C = S)
    (hAS : Commute A S) (hBS : Commute B S) : Commute C S := by
  have h : Commute (w • C) S := by
    have he : w • C = S - u • A - v • B := by rw [← hs, weightedSum]; module
    rw [he]
    exact ((Commute.refl S).sub_left (hAS.smul_left u)).sub_left (hBS.smul_left v)
  have he := h.smul_left w⁻¹
  simpa only [smul_smul, inv_mul_cancel₀ hw, one_smul] using he

/-- Russell's two displayed stationarity relations give the central weighted sum. -/
theorem russell_sum_central {a b : K} {A B C : R} (hb : b ≠ 0)
    (h₁ : Commute A (a • B + b • C)) (h₂ : Commute B (a • A + C)) :
    Commute A (weightedSum (a * b) a b A B C) ∧
      Commute B (weightedSum (a * b) a b A B C) ∧
      Commute C (weightedSum (a * b) a b A B C) := by
  have hA := weightedSum_commute_left (u := a * b) h₁
  have hB : Commute B (weightedSum (a * b) a b A B C) := by
    apply weightedSum_commute_middle
    simpa only [smul_add, smul_smul, mul_comm b a] using h₂.smul_right b
  exact ⟨hA, hB, weightedSum_commute_third hb rfl hA hB⟩

end Ring
end QuantumBehaviors.SmallInputs
