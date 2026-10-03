import QuantumBehaviors.Basic
import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.Algebra.Order.BigOperators.Group.Finset

/-!
# Finite classical models and the classical accumulation point

Finite shared randomness and deterministic response functions give the usual Bell-local set.
All finite probabilistic response tables are representable in this form by refining the finite
hidden variable; no quantum state or unproved realization theorem is built into this definition.
-/

namespace QuantumBehaviors

/-- The six balanced bit strings, i.e. indicators of the two-element subsets of four inputs. -/
def balancedResponses : Fin 6 → Response :=
  ![![true, true, false, false], ![true, false, true, false],
    ![true, false, false, true], ![false, true, true, false],
    ![false, true, false, true], ![false, false, true, true]]

noncomputable def balancedBehavior : Behavior := fun x =>
  ∑ k : Fin 6, (1 / 6 : ℝ) * deterministic (balancedResponses k) (balancedResponses k) x

theorem balancedBehavior_local : BellLocal balancedBehavior := by
  refine ⟨6, fun _ => 1 / 6, balancedResponses, balancedResponses, ?_, ?_, ?_⟩
  · intro k
    norm_num
  · norm_num
  · intro x
    rfl

/-- Proposition S9: the endpoint is the uniform mixture of six classical strategies. -/
theorem curve_two_eq_balanced : curve 2 = balancedBehavior := by
  funext x
  rcases x with ⟨i, j, a, b⟩
  fin_cases i <;> fin_cases j <;> cases a <;> cases b <;>
    norm_num [curve, balancedBehavior, balancedResponses, deterministic, Fin.sum_univ_succ]

theorem curve_two_local : BellLocal (curve 2) := by
  rw [curve_two_eq_balanced]
  exact balancedBehavior_local

noncomputable def deterministicCount (z : Response) : ℕ :=
  ∑ i : Input, if z i then 1 else 0

theorem deterministic_synchronous (z : Response) : Synchronous (deterministic z z) := by
  intro i
  cases h : z i <;> simp [deterministic, h]

theorem deterministic_diagonal_sum (z : Response) :
    (∑ i : Input, deterministic z z (i, i, true, true)) = deterministicCount z := by
  simp only [deterministicCount, Nat.cast_sum, Nat.cast_ite, Nat.cast_one, Nat.cast_zero]
  apply Finset.sum_congr rfl
  intro i hi
  cases h : z i <;> simp [deterministic, h]

theorem deterministic_joint_sum (z : Response) :
    (∑ i : Input, ∑ j : Input, deterministic z z (i, j, true, true)) =
      (deterministicCount z : ℝ) ^ 2 := by
  rw [← deterministic_diagonal_sum, pow_two, Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro i hi
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  cases hi' : z i <;> cases hj' : z j <;> simp [deterministic, hi', hj']

theorem deterministic_witness (z : Response) (α : ℝ) :
    witness (deterministic z z) α = ((deterministicCount z : ℝ) - α) ^ 2 := by
  rw [witness, deterministic_joint_sum, deterministic_diagonal_sum]
  ring

end QuantumBehaviors
