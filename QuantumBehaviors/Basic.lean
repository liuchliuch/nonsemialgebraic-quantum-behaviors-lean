import QuantumBehaviors.Definitions
import Mathlib.Data.Real.Basic
import Mathlib.Data.Fintype.Pi
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

/-!
# Four-input binary behaviors and the explicit quadratic curve

The coordinate convention is `(Alice input, Bob input, Alice output, Bob output)`.
The flat finite function space is canonically the paper's `ℝ^64`.
Source: Gao–Ji–Liu, arXiv:2609.18865v1, equations (2), (3), (S11), (S13).
-/

namespace QuantumBehaviors

@[simp] theorem card_coordinate : Fintype.card Coordinate = 64 := by decide

@[simp] theorem curve_diagonal_one (α : ℝ) (i : Input) :
    curve α (i, i, true, true) = α / 4 := by simp [curve]

@[simp] theorem curve_diagonal_zero (α : ℝ) (i : Input) :
    curve α (i, i, false, false) = 1 - α / 4 := by simp [curve]

@[simp] theorem curve_synchronous (α : ℝ) : Synchronous (curve α) := by
  intro i
  simp [curve]

theorem curve_normalized (α : ℝ) : Normalized (curve α) := by
  intro i j
  by_cases h : i = j <;> simp [curve, h, Fintype.sum_bool] <;> ring

theorem curve_alice_marginal (α : ℝ) (i j : Input) (a : Bool) :
    (∑ b : Bool, curve α (i, j, a, b)) = if a then α / 4 else 1 - α / 4 := by
  cases a <;> by_cases h : i = j <;> simp [curve, h, Fintype.sum_bool] <;> ring

theorem curve_bob_marginal (α : ℝ) (i j : Input) (b : Bool) :
    (∑ a : Bool, curve α (i, j, a, b)) = if b then α / 4 else 1 - α / 4 := by
  cases b <;> by_cases h : i = j <;> simp [curve, h, Fintype.sum_bool] <;> ring

theorem curve_nonsignaling (α : ℝ) : Nonsignaling (curve α) := by
  constructor
  · intro i j k a
    rw [curve_alice_marginal, curve_alice_marginal]
  · intro i j k b
    rw [curve_bob_marginal, curve_bob_marginal]

theorem curve_nonnegative {α : ℝ} (h₁ : 1 < α) (h₂ : α < 2) :
    Nonnegative (curve α) := by
  rintro ⟨i, j, a, b⟩
  have hα : 0 ≤ α := by linarith
  have hm : 0 ≤ α - 1 := by linarith
  have h₃ : 0 ≤ 3 - α := by linarith
  have h₄ : 0 ≤ 4 - α := by linarith
  cases a <;> cases b <;> by_cases h : i = j <;> simp [curve, h]
  all_goals first | positivity | linarith

@[simp] theorem curve_diagonal_sum (α : ℝ) :
    (∑ i : Input, curve α (i, i, true, true)) = α := by
  simp
  ring

@[simp] theorem curve_joint_sum (α : ℝ) :
    (∑ i : Input, ∑ j : Input, curve α (i, j, true, true)) = α ^ 2 := by
  simp [Input, Fin.sum_univ_succ, curve]
  ring

@[simp] theorem curve_witness (α : ℝ) : witness (curve α) α = 0 := by
  simp [witness]
  ring

@[simp] theorem curve_correlator_diagonal (α : ℝ) (i : Input) :
    correlator (curve α) i i = 1 := by
  simp [correlator, curve]

theorem curve_correlator_offdiagonal (α : ℝ) {i j : Input} (h : i ≠ j) :
    correlator (curve α) i j = ((α - 2) ^ 2 - 1) / 3 := by
  simp [correlator, curve, h]
  ring

end QuantumBehaviors
