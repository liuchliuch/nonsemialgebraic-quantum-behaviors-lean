import QuantumBehaviors.Basic
import Mathlib.LinearAlgebra.Matrix.Diagonal
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Algebra.Group.Fin.Basic
import Mathlib.Data.Fin.Rev
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.NoncommRing

/-!
# Uniform finite-dimensional construction by weighted involutions

This is the construction in Proposition S3 without choosing separate two-element blocks.
A weighted involution matrix supplies the square-root off-diagonal entries. Its fixed points
include the paper's singleton `0` and, when the dimension is even, singleton `1` cases.
The resulting two projections sum to the diagonal `2j/m`.
-/

namespace QuantumBehaviors
namespace FiniteConstruction

open Matrix

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def weightedInvolution (r : ι → ι) (w : ι → ℝ) : Matrix ι ι ℝ :=
  fun i j => if r i = j then w i else 0

theorem weightedInvolution_symmetric (r : ι → ι) (hr : Function.Involutive r)
    (w : ι → ℝ) (hw : ∀ i, w (r i) = w i) :
    (weightedInvolution r w).transpose = weightedInvolution r w := by
  ext i j
  have hrel : r j = i ↔ r i = j := by
    constructor
    · intro h
      rw [← h, hr]
    · intro h
      rw [← h, hr]
  by_cases h : r i = j
  · have hj : j = r i := h.symm
    subst j
    simp [weightedInvolution, hr i, hw]
  · simp [Matrix.transpose_apply, weightedInvolution, h, hrel]

theorem weightedInvolution_square (r : ι → ι) (hr : Function.Involutive r)
    (w : ι → ℝ) (hw : ∀ i, w (r i) = w i) :
    weightedInvolution r w * weightedInvolution r w = diagonal (fun i => w i ^ 2) := by
  ext i j
  rw [Matrix.mul_apply]
  have hsum : (∑ k : ι, weightedInvolution r w i k * weightedInvolution r w k j) =
      w i * weightedInvolution r w (r i) j := by
    rw [Finset.sum_eq_single (r i)]
    · simp [weightedInvolution]
    · intro b hb hbi
      simp [weightedInvolution, Ne.symm hbi]
    · simp
  rw [hsum]
  by_cases h : i = j
  · subst j
    simp [weightedInvolution, hr i, hw, pow_two]
  · simp [weightedInvolution, hr i, h]

theorem diagonal_weighted_anticommutator (r : ι → ι) (d w : ι → ℝ)
    (h : ∀ i, (d i + d (r i)) * w i = w i) :
    diagonal d * weightedInvolution r w + weightedInvolution r w * diagonal d =
      weightedInvolution r w := by
  ext i j
  simp only [Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  by_cases hij : r i = j
  · subst j
    simp only [weightedInvolution, ite_true]
    nlinarith [h i]
  · simp [weightedInvolution, hij]

/-- Two complementary signs of the weighted involution give the desired two projections. -/
theorem weighted_projections (r : ι → ι) (hr : Function.Involutive r)
    (d w : ι → ℝ) (hw : ∀ i, w (r i) = w i)
    (hsq : ∀ i, w i ^ 2 = d i - d i ^ 2)
    (hanti : ∀ i, (d i + d (r i)) * w i = w i) :
    let P := diagonal d + weightedInvolution r w
    let Q := diagonal d - weightedInvolution r w
    P.transpose = P ∧ Q.transpose = Q ∧ P * P = P ∧ Q * Q = Q ∧
      P + Q = diagonal (fun i => 2 * d i) := by
  dsimp only
  have hT := weightedInvolution_symmetric r hr w hw
  have hTT := weightedInvolution_square r hr w hw
  have hDT := diagonal_weighted_anticommutator r d w hanti
  have hDD : diagonal d * diagonal d + weightedInvolution r w * weightedInvolution r w =
      diagonal d := by
    rw [hTT, Matrix.diagonal_mul_diagonal, Matrix.diagonal_add]
    congr 1
    funext i
    rw [hsq i]
    ring
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · simp [Matrix.transpose_add, hT]
  · simp [Matrix.transpose_sub, hT]
  · calc
      _ = (diagonal d * diagonal d + weightedInvolution r w * weightedInvolution r w) +
          (diagonal d * weightedInvolution r w + weightedInvolution r w * diagonal d) := by
            noncomm_ring
      _ = _ := by rw [hDD, hDT]
  · calc
      _ = (diagonal d * diagonal d + weightedInvolution r w * weightedInvolution r w) -
          (diagonal d * weightedInvolution r w + weightedInvolution r w * diagonal d) := by
            noncomm_ring
      _ = _ := by rw [hDD, hDT]
  · ext i j
    by_cases h : i = j
    · subst j
      simp
      ring
    · simp [Matrix.diagonal_apply_ne _ h, h]

noncomputable def ramp {m : ℕ} (i : Fin m) : ℝ := (i : ℕ) / (m : ℝ)
noncomputable def weight {m : ℕ} (i : Fin m) : ℝ := Real.sqrt (ramp i * (1 - ramp i))

theorem ramp_nonneg {m : ℕ} (i : Fin m) : 0 ≤ ramp i := by unfold ramp; positivity

theorem ramp_lt_one {m : ℕ} [NeZero m] (i : Fin m) : ramp i < 1 := by
  have hm : (0 : ℝ) < m := Nat.cast_pos.mpr (NeZero.pos m)
  exact (div_lt_one hm).mpr (by exact_mod_cast i.isLt)

@[simp] theorem ramp_zero {m : ℕ} [NeZero m] : ramp (0 : Fin m) = 0 := by simp [ramp]
@[simp] theorem weight_zero {m : ℕ} [NeZero m] : weight (0 : Fin m) = 0 := by simp [weight]

theorem ramp_neg {m : ℕ} [NeZero m] {i : Fin m} (hi : i ≠ 0) :
    ramp (-i) = 1 - ramp i := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  rw [ramp, Fin.val_neg, if_neg hi, Nat.cast_sub (Nat.le_of_lt i.isLt)]
  unfold ramp
  field_simp

theorem weight_neg {m : ℕ} [NeZero m] (i : Fin m) : weight (-i) = weight i := by
  by_cases hi : i = 0
  · subst i
    simp
  · unfold weight
    rw [ramp_neg hi]
    congr 1
    ring

theorem weight_square {m : ℕ} [NeZero m] (i : Fin m) :
    weight i ^ 2 = ramp i - ramp i ^ 2 := by
  unfold weight
  rw [Real.sq_sqrt (mul_nonneg (ramp_nonneg i) (by linarith [ramp_lt_one i]))]
  ring

theorem ramp_weight_anticommutator {m : ℕ} [NeZero m] (i : Fin m) :
    (ramp i + ramp (-i)) * weight i = weight i := by
  by_cases hi : i = 0
  · subst i
    simp
  · rw [ramp_neg hi]
    ring

noncomputable def firstProjection {m : ℕ} [NeZero m] : Matrix (Fin m) (Fin m) ℝ :=
  diagonal ramp + weightedInvolution (fun i : Fin m => -i) weight

noncomputable def secondProjection {m : ℕ} [NeZero m] : Matrix (Fin m) (Fin m) ℝ :=
  diagonal ramp - weightedInvolution (fun i : Fin m => -i) weight

theorem first_pair {m : ℕ} [NeZero m] :
    (firstProjection : Matrix (Fin m) (Fin m) ℝ).transpose = firstProjection ∧
    (secondProjection : Matrix (Fin m) (Fin m) ℝ).transpose = secondProjection ∧
    firstProjection * firstProjection = (firstProjection : Matrix (Fin m) (Fin m) ℝ) ∧
    secondProjection * secondProjection = (secondProjection : Matrix (Fin m) (Fin m) ℝ) ∧
    firstProjection + secondProjection = diagonal (fun i : Fin m => 2 * ramp i) :=
  weighted_projections (fun i : Fin m => -i) neg_neg ramp weight weight_neg weight_square
    ramp_weight_anticommutator

noncomputable def reverseMatrix {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    Matrix (Fin m) (Fin m) ℝ := M.submatrix Fin.revPerm Fin.revPerm

@[simp] theorem reverseMatrix_mul {m : ℕ} (M N : Matrix (Fin m) (Fin m) ℝ) :
    reverseMatrix M * reverseMatrix N = reverseMatrix (M * N) := by
  exact Matrix.submatrix_mul_equiv M N Fin.revPerm Fin.revPerm Fin.revPerm

@[simp] theorem reverseMatrix_add {m : ℕ} (M N : Matrix (Fin m) (Fin m) ℝ) :
    reverseMatrix (M + N) = reverseMatrix M + reverseMatrix N := rfl

@[simp] theorem reverseMatrix_transpose {m : ℕ} (M : Matrix (Fin m) (Fin m) ℝ) :
    (reverseMatrix M).transpose = reverseMatrix M.transpose := rfl

theorem ramp_add_reverse {m : ℕ} [NeZero m] (i : Fin m) :
    2 * ramp i + 2 * ramp (Fin.revPerm i) = alpha m := by
  have hm : (m : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne m)
  have hin : i.val + 1 ≤ m := i.isLt
  simp only [ramp, Fin.revPerm_apply, Fin.val_rev, alpha]
  rw [Nat.cast_sub hin, Nat.cast_add, Nat.cast_one]
  field_simp
  ring

/-- The four real matrices of Proposition S3. -/
noncomputable def projections (m : ℕ) [NeZero m] : Input → Matrix (Fin m) (Fin m) ℝ :=
  ![firstProjection, secondProjection, reverseMatrix firstProjection, reverseMatrix secondProjection]

theorem projections_symmetric (m : ℕ) [NeZero m] (i : Input) :
    (projections m i).transpose = projections m i := by
  have h := first_pair (m := m)
  fin_cases i <;> simp [projections, h.1, h.2.1]

theorem projections_idempotent (m : ℕ) [NeZero m] (i : Input) :
    projections m i * projections m i = projections m i := by
  have h := first_pair (m := m)
  fin_cases i <;> simp [projections, h.2.2.1, h.2.2.2.1]

theorem projections_sum (m : ℕ) [NeZero m] :
    (∑ i : Input, projections m i) = alpha m • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  have h := first_pair (m := m)
  have hp := h.2.2.2.2
  simp only [Input, Fin.sum_univ_succ, projections, Matrix.cons_val_zero,
    Matrix.cons_val_succ, Fin.sum_univ_zero, add_zero]
  rw [← add_assoc, ← add_assoc, hp, add_assoc, ← reverseMatrix_add, hp]
  ext i j
  by_cases hij : i = j
  · subst j
    simpa [reverseMatrix] using ramp_add_reverse i
  · have hrev : Fin.revPerm i ≠ Fin.revPerm j := fun h => hij (Fin.revPerm.injective h)
    simp [Matrix.diagonal_apply_ne _ hij, reverseMatrix,
      Matrix.diagonal_apply_ne _ hrev, Matrix.one_apply_ne hij]

/-- Proposition S3, in the exact local dimension stated by the paper. -/
theorem exists_four_real_projections (m : ℕ) (hm : 3 ≤ m) :
    ∃ P : Input → Matrix (Fin m) (Fin m) ℝ,
      (∀ i, (P i).transpose = P i) ∧ (∀ i, P i * P i = P i) ∧
      (∑ i, P i) = alpha m • (1 : Matrix (Fin m) (Fin m) ℝ) := by
  letI : NeZero m := ⟨by omega⟩
  exact ⟨projections m, projections_symmetric m, projections_idempotent m, projections_sum m⟩

end FiniteConstruction
end QuantumBehaviors
