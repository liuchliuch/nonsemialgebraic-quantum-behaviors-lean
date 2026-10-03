import QuantumBehaviors.EntangledTrace
import Mathlib.Data.Fintype.Perm
import Mathlib.Data.Matrix.Block
import Mathlib.GroupTheory.Perm.Basic
import Mathlib.Tactic.LinearCombination

/-! Exact permutation symmetrization of four scalar-sum projections. -/
namespace QuantumBehaviors

open Matrix
open scoped BigOperators

abbrev LabelPermutation := Equiv.Perm Input

@[simp] theorem card_labelPermutation : Fintype.card LabelPermutation = 24 := by
  norm_num [LabelPermutation, Input, Fintype.card_perm, Nat.factorial]

lemma permutation_pair_transitive {i j k l : Input} (hij : i ≠ j) (hkl : k ≠ l) :
    ∃ e : LabelPermutation, e i = k ∧ e j = l := by
  let e₁ : LabelPermutation := Equiv.swap i k
  let e₂ : LabelPermutation := Equiv.swap (e₁ j) l
  have hi : e₁ i = k := Equiv.swap_apply_left i k
  have hj : e₁ j ≠ k := by
    intro h
    exact hij (e₁.injective (hi.trans h.symm))
  refine ⟨e₂ * e₁, ?_, ?_⟩
  · change e₂ (e₁ i) = k
    rw [hi]
    exact Equiv.swap_apply_of_ne_of_ne hj.symm hkl
  · exact Equiv.swap_apply_left (e₁ j) l

lemma sum_permutation_right (f : LabelPermutation → ℂ) (e : LabelPermutation) :
    (∑ π, f (π * e)) = ∑ π, f π := Equiv.sum_comp (Equiv.mulRight e) f

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def symmetrized (P : Input → Matrix ι ι ℂ) (i : Input) :
    Matrix (ι × LabelPermutation) (ι × LabelPermutation) ℂ :=
  Matrix.blockDiagonal fun π => P (π i)

@[simp] theorem symmetrized_trace (P : Input → Matrix ι ι ℂ) (i : Input) :
    (symmetrized P i).trace = ∑ π : LabelPermutation, (P (π i)).trace :=
  Matrix.trace_blockDiagonal _

@[simp] theorem symmetrized_product_trace (P : Input → Matrix ι ι ℂ) (i j : Input) :
    (symmetrized P i * symmetrized P j).trace =
      ∑ π : LabelPermutation, (P (π i) * P (π j)).trace := by
  rw [symmetrized, symmetrized, ← Matrix.blockDiagonal_mul, Matrix.trace_blockDiagonal]

theorem symmetrized_trace_uniform (P : Input → Matrix ι ι ℂ) (i k : Input) :
    (symmetrized P i).trace = (symmetrized P k).trace := by
  rw [symmetrized_trace, symmetrized_trace]
  have h := sum_permutation_right (fun π => (P (π i)).trace) (Equiv.swap i k)
  simpa only [Equiv.Perm.mul_apply, Equiv.swap_apply_left] using h.symm

theorem symmetrized_pair_uniform (P : Input → Matrix ι ι ℂ) {i j k l : Input}
    (hij : i ≠ j) (hkl : k ≠ l) :
    (symmetrized P i * symmetrized P j).trace =
      (symmetrized P k * symmetrized P l).trace := by
  rw [symmetrized_product_trace, symmetrized_product_trace]
  obtain ⟨e, hi, hj⟩ := permutation_pair_transitive hij hkl
  have h := sum_permutation_right (fun π => (P (π i) * P (π j)).trace) e
  simpa only [Equiv.Perm.mul_apply, hi, hj] using h.symm

theorem symmetrized_idempotent (P : Input → Matrix ι ι ℂ) (hP : ∀ i, P i * P i = P i)
    (i : Input) : symmetrized P i * symmetrized P i = symmetrized P i := by
  rw [symmetrized, ← Matrix.blockDiagonal_mul]
  congr 1
  funext π
  exact hP (π i)

theorem symmetrized_selfadjoint (P : Input → Matrix ι ι ℂ)
    (hP : ∀ i, (P i).conjTranspose = P i) (i : Input) :
    (symmetrized P i).conjTranspose = symmetrized P i := by
  ext ⟨r, π⟩ ⟨s, σ⟩
  by_cases h : π = σ
  · subst σ
    simpa [symmetrized, Matrix.conjTranspose_apply, Matrix.blockDiagonal_apply] using
      congrFun (congrFun (hP (π i)) r) s
  · simp [symmetrized, Matrix.conjTranspose_apply, Matrix.blockDiagonal_apply, h, Ne.symm h]

theorem symmetrized_sum (P : Input → Matrix ι ι ℂ) {α : ℂ}
    (hsum : (∑ i, P i) = α • (1 : Matrix ι ι ℂ)) :
    (∑ i, symmetrized P i) = α • (1 : Matrix (ι × LabelPermutation) (ι × LabelPermutation) ℂ) := by
  ext ⟨r, π⟩ ⟨s, σ⟩
  by_cases h : π = σ
  · subst σ
    have hperm : (∑ i : Input, P (π i)) = ∑ i, P i := Equiv.sum_comp π P
    have h := congrFun (congrFun (hperm.trans hsum) r) s
    simpa [symmetrized, Matrix.sum_apply, Matrix.blockDiagonal_apply, Matrix.one_apply] using h
  · simp [symmetrized, Matrix.sum_apply, Matrix.blockDiagonal_apply, h, Matrix.one_apply]

theorem symmetrized_first_moment (P : Input → Matrix ι ι ℂ) {α : ℂ}
    (hsum : (∑ i, P i) = α • (1 : Matrix ι ι ℂ)) (i : Input) :
    (symmetrized P i).trace = 6 * α * (Fintype.card ι : ℂ) := by
  have h := congrArg Matrix.trace (symmetrized_sum P hsum)
  have hconst : ∀ j : Input, (symmetrized P j).trace = (symmetrized P i).trace :=
    fun j => symmetrized_trace_uniform P j i
  simp only [Matrix.trace_sum, Matrix.trace_smul, Matrix.trace_one, Fintype.card_prod,
    card_labelPermutation, Nat.cast_mul, Nat.cast_ofNat, smul_eq_mul] at h
  simp only [hconst, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h
  change 4 * (symmetrized P i).trace = α * ((Fintype.card ι : ℂ) * 24) at h
  linear_combination (1 / 4 : ℂ) * h

theorem symmetrized_second_moment (P : Input → Matrix ι ι ℂ) {α : ℂ}
    (hP : ∀ i, P i * P i = P i) (hsum : (∑ i, P i) = α • (1 : Matrix ι ι ℂ))
    {i j : Input} (hij : i ≠ j) :
    (symmetrized P i * symmetrized P j).trace =
      2 * (α ^ 2 - α) * (Fintype.card ι : ℂ) := by
  let Q := symmetrized P
  have hsumQ := symmetrized_sum P hsum
  have htotal : (∑ r : Input, ∑ s : Input, (Q r * Q s).trace) =
      α ^ 2 * ((Fintype.card ι : ℂ) * 24) := by
    have htrace : ((∑ r, Q r) * (∑ s, Q s)).trace =
        ∑ r, ∑ s, (Q r * Q s).trace := by
      rw [Finset.sum_mul_sum]
      simp only [Matrix.trace_sum]
    rw [← htrace]
    change ((∑ r, symmetrized P r) * (∑ s, symmetrized P s)).trace = _
    rw [hsumQ]
    simp [smul_mul_smul_comm, Matrix.trace_smul, Fintype.card_prod, pow_two, mul_assoc]
  have hentry : ∀ r s : Input, (Q r * Q s).trace =
      if r = s then 6 * α * (Fintype.card ι : ℂ) else (Q i * Q j).trace := by
    intro r s
    by_cases hrs : r = s
    · subst s
      simp only [↓reduceIte]
      rw [symmetrized_idempotent P hP, symmetrized_first_moment P hsum]
    · simp only [hrs, ↓reduceIte]
      exact symmetrized_pair_uniform P hrs hij
  have hrewrite : (∑ r : Input, ∑ s : Input, (Q r * Q s).trace) =
      ∑ r : Input, ∑ s : Input,
        if r = s then 6 * α * (Fintype.card ι : ℂ) else (Q i * Q j).trace := by
    apply Finset.sum_congr rfl
    intro r hr
    apply Finset.sum_congr rfl
    intro s hs
    exact hentry r s
  rw [hrewrite] at htotal
  simp [Input, Fin.sum_univ_succ] at htotal
  change (Q i * Q j).trace = _
  linear_combination (1 / 12 : ℂ) * htotal

end QuantumBehaviors
