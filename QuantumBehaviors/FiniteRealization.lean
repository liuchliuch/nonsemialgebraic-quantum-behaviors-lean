import QuantumBehaviors.FiniteReindex
import QuantumBehaviors.Symmetrization
import QuantumBehaviors.FiniteConstruction
import Mathlib.Tactic.FieldSimp

/-! The actual finite-dimensional Born realization of every allowed point. -/
namespace QuantumBehaviors

open Matrix
open scoped BigOperators Kronecker ComplexOrder

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

noncomputable def normalizedTrace : Matrix ι ι ℂ →ₗ[ℂ] ℂ :=
  (Fintype.card ι : ℂ)⁻¹ • Matrix.traceLinearMap ι ℂ ℂ

theorem normalizedTrace_apply (M : Matrix ι ι ℂ) :
    normalizedTrace M = (Fintype.card ι : ℂ)⁻¹ * M.trace := rfl

@[simp] theorem normalizedTrace_one [Nonempty ι] :
    normalizedTrace (1 : Matrix ι ι ℂ) = 1 := by
  simp [normalizedTrace_apply, Fintype.card_ne_zero]

theorem entangledDensity_born (X Y : Matrix ι ι ℂ) :
    (entangledDensity * (X ⊗ₖ Y.transpose)).trace = normalizedTrace (X * Y) := by
  rw [entangledDensity_trace_kronecker, normalizedTrace_apply]
  simp [Complex.real_smul, Complex.ofReal_div]

theorem normalized_symmetrized_first (P : Input → Matrix ι ι ℂ) [Nonempty ι] {α : ℝ}
    (hsum : (∑ i, P i) = (α : ℂ) • (1 : Matrix ι ι ℂ)) (i : Input) :
    normalizedTrace (symmetrized P i) = (α / 4 : ℝ) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [normalizedTrace_apply, symmetrized_first_moment P hsum]
  simp only [Fintype.card_prod, card_labelPermutation, Nat.cast_mul, Nat.cast_ofNat,
    Complex.ofReal_div, Complex.ofReal_ofNat]
  field_simp
  ring

theorem normalized_symmetrized_second (P : Input → Matrix ι ι ℂ) [Nonempty ι] {α : ℝ}
    (hP : ∀ i, P i * P i = P i)
    (hsum : (∑ i, P i) = (α : ℂ) • (1 : Matrix ι ι ℂ))
    {i j : Input} (hij : i ≠ j) :
    normalizedTrace (symmetrized P i * symmetrized P j) = (α * (α - 1) / 12 : ℝ) := by
  have hd : (Fintype.card ι : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [normalizedTrace_apply, symmetrized_second_moment P hP hsum hij]
  simp only [Fintype.card_prod, card_labelPermutation, Nat.cast_mul, Nat.cast_ofNat,
    Complex.ofReal_div, Complex.ofReal_mul, Complex.ofReal_sub, Complex.ofReal_one,
    Complex.ofReal_ofNat]
  field_simp
  ring

/-- S7 sufficiency from an actual finite scalar-sum projection witness. -/
theorem curve_mem_cq_of_finite_projections (P : Input → Matrix ι ι ℂ) [Nonempty ι] {α : ℝ}
    (hself : ∀ i, (P i).conjTranspose = P i) (hP : ∀ i, P i * P i = P i)
    (hsum : (∑ i, P i) = (α : ℂ) • (1 : Matrix ι ι ℂ)) : curve α ∈ Cq := by
  let Q := symmetrized P
  have hQself := symmetrized_selfadjoint P hself
  have hQsq : ∀ i, Q i * Q i = Q i := symmetrized_idempotent P hP
  have hQpos : ∀ i, (Q i).PosSemidef := fun i => projection_positive (hQself i) (hQsq i)
  have hQzero : ∀ i, (1 - Q i).PosSemidef := fun i =>
    projection_complement_positive (hQself i) (hQsq i)
  apply cq_of_indexed_matrices (curve α) entangledDensity entangledDensity_positive
    entangledDensity_trace Q (fun j => (Q j).transpose) hQpos hQzero
  · intro j
    exact (hQpos j).transpose
  · intro j
    simpa using (hQzero j).transpose
  · intro i j a b
    have hb : effect ((Q j).transpose) b = (effect (Q j) b).transpose := by
      cases b <;> simp [effect]
    rw [hb, entangledDensity_born]
    have hfirst : ∀ i, normalizedTrace (Q i) = (α / 4 : ℝ) :=
      normalized_symmetrized_first P hsum
    by_cases hij : i = j
    · subst j
      cases a <;> cases b <;>
        simp [effect, curve, mul_sub, sub_mul, hQsq, map_sub, map_add, hfirst,
          Complex.ofReal_sub, Complex.ofReal_one]
      all_goals ring
    · have hsecond := normalized_symmetrized_second P hP hsum hij
      change normalizedTrace (Q i * Q j) = _ at hsecond
      cases a <;> cases b <;>
        simp [effect, curve, hij, mul_sub, sub_mul, map_sub, map_add, hfirst, hsecond,
          Complex.ofReal_sub, Complex.ofReal_add, Complex.ofReal_mul, Complex.ofReal_div,
          Complex.ofReal_ofNat]
      all_goals ring

/-- Every discrete parameter is realized by the density matrix and binary POVMs defining Cq. -/
theorem allowed_curve_mem_cq {α : ℝ} (hα : Allowed α) : curve α ∈ Cq := by
  obtain ⟨m, hm, rfl⟩ := hα
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨P, hself, hP, hsum⟩ := FiniteConstruction.exists_four_real_projections m hm
  let f : Matrix (Fin m) (Fin m) ℝ →ₐ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    (Algebra.ofId ℝ ℂ).mapMatrix
  apply curve_mem_cq_of_finite_projections (fun i => f (P i))
  · intro i
    change ((P i).map (algebraMap ℝ ℂ)).conjTranspose = (P i).map (algebraMap ℝ ℂ)
    ext r s
    have hs := congrFun (congrFun (hself i) r) s
    simpa [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply] using
      congrArg (fun x : ℝ => (x : ℂ)) hs
  · intro i
    rw [← map_mul, hP i]
  · rw [← map_sum, hsum, map_smul, map_one]
    ext i j
    simp [Complex.real_smul]

end QuantumBehaviors
