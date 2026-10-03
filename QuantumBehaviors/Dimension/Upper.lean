import QuantumBehaviors.FiniteRealization

/-! Explicit dimensions of the symmetrized finite Born realization. -/
namespace QuantumBehaviors
open Matrix
open scoped BigOperators Kronecker ComplexOrder
variable {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Fintype κ] [DecidableEq κ]

/-- Finite index types are exactly the same finite-dimensional model as natural dimensions. -/
theorem strategy_of_indexed_matrices (p : Behavior)
    (ρ : Matrix (ι × κ) (ι × κ) ℂ) (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (A : Input → Matrix ι ι ℂ) (B : Input → Matrix κ κ ℂ)
    (hA : ∀ i, (A i).PosSemidef) (hA0 : ∀ i, (1 - A i).PosSemidef)
    (hB : ∀ j, (B j).PosSemidef) (hB0 : ∀ j, (1 - B j).PosSemidef)
    (hreal : ∀ i j a b, (p (i, j, a, b) : ℂ) =
      (ρ * (effect (A i) a ⊗ₖ effect (B j) b)).trace) : ∃ s : FiniteStrategy (Fintype.card ι) (Fintype.card κ), s.realizes p := by
  let e : Fin (Fintype.card ι) ≃ ι := (Fintype.equivFin ι).symm
  let f : Fin (Fintype.card κ) ≃ κ := (Fintype.equivFin κ).symm
  let g := Equiv.prodCongr e f
  let s : FiniteStrategy (Fintype.card ι) (Fintype.card κ) := {
    density := ρ.submatrix g g
    density_pos := hρ.submatrix g
    density_trace := (trace_submatrix_equiv g ρ).trans htr
    alice := fun i => (A i).submatrix e e
    bob := fun j => (B j).submatrix f f
    alice_pos := fun i => (hA i).submatrix e
    alice_complement_pos := fun i => by simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] using (hA0 i).submatrix e
    bob_pos := fun j => (hB j).submatrix f
    bob_complement_pos := fun j => by simpa only [Matrix.submatrix_sub, Pi.sub_apply, Matrix.submatrix_one_equiv] using (hB0 j).submatrix f }
  refine ⟨s, ?_⟩
  intro i j a b
  have hea : effect ((A i).submatrix e e) a = (effect (A i) a).submatrix e e := by
    cases a <;> simp [effect, Matrix.submatrix_sub, Matrix.submatrix_one_equiv]
  have heb : effect ((B j).submatrix f f) b = (effect (B j) b).submatrix f f := by
    cases b <;> simp [effect, Matrix.submatrix_sub, Matrix.submatrix_one_equiv]
  change (p (i, j, a, b) : ℂ) =
    (ρ.submatrix g g * (effect ((A i).submatrix e e) a ⊗ₖ effect ((B j).submatrix f f) b)).trace
  rw [hea, heb]
  have hk : (effect (A i) a).submatrix e e ⊗ₖ (effect (B j) b).submatrix f f =
      (effect (A i) a ⊗ₖ effect (B j) b).submatrix g g := rfl
  rw [hk, Matrix.submatrix_mul_equiv, trace_submatrix_equiv]
  exact hreal i j a b


/-- S7 sufficiency from an actual finite scalar-sum projection witness. -/
theorem curve_strategy_of_finite_projections (P : Input → Matrix ι ι ℂ) [Nonempty ι] {α : ℝ}
    (hself : ∀ i, (P i).conjTranspose = P i) (hP : ∀ i, P i * P i = P i)
    (hsum : (∑ i, P i) = (α : ℂ) • (1 : Matrix ι ι ℂ)) : ∃ s : FiniteStrategy (24 * Fintype.card ι) (24 * Fintype.card ι), s.realizes (curve α) := by
  let Q := symmetrized P
  have hQself := symmetrized_selfadjoint P hself
  have hQsq : ∀ i, Q i * Q i = Q i := symmetrized_idempotent P hP
  have hQpos : ∀ i, (Q i).PosSemidef := fun i => projection_positive (hQself i) (hQsq i)
  have hQzero : ∀ i, (1 - Q i).PosSemidef := fun i =>
    projection_complement_positive (hQself i) (hQsq i)
  have hcard : Fintype.card (ι × LabelPermutation) = 24 * Fintype.card ι := by simp [card_labelPermutation, Nat.mul_comm]
  rw [← hcard]
  apply strategy_of_indexed_matrices (curve α) entangledDensity entangledDensity_positive
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
theorem curve_exact_dimension_strategy {m : ℕ} (hm : 3 ≤ m) :
    ∃ s : FiniteStrategy (24 * m) (24 * m), s.realizes (curve (alpha m)) := by
  letI : NeZero m := ⟨by omega⟩
  obtain ⟨P, hself, hP, hsum⟩ := FiniteConstruction.exists_four_real_projections m hm
  let f : Matrix (Fin m) (Fin m) ℝ →ₐ[ℝ] Matrix (Fin m) (Fin m) ℂ :=
    (Algebra.ofId ℝ ℂ).mapMatrix
  have h : Fintype.card (Fin m) = m := Fintype.card_fin m
  rw [← h]
  apply curve_strategy_of_finite_projections (fun i => f (P i))
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
