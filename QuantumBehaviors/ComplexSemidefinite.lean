import QuantumBehaviors.Semidefinite

/-! Complex Hermitian affine semidefinite lifts via exact real-coordinate Gram equations. -/
namespace QuantumBehaviors

open Matrix Set
open scoped BigOperators MatrixOrder ComplexOrder

theorem complex_psd_iff_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) :
    M.PosSemidef ↔ ∃ B : Matrix (Fin n) (Fin n) ℂ, M = B.conjTranspose * B := by
  constructor
  · intro hM
    let B := CFC.sqrt M
    have hB : B.conjTranspose = B := (CFC.sqrt_nonneg M).isSelfAdjoint
    have hBB : B * B = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
    exact ⟨B, by rw [hB, hBB]⟩
  · rintro ⟨B, rfl⟩
    exact Matrix.posSemidef_conjTranspose_mul_self B

noncomputable def complexGramPolynomial (n : ℕ) (c : ComplexMatrixCoordinate n) :
    MvPolynomial (ComplexMatrixCoordinate n ⊕ ComplexMatrixCoordinate n) ℝ :=
  MvPolynomial.X (Sum.inl c) - ∑ k : Fin n,
    if c.2.2 then
      MvPolynomial.X (Sum.inr (k,c.1,false)) * MvPolynomial.X (Sum.inr (k,c.2.1,true)) -
      MvPolynomial.X (Sum.inr (k,c.1,true)) * MvPolynomial.X (Sum.inr (k,c.2.1,false))
    else
      MvPolynomial.X (Sum.inr (k,c.1,false)) * MvPolynomial.X (Sum.inr (k,c.2.1,false)) +
      MvPolynomial.X (Sum.inr (k,c.1,true)) * MvPolynomial.X (Sum.inr (k,c.2.1,true))

lemma eval_complexGramPolynomial (n : ℕ) (x y : ComplexMatrixCoordinate n → ℝ)
    (i j : Fin n) (b : Bool) :
    MvPolynomial.eval (Sum.elim x y) (complexGramPolynomial n (i,j,b)) =
      if b then (complexMatrix x i j - ((complexMatrix y).conjTranspose * complexMatrix y) i j).im
      else (complexMatrix x i j - ((complexMatrix y).conjTranspose * complexMatrix y) i j).re := by
  cases b <;> simp [complexGramPolynomial, complexMatrix, Matrix.mul_apply, Complex.mul_re,
    Complex.mul_im, Complex.conj_re, Complex.conj_im, Matrix.conjTranspose_apply, ← sub_eq_add_neg, Finset.sum_sub_distrib]

theorem complex_psd_semialgebraic (n : ℕ) :
    IsSemialgebraic {x : ComplexMatrixCoordinate n → ℝ | (complexMatrix x).PosSemidef} := by
  let Z : Set ((ComplexMatrixCoordinate n ⊕ ComplexMatrixCoordinate n) → ℝ) :=
    {z | ∀ c, MvPolynomial.eval z (complexGramPolynomial n c) = 0}
  have hZ : IsSemialgebraic Z := IsSemialgebraic.forall_finite _ fun c =>
    IsSemialgebraic.polynomial_zero (complexGramPolynomial n c)
  have heq : {x : ComplexMatrixCoordinate n → ℝ | (complexMatrix x).PosSemidef} =
      {x | ∃ y : ComplexMatrixCoordinate n → ℝ, Sum.elim x y ∈ Z} := by
    ext x
    rw [Set.mem_setOf_eq, complex_psd_iff_gram]
    constructor
    · rintro ⟨B, hB⟩
      let y : ComplexMatrixCoordinate n → ℝ := fun c => if c.2.2 then (B c.1 c.2.1).im else (B c.1 c.2.1).re
      have hy : complexMatrix y = B := by ext i j <;> rfl
      refine ⟨y, ?_⟩
      rintro ⟨i,j,b⟩
      rw [eval_complexGramPolynomial, hy, hB]
      cases b <;> simp
    · rintro ⟨y, hy⟩
      refine ⟨complexMatrix y, ?_⟩
      apply Matrix.ext
      intro i j
      apply Complex.ext
      · have h := hy (i,j,false)
        simpa [eval_complexGramPolynomial, sub_eq_zero] using h
      · have h := hy (i,j,true)
        simpa [eval_complexGramPolynomial, sub_eq_zero] using h
  rw [heq]
  exact hZ.project

theorem complex_affine_psd_semialgebraic {V : Type*} [Fintype V] {n : ℕ}
    (A : ComplexAffineMatrix V n) : IsSemialgebraic {x : V → ℝ | (A.eval x).PosSemidef} := by
  have h := (complex_psd_semialgebraic n).polynomial_preimage (fun c => (A c).polynomial)
  simpa only [AffineScalar.eval_polynomial, ComplexAffineMatrix.eval,
    Set.mem_preimage, Set.mem_setOf_eq] using h

theorem HasFiniteComplexSDPLift.to_semialgebraic_lift {C : Set Behavior}
    (h : HasFiniteComplexSDPLift C) : HasFiniteSemialgebraicLift C := by
  obtain ⟨r,k,e,size,A,L,hC⟩ := h
  refine ⟨r, {x | (∀ i, (A i |>.eval x).PosSemidef) ∧ ∀ j, (L j).eval x = 0}, ?_, hC⟩
  apply IsSemialgebraic.inter
  · exact IsSemialgebraic.forall_finite _ fun i => complex_affine_psd_semialgebraic (A i)
  · apply IsSemialgebraic.forall_finite
    intro j
    simpa only [AffineScalar.eval_polynomial] using IsSemialgebraic.polynomial_zero (L j).polynomial

theorem intermediate_no_finite_complex_sdp_lift {C : Set Behavior}
    (hq : Cq ⊆ C) (hqc : C ⊆ Cqc) : ¬ HasFiniteComplexSDPLift C := fun h =>
  intermediate_no_finite_semialgebraic_lift hq hqc h.to_semialgebraic_lift

theorem quantum_no_finite_complex_sdp_lift (t : Model) :
    ¬ HasFiniteComplexSDPLift (quantumSet t) :=
  intermediate_no_finite_complex_sdp_lift (cq_subset_quantumSet t) (quantumSet_subset_cqc t)

end QuantumBehaviors
