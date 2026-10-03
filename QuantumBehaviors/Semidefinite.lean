import QuantumBehaviors.FiniteLifts
import Mathlib.Analysis.Matrix.Order

/-!
# Finite semidefinite representations really are semialgebraic

The proof uses a verified Gram-factor description of positive semidefinite matrices and the
proved projection theorem. This is equivalent to the paper's principal-minor route and avoids
assuming a principal-minor criterion. Arbitrary real affine coefficients and auxiliary variables
are supported, together with arbitrary finite affine equalities.
-/
namespace QuantumBehaviors

open Matrix Set
open scoped BigOperators MatrixOrder

namespace IsSemialgebraic

lemma forall_finite {V J : Type*} [Fintype J] (C : J → Set (V → ℝ))
    (hC : ∀ j, IsSemialgebraic (C j)) : IsSemialgebraic {x | ∀ j, x ∈ C j} := by
  classical
  have hfin : ∀ s : Finset J, IsSemialgebraic {x | ∀ j ∈ s, x ∈ C j} := by
    intro s
    induction s using Finset.induction_on with
    | empty => simpa using (IsSemialgebraic.univ (ι := V))
    | @insert j s hjs ih =>
        have h := (hC j).inter ih
        simpa only [Set.mem_inter_iff, Set.mem_setOf_eq, Finset.mem_insert, forall_eq_or_imp] using h
  simpa using hfin Finset.univ

lemma polynomial_zero {V : Type*} (p : MvPolynomial V ℝ) :
    IsSemialgebraic {x : V → ℝ | MvPolynomial.eval x p = 0} := by
  simpa only [sign_eq_zero_iff] using IsSemialgebraic.sign p 0

end IsSemialgebraic

abbrev MatrixCoordinate (n : ℕ) := Fin n × Fin n

def realMatrix {n : ℕ} (x : MatrixCoordinate n → ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => x (i, j)

theorem real_psd_iff_gram {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) :
    M.PosSemidef ↔ ∃ B : Matrix (Fin n) (Fin n) ℝ, M = B.transpose * B := by
  constructor
  · intro hM
    let B := CFC.sqrt M
    have hB : B.transpose = B := by simpa using (CFC.sqrt_nonneg M).isSelfAdjoint
    have hBB : B * B = M := CFC.sqrt_mul_sqrt_self M hM.nonneg
    exact ⟨B, by rw [hB, hBB]⟩
  · rintro ⟨B, rfl⟩
    simpa using Matrix.posSemidef_conjTranspose_mul_self B

noncomputable def gramPolynomial (n : ℕ) (ij : MatrixCoordinate n) :
    MvPolynomial (MatrixCoordinate n ⊕ MatrixCoordinate n) ℝ :=
  MvPolynomial.X (Sum.inl ij) - ∑ k : Fin n,
    MvPolynomial.X (Sum.inr (k, ij.1)) * MvPolynomial.X (Sum.inr (k, ij.2))

lemma eval_gramPolynomial (n : ℕ) (x y : MatrixCoordinate n → ℝ) (ij : MatrixCoordinate n) :
    MvPolynomial.eval (Sum.elim x y) (gramPolynomial n ij) =
      realMatrix x ij.1 ij.2 - ((realMatrix y).transpose * realMatrix y) ij.1 ij.2 := by
  simp [gramPolynomial, realMatrix, Matrix.mul_apply]

theorem real_psd_semialgebraic (n : ℕ) :
    IsSemialgebraic {x : MatrixCoordinate n → ℝ | (realMatrix x).PosSemidef} := by
  let Z : Set ((MatrixCoordinate n ⊕ MatrixCoordinate n) → ℝ) :=
    {z | ∀ ij, MvPolynomial.eval z (gramPolynomial n ij) = 0}
  have hZ : IsSemialgebraic Z := IsSemialgebraic.forall_finite _ fun ij =>
    IsSemialgebraic.polynomial_zero (gramPolynomial n ij)
  have hproj := hZ.project
  have heq : {x : MatrixCoordinate n → ℝ | (realMatrix x).PosSemidef} =
      {x | ∃ y : MatrixCoordinate n → ℝ, Sum.elim x y ∈ Z} := by
    ext x
    rw [Set.mem_setOf_eq, real_psd_iff_gram]
    constructor
    · rintro ⟨B, hB⟩
      refine ⟨fun ij => B ij.1 ij.2, ?_⟩
      intro ij
      rw [eval_gramPolynomial]
      change realMatrix x ij.1 ij.2 - (B.transpose * B) ij.1 ij.2 = 0
      rw [hB, sub_self]
    · rintro ⟨y, hy⟩
      refine ⟨realMatrix y, ?_⟩
      ext i j
      have h := hy (i, j)
      rw [eval_gramPolynomial, sub_eq_zero] at h
      exact h
  rwa [← heq] at hproj

noncomputable def AffineScalar.polynomial {V : Type*} [Fintype V] (a : AffineScalar V) : MvPolynomial V ℝ :=
  MvPolynomial.C a.constant + ∑ v, MvPolynomial.C (a.coefficient v) * MvPolynomial.X v

@[simp] theorem AffineScalar.eval_polynomial {V : Type*} [Fintype V] (a : AffineScalar V) (x : V → ℝ) :
    MvPolynomial.eval x a.polynomial = a.eval x := by simp [AffineScalar.polynomial, AffineScalar.eval]

theorem affine_psd_semialgebraic {V : Type*} [Fintype V] {n : ℕ} (A : AffineMatrix V n) :
    IsSemialgebraic {x : V → ℝ | (A.eval x).PosSemidef} := by
  have h := (real_psd_semialgebraic n).polynomial_preimage
    (fun ij : MatrixCoordinate n => (A ij.1 ij.2).polynomial)
  simpa only [AffineScalar.eval_polynomial, realMatrix, AffineMatrix.eval, Set.mem_preimage,
    Set.mem_setOf_eq] using h

theorem HasFiniteSDPLift.to_semialgebraic_lift {C : Set Behavior} (h : HasFiniteSDPLift C) :
    HasFiniteSemialgebraicLift C := by
  obtain ⟨r, k, e, size, A, L, hC⟩ := h
  let Z : Set ((Coordinate ⊕ Fin r) → ℝ) :=
    {x | (∀ i, (A i |>.eval x).PosSemidef) ∧ ∀ j, (L j).eval x = 0}
  refine ⟨r, Z, ?_, hC⟩
  apply IsSemialgebraic.inter
  · exact IsSemialgebraic.forall_finite _ fun i => affine_psd_semialgebraic (A i)
  · apply IsSemialgebraic.forall_finite
    intro j
    simpa only [AffineScalar.eval_polynomial] using IsSemialgebraic.polynomial_zero (L j).polynomial

/-- The semidefinite consequence of Corollary S11 has no imported projection assumption. -/
theorem intermediate_no_finite_sdp_lift {C : Set Behavior} (hq : Cq ⊆ C) (hqc : C ⊆ Cqc) :
    ¬ HasFiniteSDPLift C := fun h =>
  intermediate_no_finite_semialgebraic_lift hq hqc h.to_semialgebraic_lift

theorem quantum_no_finite_sdp_lift (t : Model) : ¬ HasFiniteSDPLift (quantumSet t) :=
  intermediate_no_finite_sdp_lift (cq_subset_quantumSet t) (quantumSet_subset_cqc t)

end QuantumBehaviors
