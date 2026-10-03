import QuantumBehaviors.SpectralFull
import QuantumBehaviors.FiniteConstruction
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Tactic.IntervalCases

/-!
# Finite Hilbert-space witnesses and the full four-projection classification

Real symmetric projection matrices are transported first to complex matrices
and then through Mathlib's verified matrix/operator star-algebra equivalence.
Thus the finite construction and the dimension-independent necessity theorem
meet at the same bounded-operator notion of orthogonal projection.
-/

namespace QuantumBehaviors

namespace FiniteConstruction

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Real matrices act complex-linearly on the corresponding Euclidean space. -/
noncomputable def realMatrixToOperator : Matrix ι ι ℝ →ₐ[ℝ]
    (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) :=
  ((Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι)).toAlgEquiv.toAlgHom.restrictScalars ℝ).comp
    ((Algebra.ofId ℝ ℂ).mapMatrix)

/-- Real transpose becomes Hilbert-space adjoint under this map. -/
theorem realMatrixToOperator_star (M : Matrix ι ι ℝ) :
    star (realMatrixToOperator M) = realMatrixToOperator M.transpose := by
  change star (Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (M.map (algebraMap ℝ ℂ))) =
    Matrix.toEuclideanCLM (𝕜 := ℂ) (n := ι) (M.transpose.map (algebraMap ℝ ℂ))
  rw [← map_star]
  congr 1
  ext i j
  simp [Matrix.star_apply, Matrix.map_apply, Matrix.transpose_apply]

/-- Symmetric idempotent real matrices give genuine bounded orthogonal
projections on a complex Hilbert space. -/
theorem realMatrixToOperator_projection {M : Matrix ι ι ℝ}
    (hself : M.transpose = M) (hidem : M * M = M) :
    IsStarProjection (realMatrixToOperator M) := by
  constructor
  · change realMatrixToOperator M * realMatrixToOperator M = realMatrixToOperator M
    rw [← map_mul, hidem]
  · change star (realMatrixToOperator M) = realMatrixToOperator M
    rw [realMatrixToOperator_star, hself]

/-- The real-matrix construction has the exact same scalar sum after the
complex-Hilbert-space transport. -/
theorem realMatrixToOperator_sum (P : Input → Matrix ι ι ℝ) {α : ℝ}
    (hsum : (∑ i, P i) = α • (1 : Matrix ι ι ℝ)) :
    (∑ i, realMatrixToOperator (P i)) =
      algebraMap ℝ (EuclideanSpace ℂ ι →L[ℂ] EuclideanSpace ℂ ι) α := by
  rw [← map_sum, hsum, map_smul, map_one, Algebra.algebraMap_eq_smul_one]

/-- Proposition S3 as complex Hilbert operators, still in the exact dimension
`m` asserted in the paper. -/
theorem exists_four_hilbert_projections (m : ℕ) (hm : 3 ≤ m) :
    ∃ P : Input → EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
      (∀ i, IsStarProjection (P i)) ∧
      (∑ i, P i) = algebraMap ℝ
        (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) (alpha m) := by
  obtain ⟨P, hself, hidem, hsum⟩ := exists_four_real_projections m hm
  exact ⟨fun i => realMatrixToOperator (P i),
    fun i => realMatrixToOperator_projection (hself i) (hidem i),
    realMatrixToOperator_sum P hsum⟩

end FiniteConstruction

/-- A finite-dimensional bounded-operator witness with strictly positive
complex Hilbert dimension. -/
def FiniteFourProjectionScalar (α : ℝ) : Prop := ∃ m : ℕ, 0 < m ∧
  ∃ P : Input → EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m),
    (∀ i, IsStarProjection (P i)) ∧
    (∑ i, P i) = algebraMap ℝ
      (EuclideanSpace ℂ (Fin m) →L[ℂ] EuclideanSpace ℂ (Fin m)) α

/-- The five integer scalars have one-dimensional witnesses. -/
theorem finite_four_projection_integer (k : ℕ) (hk : k ≤ 4) :
    FiniteFourProjectionScalar (k : ℝ) := by
  let P : Input → EuclideanSpace ℂ (Fin 1) →L[ℂ] EuclideanSpace ℂ (Fin 1) :=
    fun i => if i.val < k then 1 else 0
  refine ⟨1, by decide, P, ?_, ?_⟩
  · intro i
    dsimp [P]
    split_ifs
    · exact IsStarProjection.one _
    · exact IsStarProjection.zero _
  · dsimp [P]
    simp only [Input, Fin.sum_univ_succ, Fin.sum_univ_zero, add_zero]
    interval_cases k <;> norm_num [map_ofNat]

/-- Every lower discrete parameter has a finite-dimensional witness. -/
theorem finite_four_projection_of_allowed {α : ℝ} (hα : Allowed α) :
    FiniteFourProjectionScalar α := by
  obtain ⟨m, hm, rfl⟩ := hα
  exact ⟨m, by omega, FiniteConstruction.exists_four_hilbert_projections m hm⟩

/-- Complementation preserves finite-dimensional realizability. -/
theorem FiniteFourProjectionScalar.complement {α : ℝ}
    (hα : FiniteFourProjectionScalar α) : FiniteFourProjectionScalar (4 - α) := by
  obtain ⟨m, hm, P, hP, hsum⟩ := hα
  refine ⟨m, hm, fun i => 1 - P i, fun i => (hP i).one_sub, ?_⟩
  rw [Finset.sum_sub_distrib, hsum, map_sub, map_ofNat]
  congr 1
  simp [Input]

/-- Every scalar in the full classification is realized in finite dimension. -/
theorem finite_four_projection_of_mem_sigmaFour {α : ℝ} (hα : α ∈ SigmaFour) :
    FiniteFourProjectionScalar α := by
  rcases hα with h | h | h | h | h | h | h
  · subst α; simpa using finite_four_projection_integer 0 (by decide)
  · subst α; simpa using finite_four_projection_integer 1 (by decide)
  · subst α; simpa using finite_four_projection_integer 2 (by decide)
  · subst α; simpa using finite_four_projection_integer 3 (by decide)
  · subst α; simpa using finite_four_projection_integer 4 (by decide)
  · exact finite_four_projection_of_allowed h
  · have hc := (finite_four_projection_of_allowed h).complement
    simpa only [sub_sub_cancel] using hc

/-- The full scalar classification, with an actual finite-dimensional
operator-model witness on the existence side. -/
theorem finite_four_projection_iff_mem_sigmaFour (α : ℝ) :
    FiniteFourProjectionScalar α ↔ α ∈ SigmaFour := by
  constructor
  · rintro ⟨m, hm, P, hP, hsum⟩
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    apply four_projections_mem_sigmaFour (hP 0) (hP 1) (hP 2) (hP 3)
    simpa only [Input, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      zero_add, add_zero, add_assoc] using hsum
  · exact finite_four_projection_of_mem_sigmaFour

/-- Scalar realizability on an arbitrary nonzero complex Hilbert space. -/
def HilbertFourProjectionScalar (α : ℝ) : Prop :=
  ∃ (H : Type) (_ : NormedAddCommGroup H) (_ : InnerProductSpace ℂ H)
    (_ : CompleteSpace H) (_ : Nontrivial H),
    ∃ P : Input → H →L[ℂ] H, (∀ i, IsStarProjection (P i)) ∧
      (∑ i, P i) = algebraMap ℝ (H →L[ℂ] H) α

/-- The complete KRS classification is proved here from reflection/descent and
the explicit finite construction, with no classification axiom. -/
theorem hilbert_four_projection_iff_mem_sigmaFour (α : ℝ) :
    HilbertFourProjectionScalar α ↔ α ∈ SigmaFour := by
  constructor
  · rintro ⟨H, hnorm, hinner, hcomplete, hnontrivial, P, hP, hsum⟩
    apply four_projections_mem_sigmaFour (hP 0) (hP 1) (hP 2) (hP 3)
    simpa only [Input, Fin.sum_univ_succ, Fin.sum_univ_zero, Fin.val_zero, Fin.val_succ,
      zero_add, add_zero, add_assoc] using hsum
  · intro hα
    obtain ⟨m, hm, P, hP, hsum⟩ := finite_four_projection_of_mem_sigmaFour hα
    letI : NeZero m := ⟨Nat.ne_of_gt hm⟩
    exact ⟨EuclideanSpace ℂ (Fin m), inferInstance, inferInstance, inferInstance,
      inferInstance, P, hP, hsum⟩

end QuantumBehaviors
