import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Algebra.Star.StarProjection
import Mathlib.Data.Matrix.Basic

/-! Finite matrices of bounded operators act on the genuine Hilbert direct sum. -/
namespace QuantumBehaviors.POVM
open Matrix
open scoped BigOperators
variable {J H : Type*} [Fintype J] [DecidableEq J]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

abbrev Amplification (J H : Type*) := PiLp 2 (fun _ : J => H)

noncomputable def matrixOperator (M : Matrix J J (H →L[ℂ] H)) :
    Amplification J H →L[ℂ] Amplification J H :=
  (PiLp.continuousLinearEquiv 2 ℂ (fun _ : J => H)).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.pi (fun i => ∑ j, (M i j).comp (PiLp.proj (𝕜 := ℂ) 2 (fun _ : J => H) j)))

@[simp] theorem matrixOperator_apply (M : Matrix J J (H →L[ℂ] H))
    (x : Amplification J H) (i : J) : matrixOperator M x i = ∑ j, M i j (x j) := by
  simp [matrixOperator,ContinuousLinearMap.sum_apply]

@[simp] theorem matrixOperator_one : matrixOperator (1 : Matrix J J (H →L[ℂ] H)) = 1 := by
  ext x i
  simp only [matrixOperator_apply,ContinuousLinearMap.one_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro b hb hbi
    simp [Matrix.one_apply,Ne.symm hbi]
  · simp

@[simp] theorem matrixOperator_zero : matrixOperator (0 : Matrix J J (H →L[ℂ] H)) = 0 := by
  ext x i
  simp

@[simp] theorem matrixOperator_add (M N : Matrix J J (H →L[ℂ] H)) :
    matrixOperator (M+N) = matrixOperator M+matrixOperator N := by
  ext x i
  simp [Matrix.add_apply,Finset.sum_add_distrib]

@[simp] theorem matrixOperator_sub (M N : Matrix J J (H →L[ℂ] H)) :
    matrixOperator (M-N) = matrixOperator M-matrixOperator N := by
  ext x i
  simp [Matrix.sub_apply,Finset.sum_sub_distrib]

@[simp] theorem matrixOperator_mul (M N : Matrix J J (H →L[ℂ] H)) :
    matrixOperator (M*N) = matrixOperator M*matrixOperator N := by
  ext x i
  simp only [matrixOperator_apply,Matrix.mul_apply,ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.mul_apply,map_sum]
  rw [Finset.sum_comm]

lemma matrixOperator_symmetric {M : Matrix J J (H →L[ℂ] H)} (hM : M.conjTranspose = M) :
    IsSelfAdjoint (matrixOperator M) := by
  apply ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr
  intro x y
  change inner ℂ (matrixOperator M x) y = inner ℂ x (matrixOperator M y)
  simp only [PiLp.inner_apply,matrixOperator_apply,sum_inner,inner_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro j hj
  have he : star (M i j) = M j i := congrFun (congrFun hM j) i
  rw [← he]
  exact (M i j).adjoint_inner_left _ _

theorem matrixOperator_projection {M : Matrix J J (H →L[ℂ] H)} (hM : IsStarProjection M) :
    IsStarProjection (matrixOperator M) := by
  constructor
  · change matrixOperator M * matrixOperator M = matrixOperator M
    rw [← matrixOperator_mul,hM.isIdempotentElem.eq]
  · exact matrixOperator_symmetric hM.isSelfAdjoint.star_eq

theorem matrixOperator_commute {M N : Matrix J J (H →L[ℂ] H)} (h : Commute M N) :
    Commute (matrixOperator M) (matrixOperator N) := by
  change matrixOperator M * matrixOperator N = matrixOperator N * matrixOperator M
  rw [← matrixOperator_mul,← matrixOperator_mul,h.eq]

noncomputable def initial (j : J) (v : H) : Amplification J H := WithLp.toLp 2 (Pi.single j v)

@[simp] theorem initial_apply (j i : J) (v : H) : initial j v i = if i=j then v else 0 := by
  simp [initial,Pi.single_apply]

@[simp] theorem initial_inner (j : J) (v w : H) : inner ℂ (initial j v) (initial j w) = inner ℂ v w := by
  rw [PiLp.inner_apply,Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [initial_apply,hbj]
  · simp

@[simp] theorem initial_norm (j : J) (v : H) : ‖initial j v‖ = ‖v‖ := by
  apply (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).mp
  rw [norm_sq_eq_re_inner (𝕜 := ℂ),norm_sq_eq_re_inner (𝕜 := ℂ),initial_inner]

lemma matrixOperator_initial (j i : J) (v : H) (M : Matrix J J (H →L[ℂ] H)) :
    matrixOperator M (initial j v) i = M i j v := by
  rw [matrixOperator_apply,Finset.sum_eq_single j]
  · simp
  · intro b hb hbj
    simp [initial_apply,hbj]
  · simp

theorem initial_expectation (j : J) (v : H) (M : Matrix J J (H →L[ℂ] H)) :
    inner ℂ (initial j v) (matrixOperator M (initial j v)) = inner ℂ v (M j j v) := by
  rw [PiLp.inner_apply,Finset.sum_eq_single j]
  · rw [matrixOperator_initial]
    simp
  · intro b hb hbj
    simp [initial_apply,hbj]
  · simp

end QuantumBehaviors.POVM
