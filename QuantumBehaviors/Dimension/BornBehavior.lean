import QuantumBehaviors.Dimension.BehaviorFacts
import QuantumBehaviors.Dimension.Upper

namespace QuantumBehaviors
open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

noncomputable def FiniteStrategy.behavior {dA dB : ℕ} (s : FiniteStrategy dA dB) : Behavior :=
  fun x => (s.density * (effect (s.alice x.1) x.2.2.1 ⊗ₖ effect (s.bob x.2.1) x.2.2.2)).trace.re

theorem FiniteStrategy.realizes_behavior {dA dB : ℕ} (s : FiniteStrategy dA dB) :
    s.realizes s.behavior := by
  intro i j a b
  have hA : (effect (s.alice i) a).PosSemidef := by cases a; exact s.alice_complement_pos i; exact s.alice_pos i
  have hB : (effect (s.bob j) b).PosSemidef := by cases b; exact s.bob_complement_pos j; exact s.bob_pos j
  have h := (densityFunctional s.density s.density_pos).map_nonneg (hA.kronecker hB).nonneg
  apply Complex.ext
  · rfl
  · exact (RCLike.nonneg_iff.mp h).2.symm

variable {m : ℕ} [NeZero m]
noncomputable def permutationStrategy (P : Input → Matrix (Fin m) (Fin m) ℂ)
    (hself : ∀ i, (P i).conjTranspose = P i) (hP : ∀ i, P i * P i = P i)
    (π : LabelPermutation) : FiniteStrategy m m where
  density := entangledDensity
  density_pos := entangledDensity_positive
  density_trace := entangledDensity_trace
  alice := fun i => P (π i)
  bob := fun j => (P (π j)).transpose
  alice_pos := fun i => projection_positive (hself _) (hP _)
  alice_complement_pos := fun i => projection_complement_positive (hself _) (hP _)
  bob_pos := fun j => (projection_positive (hself _) (hP _)).transpose
  bob_complement_pos := fun j => by simpa using (projection_complement_positive (hself (π j)) (hP _)).transpose

lemma permutationStrategy_probability (P : Input → Matrix (Fin m) (Fin m) ℂ)
    (hself : ∀ i, (P i).conjTranspose = P i) (hP : ∀ i, P i * P i = P i)
    (π : LabelPermutation) (i j : Input) (a b : Bool) :
    (permutationStrategy P hself hP π).behavior (i,j,a,b) =
      (normalizedTrace (effect (P (π i)) a * effect (P (π j)) b)).re := by
  change (entangledDensity * (effect (P (π i)) a ⊗ₖ effect (P (π j)).transpose b)).trace.re = _
  have he : effect (P (π j)).transpose b = (effect (P (π j)) b).transpose := by
    cases b <;> simp [effect]
  rw [he, entangledDensity_born]

lemma normalized_symmetrized_trace_average (P : Input → Matrix (Fin m) (Fin m) ℂ)
    (i j : Input) (a b : Bool) :
    normalizedTrace (effect (symmetrized P i) a * effect (symmetrized P j) b) =
      (24 : ℂ)⁻¹ * ∑ π : LabelPermutation,
        normalizedTrace (effect (P (π i)) a * effect (P (π j)) b) := by
  have he (k : Input) (c : Bool) : effect (symmetrized P k) c =
      Matrix.blockDiagonal (fun π : LabelPermutation => effect (P (π k)) c) := by
    cases c
    · simp only [effect_false, symmetrized, ← Matrix.blockDiagonal_one, ← Matrix.blockDiagonal_sub]
      congr 1
    · rfl
  rw [he,he,← Matrix.blockDiagonal_mul,normalizedTrace_apply,Matrix.trace_blockDiagonal]
  simp only [normalizedTrace_apply, Fintype.card_prod, Fintype.card_fin, card_labelPermutation,
    Nat.cast_mul, Nat.cast_ofNat]
  rw [← Finset.mul_sum]
  simp [_root_.mul_inv_rev, mul_assoc]

lemma permutationStrategy_average (P : Input → Matrix (Fin m) (Fin m) ℂ)
    (hself : ∀ i, (P i).conjTranspose = P i) (hP : ∀ i, P i * P i = P i)
    {α : ℝ} (hsum : (∑ i, P i) = (α : ℂ) • 1) (x : Coordinate) :
    (24 : ℝ)⁻¹ * ∑ π : LabelPermutation, (permutationStrategy P hself hP π).behavior x = curve α x := by
  rcases x with ⟨i,j,a,b⟩
  have hQsq : ∀ i, symmetrized P i * symmetrized P i = symmetrized P i := symmetrized_idempotent P hP
  have hfirst : ∀ i, normalizedTrace (symmetrized P i) = (α / 4 : ℝ) := normalized_symmetrized_first P hsum
  have hb : normalizedTrace (effect (symmetrized P i) a * effect (symmetrized P j) b) = (curve α (i,j,a,b) : ℂ) := by
    by_cases hij : i = j
    · subst j
      cases a <;> cases b <;>
        simp [effect, curve, mul_sub, sub_mul, hQsq, map_sub, hfirst,
          Complex.ofReal_sub, Complex.ofReal_one]
      all_goals ring
    · have hsecond := normalized_symmetrized_second P hP hsum hij
      cases a <;> cases b <;>
        simp [effect, curve, hij, mul_sub, sub_mul, map_sub, hfirst, hsecond,
          Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_div, Complex.ofReal_ofNat]
      all_goals ring
  rw [normalized_symmetrized_trace_average] at hb
  have hr := congrArg Complex.re hb
  simpa [permutationStrategy_probability, map_sum, Complex.mul_re] using hr


end QuantumBehaviors
