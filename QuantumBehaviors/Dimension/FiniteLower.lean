import QuantumBehaviors.Dimension.Coefficients

/-! Sharp denominator lower bounds for the actual mixed-density, binary-POVM model. -/
namespace QuantumBehaviors.Dimension

open Matrix
open scoped BigOperators Kronecker ComplexOrder MatrixOrder Matrix.Norms.L2Operator

theorem finite_strategy_dimension_bound {dA dB m : ℕ} (hm : 3 ≤ m)
    (s : FiniteStrategy dA dB) (p : Behavior) (hp : s.realizes p)
    (hsync : Synchronous p) (hF : witness p (alpha m) = 0) :
    m / Nat.gcd m 2 ≤ dA ∧ m / Nat.gcd m 2 ≤ dB := by
  have hdA : 0 < dA := by
    by_contra h
    have hz : dA = 0 := by omega
    subst dA
    have ht := s.density_trace
    simpa using ht
  have hdB : 0 < dB := by
    by_contra h
    have hz : dB = 0 := by omega
    subst dB
    have ht := s.density_trace
    simpa using ht
  letI : NeZero dA := ⟨Nat.ne_zero_of_lt hdA⟩
  letI : NeZero dB := ⟨Nat.ne_zero_of_lt hdB⟩
  let X : Input → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ := fun i => s.alice i ⊗ₖ 1
  let Y : Input → Matrix (Fin dA × Fin dB) (Fin dA × Fin dB) ℂ := fun i => 1 ⊗ₖ s.bob i
  have hX : ∀ i, (X i).PosSemidef := fun i => (s.alice_pos i).kronecker (Matrix.PosSemidef.one)
  have hY : ∀ i, (Y i).PosSemidef := fun i => Matrix.PosSemidef.one.kronecker (s.bob_pos i)
  have hX0 : ∀ i, (1 - X i).PosSemidef := by
    intro i
    change (effect (s.alice i ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) false).PosSemidef
    rw [effect_kronecker_one]
    exact (s.alice_complement_pos i).kronecker Matrix.PosSemidef.one
  have hY0 : ∀ i, (1 - Y i).PosSemidef := by
    intro i
    change (effect ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ s.bob i) false).PosSemidef
    rw [effect_one_kronecker]
    exact Matrix.PosSemidef.one.kronecker (s.bob_complement_pos i)
  have hreal : ∀ i j a b, (p (i,j,a,b) : ℂ) =
      (s.density * (effect (X i) a * effect (Y j) b)).trace := by
    intro i j a b
    dsimp [X, Y]
    rw [effect_kronecker_one, effect_one_kronecker, ← Matrix.mul_kronecker_mul, mul_one, one_mul]
    exact hp i j a b
  obtain ⟨hxy, hee, hgg, hs⟩ := density_support_identities s.density_pos s.density_trace X Y
    hX hX0 hY hY0 (fun i j => cross_kronecker_commute _ _) p hreal hsync hF
  obtain ⟨k, hk⟩ := density_has_nonzero_column s.density s.density_pos s.density_trace
  let v := fun j => CFC.sqrt s.density j k
  have hv : v ≠ 0 := hk
  have hvxy : ∀ i, X i *ᵥ v = Y i *ᵥ v := by
    intro i
    have h := column_of_mul_zero (hxy i) k
    simpa only [Matrix.sub_mulVec, sub_eq_zero] using h
  have hvee : ∀ i, ((s.alice i * s.alice i) ⊗ₖ (1 : Matrix (Fin dB) (Fin dB) ℂ)) *ᵥ v = X i *ᵥ v := by
    intro i
    have h := column_of_mul_zero (hee i) k
    have hh : X i *ᵥ v = (X i * X i) *ᵥ v := by
      simpa only [Matrix.sub_mulVec, sub_eq_zero] using h
    simpa only [X, ← Matrix.mul_kronecker_mul, one_mul] using hh.symm
  have hvgg : ∀ i, ((1 : Matrix (Fin dA) (Fin dA) ℂ) ⊗ₖ (s.bob i * s.bob i)) *ᵥ v = Y i *ᵥ v := by
    intro i
    have h := column_of_mul_zero (hgg i) k
    have hh : Y i *ᵥ v = (Y i * Y i) *ᵥ v := by
      simpa only [Matrix.sub_mulVec, sub_eq_zero] using h
    simpa only [Y, ← Matrix.mul_kronecker_mul, one_mul] using hh.symm
  have hvs : (∑ i, X i) *ᵥ v = (alpha m : ℂ) • v := by
    have h := column_of_mul_zero hs k
    simpa only [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec, sub_eq_zero] using h
  obtain ⟨hi, he, hg, hsa, hsb⟩ := coefficient_relations v s.alice s.bob hvxy hvee hvgg hvs
  have hΨ : reshape v ≠ 0 := reshape_ne_zero hv
  refine ⟨coefficient_range_dimension_bound hm (reshape v) hΨ s.alice
    (fun i => (s.bob i).transpose) hi he hsa, ?_⟩
  have ht : (reshape v).transpose ≠ 0 := by
    intro h
    apply hΨ
    simpa only [Matrix.transpose_transpose, Matrix.transpose_zero] using congrArg Matrix.transpose h
  apply coefficient_range_dimension_bound hm (reshape v).transpose ht s.bob
    (fun i => (s.alice i).transpose) _ hg hsb
  intro i
  simpa only [Matrix.transpose_mul, Matrix.transpose_transpose] using congrArg Matrix.transpose (hi i).symm

theorem curve_finite_strategy_dimension_bound {dA dB m : ℕ} (hm : 3 ≤ m)
    (s : FiniteStrategy dA dB) (hp : s.realizes (curve (alpha m))) :
    m / Nat.gcd m 2 ≤ dA ∧ m / Nat.gcd m 2 ≤ dB :=
  finite_strategy_dimension_bound hm s _ hp (curve_synchronous _) (curve_witness _)

end QuantumBehaviors.Dimension
