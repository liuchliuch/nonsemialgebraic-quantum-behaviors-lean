import QuantumBehaviors.Dimension.NullState
import QuantumBehaviors.Basic

/-! The variance and synchrony identities on the original, undilated density support. -/
namespace QuantumBehaviors.Dimension

open Matrix
open scoped BigOperators ComplexOrder MatrixOrder Matrix.Norms.L2Operator

variable {ι : Type} [Fintype ι] [DecidableEq ι] [Nonempty ι]

lemma support_trace_congr {ρ A B : Matrix ι ι ℂ} (hρ : ρ.PosSemidef)
    (hAB : (A - B) * CFC.sqrt ρ = 0) (X : Matrix ι ι ℂ) :
    (ρ * (X * A)).trace = (ρ * (X * B)).trace := by
  have hroot : CFC.sqrt ρ * CFC.sqrt ρ = ρ := CFC.sqrt_mul_sqrt_self ρ hρ.nonneg
  have hzero : (A - B) * ρ = 0 := by
    rw [← hroot, ← Matrix.mul_assoc, hAB, zero_mul]
  have ht : (ρ * (X * (A - B))).trace = 0 := by
    rw [Matrix.trace_mul_cycle', ← Matrix.mul_assoc, hzero, zero_mul, Matrix.trace_zero]
  simpa only [mul_sub, Matrix.trace_sub, sub_eq_zero] using ht

lemma density_moment_variance {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (X : Input → Matrix ι ι ℂ) (hXself : ∀ i, (X i).conjTranspose = X i)
    (p : Behavior) (hfirst : ∀ i, (ρ * X i).trace = (p (i, i, true, true) : ℂ))
    (hsecond : ∀ i j, (ρ * (X i * X j)).trace = (p (i, j, true, true) : ℂ)) (α : ℝ) :
    (ρ * (((∑ i, X i) - (α : ℂ) • 1).conjTranspose *
      ((∑ i, X i) - (α : ℂ) • 1))).trace = (witness p α : ℂ) := by
  let S := ∑ i, X i
  let φ := densityFunctional ρ hρ
  have hS : S.conjTranspose = S := by
    simp only [S, Matrix.conjTranspose_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact hXself i
  have hself : (S - (α : ℂ) • (1 : Matrix ι ι ℂ)).conjTranspose = S - (α : ℂ) • 1 := by
    simp [hS]
  have hs : φ S = ∑ i, (p (i, i, true, true) : ℂ) := by
    change φ (∑ i, X i) = _
    rw [map_sum]
    exact Finset.sum_congr rfl fun i hi => hfirst i
  have hss : φ (S * S) = ∑ i, ∑ j, (p (i, j, true, true) : ℂ) := by
    change φ ((∑ i, X i) * ∑ j, X j) = _
    rw [Finset.sum_mul_sum]
    simp only [map_sum]
    apply Finset.sum_congr rfl
    intro i hi
    exact Finset.sum_congr rfl fun j hj => hsecond i j
  have hφ1 : φ (1 : Matrix ι ι ℂ) = 1 := by simpa [φ] using htr
  change φ ((S - (α : ℂ) • 1).conjTranspose * (S - (α : ℂ) • 1)) = _
  rw [hself]
  have hpoly : (S - (α : ℂ) • 1) * (S - (α : ℂ) • 1) =
      S * S - (α : ℂ) • S - (α : ℂ) • S + ((α : ℂ) ^ 2) • 1 := by
    simp only [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, one_mul, mul_one, smul_smul]
    module
  rw [hpoly]
  simp only [map_add, map_sub, map_smul, smul_eq_mul, hss, hs, hφ1, mul_one,
    witness, Complex.ofReal_add, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_pow,
    Complex.ofReal_sum, Complex.ofReal_ofNat]
  ring

/-- All support identities needed to retain the original local dimensions. -/
theorem density_support_identities {ρ : Matrix ι ι ℂ} (hρ : ρ.PosSemidef) (htr : ρ.trace = 1)
    (X Y : Input → Matrix ι ι ℂ)
    (hX : ∀ i, (X i).PosSemidef) (hX0 : ∀ i, (1 - X i).PosSemidef)
    (hY : ∀ i, (Y i).PosSemidef) (hY0 : ∀ i, (1 - Y i).PosSemidef)
    (hXY : ∀ i j, Commute (X i) (Y j)) (p : Behavior)
    (hreal : ∀ i j a b, (p (i, j, a, b) : ℂ) =
      (ρ * (effect (X i) a * effect (Y j) b)).trace)
    (hsync : Synchronous p) {α : ℝ} (hF : witness p α = 0) :
    (∀ i, (X i - Y i) * CFC.sqrt ρ = 0) ∧
    (∀ i, (X i - X i * X i) * CFC.sqrt ρ = 0) ∧
    (∀ i, (Y i - Y i * Y i) * CFC.sqrt ρ = 0) ∧
    ((∑ i, X i) - (α : ℂ) • 1) * CFC.sqrt ρ = 0 := by
  have hsupport : ∀ i, (X i - Y i) * CFC.sqrt ρ = 0 ∧
      (X i - X i * X i) * CFC.sqrt ρ = 0 ∧ (Y i - Y i * Y i) * CFC.sqrt ρ = 0 := by
    intro i
    apply synchronous_effect_support hρ (hX i) (hX0 i) (hY i) (hY0 i) (hXY i i)
    have h10 := hreal i i true false
    have h01 := hreal i i false true
    simp only [effect_true, effect_false] at h10 h01
    rw [mul_add, Matrix.trace_add, ← h10, ← h01]
    simp [(hsync i).1, (hsync i).2]
  have hsecond : ∀ i j, (ρ * (X i * X j)).trace = (p (i, j, true, true) : ℂ) := by
    intro i j
    rw [support_trace_congr hρ (hsupport j).1]
    exact (hreal i j true true).symm
  have hfirst : ∀ i, (ρ * X i).trace = (p (i, i, true, true) : ℂ) := by
    intro i
    have hv := support_trace_congr hρ (hsupport i).2.1 (1 : Matrix ι ι ℂ)
    simp only [one_mul] at hv
    exact hv.trans (hsecond i i)
  refine ⟨fun i => (hsupport i).1, fun i => (hsupport i).2.1, fun i => (hsupport i).2.2, ?_⟩
  apply density_square_zero hρ
  rw [density_moment_variance hρ htr X (fun i => (hX i).isHermitian.eq) p hfirst hsecond α, hF]
  rfl

end QuantumBehaviors.Dimension
